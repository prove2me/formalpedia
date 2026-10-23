-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P20.example4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T23:45:37.315482+00:00
-- url     : https://prove2.me/submissions/e5652263-8cb8-43e5-8109-95339a95c9ff

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

namespace X7Holevo

open QAlgorithms

variable {K : Type*} [Fintype K] {d : ℕ}

/-- The block of `X` at honest indices `(a,b)`. -/
def blk {a : ℕ} (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) (x y : Fin a) :
    Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i i' => X (x, i) (y, i')

/-- The partial pairing with an effect. -/
def Ymat {a : ℕ} (Fk : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    Matrix (Fin a) (Fin a) ℂ := Matrix.of fun x y => (Fk * blk X x y).trace

lemma idTensor_holevo {a : ℕ} (R F : K → Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    idTensorSuperop (Entanglement.holevoMap R F) X = ∑ k, Ymat (F k) X ⊗ₖ R k := by
  ext p q
  simp [idTensorSuperop, Entanglement.holevoMap, Matrix.kronecker, Matrix.sum_apply, Ymat, blk,
    Matrix.kroneckerMap_apply]

def Vmat {a : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (l : Fin d) : Matrix (Fin a × Fin d) (Fin a) ℂ :=
  fun p b => if p.1 = b then star (B l p.2) else 0

lemma Ymat_eq {a : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    Ymat (star B * B) X = ∑ l, (Vmat (a := a) B l)ᴴ * X * Vmat (a := a) B l := by
  ext x y
  simp only [Ymat, blk, Matrix.of_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.sum_apply, Matrix.conjTranspose_apply, Vmat, Matrix.star_apply]
  simp only [Fintype.sum_prod_type_right]
  simp only [apply_ite star, star_star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

lemma Ymat_psd {a : ℕ} {Fk : Matrix (Fin d) (Fin d) ℂ} (hF : Fk.PosSemidef)
    {X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ} (hX : X.PosSemidef) : (Ymat Fk X).PosSemidef := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin d) (Fin d) ℂ, Fk = star B * B := by
    open scoped MatrixOrder in
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hF.nonneg
  rw [hB, Ymat_eq]
  exact Matrix.posSemidef_sum _ (fun l _ => hX.conjTranspose_mul_mul_same _)

lemma holevo_cp (R F : K → Matrix (Fin d) (Fin d) ℂ) (hR : ∀ k, (R k).PosSemidef)
    (hF : ∀ k, (F k).PosSemidef) : Entanglement.IsCompletelyPositive (Entanglement.holevoMap R F) := by
  intro r X hX
  rw [idTensor_holevo]
  exact Matrix.posSemidef_sum _ (fun k _ => (Ymat_psd (hF k) hX).kronecker (hR k))

lemma holevo_eb [Fintype K] (R F : K → Matrix (Fin d) (Fin d) ℂ) (hR : ∀ k, IsDensityMatrix (R k))
    (hF : ∀ k, (F k).PosSemidef) : Entanglement.IsEntanglementBreakingPositive (Entanglement.holevoMap R F) := by
  intro a ha X hX
  rw [idTensor_holevo]
  let e := Fintype.equivFin K
  let D0 : Matrix (Fin a) (Fin a) ℂ := Matrix.diagonal (fun x => if x = ⟨0, ha⟩ then 1 else 0)
  have hD0 : IsDensityMatrix D0 := by
    refine ⟨?_, by simp [D0, Matrix.trace_diagonal]⟩
    rw [Matrix.posSemidef_diagonal_iff]
    intro x; split_ifs <;> norm_num
  let Y : K → Matrix (Fin a) (Fin a) ℂ := fun k => Ymat (F k) X
  have hY : ∀ k, (Y k).PosSemidef := fun k => Ymat_psd (hF k) hX.1
  refine ⟨Fintype.card K, fun j => (Y (e.symm j)).trace.re,
    fun j => if (Y (e.symm j)).trace = 0 then D0 else ((Y (e.symm j)).trace)⁻¹ • Y (e.symm j),
    fun j => R (e.symm j), fun j => ?_, fun j => ⟨?_, hR _⟩, ?_⟩
  · exact (RCLike.nonneg_iff.1 (hY _).trace_nonneg).1
  · dsimp only
    split_ifs with h
    · exact hD0
    · refine ⟨?_, ?_⟩
      · have hpos : 0 < (Y (e.symm j)).trace := lt_of_le_of_ne (hY _).trace_nonneg (Ne.symm h)
        exact (hY _).smul (inv_nonneg.2 hpos.le)
      · rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ h]
  · rw [← e.symm.sum_comp]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    dsimp only
    split_ifs with h
    · have h0 : Ymat (F (e.symm j)) X = 0 := (hY _).trace_eq_zero_iff.1 h
      have h1 : (Y (e.symm j)).trace.re = 0 := by simp [h]
      rw [h1, h0]
      simp
    · have him : (Y (e.symm j)).trace.im = 0 := by
        have := (RCLike.nonneg_iff.1 (hY (e.symm j)).trace_nonneg).2
        simpa using this
      have hre : ((Y (e.symm j)).trace.re : ℂ) = (Y (e.symm j)).trace :=
        Complex.ext (by simp) (by simp [him])
      rw [hre]
      ext p q
      simp only [Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, smul_eq_mul]
      change Y (e.symm j) p.1 q.1 * _ = _
      field_simp

end X7Holevo


namespace X7H20
open QAlgorithms.Papers.Independent.Frontier30.P20

def corner (d : ℕ) (i j : Fin d) : Prop := (i.val = 0 ∧ j.val + 1 = d) ∨ (j.val = 0 ∧ i.val + 1 = d)

instance (d : ℕ) (i j : Fin d) : Decidable (corner d i j) := by unfold corner; infer_instance

lemma X7_fromCoef_apply {d : ℕ} (M : Fin d × Fin d → Fin d × Fin d → ℂ) (X : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin d) : fromCoefficients M X i j = ∑ a, ∑ b, M (i, j) (a, b) * X a b := rfl

lemma X7_formula (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    negativeChannel d X i j =
      ((d : ℂ) + 1)⁻¹ * ((if corner d i j then X j i else X i j) + (if i = j then X.trace else 0)) := by
  simp only [negativeChannel, cornerTranspose, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, X7_fromCoef_apply]
  congr 1
  congr 1
  · unfold corner
    split_ifs with h
    · simp [h, ite_and, Prod.ext_iff]
    · simp [h, ite_and, Prod.ext_iff]
  · split_ifs with h
    · subst h; simp [Matrix.trace]
    · simp [h]


lemma X7_corner_iff (n : ℕ) (i j : Fin (n+2)) :
    corner (n+2) i j ↔ (i = 0 ∧ j = Fin.last (n+1)) ∨ (i = Fin.last (n+1) ∧ j = 0) := by
  unfold corner
  simp only [Fin.ext_iff, Fin.val_last, Fin.val_zero]
  omega

lemma X7_kraus_cp {d : ℕ} {ι : Type*} [Fintype ι]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (K : ι → Matrix (Fin d) (Fin d) ℂ) (h : ∀ X, Phi X = (c : ℂ) • ∑ k, K k * X * (K k)ᴴ) :
    QAlgorithms.Entanglement.IsCompletelyPositive Phi := by
  intro r X hX
  have hE : QAlgorithms.idTensorSuperop Phi X =
      (c : ℂ) • ∑ k, (Matrix.kronecker (1 : Matrix (Fin r) (Fin r) ℂ) (K k)) * X *
        (Matrix.kronecker (1 : Matrix (Fin r) (Fin r) ℂ) (K k))ᴴ := by
    ext p q
    simp only [QAlgorithms.idTensorSuperop, Matrix.of_apply, h, Matrix.smul_apply, Matrix.sum_apply]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.one_apply, ite_mul, one_mul, zero_mul, apply_ite star, star_mul',
      star_zero, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply, Finset.sum_mul]
  rw [hE]
  refine Matrix.PosSemidef.smul ?_ (by exact_mod_cast hc)
  exact Matrix.posSemidef_sum _ (fun k _ => hX.mul_mul_conjTranspose_same _)


/-- the Kraus family. -/
def krausK (n : ℕ) : Fin 3 ⊕ (Fin (n+2) × Fin (n+2)) → Matrix (Fin (n+2)) (Fin (n+2)) ℂ
  | Sum.inl 0 => 1
  | Sum.inl 1 => Matrix.single 0 (Fin.last (n+1)) 1 + Matrix.single (Fin.last (n+1)) 0 1
  | Sum.inl 2 => Matrix.single 0 0 1 - Matrix.single (Fin.last (n+1)) (Fin.last (n+1)) 1
  | Sum.inr ab => Matrix.single ab.1 ab.2
      (if (ab.1 = 0 ∨ ab.1 = Fin.last (n+1)) ∧ (ab.2 = 0 ∨ ab.2 = Fin.last (n+1)) then 0 else 1)

lemma X7_trace_split (n : ℕ) (X : Matrix (Fin (n+2)) (Fin (n+2)) ℂ) :
    X.trace = X 0 0 + X (Fin.last (n+1)) (Fin.last (n+1)) +
      ∑ b, (if b = 0 ∨ b = Fin.last (n+1) then 0 else X b b) := by
  have hne : (0 : Fin (n+2)) ≠ Fin.last (n+1) := by simp [Fin.ext_iff]
  have : ∀ b : Fin (n+2), X b b = (if b = 0 then X b b else 0) + (if b = Fin.last (n+1) then X b b else 0) +
      (if b = 0 ∨ b = Fin.last (n+1) then 0 else X b b) := by
    intro b
    by_cases h0 : b = 0
    · subst h0; simp [hne]
    · by_cases h1 : b = Fin.last (n+1)
      · subst h1; simp [h0]
      · simp [h0, h1]
  unfold Matrix.trace Matrix.diag
  conv_lhs => rw [Finset.sum_congr rfl (fun b _ => this b)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

lemma X7_kraus_eq (n : ℕ) (X : Matrix (Fin (n+2)) (Fin (n+2)) ℂ) :
    negativeChannel (n+2) X = ((((n+2 : ℕ) : ℝ) + 1)⁻¹ : ℝ) • ∑ k, krausK n k * X * (krausK n k)ᴴ := by
  have hne : (0 : Fin (n+2)) ≠ Fin.last (n+1) := by simp [Fin.ext_iff]
  ext i j
  rw [X7_formula]
  simp only [X7_corner_iff]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three, krausK, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sum_apply, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_single,
    Matrix.single_mul_mul_single, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul,
    Matrix.sub_apply, Matrix.single_apply, Fintype.sum_prod_type]
  push_cast
  simp only [star_one, mul_one, one_mul, smul_eq_mul]
  congr 1
  have hh : ∀ x : Fin (n+2), (if x = 0 ∨ x = Fin.last (n+1) then (0:ℂ) else
      if x = 0 ∨ x = Fin.last (n+1) then 0 else X x x) = if x = 0 ∨ x = Fin.last (n+1) then 0 else X x x :=
    fun x => by split_ifs <;> rfl
  by_cases hij : i = j
  · subst hij
    simp only [and_self, apply_ite star, star_one, star_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h0 : i = 0
    · subst h0
      rw [X7_trace_split]
      simp [hne, hne.symm]
      simp only [hh]; ring
    · by_cases h1 : i = Fin.last (n+1)
      · subst h1
        rw [X7_trace_split]
        simp [hne, hne.symm]
        simp only [hh]; ring
      · simp [h0, h1, Ne.symm h0, Ne.symm h1, Matrix.trace]
        ring
  · have hz : ∀ c : Fin (n+2), ¬ (c = i ∧ c = j) := fun c h => hij (h.1.symm.trans h.2)
    simp only [hz, if_false, Finset.sum_const_zero, hij, add_zero]
    by_cases h0 : i = 0
    · subst h0
      by_cases h1 : j = Fin.last (n+1)
      · subst h1; simp [hne, hne.symm]
      · simp [hne, hne.symm, h1, Ne.symm h1, hij, Ne.symm hij]
    · by_cases h1 : i = Fin.last (n+1)
      · subst h1
        by_cases h2 : j = 0
        · subst h2; simp [hne, hne.symm]
        · simp [hne, hne.symm, h2, Ne.symm h2, hij, Ne.symm hij]
      · simp [h0, h1, Ne.symm h0, Ne.symm h1]


lemma X7_channel (n : ℕ) : Channel (negativeChannel (n+2)) := by
  refine ⟨?_, ?_⟩
  · show QAlgorithms.Entanglement.IsCompletelyPositive (negativeChannel (n+2)).toLinearMap
    refine X7_kraus_cp _ ((((n+2 : ℕ) : ℝ) + 1)⁻¹) (by positivity) (krausK n) (fun X => ?_)
    rw [ContinuousLinearMap.coe_coe, X7_kraus_eq]
    rfl
  · intro X
    change (negativeChannel (n+2) X).trace = X.trace
    have hc : ∀ i : Fin (n+2), ¬ corner (n+2) i i := by
      intro i h
      rw [X7_corner_iff] at h
      have hne : (0 : Fin (n+2)) ≠ Fin.last (n+1) := by simp [Fin.ext_iff]
      rcases h with h | h
      · exact hne (h.1.symm.trans h.2)
      · exact hne (h.2.symm.trans h.1)
    unfold Matrix.trace Matrix.diag
    simp only [X7_formula, hc, if_false, if_true, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : ((n+2 : ℕ) : ℂ) + 1 ≠ 0 := by norm_cast
    field_simp
    push_cast
    simp only [Matrix.trace, Matrix.diag]
    ring


def swp (n : ℕ) : Equiv.Perm (Fin (n+2) × Fin (n+2)) :=
  Equiv.swap ((0 : Fin (n+2)), Fin.last (n+1)) (Fin.last (n+1), (0 : Fin (n+2)))

def vI (n : ℕ) : Fin (n+2) × Fin (n+2) → ℂ := fun p => if p.1 = p.2 then 1 else 0

lemma X7_coef_eq (n : ℕ) :
    QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction (negativeChannel (n+2)) =
      (((n+2 : ℕ) : ℂ) + 1)⁻¹ • ((swp n).permMatrix ℂ *
        (1 + Matrix.vecMulVec (vI n) (vI n))) := by
  have hne : (0 : Fin (n+2)) ≠ Fin.last (n+1) := by simp [Fin.ext_iff]
  have htr : ∀ x y : Fin (n+2), (Matrix.single x y (1:ℂ)).trace = if x = y then 1 else 0 := by
    intro x y
    split_ifs with h
    · subst h; exact Matrix.trace_single_eq_same _ _
    · exact Matrix.trace_single_eq_of_ne _ _ _ h
  ext p q
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  simp only [QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction, X7_formula, X7_corner_iff,
    Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, id, Matrix.add_apply,
    Matrix.vecMulVec_apply, Matrix.one_apply, vI, htr, Matrix.single_apply]
  congr 1
  clear htr
  obtain ⟨a, b⟩ := p
  obtain ⟨x, y⟩ := q
  simp only [swp, Equiv.swap_apply_def, Prod.mk.injEq]
  by_cases h1 : a = 0 <;> by_cases h2 : b = Fin.last (n+1) <;> by_cases h3 : a = Fin.last (n+1) <;>
    by_cases h4 : b = 0 <;> simp_all [eq_comm] <;> split_ifs <;> rfl


lemma X7_det (n : ℕ) : complexDet (negativeChannel (n+2)) =
    (-((((n+2 : ℕ) : ℂ) + 1) ^ (1 - (((n+2 : ℕ) : ℤ)) ^ 2))) := by
  have hne : (0 : Fin (n+2)) ≠ Fin.last (n+1) := by simp [Fin.ext_iff]
  have hne2 : ((0 : Fin (n+2)), Fin.last (n+1)) ≠ (Fin.last (n+1), (0 : Fin (n+2))) := by
    simp [Prod.ext_iff, hne]
  have hvv : vI n ⬝ᵥ vI n = ((n+2 : ℕ) : ℂ) := by
    simp [dotProduct, vI, Fintype.sum_prod_type]
  unfold complexDet
  rw [X7_coef_eq, Matrix.det_smul, Matrix.det_mul, Matrix.det_permutation, swp, Equiv.Perm.sign_swap hne2,
    Matrix.vecMulVec_eq (Fin 1), Matrix.det_one_add_replicateCol_mul_replicateRow, hvv]
  have hx : (((n+2 : ℕ) : ℂ) + 1) ≠ 0 := by norm_cast
  rw [show (1 : ℤ) - (((n+2 : ℕ) : ℤ)) ^ 2 = 1 - (((n+2)*(n+2) : ℕ) : ℤ) by push_cast; ring,
    zpow_sub₀ hx, zpow_one, zpow_natCast]
  simp only [Fintype.card_prod, Fintype.card_fin, inv_pow]
  field_simp
  push_cast
  ring


def cn (n : ℕ) (i j : Fin (n+2)) : Prop := (i = 0 ∧ j = Fin.last (n+1)) ∨ (i = Fin.last (n+1) ∧ j = 0)

instance (n : ℕ) (i j : Fin (n+2)) : Decidable (cn n i j) := by unfold cn; infer_instance

def Amat (n : ℕ) : Matrix (Fin (n+2) × Fin (n+2)) (Fin (n+2) × Fin (n+2)) ℂ := fun p q =>
  (if cn n p.1 q.1 then (if p.2 = q.1 ∧ q.2 = p.1 then 1 else 0) else (if p.2 = p.1 ∧ q.2 = q.1 then 1 else 0)) +
    (if p.1 = q.1 ∧ p.2 = q.2 then 1 else 0)

lemma X7_choi_eq (n : ℕ) : jamiolkowskiState (negativeChannel (n+2)) =
    ((((n+2 : ℕ) : ℂ))⁻¹ * (((n+2 : ℕ) : ℂ) + 1)⁻¹) • Amat n := by
  have htr : ∀ x y : Fin (n+2), (Matrix.single x y (1:ℂ)).trace = if x = y then 1 else 0 := by
    intro x y
    split_ifs with h
    · subst h; exact Matrix.trace_single_eq_same _ _
    · exact Matrix.trace_single_eq_of_ne _ _ _ h
  ext p q
  simp only [jamiolkowskiState, QAlgorithms.Papers.Independent.Information100.P50.choiMatrix,
    Matrix.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe, X7_formula, Amat, mul_assoc]
  congr 2
  have hc : corner (n+2) p.1 q.1 ↔ cn n p.1 q.1 := X7_corner_iff n _ _
  simp only [hc, htr, Matrix.single_apply]
  congr 1
  split_ifs <;> simp_all


lemma X7_mulVec (n : ℕ) (w : Fin (n+2) × Fin (n+2) → ℂ) (a b : Fin (n+2)) :
    (Amat n *ᵥ w) (a, b) = w (a, b) + (if cn n a b then w (b, a) else 0) +
      (if a = b then ∑ k, (if cn n a k then 0 else w (k, k)) else 0) := by
  have hsplit : ∀ x : Fin (n+2), ∀ f g : ℂ, (if cn n a x then f else g) =
      (if cn n a x then f else 0) + (if cn n a x then 0 else g) := by
    intro x f g; split_ifs <;> simp
  simp only [Matrix.mulVec, dotProduct, Amat, Fintype.sum_prod_type, add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, one_mul, zero_mul, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [add_comm (w (a, b)), add_right_comm _ (w (a, b))]
  congr 1
  rw [Finset.sum_congr rfl (fun x _ => hsplit x _ _), Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_congr rfl (fun x _ => (show (if cn n a x then (if b = x then w (x, a) else 0) else 0) =
        (if b = x then (if cn n a x then w (x, a) else 0) else 0) by split_ifs <;> rfl))]
    simp
  · by_cases hab : a = b
    · subst hab; simp
    · simp [Ne.symm hab, hab]


def uvec (n : ℕ) : Fin (n+2) × Fin (n+2) → ℂ := fun p =>
  if p = ((0 : Fin (n+2)), Fin.last (n+1)) then 1 else if p = (Fin.last (n+1), (0 : Fin (n+2))) then -1 else 0

lemma X7_sum_ne (n : ℕ) (f : Fin (n+2) → ℂ) (m : Fin (n+2)) :
    ∑ k, (if k = m then 0 else f k) = ∑ k, f k - f m := by
  have h : ∀ k, f k = (if k = m then 0 else f k) + (if k = m then f k else 0) := by
    intro k; split_ifs <;> simp
  conv_rhs => rw [Finset.sum_congr rfl (fun k _ => h k)]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma X7_ker (n : ℕ) : LinearMap.ker (Amat n).mulVecLin = Submodule.span ℂ {uvec n} := by
  have hne : (0 : Fin (n+2)) ≠ Fin.last (n+1) := by simp [Fin.ext_iff]
  have hcnd : ∀ a, ¬ cn n a a := by
    intro a h; rcases h with h | h
    · exact hne (h.1.symm.trans h.2)
    · exact hne (h.2.symm.trans h.1)
  ext w
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_span_singleton]
  constructor
  · intro h
    have E : ∀ a b, w (a, b) + (if cn n a b then w (b, a) else 0) +
        (if a = b then ∑ k, (if cn n a k then 0 else w (k, k)) else 0) = 0 := by
      intro a b; rw [← X7_mulVec]; exact congrFun h (a, b)
    have hoff : ∀ a b, a ≠ b → ¬ cn n a b → w (a, b) = 0 := by
      intro a b hab hc
      have := E a b
      simpa [hab, hc] using this
    have hcor : w ((Fin.last (n+1)), 0) = - w (0, (Fin.last (n+1))) := by
      have := E 0 (Fin.last (n+1))
      simp only [cn, true_and, and_true, hne, if_true, if_false, add_zero, true_or] at this
      linear_combination this
    set s := ∑ k, w (k, k) with hs
    have hS0 : ∑ k, (if cn n 0 k then 0 else w (k, k)) = s - w ((Fin.last (n+1)), (Fin.last (n+1))) := by
      rw [← X7_sum_ne n (fun k => w (k, k)) (Fin.last (n+1))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [cn, hne, hne.symm]
    have hSl : ∑ k, (if cn n (Fin.last (n+1)) k then 0 else w (k, k)) = s - w (0, 0) := by
      rw [← X7_sum_ne n (fun k => w (k, k)) 0]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [cn, hne, hne.symm]
    have hSm : ∀ a, a ≠ 0 → a ≠ (Fin.last (n+1)) → ∑ k, (if cn n a k then 0 else w (k, k)) = s := by
      intro a h0 h1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [cn, h0, h1]
    have E0 := E 0 0
    have El := E (Fin.last (n+1)) (Fin.last (n+1))
    simp only [hcnd, if_false, if_true, add_zero, hS0, hSl] at E0 El
    have hs0 : s = 0 := by linear_combination (E0 + El) / 2
    have hmid : ∀ a, a ≠ 0 → a ≠ (Fin.last (n+1)) → w (a, a) = 0 := by
      intro a h0 h1
      have := E a a
      simp only [hcnd, if_false, if_true, add_zero, hSm a h0 h1, hs0] at this
      exact this
    have hsplit := X7_trace_split n (Matrix.of fun i j => w (i, j))
    have hz : ∑ b, (if b = 0 ∨ b = (Fin.last (n+1)) then 0 else (Matrix.of fun i j => w (i, j)) b b) = 0 := by
      refine Finset.sum_eq_zero (fun b _ => ?_)
      split_ifs with hb
      · rfl
      · push_neg at hb; exact hmid b hb.1 hb.2
    rw [hz] at hsplit
    have htr : (Matrix.of fun i j => w (i, j)).trace = s := rfl
    rw [htr] at hsplit
    simp only [Matrix.of_apply, add_zero] at hsplit
    have h00 : w (0, 0) = 0 := by linear_combination (E0 - hsplit) / 2
    have hll : w ((Fin.last (n+1)), (Fin.last (n+1))) = 0 := by linear_combination -E0 + h00 + hs0
    refine ⟨w (0, (Fin.last (n+1))), ?_⟩
    funext ⟨a, b⟩
    simp only [Pi.smul_apply, uvec, smul_eq_mul, Prod.mk.injEq]
    by_cases hab : a = b
    · subst hab
      have h1 : ¬ (a = 0 ∧ a = (Fin.last (n+1))) := fun h => hne (h.1.symm.trans h.2)
      have h2 : ¬ (a = (Fin.last (n+1)) ∧ a = 0) := fun h => hne (h.2.symm.trans h.1)
      simp only [h1, h2, if_false, mul_zero]
      by_cases ha0 : a = 0
      · subst ha0; exact h00.symm
      · by_cases hal : a = (Fin.last (n+1))
        · subst hal; exact hll.symm
        · exact (hmid a ha0 hal).symm
    · by_cases hc : cn n a b
      · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp
        · simp [hne.symm, hcor]
      · have h1 : ¬ (a = 0 ∧ b = (Fin.last (n+1))) := fun h => hc (Or.inl h)
        have h2 : ¬ (a = (Fin.last (n+1)) ∧ b = 0) := fun h => hc (Or.inr h)
        simp only [h1, h2, if_false, mul_zero]
        exact (hoff a b hab hc).symm
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul]
    funext ⟨a, b⟩
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_eq_zero]
    right
    rw [X7_mulVec]
    have hd : ∀ k, uvec n (k, k) = 0 := by
      intro k
      have h1 : ¬ ((k, k) = ((0 : Fin (n+2)), Fin.last (n+1))) := by
        simp only [Prod.mk.injEq]; exact fun h => hne (h.1.symm.trans h.2)
      have h2 : ¬ ((k, k) = (Fin.last (n+1), (0 : Fin (n+2)))) := by
        simp only [Prod.mk.injEq]; exact fun h => hne (h.2.symm.trans h.1)
      simp [uvec, h1, h2]
    simp only [hd, ite_self, Finset.sum_const_zero, add_zero]
    by_cases hc : cn n a b
    · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [uvec, cn, hne, hne.symm]
      · simp [uvec, cn, hne, hne.symm]
    · have h1 : ¬ (a = 0 ∧ b = Fin.last (n+1)) := fun h => hc (Or.inl h)
      have h2 : ¬ (a = Fin.last (n+1) ∧ b = 0) := fun h => hc (Or.inr h)
      simp [uvec, hc, h1, h2]

lemma X7_rank (n : ℕ) : krausRank (negativeChannel (n+2)) = (n+2) ^ 2 - 1 := by
  have hu : uvec n ≠ 0 := by
    intro h
    have := congrFun h ((0 : Fin (n+2)), Fin.last (n+1))
    simp [uvec] at this
  have hA : (Amat n).rank = (n+2) ^ 2 - 1 := by
    unfold Matrix.rank
    have := LinearMap.finrank_range_add_finrank_ker (Amat n).mulVecLin
    rw [X7_ker, finrank_span_singleton hu, Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
      Fintype.card_fin] at this
    rw [sq]
    omega
  unfold krausRank
  rw [X7_choi_eq, Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero ?_), hA]
  have h1 : ((n+2 : ℕ) : ℂ) ≠ 0 := by norm_cast
  have h2 : ((n+2 : ℕ) : ℂ) + 1 ≠ 0 := by norm_cast
  exact mul_ne_zero (inv_ne_zero h1) (inv_ne_zero h2)


open QAlgorithms.Papers.Independent.Information100.P26 (outer) in
lemma X7_outer_sandwich (u v : Fin 2 → ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    twoSidedMap (outer u v) (outer u v)ᴴ X = ((outer v v) * X).trace • outer u u := by
  ext i j
  simp only [twoSidedMap, LinearMap.coe_toContinuousLinearMap',
    QAlgorithms.Papers.Independent.Dependency50.P16.sandwich, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, outer,
    Matrix.trace, Matrix.diag, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two, star_mul', star_star,
    Complex.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring


open QAlgorithms.Papers.Independent.Information100.P26 (outer) in
lemma X7_six_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    negativeChannel 2 X = (1 / 3 : ℂ) • ∑ j : Fin 6, ((outer (pauliEigenvectors j) (pauliEigenvectors j)) * X).trace •
      outer (fun k => conj (pauliEigenvectors j k)) (fun k => conj (pauliEigenvectors j k)) := by
  have hs : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    push_cast; ring
  have hc : conj ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  ext i j
  rw [X7_formula]
  fin_cases i <;> fin_cases j <;>
    simp [corner, outer, pauliEigenvectors, Fin.sum_univ_succ, Matrix.mul_apply, Matrix.trace, hc,
      Matrix.sum_apply] <;>
    (generalize ((Real.sqrt 2 : ℂ))⁻¹ = t at hs ⊢
     have ht2 : t ^ 2 = 1 / 2 := by rw [sq]; exact hs
     have ht4 : t ^ 4 = 1 / 4 := by rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2]; norm_num
     ring_nf
     simp only [ht2, ht4, Complex.I_sq, Complex.I_pow_four]
     ring_nf)


open QAlgorithms.Papers.Independent.Information100.P26 (outer) in
lemma X7_six : negativeChannel 2 = (1 / 3 : ℂ) • ∑ j : Fin 6,
        twoSidedMap (outer (fun k => conj (pauliEigenvectors j k)) (pauliEigenvectors j))
          (outer (fun k => conj (pauliEigenvectors j k)) (pauliEigenvectors j))ᴴ := by
  ext1 X
  rw [X7_six_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, X7_outer_sandwich]

open QAlgorithms.Papers.Independent.Information100.P26 (outer) in
lemma X7_eb : QAlgorithms.Entanglement.IsEntanglementBreakingPositive (negativeChannel 2).toLinearMap := by
  have hL : (negativeChannel 2).toLinearMap = QAlgorithms.Entanglement.holevoMap
      (fun j : Fin 6 => outer (fun k => conj (pauliEigenvectors j k)) (fun k => conj (pauliEigenvectors j k)))
      (fun j : Fin 6 => (1 / 3 : ℂ) • outer (pauliEigenvectors j) (pauliEigenvectors j)) := by
    ext1 X
    simp only [ContinuousLinearMap.coe_coe, X7_six_apply, QAlgorithms.Entanglement.holevoMap, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.smul_mul, Matrix.trace_smul, Finset.smul_sum, smul_smul, smul_eq_mul]
  rw [hL]
  have hs : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    push_cast; ring
  have hc : conj ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  have hpsd : ∀ u : Fin 2 → ℂ, (outer u u).PosSemidef := by
    intro u
    have : outer u u = Matrix.vecMulVec u (star u) := by
      ext i j; simp [outer, Matrix.vecMulVec]
    rw [this]; exact Matrix.posSemidef_vecMulVec_self_star u
  refine X7Holevo.holevo_eb _ _ (fun j => ⟨hpsd _, ?_⟩) (fun j => (hpsd _).smul (by norm_num [Complex.le_def]))
  fin_cases j <;> simp [outer, pauliEigenvectors, Matrix.trace, Fin.sum_univ_two, hc, hs] <;> norm_num <;> linear_combination (-(Complex.I ^ 2)) * hs + (-1/2 : ℂ) * Complex.I_sq

end X7H20

end

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

open QAlgorithms.Papers.Independent.Frontier30.P20
open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)
open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

theorem solution :
    (∀ d : ℕ, 2 ≤ d → Channel (negativeChannel d) ∧
      krausRank (negativeChannel d) = d ^ 2 - 1 ∧
      complexDet (negativeChannel d) = (-((d + 1 : ℂ) ^ (1 - (d : ℤ) ^ 2)))) ∧
    (QAlgorithms.Entanglement.IsEntanglementBreakingPositive
      (negativeChannel 2).toLinearMap ∧
      negativeChannel 2 = (1 / 3 : ℂ) • ∑ j : Fin 6,
        twoSidedMap (outer (fun k => conj (pauliEigenvectors j k)) (pauliEigenvectors j))
          (outer (fun k => conj (pauliEigenvectors j k)) (pauliEigenvectors j))ᴴ) := by
  refine ⟨fun d hd => ?_, X7H20.X7_eb, X7H20.X7_six⟩
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  exact ⟨X7H20.X7_channel n, X7H20.X7_rank n, X7H20.X7_det n⟩

end
