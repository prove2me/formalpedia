-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P23.completelyDephasingAttains
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:39:59.896321+00:00
-- url     : https://prove2.me/submissions/ba426639-4831-4f41-8bdb-9a71ec83c637

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23

noncomputable section

open scoped Matrix ComplexOrder Kronecker

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

end


noncomputable section

open scoped Matrix ComplexOrder Kronecker

namespace X7P23

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P23

lemma vn_sq {n : ℕ} (r : Fin n → ℝ) : vectorNorm r ^ 2 = ∑ i, r i ^ 2 := by
  unfold vectorNorm
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
  simp

lemma vn_nonneg {n : ℕ} (r : Fin n → ℝ) : 0 ≤ vectorNorm r := norm_nonneg _

lemma vn_smul {n : ℕ} (a : ℝ) (r : Fin n → ℝ) : vectorNorm (a • r) = |a| * vectorNorm r := by
  unfold vectorNorm
  rw [show (WithLp.toLp 2 (a • r) : EuclideanSpace ℝ (Fin n)) = a • WithLp.toLp 2 r from rfl,
    norm_smul, Real.norm_eq_abs]

variable (B : BlochBasis 2)

/-- `Σ s_j λ_j`. -/
def S (s : BlochVector 2) : Operator 2 := ∑ j, (s j : ℂ) • B.generator j

lemma blochState_eq (s : BlochVector 2) : blochState B s = (1 / 2 : ℂ) • (1 + S B s) := by
  unfold blochState S
  rw [smul_add]
  norm_num

lemma trace_gen_S (i : BlochIndex 2) (s : BlochVector 2) :
    (B.generator i * S B s).trace = 2 * (s i : ℂ) := by
  simp only [S, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, B.normalized,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma trace_S (s : BlochVector 2) : (S B s).trace = 0 := by
  simp [S, Matrix.trace_sum, Matrix.trace_smul, B.traceless]

lemma trace_gen_state (i : BlochIndex 2) (s : BlochVector 2) :
    (B.generator i * blochState B s).trace = (s i : ℂ) := by
  rw [blochState_eq, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.trace_smul,
    Matrix.trace_add, trace_gen_S, B.traceless]
  simp only [smul_eq_mul]; ring

lemma trace_state (s : BlochVector 2) : (blochState B s).trace = 1 := by
  rw [blochState_eq, Matrix.trace_smul, Matrix.trace_add, trace_S]
  simp [Matrix.trace_one]

lemma S_herm (s : BlochVector 2) : (S B s).IsHermitian := by
  unfold S Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.conjTranspose_smul, (B.hermitian j).eq]
  simp

lemma sq_traceless (T : Matrix (Fin 2) (Fin 2) ℂ) (h : T.trace = 0) :
    T * T = (T 0 0 * T 0 0 + T 0 1 * T 1 0) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.trace_fin_two] at h
  have h11 : T 1 1 = -T 0 0 := by linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11] <;> ring

lemma trace_S_mul (s : BlochVector 2) (M : Operator 2) :
    (S B s * M).trace = ∑ j, (s j : ℂ) * (B.generator j * M).trace := by
  simp only [S, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

lemma S_sq (s : BlochVector 2) :
    S B s * S B s = ((∑ j, s j ^ 2 : ℝ) : ℂ) • (1 : Operator 2) := by
  have h := sq_traceless (S B s) (trace_S B s)
  have htr : (S B s * S B s).trace = 2 * ((∑ j, s j ^ 2 : ℝ) : ℂ) := by
    rw [trace_S_mul]
    simp only [trace_gen_S]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  rw [h] at htr ⊢
  rw [Matrix.trace_smul, Matrix.trace_one] at htr
  simp only [Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul] at htr
  congr 1
  linear_combination htr / 2

lemma state_herm (s : BlochVector 2) : (blochState B s).IsHermitian := by
  rw [blochState_eq]
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one, (S_herm B s).eq]
  simp

lemma state_idem (s : BlochVector 2) (hs : vectorNorm s = 1) :
    blochState B s * blochState B s = blochState B s := by
  have h1 : (∑ j, s j ^ 2 : ℝ) = 1 := by rw [← vn_sq, hs]; norm_num
  rw [blochState_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, S_sq, h1]
  simp only [Complex.ofReal_one, one_smul]
  rw [add_comm (S B s) 1, ← add_smul]
  norm_num

lemma state_psd (s : BlochVector 2) (hs : vectorNorm s = 1) : (blochState B s).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (blochState B s)
  rwa [(state_herm B s).eq, state_idem B s hs] at h

lemma state_density (s : BlochVector 2) (hs : vectorNorm s = 1) :
    IsDensityMatrix (blochState B s) := ⟨state_psd B s hs, trace_state B s⟩

lemma cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma sqrt_trace_of_sq {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n ℂ)
    (hN : N.IsHermitian) (c : ℝ) (hc : 0 ≤ c) (hNN : N * N = (c : ℂ) • N)
    (htr : N.trace.re = c) : (cfc Real.sqrt N).trace.re = Real.sqrt c := by
  rw [cfc_trace hN]
  have heig : ∀ i, hN.eigenvalues i * (hN.eigenvalues i - c) = 0 := by
    intro i
    have hv0 := hN.mulVec_eigenvectorBasis i
    have hv : N *ᵥ ⇑(hN.eigenvectorBasis i) =
        ((hN.eigenvalues i : ℝ) : ℂ) • ⇑(hN.eigenvectorBasis i) := by
      rw [hv0]; ext k; simp [Complex.real_smul]
    have h2 : (N * N) *ᵥ ⇑(hN.eigenvectorBasis i) =
        (((hN.eigenvalues i : ℝ) : ℂ) * ((hN.eigenvalues i : ℝ) : ℂ)) • ⇑(hN.eigenvectorBasis i) := by
      rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, hv, smul_smul]
    have h2' : (N * N) *ᵥ ⇑(hN.eigenvectorBasis i) =
        ((c : ℂ) * ((hN.eigenvalues i : ℝ) : ℂ)) • ⇑(hN.eigenvectorBasis i) := by
      rw [hNN, Matrix.smul_mulVec, hv, smul_smul]
    have hne : (⇑(hN.eigenvectorBasis i) : n → ℂ) ≠ 0 := by
      intro h0
      have := (hN.eigenvectorBasis).orthonormal.1 i
      rw [show (hN.eigenvectorBasis i) = 0 from by
        ext k; exact congrFun h0 k] at this
      simp at this
    have h3 : ((((hN.eigenvalues i : ℝ) : ℂ) * ((hN.eigenvalues i : ℝ) : ℂ)) -
        (c : ℂ) * ((hN.eigenvalues i : ℝ) : ℂ)) • (⇑(hN.eigenvectorBasis i) : n → ℂ) = 0 := by
      rw [sub_smul, ← h2, ← h2', sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · have : ((hN.eigenvalues i * (hN.eigenvalues i - c) : ℝ) : ℂ) = 0 := by
        push_cast; linear_combination h
      exact_mod_cast this
    · exact absurd h hne
  have hsum : ∑ i, hN.eigenvalues i = c := by
    rw [← htr, hN.trace_eq_sum_eigenvalues]
    simp
  simp only [Complex.re_sum, Complex.ofReal_re]
  rcases eq_or_lt_of_le hc with h0 | hpos
  · subst h0
    have : ∀ i, hN.eigenvalues i = 0 := fun i => by
      have := heig i; simp at this; exact this
    simp [this]
  · have : ∀ i, Real.sqrt (hN.eigenvalues i) = hN.eigenvalues i / Real.sqrt c := by
      intro i
      rcases mul_eq_zero.1 (heig i) with h | h
      · rw [h]; simp
      · rw [show hN.eigenvalues i = c by linarith]
        field_simp
        rw [Real.sq_sqrt hc]
    simp only [this, ← Finset.sum_div, hsum]
    field_simp
    rw [Real.sq_sqrt hc]

lemma nuclear_rank_one {n : ℕ} (u m : Fin n → ℝ) (hm : ∑ j, m j ^ 2 = 1) :
    nuclearNorm (fun i j => u i * m j) = Real.sqrt (∑ i, u i ^ 2) := by
  unfold nuclearNorm traceNorm
  set M : Matrix (Fin n) (Fin n) ℂ := (Matrix.of fun i j => u i * m j).map fun x => (x : ℂ) with hM
  set U : ℝ := ∑ i, u i ^ 2 with hU
  have hent : ∀ i j, (Mᴴ * M) i j = ((U * m i * m j : ℝ) : ℂ) := by
    intro i j
    simp only [hM, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply,
      Complex.star_def, Complex.conj_ofReal, hU]
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun i _ => by positivity)
  apply sqrt_trace_of_sq _ (Matrix.isHermitian_conjTranspose_mul_self M) U hU0
  · ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply, hent]
    simp only [hent, smul_eq_mul]
    push_cast
    have hm' : ∑ k, (m k : ℂ) ^ 2 = 1 := by exact_mod_cast hm
    calc ∑ k, (U : ℂ) * m i * m k * (U * m k * m j)
        = (U : ℂ) * m i * (U * m j) * ∑ k, (m k : ℂ) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
      _ = _ := by rw [hm']; ring
  · rw [Matrix.trace]
    simp only [Matrix.diag, hent]
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re]
    calc ∑ i, U * m i * m i = U * ∑ i, m i ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
      _ = U := by rw [hm, mul_one]

lemma rank_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ≠ 0) : A.rank ≠ 0 := by
  intro h
  apply hA
  unfold Matrix.rank at h
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using this

variable (m s1 s2 : BlochVector 2)

lemma phi_apply (X : Operator 2) : projectivePreparation B m s1 s2 X =
    (blochState B m * X).trace • blochState B s1 + (blochState B (-m) * X).trace • blochState B s2 := by
  simp [projectivePreparation, Entanglement.holevoMap, Fin.sum_univ_two]

lemma trace_state_gen (s : BlochVector 2) (j : BlochIndex 2) :
    (blochState B s * B.generator j).trace = (s j : ℂ) := by
  rw [Matrix.trace_mul_comm, trace_gen_state]

lemma blochC_proj : blochC B (projectivePreparation B m s1 s2) = (1 / 2 : ℝ) • (s1 + s2) := by
  funext i
  simp only [blochC, coordinates, phi_apply, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    trace_state, Matrix.mul_add, Matrix.trace_add, trace_gen_state, smul_eq_mul]
  simp
  ring

lemma blochA_proj : blochA B (projectivePreparation B m s1 s2) =
    (fun i j => (1 / 2 : ℝ) * (s1 i - s2 i) * m j) := by
  funext i j
  simp only [blochA, phi_apply, trace_state_gen, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, trace_gen_state, smul_eq_mul]
  simp
  ring

end X7P23

namespace X7P23

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P23

lemma S_neg (B : BlochBasis 2) (m : BlochVector 2) : S B (-m) = -S B m := by
  simp [S, Finset.sum_neg_distrib]

lemma state_add_neg (B : BlochBasis 2) (m : BlochVector 2) :
    blochState B m + blochState B (-m) = 1 := by
  rw [blochState_eq, blochState_eq, S_neg, ← smul_add]
  rw [show (1 : Operator 2) + S B m + (1 + -S B m) = (2 : ℂ) • 1 by rw [two_smul]; abel, smul_smul]
  norm_num

lemma sum_sq_of_vn {n : ℕ} (r : Fin n → ℝ) (h : vectorNorm r = 1) : ∑ i, r i ^ 2 = 1 := by
  rw [← vn_sq, h]; norm_num

end X7P23


end


noncomputable section

open scoped Matrix ComplexOrder Kronecker

namespace X7P23D

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P23 X7P23

variable {d : ℕ}

lemma deph_apply (X : Operator d) :
    completelyDephasing d X = Matrix.diagonal (fun k => X k k) := by
  ext i j
  simp only [completelyDephasing, Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.trace_single_mul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp [Matrix.single_apply, Matrix.diagonal]
  · simp [Matrix.single_apply, Matrix.diagonal, h]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact h rfl

lemma single_psd (k : Fin d) : (Matrix.single k k (1 : ℂ)).PosSemidef := by
  rw [← Matrix.diagonal_single]
  · rw [Matrix.posSemidef_diagonal_iff]
    intro i; by_cases h : i = k <;> simp [Pi.single_apply, h]

lemma single_density (k : Fin d) : IsDensityMatrix (Matrix.single k k (1 : ℂ)) :=
  ⟨single_psd k, by simp⟩

/-- Generic: idempotent Hermitian matrices have `tr √N = tr N`. -/
lemma sqrt_trace_idem {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n ℂ)
    (hN : N.IsHermitian) (hNN : N * N = N) : (cfc Real.sqrt N).trace.re = N.trace.re := by
  rw [cfc_trace hN]
  have heig : ∀ i, hN.eigenvalues i * (hN.eigenvalues i - 1) = 0 := by
    intro i
    have hv0 := hN.mulVec_eigenvectorBasis i
    have hv : N *ᵥ ⇑(hN.eigenvectorBasis i) =
        ((hN.eigenvalues i : ℝ) : ℂ) • ⇑(hN.eigenvectorBasis i) := by
      rw [hv0]; ext k; simp [Complex.real_smul]
    have h2 : (N * N) *ᵥ ⇑(hN.eigenvectorBasis i) =
        (((hN.eigenvalues i : ℝ) : ℂ) * ((hN.eigenvalues i : ℝ) : ℂ)) • ⇑(hN.eigenvectorBasis i) := by
      rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, hv, smul_smul]
    rw [hNN, hv] at h2
    have hne : (⇑(hN.eigenvectorBasis i) : n → ℂ) ≠ 0 := by
      intro h0
      have := (hN.eigenvectorBasis).orthonormal.1 i
      rw [show (hN.eigenvectorBasis i) = 0 from by
        ext k; exact congrFun h0 k] at this
      simp at this
    have h3 : ((((hN.eigenvalues i : ℝ) : ℂ) * ((hN.eigenvalues i : ℝ) : ℂ)) -
        ((hN.eigenvalues i : ℝ) : ℂ)) • (⇑(hN.eigenvectorBasis i) : n → ℂ) = 0 := by
      rw [sub_smul, ← h2, sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · have : ((hN.eigenvalues i * (hN.eigenvalues i - 1) : ℝ) : ℂ) = 0 := by
        push_cast; linear_combination h
      exact_mod_cast this
    · exact absurd h hne
  have : ∀ i, Real.sqrt (hN.eigenvalues i) = hN.eigenvalues i := by
    intro i
    rcases mul_eq_zero.1 (heig i) with h | h
    · rw [h]; simp
    · rw [show hN.eigenvalues i = 1 by linarith]; simp
  rw [hN.trace_eq_sum_eigenvalues]
  simp [this, Complex.re_sum]

variable (B : BlochBasis d)

lemma gen_diag_real (i : BlochIndex d) (k : Fin d) : ((B.generator i) k k).im = 0 := by
  have := congrFun (congrFun (B.hermitian i).eq k) k
  simp [Matrix.conjTranspose_apply] at this
  have h2 := congrArg Complex.im this
  simp at h2; linarith

lemma trace_gen_deph (i j : BlochIndex d) :
    (B.generator i * completelyDephasing d (B.generator j)).trace =
      ∑ k, (B.generator i) k k * (B.generator j) k k := by
  rw [deph_apply]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal]

lemma diag_sq_sum (k : Fin d) (hd : 1 ≤ d) :
    ∑ i, ((B.generator i) k k).re ^ 2 = 2 * (1 - 1 / (d : ℝ)) := by
  set X : Operator d := Matrix.single k k 1 - (d : ℂ)⁻¹ • 1 with hX
  have hXh : X.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hX, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  have hXt : X.trace = 0 := by
    have : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    rw [hX, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp [this]
  have hrec := congrFun (congrFun (B.reconstruction X hXh hXt) k) k
  have hcoef : ∀ i, (B.generator i * X).trace.re = ((B.generator i) k k).re := by
    intro i
    rw [hX, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
      B.traceless, Matrix.trace_mul_single]
    simp
  simp only [hcoef, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul] at hrec
  rw [hX] at hrec
  simp at hrec
  have hre := congrArg Complex.re hrec
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  simp [Complex.re_sum, gen_diag_real] at hre
  simp only [sq, one_div]
  linarith [hre]

lemma A_symm (i j : BlochIndex d) : blochA B (completelyDephasing d) i j =
    blochA B (completelyDephasing d) j i := by
  simp only [blochA, trace_gen_deph]
  congr 2
  refine Finset.sum_congr rfl (fun k _ => mul_comm _ _)

lemma trace_A (hd : 1 ≤ d) : ∑ i, blochA B (completelyDephasing d) i i = (d : ℝ) - 1 := by
  simp only [blochA, trace_gen_deph, Complex.re_sum]
  have : ∀ i k, ((B.generator i) k k * (B.generator i) k k).re = ((B.generator i) k k).re ^ 2 := by
    intro i k; simp [Complex.mul_re, gen_diag_real, sq]
  simp only [this, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [diag_sq_sum B _ hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  field_simp <;> ring

lemma deph_herm (j : BlochIndex d) : (completelyDephasing d (B.generator j)).IsHermitian := by
  rw [deph_apply]
  unfold Matrix.IsHermitian
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  have := gen_diag_real B j k
  apply Complex.ext <;> simp [this]

lemma deph_traceless (j : BlochIndex d) : (completelyDephasing d (B.generator j)).trace = 0 := by
  rw [deph_apply, Matrix.trace_diagonal]
  have := B.traceless j
  rw [Matrix.trace] at this
  simpa using this

lemma deph_idem (X : Operator d) : completelyDephasing d (completelyDephasing d X) =
    completelyDephasing d X := by
  rw [deph_apply, deph_apply]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.diagonal, h]

lemma A_idem : blochA B (completelyDephasing d) * blochA B (completelyDephasing d) =
    blochA B (completelyDephasing d) := by
  ext i k
  have hrec := B.reconstruction _ (deph_herm B k) (deph_traceless B k)
  have key : (B.generator i * completelyDephasing d (B.generator k)).trace =
      (1 / 2 : ℂ) * ∑ j, ((B.generator j * completelyDephasing d (B.generator k)).trace.re : ℂ) *
        (B.generator i * completelyDephasing d (B.generator j)).trace := by
    conv_lhs => rw [← deph_idem, hrec]
    rw [map_smul, map_sum, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum]
    simp only [map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have hre := congrArg Complex.re key
  rw [Matrix.mul_apply]
  simp only [blochA]
  rw [hre]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  norm_num
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma nuclear_deph (hd : 1 ≤ d) : nuclearNorm (blochA B (completelyDephasing d)) = (d : ℝ) - 1 := by
  unfold nuclearNorm traceNorm
  set A := blochA B (completelyDephasing d) with hAdef
  set M : Matrix (BlochIndex d) (BlochIndex d) ℂ := A.map fun x => (x : ℂ) with hM
  have hMM : Mᴴ * M = M := by
    ext i k
    have := congrFun (congrFun (A_idem B) i) k
    rw [Matrix.mul_apply, ← hAdef] at this
    simp only [hM, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def,
      Complex.conj_ofReal]
    have hs : ∀ j, A j i = A i j := fun j => by rw [hAdef]; exact A_symm B j i
    simp only [hs]
    exact_mod_cast this
  have hH : M.IsHermitian := by
    have := Matrix.isHermitian_conjTranspose_mul_self M
    rwa [hMM] at this
  have hidem : M * M = M := by
    have := hMM
    rwa [hH.eq] at this
  rw [hMM, sqrt_trace_idem M hH hidem]
  rw [Matrix.trace, Complex.re_sum]
  simp only [Matrix.diag, hM, Matrix.map_apply, Complex.ofReal_re]
  exact trace_A B hd

end X7P23D

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P23 X7P23 X7P23D in
theorem solution {d : ℕ} (hd : 1 ≤ d) (B : BlochBasis d) :
    IsCPTP (completelyDephasing d) ∧
    Entanglement.IsEntanglementBreakingPositive (completelyDephasing d) ∧
    (∀ X : Operator d, completelyDephasing d X = Matrix.diagonal (fun k => X k k)) ∧
    blochC B (completelyDephasing d) = 0 ∧
    nuclearNorm (blochA B (completelyDephasing d)) = (d : ℝ) - 1 ∧
    nuclearNorm (blochA B (completelyDephasing d)) ^ 2 +
      ((d : ℝ) * ((d : ℝ) - 1) / 2) * vectorNorm (blochC B (completelyDephasing d)) ^ 2 =
        ((d : ℝ) - 1) ^ 2 := by
  have hC : blochC B (completelyDephasing d) = 0 := by
    funext i
    simp only [blochC, coordinates]
    rw [deph_apply]
    have : Matrix.diagonal (fun k => (((d : ℂ)⁻¹ • (1 : Operator d)) k k)) = (d : ℂ)⁻¹ • 1 := by
      ext a b
      by_cases h : a = b
      · subst h; simp
      · simp [Matrix.diagonal, Matrix.one_apply, h]
    rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, B.traceless]
    simp
  have hN := nuclear_deph B hd
  refine ⟨⟨X7Holevo.holevo_cp _ _ (fun k => single_psd k) (fun k => single_psd k), fun X => ?_⟩,
    X7Holevo.holevo_eb _ _ (fun k => single_density k) (fun k => single_psd k),
    deph_apply, hC, hN, ?_⟩
  · rw [deph_apply, Matrix.trace_diagonal]; rfl
  · rw [hN, hC]
    simp [vectorNorm]
