-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P10.bipartite_locc_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:08:58.591401+00:00
-- url     : https://prove2.me/submissions/85ef6f6e-1184-4372-a6be-155443d338c1

import Theorems.Thm_TroppMatrixConcentration_ch8_entropy_joint_convex
import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10


/-! X6 SSA library, part 1: star-algebra homomorphisms between matrix algebras commute with the
functional calculus; joint convexity of Tropp's relative entropy on arbitrary finite index types;
unitary invariance. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix

variable {m n ι : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype ι] [DecidableEq ι]

lemma cont_hom (φ : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ) : Continuous φ :=
  LinearMap.continuous_of_finiteDimensional (φ.toAlgHom.toLinearMap)

lemma map_cfc_mat (φ : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ) (f : ℝ → ℝ) (A : Matrix m m ℂ)
    (hA : A.IsHermitian) : φ (cfc f A) = cfc f (φ A) := by
  have hA' : IsSelfAdjoint A := hA
  have hφ : IsSelfAdjoint (φ A) := by
    rw [IsSelfAdjoint, ← map_star, hA'.star_eq]
  exact StarAlgHomClass.map_cfc φ f A (A.finite_real_spectrum.continuousOn f) (cont_hom φ) hA' hφ

/-- `M ↦ M ⊗ I`. -/
def kronR (n : Type*) [Fintype n] [DecidableEq n] : Matrix m m ℂ →⋆ₐ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun M := M ⊗ₖ (1 : Matrix n n ℂ)
  map_one' := one_kronecker_one
  map_mul' M N := by rw [← mul_kronecker_mul, mul_one]
  map_zero' := zero_kronecker _
  map_add' M N := add_kronecker _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [smul_kronecker, one_kronecker_one]
  map_star' M := by
    simp only [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one]

/-- `M ↦ I ⊗ M`. -/
def kronL (n : Type*) [Fintype n] [DecidableEq n] : Matrix m m ℂ →⋆ₐ[ℂ] Matrix (n × m) (n × m) ℂ where
  toFun M := (1 : Matrix n n ℂ) ⊗ₖ M
  map_one' := one_kronecker_one
  map_mul' M N := by rw [← mul_kronecker_mul, mul_one]
  map_zero' := kronecker_zero _
  map_add' M N := kronecker_add _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [kronecker_smul, one_kronecker_one]
  map_star' M := by
    simp only [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one]

@[simp] lemma kronR_apply (M : Matrix m m ℂ) : kronR n M = M ⊗ₖ (1 : Matrix n n ℂ) := rfl
@[simp] lemma kronL_apply (M : Matrix m m ℂ) : kronL n M = (1 : Matrix n n ℂ) ⊗ₖ M := rfl

/-- reindexing as a star-algebra equivalence. -/
def reind (e : m ≃ n) : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ where
  toFun M := reindex e e M
  map_one' := by simp
  map_mul' M N := by simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  map_zero' := by simp
  map_add' M N := by ext i j; simp
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    ext i j; simp [Matrix.one_apply]
  map_star' M := by
    simp [star_eq_conjTranspose, Matrix.reindex_apply, conjTranspose_submatrix]

@[simp] lemma reind_apply (e : m ≃ n) (M : Matrix m m ℂ) : reind e M = reindex e e M := rfl

lemma trace_reind (e : m ≃ n) (M : Matrix m m ℂ) : (reindex e e M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

lemma relEnt_reind (e : m ≃ n) (A H : Matrix m m ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian) :
    ch8_relativeEntropy (reindex e e A) (reindex e e H) = ch8_relativeEntropy A H := by
  unfold ch8_relativeEntropy matrixLog
  have h1 := map_cfc_mat (reind e) Real.log A hA
  have h2 := map_cfc_mat (reind e) Real.log H hH
  simp only [reind_apply] at h1 h2
  rw [← h1, ← h2, ← trace_reind e]
  congr 2
  simp only [← reind_apply, ← map_mul, ← map_sub]

lemma posDef_reind (e : m ≃ n) {A : Matrix m m ℂ} (hA : A.PosDef) : (reindex e e A).PosDef := by
  rw [Matrix.reindex_apply]; exact hA.submatrix e.symm.injective

/-- Joint convexity of relative entropy on an arbitrary nonempty finite index type. -/
theorem joint_convex [Nonempty ι] :
    ConvexOn ℝ {P : Matrix ι ι ℂ × Matrix ι ι ℂ | P.1.PosDef ∧ P.2.PosDef}
      (fun P => ch8_relativeEntropy P.1 P.2) := by
  set e := Fintype.equivFin ι
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  have hc := (ch8_entropy_joint_convex (d := Fintype.card ι))
  let L : (Matrix ι ι ℂ × Matrix ι ι ℂ) →ₗ[ℝ]
      (Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ ×
        Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) :=
    LinearMap.prodMap ((reindexLinearEquiv ℂ ℂ e e).toLinearMap.restrictScalars ℝ)
      ((reindexLinearEquiv ℂ ℂ e e).toLinearMap.restrictScalars ℝ)
  have h := hc.comp_linearMap L
  have hset : L ⁻¹' {P | P.1.PosDef ∧ P.2.PosDef} =
      {P : Matrix ι ι ℂ × Matrix ι ι ℂ | P.1.PosDef ∧ P.2.PosDef} := by
    ext P
    simp only [Set.mem_preimage, Set.mem_setOf_eq, L, LinearMap.prodMap_apply,
      LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, reindexLinearEquiv_apply]
    constructor
    · rintro ⟨h1, h2⟩
      have k1 := posDef_reind e.symm h1
      have k2 := posDef_reind e.symm h2
      simp only [reindex_apply, submatrix_submatrix, Equiv.symm_symm] at k1 k2
      simpa using And.intro k1 k2
    · rintro ⟨h1, h2⟩; exact ⟨posDef_reind e h1, posDef_reind e h2⟩
  rw [hset] at h
  refine h.congr fun P hP => ?_
  simp only [Function.comp_apply, L, LinearMap.prodMap_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, reindexLinearEquiv_apply]
  exact relEnt_reind e _ _ hP.1.isHermitian hP.2.isHermitian

/-- Finite Jensen form of joint convexity. -/
theorem jensen [Nonempty ι] {G : Type*} (s : Finset G) (w : G → ℝ) (hw : ∀ g ∈ s, 0 ≤ w g)
    (hw1 : ∑ g ∈ s, w g = 1) (A H : G → Matrix ι ι ℂ) (hA : ∀ g ∈ s, (A g).PosDef)
    (hH : ∀ g ∈ s, (H g).PosDef) :
    ch8_relativeEntropy (∑ g ∈ s, w g • A g) (∑ g ∈ s, w g • H g) ≤
      ∑ g ∈ s, w g * ch8_relativeEntropy (A g) (H g) := by
  have := (joint_convex (ι := ι)).map_sum_le hw hw1 (p := fun g => (A g, H g))
    (fun g hg => ⟨hA g hg, hH g hg⟩)
  have e1 : (∑ i ∈ s, w i • (A i, H i)).1 = ∑ g ∈ s, w g • A g := by simp [Prod.fst_sum]
  have e2 : (∑ i ∈ s, w i • (A i, H i)).2 = ∑ g ∈ s, w g • H g := by simp [Prod.snd_sum]
  rw [e1, e2] at this
  simpa only [smul_eq_mul] using this

/-- Unitary invariance of relative entropy. -/
lemma relEnt_unitary (U : unitary (Matrix ι ι ℂ)) (A H : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hH : H.IsHermitian) :
    ch8_relativeEntropy ((U : Matrix ι ι ℂ) * A * star (U : Matrix ι ι ℂ))
      ((U : Matrix ι ι ℂ) * H * star (U : Matrix ι ι ℂ)) = ch8_relativeEntropy A H := by
  set φ : Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix ι ι ℂ :=
    (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ).toStarAlgHom
  have hφ : ∀ X, φ X = (U : Matrix ι ι ℂ) * X * star (U : Matrix ι ι ℂ) := fun X => rfl
  unfold ch8_relativeEntropy matrixLog
  rw [← hφ, ← hφ, ← map_cfc_mat φ _ _ hA, ← map_cfc_mat φ _ _ hH, ← map_sub φ (cfc _ A),
    ← map_mul, ← map_sub φ A H, ← map_sub, hφ]
  rw [Matrix.trace_mul_cycle]
  rw [show star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = 1 from Unitary.star_mul_self_of_mem U.2,
    one_mul]

end X6SSA


/-! X6 SSA library, part 2: twirling the middle factor of `A × (B × C)` and monotonicity of
relative entropy under the partial trace over `B`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

def sg (b : Bool) : ℂ := if b then 1 else -1

lemma sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

lemma star_sg (b : Bool) : star (sg b) = sg b := by cases b <;> simp [sg]

omit [Fintype B] in
lemma sg_sum [Fintype B] (u v : B) :
    ∑ s : B → Bool, sg (s u) * sg (s v) = if u = v then (2 : ℂ) ^ Fintype.card B else 0 := by
  split_ifs with h
  · subst h
    simp [sg_mul_self, Fintype.card_fun, Fintype.card_bool]
  · refine Finset.sum_involution (fun s _ => Function.update s v (!s v)) ?_ ?_ ?_ ?_
    · intro s _
      simp only [Function.update_of_ne h, Function.update_self]
      cases s v <;> cases s u <;> simp [sg]
    · intro s _ _ heq
      have := congrFun heq v
      simp only [Function.update_self] at this
      cases hs : s v <;> simp [hs] at this
    · intro s _; exact Finset.mem_univ _
    · intro s _
      ext w
      by_cases hw : w = v
      · subst hw; simp
      · simp [Function.update_of_ne hw]

/-- diagonal sign unitary acting on the middle factor. -/
def Dm (s : B → Bool) : Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  diagonal fun x => sg (s x.2.1)

lemma Dm_mul_self (s : B → Bool) : (Dm s : Matrix (A × (B × C)) _ ℂ) * Dm s = 1 := by
  simp [Dm, diagonal_mul_diagonal, sg_mul_self]

lemma Dm_star (s : B → Bool) : star (Dm s : Matrix (A × (B × C)) _ ℂ) = Dm s := by
  rw [Dm, star_eq_conjTranspose, diagonal_conjTranspose]
  congr 1; funext x; exact star_sg _

lemma Dm_mem (s : B → Bool) : (Dm s : Matrix (A × (B × C)) _ ℂ) ∈ unitary _ := by
  rw [Unitary.mem_iff, Dm_star, Dm_mul_self]; exact ⟨rfl, rfl⟩

/-- cyclic shift of the middle factor. -/
def tau {N : ℕ} [NeZero N] (e : B ≃ Fin N) (k : Fin N) : A × (B × C) ≃ A × (B × C) :=
  Equiv.prodCongr (Equiv.refl A)
    (Equiv.prodCongr ((e.trans (Equiv.addRight k)).trans e.symm) (Equiv.refl C))

lemma tau_symm_apply {N : ℕ} [NeZero N] (e : B ≃ Fin N) (k : Fin N) (x : A × (B × C)) :
    (tau e k).symm x = (x.1, (e.symm (e x.2.1 - k), x.2.2)) := by
  simp [tau, Equiv.prodCongr, sub_eq_add_neg]; rfl

/-- one element of the twirling group. -/
def term {N : ℕ} [NeZero N] (e : B ≃ Fin N) (g : Fin N × (B → Bool))
    (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) : Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  Dm g.2 * reindex (tau e g.1) (tau e g.1) M * Dm g.2

lemma term_apply {N : ℕ} [NeZero N] (e : B ≃ Fin N) (g : Fin N × (B → Bool))
    (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) (x y : A × (B × C)) :
    term e g M x y = sg (g.2 x.2.1) * sg (g.2 y.2.1) *
      M (x.1, (e.symm (e x.2.1 - g.1), x.2.2)) (y.1, (e.symm (e y.2.1 - g.1), y.2.2)) := by
  simp only [term, Dm, diagonal_mul, mul_diagonal, reindex_apply, submatrix_apply,
    tau_symm_apply]
  ring

/-- partial trace over the middle factor. -/
def trB (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) : Matrix (A × C) (A × C) ℂ :=
  of fun p q => ∑ b, M (p.1, (b, p.2)) (q.1, (b, q.2))

/-- the equivalence `(A × C) × B ≃ A × (B × C)`. -/
def eqv : (A × C) × B ≃ A × (B × C) where
  toFun z := (z.1.1, (z.2, z.1.2))
  invFun x := ((x.1, x.2.2), x.2.1)
  left_inv z := rfl
  right_inv x := rfl

/-- `N ↦ N ⊗ I_B` placed in the middle. -/
def midH : Matrix (A × C) (A × C) ℂ →⋆ₐ[ℂ] Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  (reind (eqv (A := A) (B := B) (C := C))).comp (kronR B)

lemma midH_apply (N : Matrix (A × C) (A × C) ℂ) (x y : A × (B × C)) :
    midH N x y = if x.2.1 = y.2.1 then N (x.1, x.2.2) (y.1, y.2.2) else 0 := by
  show N (x.1, x.2.2) (y.1, y.2.2) * (1 : Matrix B B ℂ) x.2.1 y.2.1 = _
  rw [one_apply]
  split_ifs <;> simp

lemma twirl {N : ℕ} [NeZero N] (e : B ≃ Fin N) (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    ∑ g : Fin N × (B → Bool), term e g M = ((2 : ℂ) ^ Fintype.card B) • midH (trB M) := by
  ext x y
  rw [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.smul_apply, midH_apply]
  simp only [term_apply]
  have : ∀ k : Fin N, ∑ s : B → Bool, sg (s x.2.1) * sg (s y.2.1) *
      M (x.1, (e.symm (e x.2.1 - k), x.2.2)) (y.1, (e.symm (e y.2.1 - k), y.2.2)) =
      (if x.2.1 = y.2.1 then (2 : ℂ) ^ Fintype.card B else 0) *
      M (x.1, (e.symm (e x.2.1 - k), x.2.2)) (y.1, (e.symm (e y.2.1 - k), y.2.2)) := by
    intro k; rw [← sg_sum, Finset.sum_mul]
  simp only [this]
  split_ifs with h
  · rw [← Finset.mul_sum, smul_eq_mul]
    congr 1
    simp only [trB, of_apply, h]
    rw [← Equiv.sum_comp e.symm]
    exact (Equiv.sum_comp (Equiv.subLeft (e y.2.1))
      (fun j => M (x.1, (e.symm j, x.2.2)) (y.1, (e.symm j, y.2.2))))
  · simp

lemma term_posDef {N : ℕ} [NeZero N] (e : B ≃ Fin N) (g : Fin N × (B → Bool))
    {M : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hM : M.PosDef) : (term e g M).PosDef := by
  have h := (posDef_reind (tau e g.1) hM).mul_mul_conjTranspose_same (B := Dm g.2) (by
    intro u v huv
    have := congrArg (fun z => z ᵥ* Dm g.2) huv
    simpa [vecMul_vecMul, Dm_mul_self] using this)
  rwa [← star_eq_conjTranspose, Dm_star] at h

lemma term_relEnt {N : ℕ} [NeZero N] (e : B ≃ Fin N) (g : Fin N × (B → Bool))
    {M H : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hM : M.IsHermitian) (hH : H.IsHermitian) :
    ch8_relativeEntropy (term e g M) (term e g H) = ch8_relativeEntropy M H := by
  have h := relEnt_unitary (⟨Dm g.2, Dm_mem g.2⟩ : unitary (Matrix (A × (B × C)) (A × (B × C)) ℂ)) (reindex (tau e g.1) (tau e g.1) M)
    (reindex (tau e g.1) (tau e g.1) H) (by rw [reindex_apply]; exact hM.submatrix _)
    (by rw [reindex_apply]; exact hH.submatrix _)
  simp only [Dm_star] at h
  rw [term, term, h, relEnt_reind _ _ _ hM hH]

/-- Monotonicity of relative entropy under the partial trace over the middle factor, in the
form `D(trB ρ ⊗ I/|B|, trB σ ⊗ I/|B|) ≤ D(ρ, σ)`. -/
theorem mono_trB [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ σ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    ch8_relativeEntropy (((Fintype.card B : ℝ)⁻¹) • midH (B := B) (trB ρ))
      (((Fintype.card B : ℝ)⁻¹) • midH (B := B) (trB σ)) ≤ ch8_relativeEntropy ρ σ := by
  set N := Fintype.card B
  haveI : NeZero N := ⟨Fintype.card_ne_zero⟩
  set e := Fintype.equivFin B
  set w : ℝ := ((N : ℝ) * 2 ^ N)⁻¹
  have hT : ∀ M : Matrix (A × (B × C)) (A × (B × C)) ℂ,
      ((N : ℝ)⁻¹) • midH (B := B) (trB M) = ∑ g : Fin N × (B → Bool), w • term e g M := by
    intro M
    rw [← Finset.smul_sum, twirl]
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, w]
    push_cast
    field_simp
    rfl
  rw [hT, hT]
  have hw1 : ∑ _g : Fin N × (B → Bool), w = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul, w]
    push_cast
    field_simp
    exact mul_div_cancel_left₀ (2 ^ N : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have := jensen (Finset.univ : Finset (Fin N × (B → Bool))) (fun _ => w)
    (fun _ _ => by positivity) hw1 (fun g => term e g ρ) (fun g => term e g σ)
    (fun g _ => term_posDef e g hρ) (fun g _ => term_posDef e g hσ)
  refine this.trans (le_of_eq ?_)
  simp only [term_relEnt e _ hρ.isHermitian hσ.isHermitian, ← Finset.sum_mul, hw1, one_mul]

end X6SSA


/-! X6 SSA library, part 3: strong subadditivity for positive-definite states,
`S(AC) + S(BC) - S(C) - S(ABC) ≥ 0` on `A × (B × C)`, in the form
`ent ρ_AC - ent ρ_C ≤ ent ρ - ent ρ_BC` with `ent M = Re tr (M log M)`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix MatrixOrder
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix

/-- negative entropy `Re tr (M log M)` (nats). -/
def ent {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) : ℝ :=
  (trace (M * cfc Real.log M)).re

section general
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

lemma log_smul (N : Matrix n n ℂ) (hN : N.PosDef) {c : ℝ} (hc : 0 < c) :
    cfc Real.log (c • N) = algebraMap ℝ (Matrix n n ℂ) (Real.log c) + cfc Real.log N := by
  have hsa : IsSelfAdjoint N := hN.isHermitian
  have hpos := hN.isStrictlyPositive
  rw [← cfc_comp_smul c Real.log N (by
    refine Real.continuousOn_log.mono ?_
    rintro _ ⟨x, hx, rfl⟩
    have := hpos.spectrum_pos hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, smul_eq_mul]
    positivity)]
  rw [← cfc_const (Real.log c) N, ← cfc_add N (fun _ => Real.log c) Real.log
    (by fun_prop) (by
      refine Real.continuousOn_log.mono fun x hx => ?_
      have := hpos.spectrum_pos hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact this.ne')]
  refine cfc_congr fun x hx => ?_
  have := hpos.spectrum_pos hx
  simp only [smul_eq_mul]
  rw [Real.log_mul hc.ne' this.ne']

lemma posDef_smul {N : Matrix n n ℂ} (hN : N.PosDef) {c : ℝ} (hc : 0 < c) : (c • N).PosDef := by
  have : c • N = (c : ℂ) • N := by ext i j; simp [Complex.real_smul]
  rw [this]; exact hN.smul (by exact_mod_cast hc)

lemma trace_smul_re (c : ℝ) (N : Matrix n n ℂ) : (trace (c • N)).re = c * (trace N).re := by
  rw [trace_smul]; simp [Complex.real_smul]

lemma trace_alg_mul_re (c : ℝ) (N : Matrix n n ℂ) :
    (trace (N * algebraMap ℝ (Matrix n n ℂ) c)).re = c * (trace N).re := by
  rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, trace_smul_re]

/-- relative entropy against a scaled image under a star-algebra homomorphism. -/
lemma relEnt_hom (ρ : Matrix n n ℂ) (φ : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ) (M : Matrix m m ℂ)
    (hM : M.PosDef) (hφM : (φ M).PosDef) {c : ℝ} (hc : 0 < c) :
    ch8_relativeEntropy ρ (c • φ M) = ent ρ - Real.log c * (trace ρ).re -
      (trace (ρ * φ (cfc Real.log M))).re - (trace ρ).re + c * (trace (φ M)).re := by
  unfold ch8_relativeEntropy matrixLog ent
  rw [log_smul _ hφM hc, ← map_cfc_mat φ _ _ hM.isHermitian]
  simp only [mul_sub, mul_add, trace_sub, trace_add, Complex.sub_re, Complex.add_re,
    trace_alg_mul_re, trace_smul_re]
  ring

lemma ent_hom (φ : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ) (M : Matrix m m ℂ)
    (hM : M.PosDef) (hφM : (φ M).PosDef) {c : ℝ} (hc : 0 < c) :
    ent (c • φ M) = c * (Real.log c * (trace (φ M)).re + (trace (φ (M * cfc Real.log M))).re) := by
  unfold ent
  rw [log_smul _ hφM hc, ← map_cfc_mat φ _ _ hM.isHermitian, smul_mul_assoc, trace_smul_re,
    mul_add, trace_add, Complex.add_re, trace_alg_mul_re, map_mul]

end general

section ptr
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- partial trace over the first factor. -/
def trF (M : Matrix (P × Q) (P × Q) ℂ) : Matrix Q Q ℂ := of fun q q' => ∑ p, M (p, q) (p, q')

/-- the isometric embedding `x ↦ e_p ⊗ x`. -/
def V (p : P) : Matrix (P × Q) Q ℂ := of fun x q => if x.1 = p ∧ x.2 = q then 1 else 0

lemma V_conj (p : P) (M : Matrix (P × Q) (P × Q) ℂ) :
    (V p : Matrix (P × Q) Q ℂ)ᴴ * M * (V p : Matrix (P × Q) Q ℂ) = of fun q q' => M (p, q) (p, q') := by
  ext q q'
  simp only [mul_apply, conjTranspose_apply, V, of_apply]
  simp [Fintype.sum_prod_type, ite_and, apply_ite (starRingEnd ℂ), ite_mul]

lemma trF_eq (M : Matrix (P × Q) (P × Q) ℂ) : trF M = ∑ p, (V p : Matrix (P × Q) Q ℂ)ᴴ * M * (V p : Matrix (P × Q) Q ℂ) := by
  ext q q'
  simp only [trF, of_apply, V_conj, Matrix.sum_apply]

lemma trF_posDef [Nonempty P] {M : Matrix (P × Q) (P × Q) ℂ} (hM : M.PosDef) : (trF M).PosDef := by
  obtain ⟨p0⟩ := ‹Nonempty P›
  rw [trF_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ p0)]
  refine PosDef.add_posSemidef ?_ (posSemidef_sum _ fun p _ => hM.posSemidef.conjTranspose_mul_mul_same _)
  refine hM.conjTranspose_mul_mul_same fun u v huv => ?_
  funext q
  have := congrFun huv (p0, q)
  simpa [mulVec, dotProduct, V, Prod.ext_iff, Fintype.sum_prod_type, ite_and] using this

lemma trace_trF (M : Matrix (P × Q) (P × Q) ℂ) : trace (trF M) = trace M := by
  simp [trace, trF, Fintype.sum_prod_type]; exact Finset.sum_comm

lemma trace_kronL (L : Matrix Q Q ℂ) : trace (kronL P L) = Fintype.card P * trace L := by
  rw [kronL_apply, trace_kronecker, trace_one]

/-- `tr (ρ (1 ⊗ L)) = tr (trF ρ L)`. -/
lemma trace_mul_kronL (M : Matrix (P × Q) (P × Q) ℂ) (L : Matrix Q Q ℂ) :
    trace (M * kronL P L) = trace (trF M * L) := by
  simp only [trace, diag_apply, mul_apply, kronL_apply, kronecker_apply, one_apply, trF, of_apply,
    Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_eq, Finset.sum_mul, ite_mul, zero_mul]
  have h : ∀ (x : P) (x1 : Q), (∑ x2 : P, ∑ x3 : Q,
      if x2 = x then M (x, x1) (x2, x3) * (1 * L x3 x1) else 0) =
      ∑ x3, M (x, x1) (x, x3) * L x3 x1 := by
    intro x x1; rw [Finset.sum_comm]; simp
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]

end ptr

section three
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- `A × (B × C) ≃ B × (A × C)`. -/
def swp : A × (B × C) ≃ B × (A × C) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun y := (y.2.1, (y.1, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

lemma trB_eq (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) : trB M = trF (reindex swp swp M) := rfl

lemma trB_posDef [Nonempty B] {M : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hM : M.PosDef) :
    (trB M).PosDef := by
  rw [trB_eq]; exact trF_posDef (posDef_reind _ hM)

lemma trace_midH (N : Matrix (A × C) (A × C) ℂ) :
    trace (midH (B := B) N) = Fintype.card B * trace N := by
  simp only [midH, StarAlgHom.comp_apply, reind_apply, trace_reind, kronR_apply,
    trace_kronecker, trace_one]
  ring

lemma midH_posDef {N : Matrix (A × C) (A × C) ℂ} (hN : N.PosDef) : (midH (B := B) N).PosDef := by
  simp only [midH, StarAlgHom.comp_apply, reind_apply, kronR_apply]
  exact posDef_reind _ (hN.kronecker PosDef.one)

lemma kronL_posDef {Q : Type*} [Fintype Q] [DecidableEq Q] {N : Matrix Q Q ℂ} (hN : N.PosDef) :
    (kronL A N).PosDef := by
  rw [kronL_apply]; exact PosDef.one.kronecker hN

lemma trB_kronL (M : Matrix (B × C) (B × C) ℂ) : trB (kronL A M) = kronL A (trF M) := by
  ext x y
  simp [trB, trF, kronecker_apply, one_apply, Finset.mul_sum]

lemma trF_trB (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) : trF (trB M) = trF (trF M) := by
  ext c c'
  simp only [trF, trB, of_apply]
  exact Finset.sum_comm

lemma natmul_re (k : ℕ) (z : ℂ) : ((k : ℂ) * z).re = k * z.re := by simp

lemma hom_rsmul {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ) (c : ℝ) (X : Matrix m m ℂ) : φ (c • X) = c • φ X := by
  rw [← algebraMap_smul ℂ c X, map_smul, algebraMap_smul]

/-- Strong subadditivity for positive-definite states of trace one. -/
theorem ssa_posDef [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosDef) (htr : trace ρ = 1) :
    ent (trB ρ) - ent (trF (trF ρ)) ≤ ent ρ - ent (trF ρ) := by
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have h := mono_trB ρ (((Fintype.card A : ℝ)⁻¹) • kronL A (trF ρ)) hρ
    (posDef_smul (kronL_posDef (trF_posDef hρ)) (inv_pos.mpr hA))
  have hρBC := trF_posDef hρ
  have hρAC := trB_posDef (B := B) hρ
  have hρC := trF_posDef hρBC
  have tBC : (trace (trF ρ)).re = 1 := by rw [trace_trF, htr]; simp
  have tAC : (trace (trB ρ)).re = 1 := by rw [trB_eq, trace_trF, trace_reind, htr]; simp
  have tC : (trace (trF (trF ρ))).re = 1 := by rw [trace_trF, tBC]
  -- right-hand side
  have hR := relEnt_hom ρ (kronL A) (trF ρ) hρBC (kronL_posDef hρBC) (inv_pos.mpr hA)
  rw [trace_mul_kronL, trace_kronL, htr, natmul_re, tBC, Complex.one_re] at hR
  -- left-hand side
  have e2 : trB ((Fintype.card A : ℝ)⁻¹ • kronL A (trF ρ)) =
      (Fintype.card A : ℝ)⁻¹ • kronL A (trF (trF ρ)) := by
    rw [show trB ((Fintype.card A : ℝ)⁻¹ • kronL A (trF ρ)) =
        (Fintype.card A : ℝ)⁻¹ • trB (kronL A (trF ρ)) by
      ext x y; simp [trB, Finset.smul_sum], trB_kronL]
  rw [e2, hom_rsmul, smul_smul] at h
  set φ := (midH (A := A) (B := B) (C := C)).comp (kronL A)
  have hφ : ∀ N, midH (B := B) (kronL A N) = φ N := fun N => rfl
  rw [hφ] at h
  have hφC : (φ (trF (trF ρ))).PosDef := by
    rw [← hφ]; exact midH_posDef (kronL_posDef hρC)
  have hL := relEnt_hom (((Fintype.card B : ℝ))⁻¹ • midH (B := B) (trB ρ)) φ (trF (trF ρ)) hρC hφC
    (show 0 < (Fintype.card B : ℝ)⁻¹ * (Fintype.card A : ℝ)⁻¹ by positivity)
  rw [hL, hR] at h
  have k1 : ent (((Fintype.card B : ℝ))⁻¹ • midH (B := B) (trB ρ)) =
      - Real.log (Fintype.card B) + ent (trB ρ) := by
    rw [ent_hom _ _ hρAC (midH_posDef hρAC) (inv_pos.mpr hB), trace_midH, trace_midH, natmul_re,
      natmul_re, tAC, Real.log_inv, ent]
    field_simp
  have k2 : (trace (((Fintype.card B : ℝ))⁻¹ • midH (B := B) (trB ρ))).re = 1 := by
    rw [trace_smul_re, trace_midH, natmul_re, tAC]
    field_simp
  have k3 : (trace (((Fintype.card B : ℝ))⁻¹ • midH (B := B) (trB ρ) *
      φ (cfc Real.log (trF (trF ρ))))).re = ent (trF (trF ρ)) := by
    rw [smul_mul_assoc, trace_smul_re, ← hφ, ← map_mul, trace_midH, trace_mul_kronL, ent,
      trF_trB, natmul_re]
    field_simp
  have k4 : (trace (φ (trF (trF ρ)))).re = Fintype.card B * Fintype.card A := by
    rw [← hφ, trace_midH, trace_kronL, ← mul_assoc, ← Nat.cast_mul, natmul_re, tC]
    push_cast; ring
  rw [k1, k2, k3, k4] at h
  rw [Real.log_mul (inv_pos.mpr hB).ne' (inv_pos.mpr hA).ne', Real.log_inv, Real.log_inv] at h
  have e5 : ((Fintype.card B : ℝ)⁻¹ * (Fintype.card A : ℝ)⁻¹) *
      ((Fintype.card B : ℝ) * Fintype.card A) = 1 := by field_simp
  have e6 : (Fintype.card A : ℝ)⁻¹ * Fintype.card A = 1 := by field_simp
  unfold ent at *
  linarith

end three
end X6SSA


/-! X6 SSA library, part 4: strong subadditivity for arbitrary density matrices
(`QAlgorithms.vnEntropy`, bits), by continuity from the positive-definite case. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix MatrixOrder
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix Filter Topology

section gen
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Re tr (M log M)` through the functional calculus of `x log x`. -/
def Hn (M : Matrix n n ℂ) : ℝ := (trace (cfc (fun x : ℝ => x * Real.log x) M)).re

lemma Hn_posDef {M : Matrix n n ℂ} (hM : M.PosDef) : Hn M = ent M := by
  have hpos := hM.isStrictlyPositive
  unfold Hn ent
  rw [cfc_mul (fun x : ℝ => x) Real.log M (by fun_prop) (by
      refine Real.continuousOn_log.mono fun x hx => ?_
      have := hpos.spectrum_pos hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact this.ne')]
  congr 3
  exact cfc_id' ℝ M hM.isHermitian

lemma vn_eq (M : Matrix n n ℂ) : QAlgorithms.vnEntropy M = - Hn M / Real.log 2 := by
  unfold QAlgorithms.vnEntropy Hn
  have : (fun x : ℝ => x * Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * (x * Real.log x) := by
    funext x; rw [Real.logb]; ring
  rw [this, cfc_const_mul (Real.log 2)⁻¹ (fun x : ℝ => x * Real.log x) M
    Real.continuous_mul_log.continuousOn, trace_smul_re]
  ring

lemma spec_density {M : Matrix n n ℂ} (hM : M.PosSemidef) (htr : M.trace = 1) :
    spectrum ℝ M ⊆ Set.Icc 0 1 := by
  intro x hx
  rw [hM.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  have h0 := hM.eigenvalues_nonneg
  refine ⟨h0 i, ?_⟩
  have hs := hM.1.trace_eq_sum_eigenvalues
  rw [htr] at hs
  have hs' : ∑ j, hM.1.eigenvalues j = 1 := by
    have := congrArg Complex.re hs
    simpa using this.symm
  rw [← hs']
  exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

lemma psd_rsmul {M : Matrix n n ℂ} (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    (c • M).PosSemidef := by
  have : c • M = (c : ℂ) • M := by ext; simp [Complex.real_smul]
  rw [this]; exact hM.smul (by exact_mod_cast hc)

lemma cont_tr_re : Continuous fun M : Matrix n n ℂ => (trace M).re :=
  Complex.continuous_re.comp
    (LinearMap.continuous_of_finiteDimensional (traceLinearMap n ℂ ℂ))

lemma Hn_contOn : ContinuousOn (Hn : Matrix n n ℂ → ℝ)
    {a | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Icc 0 1} :=
  cont_tr_re.comp_continuousOn
    (continuousOn_cfc (Matrix n n ℂ) isCompact_Icc _ Real.continuous_mul_log.continuousOn)

end gen

section ptr
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

lemma trF_psd {M : Matrix (P × Q) (P × Q) ℂ} (hM : M.PosSemidef) : (trF M).PosSemidef := by
  rw [trF_eq]
  exact posSemidef_sum _ fun p _ => hM.conjTranspose_mul_mul_same _

lemma trF_lin (a b : ℝ) (X Y : Matrix (P × Q) (P × Q) ℂ) :
    trF (a • X + b • Y) = a • trF X + b • trF Y := by
  ext i j; simp [trF, Finset.sum_add_distrib, Finset.mul_sum, Complex.real_smul]

end ptr

section three
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

lemma trB_psd {M : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hM : M.PosSemidef) :
    (trB M).PosSemidef := by
  rw [trB_eq]; exact trF_psd (by rw [reindex_apply]; exact hM.submatrix _)

lemma trB_lin (a b : ℝ) (X Y : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    trB (a • X + b • Y) = a • trB X + b • trB Y := by
  ext i j; simp [trB, Finset.sum_add_distrib, Finset.mul_sum, Complex.real_smul]

lemma dens_ok {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (hM : M.PosSemidef)
    (htr : M.trace = 1) : M ∈ {a : Matrix n n ℂ | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Icc 0 1} :=
  ⟨hM.1, spec_density hM htr⟩

/-- Strong subadditivity in the `Hn` form for every density matrix. -/
theorem ssa_Hn [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    Hn (trB ρ) - Hn (trF (trF ρ)) - Hn ρ + Hn (trF ρ) ≤ 0 := by
  set N : ℝ := (Fintype.card (A × (B × C)) : ℝ)
  have hN : 0 < N := by simp only [N]; exact_mod_cast Fintype.card_pos
  set E : Matrix (A × (B × C)) (A × (B × C)) ℂ := N⁻¹ • (1 : Matrix _ _ ℂ)
  have hE : E.PosDef := posDef_smul PosDef.one (inv_pos.mpr hN)
  have htrE : trace E = 1 := by
    rw [trace_smul, trace_one]; simp only [N]
    rw [Complex.real_smul]; push_cast
    field_simp
  let path : ℝ → Matrix (A × (B × C)) (A × (B × C)) ℂ := fun t => (1 - t) • ρ + t • E
  have tr_path : ∀ t, trace (path t) = 1 := by
    intro t
    simp only [path, trace_add, trace_smul, htr, htrE, Complex.real_smul]
    push_cast; ring
  have psd_path : ∀ t ∈ Set.Icc (0 : ℝ) 1, (path t).PosSemidef := by
    intro t ht
    refine PosSemidef.add ?_ ?_
    · exact psd_rsmul hρ (sub_nonneg.mpr ht.2)
    · exact psd_rsmul hE.posSemidef ht.1
  have pd_path : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (path t).PosDef := by
    intro t ht
    have h1 : ((1 - t) • ρ).PosSemidef := psd_rsmul hρ (sub_pos.mpr ht.2).le
    exact PosDef.posSemidef_add h1 (posDef_smul hE ht.1)
  let F : ℝ → ℝ := fun t =>
    Hn (trB (path t)) - Hn (trF (trF (path t))) - Hn (path t) + Hn (trF (path t))
  have hF : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F t ≤ 0 := by
    intro t ht
    have hp := pd_path t ht
    have := ssa_posDef (path t) hp (tr_path t)
    simp only [F]
    rw [Hn_posDef (trB_posDef hp), Hn_posDef (trF_posDef (trF_posDef hp)), Hn_posDef hp,
      Hn_posDef (trF_posDef hp)]
    linarith
  -- continuity of `F` on `[0,1]`
  have c_path : Continuous path := by fun_prop
  have c1 : Continuous fun t => trB (path t) := by
    simp only [path, trB_lin]; fun_prop
  have c2 : Continuous fun t => trF (path t) := by
    simp only [path, trF_lin]; fun_prop
  have c3 : Continuous fun t => trF (trF (path t)) := by
    simp only [path, trF_lin]; fun_prop
  have tr1 : ∀ t, trace (trB (path t)) = 1 := fun t => by
    rw [trB_eq, trace_trF, trace_reind, tr_path]
  have tr2 : ∀ t, trace (trF (path t)) = 1 := fun t => by rw [trace_trF, tr_path]
  have tr3 : ∀ t, trace (trF (trF (path t))) = 1 := fun t => by rw [trace_trF, tr2]
  have hFc : ContinuousOn F (Set.Icc 0 1) := by
    refine ((((Hn_contOn.comp c1.continuousOn fun t ht =>
      dens_ok (trB_psd (psd_path t ht)) (tr1 t)).sub
      (Hn_contOn.comp c3.continuousOn fun t ht =>
      dens_ok (trF_psd (trF_psd (psd_path t ht))) (tr3 t))).sub
      (Hn_contOn.comp c_path.continuousOn fun t ht =>
      dens_ok (psd_path t ht) (tr_path t))).add
      (Hn_contOn.comp c2.continuousOn fun t ht =>
      dens_ok (trF_psd (psd_path t ht)) (tr2 t)))
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 (F 0)) := by
    have := (hFc 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
      (show Set.Icc (0 : ℝ) 1 ∈ 𝓝[>] 0 from
        mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) Set.Ioo_subset_Icc_self)
    exact this
  have h0 : F 0 ≤ 0 := le_of_tendsto hlim
    (mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) fun t ht => hF t ht)
  have hp0 : path 0 = ρ := by simp [path]
  simpa only [F, hp0] using h0

/-- Strong subadditivity `S(AC) + S(BC) - S(C) - S(ABC) ≥ 0` (von Neumann entropy in bits) for
every density matrix on `A × (B × C)`. -/
theorem ssa [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    0 ≤ QAlgorithms.vnEntropy (trB ρ) + QAlgorithms.vnEntropy (trF ρ) -
      QAlgorithms.vnEntropy (trF (trF ρ)) - QAlgorithms.vnEntropy ρ := by
  have h := ssa_Hn ρ hρ htr
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  simp only [vn_eq]
  rw [show -Hn (trB ρ) / Real.log 2 + -Hn (trF ρ) / Real.log 2 - -Hn (trF (trF ρ)) / Real.log 2 -
      -Hn ρ / Real.log 2 = -(Hn (trB ρ) - Hn (trF (trF ρ)) - Hn ρ + Hn (trF ρ)) / Real.log 2 by ring]
  exact div_nonneg (by linarith) hl.le

end three
end X6SSA


/-! X6 SSA library, part 5: reindexing invariance of `vnEntropy` and strong subadditivity
conditioned on the middle factor, `S(AB) + S(BC) - S(B) - S(ABC) ≥ 0`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix

lemma vn_reind {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (M : Matrix m m ℂ) (hM : M.IsHermitian) :
    QAlgorithms.vnEntropy (reindex e e M) = QAlgorithms.vnEntropy M := by
  unfold QAlgorithms.vnEntropy
  have h := map_cfc_mat (reind e) (fun x : ℝ => x * Real.logb 2 x) M hM
  simp only [reind_apply] at h
  rw [← h, trace_reind]

section three
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- trace out the last factor. -/
def trC (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) : Matrix (A × B) (A × B) ℂ :=
  of fun i j => ∑ k, M (i.1, (i.2, k)) (j.1, (j.2, k))

/-- trace out the second factor of a pair. -/
def trR {P Q : Type*} [Fintype Q] (M : Matrix (P × Q) (P × Q) ℂ) : Matrix P P ℂ :=
  of fun i j => ∑ k, M (i, k) (j, k)

/-- `A × (B × C) ≃ A × (C × B)`. -/
def swBC : A × (B × C) ≃ A × (C × B) where
  toFun x := (x.1, (x.2.2, x.2.1))
  invFun y := (y.1, (y.2.2, y.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Strong subadditivity conditioned on the middle factor. -/
theorem ssa_mid [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    0 ≤ QAlgorithms.vnEntropy (trC ρ) + QAlgorithms.vnEntropy (trF ρ) -
      QAlgorithms.vnEntropy (trR (trF ρ)) - QAlgorithms.vnEntropy ρ := by
  set τ := reindex (swBC (A := A) (B := B) (C := C)) swBC ρ
  have hτ : τ.PosSemidef := by simp only [τ, reindex_apply]; exact hρ.submatrix _
  have htτ : trace τ = 1 := by simp only [τ]; rw [trace_reind, htr]
  have h := ssa τ hτ htτ
  have e1 : trB τ = trC ρ := by ext i j; rfl
  have e2 : trF τ = reindex (Equiv.prodComm B C) (Equiv.prodComm B C) (trF ρ) := by ext i j; rfl
  have e3 : trF (trF τ) = trR (trF ρ) := by ext i j; rfl
  rw [e1, e3, e2, vn_reind _ _ (trF_psd hρ).1] at h
  simp only [τ] at h
  rw [vn_reind _ _ hρ.1] at h
  exact h

end three
end X6SSA


/-! X6 SSA library, part 6: subadditivity `S(AB) ≤ S(A) + S(B)`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix

lemma vn_one {u : Type*} [Fintype u] [DecidableEq u] : QAlgorithms.vnEntropy (1 : Matrix u u ℂ) = 0 := by
  unfold QAlgorithms.vnEntropy
  rw [show (1 : Matrix u u ℂ) = algebraMap ℝ (Matrix u u ℂ) 1 from (map_one _).symm,
    cfc_algebraMap]
  simp

/-- `ι × κ ≃ ι × (κ × Unit)`. -/
def addU {ι κ : Type*} : ι × κ ≃ ι × (κ × Unit) where
  toFun x := (x.1, (x.2, ()))
  invFun y := (y.1, y.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `ι ≃ ι × Unit`. -/
def addU1 {ι : Type*} : ι ≃ ι × Unit where
  toFun x := (x, ())
  invFun y := y.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- Subadditivity of von Neumann entropy (bits). -/
theorem subadd {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Nonempty ι] [Nonempty κ] (ρ : Matrix (ι × κ) (ι × κ) ℂ) (hρ : ρ.PosSemidef)
    (htr : trace ρ = 1) :
    QAlgorithms.vnEntropy ρ ≤ QAlgorithms.vnEntropy (trR ρ) + QAlgorithms.vnEntropy (trF ρ) := by
  set τ := reindex (addU (ι := ι) (κ := κ)) addU ρ
  have hτ : τ.PosSemidef := by simp only [τ, reindex_apply]; exact hρ.submatrix _
  have htτ : trace τ = 1 := by simp only [τ]; rw [trace_reind, htr]
  have h := ssa τ hτ htτ
  have e1 : trB τ = reindex addU1 addU1 (trR ρ) := by ext i j; rfl
  have e2 : trF τ = reindex addU1 addU1 (trF ρ) := by ext i j; rfl
  have e3 : trF (trF τ) = 1 := by
    ext i j
    have : trF (trF τ) i j = trace ρ := by
      simp only [trF, of_apply, τ, reindex_apply, submatrix_apply, trace, diag_apply,
        Fintype.sum_prod_type]
      exact Finset.sum_comm
    rw [this, htr]; simp [one_apply]
  have hR : (trR ρ).IsHermitian := by
    have := trB_psd (B := κ) hτ
    rw [show trB τ = reindex addU1 addU1 (trR ρ) from e1] at this
    have h2 := this.1.submatrix addU1
    simpa [reindex_apply] using h2
  rw [e3, e1, e2, vn_one, vn_reind _ _ hR, vn_reind _ _ (trF_psd hρ).1] at h
  simp only [τ] at h
  rw [vn_reind _ _ hρ.1] at h
  linarith

end X6SSA


/-! X6 SSA library, part 7: marginals along abstract coordinate splittings `Ω ≃ K × F`, their
comparison, and strong subadditivity for a four-part splitting `Ω ≃ (A × (B × C)) × D`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix

/-- marginal on `K` along a splitting `Φ : Ω ≃ K × F`. -/
def marg {Ω K F : Type*} [Fintype F] (Φ : Ω ≃ K × F) (ρ : Matrix Ω Ω ℂ) : Matrix K K ℂ :=
  trR (reindex Φ Φ ρ)

lemma marg_psd {Ω K F : Type*} [Fintype F] [Fintype K] [DecidableEq K] [DecidableEq F]
    (Φ : Ω ≃ K × F) {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) : (marg Φ ρ).PosSemidef := by
  have h : marg Φ ρ = trF (reindex (Φ.trans (Equiv.prodComm K F)) (Φ.trans (Equiv.prodComm K F)) ρ) := by
    ext i j; rfl
  rw [h]; exact trF_psd (by rw [reindex_apply]; exact hρ.submatrix _)

lemma marg_trace {Ω K F : Type*} [Fintype Ω] [Fintype F] [Fintype K]
    (Φ : Ω ≃ K × F) (ρ : Matrix Ω Ω ℂ) : trace (marg Φ ρ) = trace ρ := by
  classical
  have h : trace (marg Φ ρ) = trace (reindex Φ Φ ρ) := by
    simp only [marg, trR, trace, diag_apply, of_apply, Fintype.sum_prod_type]
  rw [h, trace_reind]

/-- Two splittings that keep the same information give the same marginal up to reindexing. -/
lemma marg_transport {Ω K₁ F₁ K₂ F₂ : Type*} [Fintype F₁] [Fintype F₂]
    (Φ₁ : Ω ≃ K₁ × F₁) (Φ₂ : Ω ≃ K₂ × F₂) [Nonempty K₁] [Nonempty F₁]
    (h1 : ∀ ω ω', (Φ₁ ω).1 = (Φ₁ ω').1 ↔ (Φ₂ ω).1 = (Φ₂ ω').1)
    (h2 : ∀ ω ω', (Φ₁ ω).2 = (Φ₁ ω').2 ↔ (Φ₂ ω).2 = (Φ₂ ω').2) (ρ : Matrix Ω Ω ℂ) :
    ∃ κ : K₁ ≃ K₂, marg Φ₂ ρ = reindex κ κ (marg Φ₁ ρ) := by
  obtain ⟨k0⟩ := ‹Nonempty K₁›
  obtain ⟨z0⟩ := ‹Nonempty F₁›
  let f : K₁ → K₂ := fun k => (Φ₂ (Φ₁.symm (k, z0))).1
  let g : F₁ → F₂ := fun z => (Φ₂ (Φ₁.symm (k0, z))).2
  have kf : ∀ ω, (Φ₂ ω).1 = f (Φ₁ ω).1 := by
    intro ω
    refine ((h1 _ _).mp ?_).symm
    simp
  have kg : ∀ ω, (Φ₂ ω).2 = g (Φ₁ ω).2 := by
    intro ω
    refine ((h2 _ _).mp ?_).symm
    simp
  have fb : Function.Bijective f := by
    constructor
    · intro k k' hk
      have := (h1 (Φ₁.symm (k, z0)) (Φ₁.symm (k', z0))).mpr hk
      simpa using this
    · intro k₂
      have hF₂ : Nonempty F₂ := ⟨(Φ₂ (Φ₁.symm (k0, z0))).2⟩
      obtain ⟨z2⟩ := hF₂
      refine ⟨(Φ₁ (Φ₂.symm (k₂, z2))).1, ?_⟩
      rw [← kf]; simp
  have gb : Function.Bijective g := by
    constructor
    · intro z z' hz
      have := (h2 (Φ₁.symm (k0, z)) (Φ₁.symm (k0, z'))).mpr hz
      simpa using this
    · intro z₂
      obtain ⟨k2⟩ : Nonempty K₂ := ⟨f k0⟩
      refine ⟨(Φ₁ (Φ₂.symm (k2, z₂))).2, ?_⟩
      rw [← kg]; simp
  let κ := Equiv.ofBijective f fb
  let lam := Equiv.ofBijective g gb
  have key : ∀ k z, Φ₂.symm (κ k, lam z) = Φ₁.symm (k, z) := by
    intro k z
    apply Φ₂.injective
    rw [Equiv.apply_symm_apply, Prod.ext_iff, kf, kg]
    simp [κ, lam]
  refine ⟨κ, ?_⟩
  ext x y
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply]
  rw [← Equiv.sum_comp lam]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hx : x = κ (κ.symm x) := (κ.apply_symm_apply x).symm
  have hy : y = κ (κ.symm y) := (κ.apply_symm_apply y).symm
  conv_lhs => rw [hx, hy, key, key]

lemma vn_marg_eq {Ω K₁ F₁ K₂ F₂ : Type*} [Fintype F₁] [Fintype F₂] [Fintype K₁] [Fintype K₂]
    [DecidableEq K₁] [DecidableEq K₂] [DecidableEq F₁]
    (Φ₁ : Ω ≃ K₁ × F₁) (Φ₂ : Ω ≃ K₂ × F₂) [Nonempty K₁] [Nonempty F₁]
    (h1 : ∀ ω ω', (Φ₁ ω).1 = (Φ₁ ω').1 ↔ (Φ₂ ω).1 = (Φ₂ ω').1)
    (h2 : ∀ ω ω', (Φ₁ ω).2 = (Φ₁ ω').2 ↔ (Φ₂ ω).2 = (Φ₂ ω').2) {ρ : Matrix Ω Ω ℂ}
    (hρ : ρ.PosSemidef) :
    QAlgorithms.vnEntropy (marg Φ₂ ρ) = QAlgorithms.vnEntropy (marg Φ₁ ρ) := by
  obtain ⟨κ, hκ⟩ := marg_transport Φ₁ Φ₂ h1 h2 ρ
  rw [hκ, vn_reind _ _ (marg_psd Φ₁ hρ).1]

section four
variable {A B C D : Type*}

def r21 : (A × (B × C)) × D ≃ (A × C) × (B × D) where
  toFun x := ((x.1.1, x.1.2.2), (x.1.2.1, x.2))
  invFun y := ((y.1.1, (y.2.1, y.1.2)), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def r31 : (A × (B × C)) × D ≃ (B × C) × (A × D) where
  toFun x := (x.1.2, (x.1.1, x.2))
  invFun y := ((y.2.1, y.1), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def r1 : (A × (B × C)) × D ≃ C × ((A × B) × D) where
  toFun x := (x.1.2.2, ((x.1.1, x.1.2.1), x.2))
  invFun y := ((y.2.1.1, (y.2.1.2, y.1)), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D]

/-- SSA for a four-part splitting: `S(AC) + S(BC) - S(C) - S(ABC) ≥ 0`, the `D` part discarded. -/
theorem ssa_split {Ω : Type*} [Fintype Ω] [Nonempty A] [Nonempty B] [Nonempty C]
    (Φ : Ω ≃ (A × (B × C)) × D) (ρ : Matrix Ω Ω ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    0 ≤ QAlgorithms.vnEntropy (marg (Φ.trans r21) ρ) +
      QAlgorithms.vnEntropy (marg (Φ.trans r31) ρ) -
      QAlgorithms.vnEntropy (marg (Φ.trans r1) ρ) - QAlgorithms.vnEntropy (marg Φ ρ) := by
  have h := ssa (marg Φ ρ) (marg_psd Φ hρ) (by rw [marg_trace, htr])
  have e1 : trB (marg Φ ρ) = marg (Φ.trans r21) ρ := by
    ext i j
    simp only [trB, marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type]
    rfl
  have e2 : trF (marg Φ ρ) = marg (Φ.trans r31) ρ := by
    ext i j
    simp only [trF, marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type]
    rfl
  have e3 : trF (trF (marg Φ ρ)) = marg (Φ.trans r1) ρ := by
    ext i j
    simp only [trF, marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    rfl
  rw [e3, e1, e2] at h
  exact h

end four
end X6SSA


/-! X6 SSA library, part 8: `S(M Mᴴ) = S(Mᴴ M)` for rectangular `M`, hence complementary
marginals of a pure state have equal entropy. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix
noncomputable section
namespace X6SSA
open Matrix Polynomial

lemma roots_prod {κ : Type*} [Fintype κ] (ν : κ → ℂ) :
    (∏ j, (X - C (ν j))).roots = Multiset.map ν Finset.univ.val := by
  rw [Finset.prod_eq_multiset_prod]
  have : Multiset.map (fun j => X - C (ν j)) Finset.univ.val =
      Multiset.map (fun a => X - C a) (Multiset.map ν Finset.univ.val) := by
    rw [Multiset.map_map]; rfl
  rw [this, Polynomial.roots_multiset_prod_X_sub_C]

lemma sum_of_prod_eq {κ κ' : Type*} [Fintype κ] [Fintype κ'] (ν : κ → ℂ) (ν' : κ' → ℂ)
    (h : ∏ j, (X - C (ν j)) = ∏ j, (X - C (ν' j))) (g : ℂ → ℝ) :
    ∑ j, g (ν j) = ∑ j, g (ν' j) := by
  have h1 := congrArg Polynomial.roots h
  rw [roots_prod, roots_prod] at h1
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  have a1 : Multiset.map (fun j => g (ν j)) Finset.univ.val =
      Multiset.map g (Multiset.map ν Finset.univ.val) := by rw [Multiset.map_map]; rfl
  have a2 : Multiset.map (fun j => g (ν' j)) Finset.univ.val =
      Multiset.map g (Multiset.map ν' Finset.univ.val) := by rw [Multiset.map_map]; rfl
  rw [a1, a2, h1]

lemma vn_eig {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy A = ∑ i, -(hA.eigenvalues i * Real.logb 2 (hA.eigenvalues i)) := by
  unfold QAlgorithms.vnEntropy
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal,
    Complex.re_sum, ← Finset.sum_neg_distrib]
  simp

/-- `S(M Mᴴ) = S(Mᴴ M)`. -/
theorem vn_mul_conj {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : QAlgorithms.vnEntropy (M * Mᴴ) = QAlgorithms.vnEntropy (Mᴴ * M) := by
  have hP : (M * Mᴴ).IsHermitian := isHermitian_mul_conjTranspose_self M
  have hQ : (Mᴴ * M).IsHermitian := isHermitian_conjTranspose_mul_self M
  rw [vn_eig hP, vn_eig hQ]
  let g : ℂ → ℝ := fun z => -(z.re * Real.logb 2 z.re)
  let ν : Fin (Fintype.card n) ⊕ m → ℂ := Sum.elim (fun _ => 0) fun i => (hP.eigenvalues i : ℂ)
  let ν' : Fin (Fintype.card m) ⊕ n → ℂ := Sum.elim (fun _ => 0) fun i => (hQ.eigenvalues i : ℂ)
  have hprod : ∏ j, (X - C (ν j)) = ∏ j, (X - C (ν' j)) := by
    simp only [ν, ν', Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, map_zero, sub_zero,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have e1 := hP.charpoly_eq
    have e2 := hQ.charpoly_eq
    have := charpoly_mul_comm' Mᴴ M
    have c1 : (∏ i, (X - C ((hP.eigenvalues i : ℝ) : ℂ))) = (M * Mᴴ).charpoly := by
      rw [e1]; rfl
    have c2 : (∏ i, (X - C ((hQ.eigenvalues i : ℝ) : ℂ))) = (Mᴴ * M).charpoly := by
      rw [e2]; rfl
    rw [c1, c2]
    exact this.symm
  have := sum_of_prod_eq ν ν' hprod g
  simp only [ν, ν', g, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Complex.zero_re,
    zero_mul, neg_zero, Finset.sum_const_zero, zero_add, Complex.ofReal_re] at this
  exact this

lemma vn_transpose {n : Type*} [Fintype n] [DecidableEq n] {N : Matrix n n ℂ}
    (hN : N.IsHermitian) : QAlgorithms.vnEntropy Nᵀ = QAlgorithms.vnEntropy N := by
  have hT : Nᵀ.IsHermitian := hN.transpose
  rw [vn_eig hT, vn_eig hN]
  have hprod : ∏ j, (X - C ((hT.eigenvalues j : ℝ) : ℂ)) = ∏ j, (X - C ((hN.eigenvalues j : ℝ) : ℂ)) := by
    have e1 := hT.charpoly_eq
    have e2 := hN.charpoly_eq
    have c1 : (∏ i, (X - C ((hT.eigenvalues i : ℝ) : ℂ))) = Nᵀ.charpoly := by rw [e1]; rfl
    have c2 : (∏ i, (X - C ((hN.eigenvalues i : ℝ) : ℂ))) = N.charpoly := by rw [e2]; rfl
    rw [c1, c2, charpoly_transpose]
  have := sum_of_prod_eq _ _ hprod (fun z => -(z.re * Real.logb 2 z.re))
  simpa using this

/-- complementary marginals of a pure state have equal entropy. -/
theorem vn_pure_marginals {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ψ : EuclideanSpace ℂ (m × n)) :
    QAlgorithms.vnEntropy (trR (QAlgorithms.pureDensity ψ)) =
      QAlgorithms.vnEntropy (trF (QAlgorithms.pureDensity ψ)) := by
  let M : Matrix m n ℂ := of fun x y => ψ (x, y)
  have e1 : trR (QAlgorithms.pureDensity ψ) = M * Mᴴ := by
    ext x x'; simp [trR, QAlgorithms.pureDensity, M, mul_apply]
  have e2 : trF (QAlgorithms.pureDensity ψ) = (Mᴴ * M)ᵀ := by
    ext y y'; simp [trF, QAlgorithms.pureDensity, M, mul_apply, mul_comm]
  rw [e1, e2, vn_transpose (isHermitian_conjTranspose_mul_self M), vn_mul_conj]

end X6SSA


/-! X6 channel library, part 1: entropies of complementary marginals of pure states along
abstract splittings, subadditivity along splittings, and the two-channel Stinespring vector
`lam Ψ E F` on `R × (C × (L × K))` with its marginals. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms

section gen
variable {Ω X Y Z : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

lemma pd_psd {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) : (pureDensity v).PosSemidef := by
  have : pureDensity v = Matrix.vecMulVec (v : ι → ℂ) (star (v : ι → ℂ)) := by
    ext i j; simp [pureDensity, Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

omit [Fintype Ω] [DecidableEq Ω] in
/-- complementary marginals of a pure state along a splitting have equal entropy. -/
lemma pure_comp (Φ : Ω ≃ X × Y) (w : EuclideanSpace ℂ Ω) :
    vnEntropy (marg Φ (pureDensity w)) =
      vnEntropy (marg (Φ.trans (Equiv.prodComm X Y)) (pureDensity w)) := by
  let v : EuclideanSpace ℂ (X × Y) := WithLp.toLp 2 fun p => w (Φ.symm p)
  have e1 : marg Φ (pureDensity w) = trR (pureDensity v) := by
    ext i j; simp [marg, trR, pureDensity, v, reindex_apply]
  have e2 : marg (Φ.trans (Equiv.prodComm X Y)) (pureDensity w) = trF (pureDensity v) := by
    ext i j; simp [marg, trR, trF, pureDensity, v, reindex_apply]
  rw [e1, e2, vn_pure_marginals]

def rX : (X × Y) × Z ≃ X × (Y × Z) := Equiv.prodAssoc X Y Z

def rY : (X × Y) × Z ≃ Y × (X × Z) where
  toFun p := (p.1.2, (p.1.1, p.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- subadditivity along a splitting `Ω ≃ (X × Y) × Z`. -/
lemma subadd_split [Nonempty X] [Nonempty Y] (Φ : Ω ≃ (X × Y) × Z) (ρ : Matrix Ω Ω ℂ)
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    vnEntropy (marg Φ ρ) ≤ vnEntropy (marg (Φ.trans rX) ρ) + vnEntropy (marg (Φ.trans rY) ρ) := by
  have h := subadd (marg Φ ρ) (marg_psd Φ hρ) (by rw [marg_trace, htr])
  have e1 : trR (marg Φ ρ) = marg (Φ.trans rX) ρ := by
    ext i j
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type]
    rfl
  have e2 : trF (marg Φ ρ) = marg (Φ.trans rY) ρ := by
    ext i j
    simp only [trF, marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type]
    rfl
  rw [e1, e2] at h
  exact h

lemma pd_trace {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    (pureDensity v).trace = 1 := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [hv] at h
  simp only [Matrix.trace, Matrix.diag_apply, pureDensity, Matrix.of_apply, Complex.mul_conj]
  have : ∑ i, ((Complex.normSq (v i) : ℝ) : ℂ) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [this, ← h]; simp

end gen

section kraus
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

lemma kraus_rank1 {K : Type*} [Fintype K] (E : K → Matrix B A ℂ) (u v : A → ℂ) :
    krausApply E (vecMulVec u (star v)) = ∑ k, vecMulVec (E k *ᵥ u) (star (E k *ᵥ v)) := by
  unfold krausApply
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

lemma kraus_sum {K ι : Type*} [Fintype K] (E : K → Matrix B A ℂ) (s : Finset ι)
    (X : ι → Matrix A A ℂ) : krausApply E (∑ i ∈ s, X i) = ∑ i ∈ s, krausApply E (X i) := by
  show ∑ j, E j * (∑ i ∈ s, X i) * (E j)ᴴ = ∑ i ∈ s, ∑ j, E j * X i * (E j)ᴴ
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_comm

end kraus

end X6CH


/-! X6 channel library, part 2: the two-channel Stinespring vector and its marginals. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms

variable {R A B C K L : Type*} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L]

/-- `ψ(r, a) = Ψ a r`. -/
def vecOf (Ψ : Matrix A R ℂ) : EuclideanSpace ℂ (R × A) := WithLp.toLp 2 fun p => Ψ p.2 p.1

/-- the Stinespring vector of `F ∘ E` applied to `vecOf Ψ`, environments `L` (for `F`) and `K`. -/
def lam (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ) :
    EuclideanSpace ℂ (R × (C × (L × K))) :=
  WithLp.toLp 2 fun x => (F x.2.2.1 * E x.2.2.2 * Ψ) x.2.1 x.1

/-- complementary-channel output `(k, k') ↦ tr(E_k σ E_k'ᴴ)`. -/
def comp (E : K → Matrix B A ℂ) (σ : Matrix A A ℂ) : Matrix K K ℂ :=
  of fun k k' => trace (E k * σ * (E k')ᴴ)

/-- Stinespring isometry of a Kraus family. -/
def stV (F : L → Matrix C B ℂ) : Matrix (C × L) B ℂ := of fun p b => F p.2 p.1 b

def sRC : R × (C × (L × K)) ≃ (R × C) × (L × K) where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun y := (y.1.1, (y.1.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

def sC : R × (C × (L × K)) ≃ C × (R × (L × K)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun y := (y.2.1, (y.1, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def sL : R × (C × (L × K)) ≃ L × (R × (C × K)) where
  toFun x := (x.2.2.1, (x.1, (x.2.1, x.2.2.2)))
  invFun y := (y.2.1, (y.2.2.1, (y.1, y.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

def sK : R × (C × (L × K)) ≃ K × (R × (C × L)) where
  toFun x := (x.2.2.2, (x.1, (x.2.1, x.2.2.1)))
  invFun y := (y.2.1, (y.2.2.1, (y.2.2.2, y.1)))
  left_inv _ := rfl
  right_inv _ := rfl

def sCL : R × (C × (L × K)) ≃ (C × L) × (R × K) where
  toFun x := ((x.2.1, x.2.2.1), (x.1, x.2.2.2))
  invFun y := (y.2.1, (y.1.1, (y.1.2, y.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

lemma mulVec_col (M : Matrix C A ℂ) (Ψ : Matrix A R ℂ) (r : R) :
    (M *ᵥ fun a => Ψ a r) = fun c => (M * Ψ) c r := by
  ext c; simp [mulVec, dotProduct, mul_apply]

lemma gram (Ψ : Matrix A R ℂ) :
    Ψ * Ψᴴ = ∑ r, vecMulVec (fun a => Ψ a r) (star fun a => Ψ a r) := by
  ext a a'; simp [mul_apply, Matrix.sum_apply, vecMulVec_apply]

lemma conj_eq (z : ℂ) : star z = conj z := rfl

lemma trace_mul_conjT {P Q : Type*} [Fintype P] [Fintype Q] (X Y : Matrix P Q ℂ) :
    trace (X * Yᴴ) = ∑ p, ∑ q, X p q * conj (Y p q) := by
  simp [trace, mul_apply, conjTranspose_apply, conj_eq]

lemma mul_conjT_apply {P P' Q : Type*} [Fintype Q] (X : Matrix P Q ℂ) (Y : Matrix P' Q ℂ)
    (p : P) (p' : P') : (X * Yᴴ) p p' = ∑ q, X p q * conj (Y p' q) := by
  simp [mul_apply, conjTranspose_apply, conj_eq]

lemma sum3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

/-- the `C` marginal is the output `F(E(ΨΨᴴ))`. -/
lemma m_C (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ) :
    marg sC (pureDensity (lam Ψ E F)) = krausApply F (krausApply E (Ψ * Ψᴴ)) := by
  rw [gram, kraus_sum]
  simp only [kraus_rank1, kraus_sum, mulVec_mulVec, mulVec_col]
  ext c c'
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, pureDensity, lam, sC,
    Equiv.coe_fn_symm_mk, Matrix.sum_apply, vecMulVec_apply, Fintype.sum_prod_type, Pi.star_apply,
    conj_eq, Matrix.mul_assoc]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact Finset.sum_comm

/-- the `L × K`-free (`R × C`) marginal is `id ⊗ F` after `id ⊗ E`. -/
lemma m_RC (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ) :
    marg sRC (pureDensity (lam Ψ E F)) =
      idTensorSuperop (krausApply F) (idTensorSuperop (krausApply E) (pureDensity (vecOf Ψ))) := by
  ext ⟨r, c⟩ ⟨r', c'⟩
  have h1 : (of fun i i' => (idTensorSuperop (krausApply E) (pureDensity (vecOf Ψ))) (r, i) (r', i'))
      = krausApply E (vecMulVec (fun a => Ψ a r) (star fun a => Ψ a r')) := by
    ext b b'
    simp only [idTensorSuperop, of_apply]
    congr 2
  simp only [idTensorSuperop, of_apply] at h1 ⊢
  rw [h1, kraus_rank1, kraus_sum]
  simp only [kraus_rank1, mulVec_mulVec, mulVec_col]
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, pureDensity, lam, sRC,
    Equiv.coe_fn_symm_mk, Matrix.sum_apply, vecMulVec_apply, Fintype.sum_prod_type, Pi.star_apply,
    conj_eq, Matrix.mul_assoc]
  exact Finset.sum_comm

/-- the `K` marginal is the complementary output of `E`. -/
lemma m_K (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ)
    (hF : ∑ l, (F l)ᴴ * F l = 1) :
    marg sK (pureDensity (lam Ψ E F)) = comp E (Ψ * Ψᴴ) := by
  ext k k'
  have key : trace (E k * (Ψ * Ψᴴ) * (E k')ᴴ) =
      ∑ l, trace ((F l * E k * Ψ) * (F l * E k' * Ψ)ᴴ) := by
    have : ∀ l, trace ((F l * E k * Ψ) * (F l * E k' * Ψ)ᴴ) =
        trace ((F l)ᴴ * F l * (E k * (Ψ * Ψᴴ) * (E k')ᴴ)) := by
      intro l
      rw [show F l * E k * Ψ * (F l * E k' * Ψ)ᴴ = (F l * (E k * (Ψ * Ψᴴ) * (E k')ᴴ)) * (F l)ᴴ by
        simp only [conjTranspose_mul, Matrix.mul_assoc], trace_mul_comm]
      simp only [Matrix.mul_assoc]
    simp only [this, ← trace_sum, ← Matrix.sum_mul, hF, Matrix.one_mul]
  rw [comp, of_apply, key]
  simp only [trace_mul_conjT]
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, pureDensity, lam, sK,
    Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
  exact sum3 _

/-- the `L` marginal is the complementary output of `F` on `E(ΨΨᴴ)`. -/
lemma m_L (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ) :
    marg sL (pureDensity (lam Ψ E F)) = comp F (krausApply E (Ψ * Ψᴴ)) := by
  ext l l'
  have key : trace (F l * krausApply E (Ψ * Ψᴴ) * (F l')ᴴ) =
      ∑ k, trace ((F l * E k * Ψ) * (F l' * E k * Ψ)ᴴ) := by
    show trace (F l * (∑ j, E j * (Ψ * Ψᴴ) * (E j)ᴴ) * (F l')ᴴ) = _
    simp only [Matrix.mul_sum, Matrix.sum_mul, trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [comp, of_apply, key]
  simp only [trace_mul_conjT]
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, pureDensity, lam, sL,
    Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
  exact sum3 _

/-- the `C × L` marginal is the Stinespring image of `E(ΨΨᴴ)`. -/
lemma m_CL (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ) :
    marg sCL (pureDensity (lam Ψ E F)) = stV F * krausApply E (Ψ * Ψᴴ) * (stV F)ᴴ := by
  have hG : ∀ k, stV F * E k * Ψ = of fun (p : C × L) r => (F p.2 * E k * Ψ) p.1 r := by
    intro k; ext p r; simp [stV, mul_apply, Finset.sum_mul, Matrix.mul_assoc]
  have e : stV F * krausApply E (Ψ * Ψᴴ) * (stV F)ᴴ =
      ∑ k, (stV F * E k * Ψ) * (stV F * E k * Ψ)ᴴ := by
    show stV F * (∑ j, E j * (Ψ * Ψᴴ) * (E j)ᴴ) * (stV F)ᴴ = _
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e]
  simp only [hG]
  ext p p'
  simp only [Matrix.sum_apply, mul_conjT_apply, of_apply]
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, pureDensity, lam, sCL,
    Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- the `R` marginal. -/
lemma m_R (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = 1) (hF : ∑ l, (F l)ᴴ * F l = 1) :
    marg (Equiv.refl _) (pureDensity (lam Ψ E F)) = (Ψᴴ * Ψ)ᵀ := by
  have e : Ψᴴ * Ψ = ∑ l, ∑ k, (F l * E k * Ψ)ᴴ * (F l * E k * Ψ) := by
    have : ∀ l k, (F l * E k * Ψ)ᴴ * (F l * E k * Ψ) = Ψᴴ * ((E k)ᴴ * ((F l)ᴴ * F l) * E k) * Ψ := by
      intro l k; simp only [conjTranspose_mul, Matrix.mul_assoc]
    simp only [this]
    rw [Finset.sum_comm]
    simp only [← Matrix.sum_mul, ← Matrix.mul_sum, hF, Matrix.mul_one, hE]
  rw [e]
  ext r r'
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, pureDensity, lam,
    Equiv.refl_symm, Equiv.refl_apply, Fintype.sum_prod_type, Matrix.sum_apply, mul_apply,
    conjTranspose_apply, conj_eq, transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end X6CH


/-! X6 channel library, part 3: isometric invariance, the entropy of `id ⊗ E` on a pure state
equals the entropy of the complementary output, and the four entropy inequalities of the
two-channel Stinespring state. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms

/-- isometric invariance of the entropy. -/
lemma vn_iso {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (X : Matrix n n ℂ) (hX : X.PosSemidef) :
    vnEntropy (V * X * Vᴴ) = vnEntropy X := by
  open scoped MatrixOrder in
  have h0 : (0 : Matrix n n ℂ) ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
  open scoped MatrixOrder in
  have hs : (CFC.sqrt X)ᴴ = CFC.sqrt X :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)).isHermitian.eq
  open scoped MatrixOrder in
  have hX' : X = CFC.sqrt X * CFC.sqrt X := (CFC.sqrt_mul_sqrt_self X h0).symm
  set s := CFC.sqrt X
  have e1 : V * X * Vᴴ = (V * s) * (V * s)ᴴ := by
    rw [conjTranspose_mul, hs]; conv_lhs => rw [hX']
    simp only [Matrix.mul_assoc]
  have e2 : (V * s)ᴴ * (V * s) = X := by
    rw [conjTranspose_mul, hs, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul, ← hX']
  rw [e1, vn_mul_conj, e2]

lemma kraus_psd {A B K : Type*} [Fintype A] [Fintype B] [Fintype K] (E : K → Matrix B A ℂ)
    {X : Matrix A A ℂ} (hX : X.PosSemidef) : (krausApply E X).PosSemidef :=
  Matrix.posSemidef_sum _ fun k _ => hX.mul_mul_conjTranspose_same (E k)

lemma kraus_trace {A B K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [Fintype K]
    (E : K → Matrix B A ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (X : Matrix A A ℂ) :
    trace (krausApply E X) = trace X := by
  show trace (∑ k, E k * X * (E k)ᴴ) = _
  rw [trace_sum]
  have : ∀ k, trace (E k * X * (E k)ᴴ) = trace ((E k)ᴴ * E k * X) := by
    intro k; rw [trace_mul_comm, ← Matrix.mul_assoc]
  simp only [this, ← trace_sum, ← Matrix.sum_mul, hE, Matrix.one_mul]

variable {R A B C K L : Type*} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L]

lemma stV_iso (F : L → Matrix C B ℂ) (hF : ∑ l, (F l)ᴴ * F l = 1) : (stV F)ᴴ * stV F = 1 := by
  rw [← hF]
  ext b b'
  simp only [stV, mul_apply, conjTranspose_apply, of_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  exact Finset.sum_comm

lemma kraus_id (X : Matrix B B ℂ) : krausApply (fun _ : Unit => (1 : Matrix B B ℂ)) X = X := by
  simp [krausApply]

lemma idT_id (Y : Matrix (R × B) (R × B) ℂ) :
    idTensorSuperop (krausApply (fun _ : Unit => (1 : Matrix B B ℂ))) Y = Y := by
  ext p q; simp only [idTensorSuperop, kraus_id, of_apply]

/-- entropy of `id ⊗ E` on a pure state = entropy of the complementary output. -/
theorem sc [Nonempty R] [Nonempty B] [Nonempty K] (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) :
    vnEntropy (idTensorSuperop (krausApply E) (pureDensity (vecOf Ψ))) =
      vnEntropy (comp E (Ψ * Ψᴴ)) := by
  have h := m_RC Ψ E (fun _ : Unit => (1 : Matrix B B ℂ))
  rw [idT_id] at h
  rw [← h, pure_comp, ← m_K Ψ E (fun _ : Unit => (1 : Matrix B B ℂ)) (by simp)]
  refine vn_marg_eq sK _ ?_ ?_ (pd_psd _)
  all_goals intro ω ω'
  all_goals simp only [sK, sRC, Equiv.coe_fn_mk, Equiv.trans_apply, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Prod.ext_iff]
  all_goals simp

section ineq
variable [Nonempty R] [Nonempty C] [Nonempty L] [Nonempty K]

def p1 : R × (C × (L × K)) ≃ (R × (L × K)) × C where
  toFun x := ((x.1, (x.2.2.1, x.2.2.2)), x.2.1)
  invFun y := (y.1.1, (y.2, (y.1.2.1, y.1.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

def p2 : R × (C × (L × K)) ≃ (C × (K × L)) × R where
  toFun x := ((x.2.1, (x.2.2.2, x.2.2.1)), x.1)
  invFun y := (y.2, (y.1.1, (y.1.2.2, y.1.2.1)))
  left_inv _ := rfl
  right_inv _ := rfl

lemma tr_one (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = 1) (hF : ∑ l, (F l)ᴴ * F l = 1) (hΨ : trace (Ψ * Ψᴴ) = 1) :
    trace (pureDensity (lam Ψ E F)) = 1 := by
  rw [← marg_trace (Equiv.refl _), m_R Ψ E F hE hF, trace_transpose, trace_mul_comm, hΨ]

/-- the four inequalities: with `σ = ΨΨᴴ`, `S(K)+S(C) ≤ S(CL)+S(RC)`, `S(R)+S(L) ≤ S(RC)+S(CL)`,
`S(CL) ≤ S(C)+S(L)`, `S(CL) ≤ S(R)+S(K)`. -/
theorem ineqs (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = 1) (hF : ∑ l, (F l)ᴴ * F l = 1) (hΨ : trace (Ψ * Ψᴴ) = 1) :
    let SR := vnEntropy (Ψ * Ψᴴ)
    let SC := vnEntropy (krausApply F (krausApply E (Ψ * Ψᴴ)))
    let SRC := vnEntropy
      (idTensorSuperop (krausApply F) (idTensorSuperop (krausApply E) (pureDensity (vecOf Ψ))))
    let SK := vnEntropy (comp E (Ψ * Ψᴴ))
    let SL := vnEntropy (comp F (krausApply E (Ψ * Ψᴴ)))
    let SCL := vnEntropy (krausApply E (Ψ * Ψᴴ))
    SK + SC ≤ SCL + SRC ∧ SR + SL ≤ SRC + SCL ∧ SCL ≤ SC + SL ∧ SCL ≤ SR + SK := by
  intro SR SC SRC SK SL SCL
  have hP : (pureDensity (lam Ψ E F)).PosSemidef := pd_psd _
  have ht : trace (pureDensity (lam Ψ E F)) = 1 := tr_one Ψ E F hE hF hΨ
  have eR : vnEntropy (marg (Equiv.refl _) (pureDensity (lam Ψ E F))) = SR := by
    rw [m_R Ψ E F hE hF, vn_transpose (isHermitian_conjTranspose_mul_self Ψ), ← vn_mul_conj]
  have eC : vnEntropy (marg sC (pureDensity (lam Ψ E F))) = SC := by rw [m_C]
  have eRC : vnEntropy (marg sRC (pureDensity (lam Ψ E F))) = SRC := by rw [m_RC]
  have eK : vnEntropy (marg sK (pureDensity (lam Ψ E F))) = SK := by rw [m_K Ψ E F hF]
  have eL : vnEntropy (marg sL (pureDensity (lam Ψ E F))) = SL := by rw [m_L]
  have eCL : vnEntropy (marg sCL (pureDensity (lam Ψ E F))) = SCL := by
    rw [m_CL, vn_iso _ (stV_iso F hF) _ (kraus_psd E (posSemidef_self_mul_conjTranspose Ψ))]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ssa_split p1 (pureDensity (lam Ψ E F)) hP ht
    rw [pure_comp (p1.trans r21), pure_comp (p1.trans r31), pure_comp p1] at h
    rw [vn_marg_eq sCL ((p1.trans r21).trans (Equiv.prodComm _ _)) ?_ ?_ hP,
      vn_marg_eq sRC ((p1.trans r31).trans (Equiv.prodComm _ _)) ?_ ?_ hP,
      vn_marg_eq sK (p1.trans r1) ?_ ?_ hP,
      vn_marg_eq sC (p1.trans (Equiv.prodComm _ _)) ?_ ?_ hP, eCL, eRC, eK, eC] at h
    · linarith
    all_goals intro ω ω'
    all_goals simp only [sK, sRC, sCL, sC, p1, r21, r31, r1, Equiv.coe_fn_mk, Equiv.trans_apply,
      Equiv.prodComm_apply, Prod.swap_prod_mk, Prod.ext_iff]
    all_goals tauto
  · have h := ssa_split p2 (pureDensity (lam Ψ E F)) hP ht
    rw [pure_comp (p2.trans r31), pure_comp p2] at h
    rw [vn_marg_eq sCL (p2.trans r21) ?_ ?_ hP,
      vn_marg_eq sRC ((p2.trans r31).trans (Equiv.prodComm _ _)) ?_ ?_ hP,
      vn_marg_eq sL (p2.trans r1) ?_ ?_ hP,
      vn_marg_eq (Equiv.refl _) (p2.trans (Equiv.prodComm _ _)) ?_ ?_ hP, eCL, eRC, eL, eR] at h
    · linarith
    all_goals intro ω ω'
    all_goals simp only [sL, sRC, sCL, p2, r21, r31, r1, Equiv.coe_fn_mk, Equiv.trans_apply,
      Equiv.prodComm_apply, Prod.swap_prod_mk, Prod.ext_iff, Equiv.refl_apply]
    all_goals tauto
  · have h := subadd_split sCL (pureDensity (lam Ψ E F)) hP ht
    rw [vn_marg_eq sC (sCL.trans rX) ?_ ?_ hP, vn_marg_eq sL (sCL.trans rY) ?_ ?_ hP,
      eCL, eC, eL] at h
    · exact h
    all_goals intro ω ω'
    all_goals simp only [sL, sC, sCL, rX, rY, Equiv.coe_fn_mk, Equiv.trans_apply,
      Equiv.prodAssoc_apply, Prod.ext_iff]
    all_goals tauto
  · have h := subadd_split (sCL.trans (Equiv.prodComm _ _)) (pureDensity (lam Ψ E F)) hP ht
    rw [← pure_comp, vn_marg_eq (Equiv.refl _) ((sCL.trans (Equiv.prodComm _ _)).trans rX) ?_ ?_ hP,
      vn_marg_eq sK ((sCL.trans (Equiv.prodComm _ _)).trans rY) ?_ ?_ hP,
      eCL, eR, eK] at h
    · exact h
    all_goals intro ω ω'
    all_goals simp only [sK, sCL, rX, rY, Equiv.coe_fn_mk, Equiv.trans_apply,
      Equiv.prodAssoc_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Prod.ext_iff, Equiv.refl_apply]
    all_goals tauto

end ineq
end X6CH


/-! X6 channel library, part 4: bridge to `entropyExchange`/`inputMutualInfo`/`loss` and the
data-processing inequalities of Adami–Cerf. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

lemma sqrt_herm (ρ : Matrix A A ℂ) : (cfc Real.sqrt ρ)ᴴ = cfc Real.sqrt ρ := by
  have : IsSelfAdjoint (cfc Real.sqrt ρ) := cfc_predicate _ _
  exact this

lemma sqrt_sq {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    cfc Real.sqrt ρ * (cfc Real.sqrt ρ)ᴴ = ρ := by
  open scoped MatrixOrder in
  have h0 : (0 : Matrix A A ℂ) ≤ ρ := Matrix.nonneg_iff_posSemidef.mpr hρ
  rw [sqrt_herm, ← cfc_mul Real.sqrt Real.sqrt ρ]
  conv_rhs => rw [← cfc_id ℝ ρ]
  open scoped MatrixOrder in
  exact cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg h0 hx)

/-- the entropy exchange through the canonical purification. -/
lemma ee_eq (N : Superop A B) {ρ : Matrix A A ℂ} (hρ : ρ.IsHermitian) :
    entropyExchange N ρ =
      vnEntropy (idTensorSuperop N (pureDensity (vecOf (cfc Real.sqrt ρ)))) := by
  unfold entropyExchange
  simp only []
  congr 3
  ext z
  simp only [canonicalPurification, vecOf, PiLp.toLp_apply]
  have h := map_cfc_mat (reind (Fintype.equivFin A)) Real.sqrt ρ hρ
  simp only [reind_apply] at h
  have e : (fun i j => ρ ((Fintype.equivFin A).symm i) ((Fintype.equivFin A).symm j)) =
      reindex (Fintype.equivFin A) (Fintype.equivFin A) ρ := rfl
  rw [e, ← h]
  simp

lemma kraus_of_channel [Nonempty A] {N : Superop A B} (hN : IsChannel N) :
    ∃ (m : ℕ) (E : Fin m → Matrix B A ℂ), 0 < m ∧ ∑ k, (E k)ᴴ * E k = 1 ∧ N = krausApply E := by
  obtain ⟨m, E, hE, hNE⟩ := hN
  refine ⟨m, E, ?_, hE, funext hNE⟩
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    obtain ⟨a⟩ := ‹Nonempty A›
    have := congrFun (congrFun hE a) a
    simp at this
  · exact h

lemma idT_comp {R : Type*} (M : Superop B C) (N : Superop A B) (X : Matrix (R × A) (R × A) ℂ) :
    idTensorSuperop (M ∘ N) X = idTensorSuperop M (idTensorSuperop N X) := rfl

/-- all entropic quantities of the two-channel problem, in terms of the Stinespring state. -/
theorem dpi [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop A B) (M : Superop B C) (hN : IsChannel N) (hM : IsChannel M)
    (ρ : Matrix A A ℂ) (hρ : IsDensityMatrix ρ) :
    inputMutualInfo (M ∘ N) ρ ≤ inputMutualInfo N ρ ∧
    inputMutualInfo N ρ ≤ 2 * vnEntropy ρ ∧
    inputMutualInfo (M ∘ N) ρ ≤ inputMutualInfo M (N ρ) ∧
    inputMutualInfo M (N ρ) ≤ 2 * vnEntropy (M (N ρ)) ∧
    0 ≤ vnEntropy ρ + entropyExchange N ρ - vnEntropy (N ρ) ∧
    vnEntropy ρ + entropyExchange N ρ - vnEntropy (N ρ) ≤
      vnEntropy ρ + entropyExchange (M ∘ N) ρ - vnEntropy (M (N ρ)) := by
  obtain ⟨m, E, hm, hE, rfl⟩ := kraus_of_channel hN
  obtain ⟨m', F, hm', hF, rfl⟩ := kraus_of_channel hM
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nonempty (Fin m') := ⟨⟨0, hm'⟩⟩
  set s := cfc Real.sqrt ρ
  have hs : s * sᴴ = ρ := sqrt_sq hρ.1
  have hΨ : trace (s * sᴴ) = 1 := by rw [hs, hρ.2]
  have hNρ : (krausApply E ρ).PosSemidef := kraus_psd E hρ.1
  set t := cfc Real.sqrt (krausApply E ρ)
  have ht : t * tᴴ = krausApply E ρ := sqrt_sq hNρ
  obtain ⟨i1, i2, i3, i4⟩ := ineqs s E F hE hF hΨ
  simp only [hs] at i1 i2 i3 i4
  have eN : entropyExchange (krausApply E) ρ = vnEntropy (comp E ρ) := by
    rw [ee_eq _ hρ.1.isHermitian, sc, hs]
  have eM : entropyExchange (krausApply F) (krausApply E ρ) =
      vnEntropy (comp F (krausApply E ρ)) := by
    rw [ee_eq _ hNρ.isHermitian, sc, ht]
  have eMN : entropyExchange (krausApply F ∘ krausApply E) ρ =
      vnEntropy (idTensorSuperop (krausApply F)
        (idTensorSuperop (krausApply E) (pureDensity (vecOf s)))) := by
    rw [ee_eq _ hρ.1.isHermitian, idT_comp]
  unfold inputMutualInfo
  simp only [Function.comp_apply, eN, eM, eMN]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- `I(R:A)` of the canonical purification of a density matrix is `2 S(τ)`. -/
lemma mi_pure {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] {τ : Matrix A A ℂ} (hτ : IsDensityMatrix τ) :
    QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation
      (pureDensity (canonicalPurification τ)) = 2 * vnEntropy τ := by
  unfold QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation
  set u := cfc Real.sqrt τ
  have hu : u * uᴴ = τ := sqrt_sq hτ.1
  have hv : canonicalPurification τ = vecOf u := rfl
  have hL : traceLeft (pureDensity (vecOf u)) = u * uᴴ := by
    ext a a'
    simp [traceLeft, pureDensity, vecOf, mul_apply, conjTranspose_apply]
  have hRL : vnEntropy (traceRight (pureDensity (vecOf u))) =
      vnEntropy (traceLeft (pureDensity (vecOf u))) := vn_pure_marginals (vecOf u)
  let Mv : Matrix (A × A) Unit ℂ := of fun p _ => vecOf u p
  have h1 : pureDensity (vecOf u) = Mv * Mvᴴ := by
    ext p q; simp [pureDensity, Mv, mul_apply, conjTranspose_apply]
  have h2 : Mvᴴ * Mv = 1 := by
    ext i j
    have : (Mvᴴ * Mv) i j = trace (u * uᴴ) := by
      simp only [Mv, mul_apply, conjTranspose_apply, of_apply, trace, diag_apply, vecOf,
        PiLp.toLp_apply, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun r _ => ?_
      simp [mul_comm]
    rw [this, hu, hτ.2]; simp [one_apply]
  rw [hv, hRL, hL, hu, h1, vn_mul_conj, h2, vn_one]
  ring

end X6CH


/-! X6 channel library, part 5: the loss/information balance for a single Kraus channel, via the
Stinespring state `lam Ψ E 1`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)
open QAlgorithms.Papers.Independent.Gap48.P33

variable {A B K : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype K] [DecidableEq K]

/-- the identity Kraus family. -/
def F0 : Unit → Matrix B B ℂ := fun _ => 1

lemma kraus_F0 (X : Matrix B B ℂ) : krausApply (F0 (B := B)) X = X := kraus_id X

lemma idT_F0 {R : Type*} [Fintype R] [DecidableEq R] (Y : Matrix (R × B) (R × B) ℂ) :
    idTensorSuperop (krausApply (F0 (B := B))) Y = Y := idT_id Y

lemma F0_kraus : ∑ l, (F0 (B := B) l)ᴴ * F0 l = 1 := by simp [F0]

lemma vn_pd_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι)
    (h : trace (pureDensity v) = 1) : vnEntropy (pureDensity v) = 0 := by
  let Mv : Matrix ι Unit ℂ := of fun p _ => v p
  have h1 : pureDensity v = Mv * Mvᴴ := by
    ext p q; simp [pureDensity, Mv, mul_apply, conjTranspose_apply]
  have h2 : Mvᴴ * Mv = 1 := by
    ext i j
    have : (Mvᴴ * Mv) i j = trace (pureDensity v) := by
      simp only [Mv, mul_apply, conjTranspose_apply, of_apply, trace, diag_apply, pureDensity]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [mul_comm]
    rw [this, h]; simp [one_apply]
  rw [h1, vn_mul_conj, h2, vn_one]

lemma comp_F0 (σ : Matrix B B ℂ) (hσ : trace σ = 1) : vnEntropy (comp (F0 (B := B)) σ) = 0 := by
  have : comp (F0 (B := B)) σ = 1 := by
    ext i j; simp [comp, F0, hσ, one_apply]
  rw [this, vn_one]

def sKB : A × (B × (Unit × K)) ≃ (K × B) × (A × Unit) where
  toFun x := ((x.2.2.2, x.2.1), (x.1, x.2.2.1))
  invFun y := (y.2.1, (y.1.2, (y.2.2, y.1.1)))
  left_inv _ := rfl
  right_inv _ := rfl

def sRK : A × (B × (Unit × K)) ≃ (A × K) × (B × Unit) where
  toFun x := ((x.1, x.2.2.2), (x.2.1, x.2.2.1))
  invFun y := (y.1.1, (y.2.1, (y.2.2, y.1.2)))
  left_inv _ := rfl
  right_inv _ := rfl

theorem balance [Nonempty A] [Nonempty B] [Nonempty K]
    (E : K → Matrix B A ℂ) (hE : IsKrausFamily E)
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    let N := krausApply E
    let omega := pureDensity (dilationReference E (canonicalPurification rho))
    loss N rho = middleConditionalInformation omega ∧
    loss N rho = QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation
      (discardMiddle omega) ∧
    entropyExchange N rho = vnEntropy (traceLeft (traceLeft omega)) ∧
    0 ≤ loss N rho ∧ loss N rho ≤ 2 * min (vnEntropy rho) (entropyExchange N rho) ∧
    inputMutualInfo N rho + loss N rho = 2 * vnEntropy rho ∧
    0 ≤ inputMutualInfo N rho ∧ inputMutualInfo N rho ≤ 2 * vnEntropy rho := by
  intro N omega
  have hE' : ∑ k, (E k)ᴴ * E k = 1 := hE
  set s := cfc Real.sqrt rho
  have hs : s * sᴴ = rho := sqrt_sq hrho.1
  have hΨ : trace (s * sᴴ) = 1 := by rw [hs, hrho.2]
  have hNρ : (krausApply E rho).PosSemidef := kraus_psd E hrho.1
  have htN : trace (krausApply E rho) = 1 := by rw [kraus_trace E hE', hrho.2]
  set P := pureDensity (lam s E (F0 (B := B)))
  have hP : P.PosSemidef := pd_psd _
  have hPt : trace P = 1 := tr_one s E F0 hE' F0_kraus hΨ
  -- entries of omega
  have hω : ∀ x y : A × (B × K), omega x y =
      P (x.1, (x.2.1, ((), x.2.2))) (y.1, (y.2.1, ((), y.2.2))) := by
    intro x y
    simp [omega, P, pureDensity, dilationReference, lam, F0, canonicalPurification, s, mul_apply]
  -- entropies of the Stinespring state
  obtain ⟨i1, i2, i3, i4⟩ := ineqs s E (F0 (B := B)) hE' F0_kraus hΨ
  simp only [hs, kraus_F0, idT_F0, comp_F0 _ htN] at i1 i2 i3 i4
  rw [← ee_eq _ hrho.1.isHermitian] at i1 i2
  have eEE : entropyExchange N rho = vnEntropy (comp E rho) := by
    rw [ee_eq _ hrho.1.isHermitian, sc, hs]
  have eR : vnEntropy (marg (Equiv.refl _) P) = vnEntropy rho := by
    rw [m_R s E F0 hE' F0_kraus, vn_transpose (isHermitian_conjTranspose_mul_self s), ← vn_mul_conj,
      hs]
  have eC : vnEntropy (marg sC P) = vnEntropy (N rho) := by
    rw [m_C, kraus_F0, hs]
  have eRC : vnEntropy (marg sRC P) = entropyExchange N rho := by
    rw [m_RC, idT_F0, ee_eq _ hrho.1.isHermitian]
  have eK : vnEntropy (marg sK P) = entropyExchange N rho := by
    rw [m_K s E F0 F0_kraus, hs, eEE]
  have eCL : vnEntropy (marg sCL P) = vnEntropy (N rho) := by
    rw [m_CL, vn_iso _ (stV_iso F0 F0_kraus) _ (kraus_psd E (posSemidef_self_mul_conjTranspose s)), hs]
  have eKB : vnEntropy (marg sKB P) = vnEntropy rho := by
    rw [pure_comp, ← eR]
    refine vn_marg_eq (Equiv.refl _) _ ?_ ?_ hP
    all_goals intro ω ω'
    all_goals simp only [sKB, Equiv.coe_fn_mk, Equiv.trans_apply, Equiv.prodComm_apply,
      Prod.swap_prod_mk, Prod.ext_iff, Equiv.refl_apply]
    all_goals (try simp)
    all_goals (try tauto)
  have eRK : vnEntropy (marg sRK P) = vnEntropy (N rho) := by
    rw [pure_comp, ← eCL]
    refine vn_marg_eq sCL _ ?_ ?_ hP
    all_goals intro ω ω'
    all_goals simp only [sRK, sCL, Equiv.coe_fn_mk, Equiv.trans_apply, Equiv.prodComm_apply,
      Prod.swap_prod_mk, Prod.ext_iff]
    all_goals (try simp)
    all_goals (try tauto)
  have sub : vnEntropy (marg sRC P) ≤ vnEntropy (marg (Equiv.refl _) P) + vnEntropy (marg sC P) := by
    have h := subadd_split sRC P hP hPt
    rw [vn_marg_eq (Equiv.refl _) (sRC.trans rX) ?_ ?_ hP, vn_marg_eq sC (sRC.trans rY) ?_ ?_ hP] at h
    · exact h
    all_goals intro ω ω'
    all_goals simp only [sRC, sC, rX, rY, Equiv.coe_fn_mk, Equiv.trans_apply,
      Equiv.prodAssoc_apply, Prod.ext_iff, Equiv.refl_apply]
    all_goals tauto
  -- the matrices of the statement as marginals
  have hM0 : vnEntropy omega = 0 := vn_pd_zero _ (by
    show trace omega = 1
    rw [← hPt]
    simp only [trace, diag_apply, hω, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
    try rfl)
  have hMCI : middleConditionalInformation omega = vnEntropy (marg sRC P) +
      vnEntropy (marg sKB P) - vnEntropy (marg sC P) := by
    show vnEntropy (fun i j : A × B => ∑ b : K, omega (i.1, (i.2, b)) (j.1, (j.2, b))) +
      vnEntropy (fun i j : K × B => ∑ a : A, omega (a, (i.2, i.1)) (a, (j.2, j.1))) -
      vnEntropy (traceLeft (fun x y : (A × K) × B => omega (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2)))) -
      vnEntropy (fun x y : (A × K) × B => omega (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2))) = _
    have e4 : vnEntropy (fun x y : (A × K) × B => omega (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2))) =
        vnEntropy omega := by
      have := vn_reind (show A × (B × K) ≃ (A × K) × B from
        { toFun := fun x => ((x.1, x.2.2), x.2.1), invFun := fun y => (y.1.1, (y.2, y.1.2)),
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }) omega (pd_psd _).1
      exact this
    have h1 : (fun i j : A × B => ∑ b : K, omega (i.1, (i.2, b)) (j.1, (j.2, b))) = marg sRC P := by
      ext i j
      simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, sRC, Equiv.coe_fn_symm_mk,
        Fintype.sum_prod_type, hω]
      simp
    have h2 : (fun i j : K × B => ∑ a : A, omega (a, (i.2, i.1)) (a, (j.2, j.1))) = marg sKB P := by
      ext i j
      simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, sKB, Equiv.coe_fn_symm_mk,
        Fintype.sum_prod_type, hω]
      simp
    have h3 : traceLeft (fun x y : (A × K) × B => omega (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2))) =
        marg sC P := by
      ext i j
      simp only [traceLeft, marg, trR, reindex_apply, submatrix_apply, of_apply, sC,
        Equiv.coe_fn_symm_mk, Fintype.sum_prod_type, hω]
      simp
    rw [e4, hM0, h1, h2, h3]; ring
  have hD : discardMiddle omega = marg sRK P := by
    ext i j
    simp only [discardMiddle, marg, trR, reindex_apply, submatrix_apply, of_apply, sRK,
      Equiv.coe_fn_symm_mk, Fintype.sum_prod_type, hω]
    simp
  have hDR : traceRight (marg sRK P) = marg (Equiv.refl _) P := by
    ext i j
    simp only [traceRight, marg, trR, reindex_apply, submatrix_apply, of_apply, sRK,
      Equiv.coe_fn_symm_mk, Fintype.sum_prod_type, Equiv.refl_symm, Equiv.refl_apply]
    try simp only [Finset.univ_unique, Finset.sum_singleton]
    try exact Finset.sum_comm
  have hDL : traceLeft (marg sRK P) = marg sK P := by
    ext i j
    simp only [traceLeft, marg, trR, reindex_apply, submatrix_apply, of_apply, sRK, sK,
      Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
    try simp only [Finset.univ_unique, Finset.sum_singleton]
    try rfl
  have hLL : traceLeft (traceLeft omega) = marg sK P := by
    ext i j
    simp only [traceLeft, marg, trR, reindex_apply, submatrix_apply, of_apply, sK,
      Equiv.coe_fn_symm_mk, Fintype.sum_prod_type, hω]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact Finset.sum_comm
  have hL : loss N rho = vnEntropy rho + entropyExchange N rho - vnEntropy (N rho) := rfl
  have hI : inputMutualInfo N rho = vnEntropy rho + vnEntropy (N rho) - entropyExchange N rho := rfl
  rw [eR, eC, eRC] at sub
  rw [← eEE] at i4
  have hmin : 2 * min (vnEntropy rho) (entropyExchange N rho) =
      min (2 * vnEntropy rho) (2 * entropyExchange N rho) :=
    mul_min_of_nonneg _ _ (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hMCI, eRC, eKB, eC, hL]; ring
  · unfold QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation
    rw [hD, hDR, hDL, eR, eK, eRK, hL]
  · rw [hLL, eK]
  · rw [hL]; linarith
  · rw [hmin, hL]; exact le_min (by linarith) (by linarith)
  · rw [hL, hI]; ring
  · rw [hI]; linarith
  · rw [hI]; linarith

end X6CH


noncomputable section

open Polynomial

namespace X6G41D

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma spec_sub (d : n → ℝ) : spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ))) ⊆ Set.range d := by
  intro μ hμ
  by_contra hc
  rw [spectrum.mem_iff] at hμ
  apply hμ
  have e : (μ • 1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => (μ : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Complex.real_smul]
    · simp [Matrix.one_apply, h]
  rw [Algebra.algebraMap_eq_smul_one, e, Matrix.diagonal_sub,
    Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  simp only [isUnit_iff_ne_zero, ne_eq, sub_eq_zero]
  intro h
  apply hc
  refine ⟨i, ?_⟩
  have := congrArg Complex.re h
  simpa using this.symm

lemma aeval_diag (d : n → ℝ) (P : ℝ[X]) :
    aeval (Matrix.diagonal (fun i => (d i : ℂ))) P =
      Matrix.diagonal (fun i => ((P.eval (d i) : ℝ) : ℂ)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Matrix.diagonal_add]
  | monomial k a =>
    rw [aeval_monomial, Matrix.diagonal_pow, Algebra.algebraMap_eq_smul_one, smul_one_mul,
      ← Matrix.diagonal_smul]
    congr 1; funext i
    simp only [eval_monomial, Pi.smul_apply, Pi.pow_apply, Complex.real_smul]
    push_cast; ring

lemma cfc_diag (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  set S := Finset.univ.image d
  set P := Lagrange.interpolate S id f
  have hP : ∀ i, P.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    rwa [id] at this
  have hsa : IsSelfAdjoint (Matrix.diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  rw [cfc_congr (g := fun t => P.eval t), cfc_polynomial P _ hsa, aeval_diag]
  · congr 1; funext i; rw [hP]
  · intro t ht
    obtain ⟨i, rfl⟩ := spec_sub d ht
    exact (hP i).symm

end X6G41D


/-! X6 channel library, part 6: entropy of block-diagonal (classical-quantum) states, concavity of
the conditional entropy `S(XY) - S(Y)` and of the entropy, from strong subadditivity. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms Real

lemma vn_diag' {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) :
    vnEntropy (Matrix.diagonal fun i => (f i : ℂ)) = ∑ i, negMulLog (f i) / log 2 := by
  unfold vnEntropy
  rw [X6G41D.cfc_diag, Matrix.trace_diagonal, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.ofReal_re, Real.logb, negMulLog]
  ring

lemma vn_eig' {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    vnEntropy A = ∑ i, negMulLog (hA.eigenvalues i) / log 2 := by
  rw [vn_eig hA]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Real.logb, negMulLog]
  ring

lemma eig_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (htr : trace A = 1) : ∑ i, hA.eigenvalues i = 1 := by
  have h := hA.trace_eq_sum_eigenvalues
  rw [htr] at h
  have h2 : ((∑ i, hA.eigenvalues i : ℝ) : ℂ) = 1 := by rw [h]; push_cast; rfl
  exact_mod_cast h2

section blocks
variable {Z J : Type*} [Fintype Z] [DecidableEq Z] [Fintype J] [DecidableEq J]

/-- entropy of a block-diagonal mixture `⊕_j w_j ω_j`, in bits. -/
theorem blk_ent (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (ω : J → Matrix Z Z ℂ)
    (hω : ∀ j, (ω j).PosSemidef) (htr : ∀ j, trace (ω j) = 1) :
    vnEntropy (blockDiagonal fun j => (w j : ℂ) • ω j) =
      ∑ j, negMulLog (w j) / log 2 + ∑ j, w j * vnEntropy (ω j) := by
  let U : J → Matrix Z Z ℂ := fun j => ((hω j).1.eigenvectorUnitary : Matrix Z Z ℂ)
  let lam : J → Z → ℝ := fun j => (hω j).1.eigenvalues
  have hU : ∀ j, (U j)ᴴ * U j = 1 := fun j =>
    Unitary.star_mul_self_of_mem (hω j).1.eigenvectorUnitary.2
  have hdec : ∀ j, (w j : ℂ) • ω j =
      U j * diagonal (fun i => ((w j * lam j i : ℝ) : ℂ)) * (U j)ᴴ := by
    intro j
    have h := (hω j).1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    conv_lhs => rw [h]
    have : diagonal (fun i => ((w j * lam j i : ℝ) : ℂ)) =
        (w j : ℂ) • diagonal (RCLike.ofReal ∘ (hω j).1.eigenvalues) := by
      ext a b; by_cases hab : a = b <;> simp [diagonal_apply, hab, lam]
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have hB : (blockDiagonal fun j => (w j : ℂ) • ω j) =
      blockDiagonal U * diagonal (fun p : Z × J => ((w p.2 * lam p.2 p.1 : ℝ) : ℂ)) *
        (blockDiagonal U)ᴴ := by
    simp only [hdec]
    rw [blockDiagonal_mul, blockDiagonal_mul, blockDiagonal_conjTranspose, blockDiagonal_diagonal]
  have hW : (blockDiagonal U)ᴴ * blockDiagonal U = 1 := by
    rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp only [hU]
    exact blockDiagonal_one
  have hD : (diagonal (fun p : Z × J => ((w p.2 * lam p.2 p.1 : ℝ) : ℂ))).PosSemidef := by
    refine Matrix.posSemidef_diagonal_iff.mpr fun p => ?_
    have := (hω p.2).eigenvalues_nonneg p.1
    exact_mod_cast mul_nonneg (hw p.2) this
  rw [hB, vn_iso _ hW _ hD, vn_diag']
  have key : ∀ j, ∑ i, negMulLog (w j * lam j i) / log 2 =
      negMulLog (w j) / log 2 + w j * vnEntropy (ω j) := by
    intro j
    simp only [negMulLog_mul, add_div, Finset.sum_add_distrib]
    rw [vn_eig' (hω j).1, Finset.mul_sum]
    congr 1
    · rw [← Finset.sum_div, ← Finset.sum_mul, eig_sum (hω j).1 (htr j), one_mul]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [lam]; ring
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [key, Finset.sum_add_distrib]

end blocks

section concave
variable {X Y J : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype J] [DecidableEq J]

lemma psd_smul {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) : ((c : ℂ) • M).PosSemidef := by
  have := hM.smul (show (0 : ℂ) ≤ (c : ℂ) from by exact_mod_cast hc)
  exact this

lemma blk_psd {Z : Type*} [Fintype Z] [DecidableEq Z] (M : J → Matrix Z Z ℂ)
    (hM : ∀ j, (M j).PosSemidef) : (blockDiagonal M).PosSemidef := by
  let P : J → Matrix Z (Z × J) ℂ := fun j => of fun z p => if p = (z, j) then 1 else 0
  have : blockDiagonal M = ∑ j, (P j)ᴴ * M j * P j := by
    ext p q
    simp only [blockDiagonal_apply, Matrix.sum_apply, mul_apply, conjTranspose_apply, P, of_apply]
    simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Prod.ext_iff]
    obtain ⟨z, j⟩ := p
    obtain ⟨z', j'⟩ := q
    simp only
    by_cases h : j = j'
    · subst h
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · rw [if_neg h]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      by_cases h1 : j = b
      · subst h1; simp [h, Ne.symm h]
      · simp [h1]
  rw [this]
  exact Matrix.posSemidef_sum _ fun j _ => (hM j).conjTranspose_mul_mul_same (P j)

/-- concavity of the conditional entropy `S(XY) - S(Y)` (from SSA). -/
theorem cond_concave [Nonempty X] [Nonempty Y] (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (ω : J → Matrix (X × Y) (X × Y) ℂ) (hω : ∀ j, IsDensityMatrix (ω j)) :
    ∑ j, w j * (vnEntropy (ω j) - vnEntropy (trF (ω j))) ≤
      vnEntropy (∑ j, (w j : ℂ) • ω j) - vnEntropy (trF (∑ j, (w j : ℂ) • ω j)) := by
  haveI : Nonempty J := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  let e : (X × Y) × J ≃ X × (J × Y) :=
    { toFun := fun p => (p.1.1, (p.2, p.1.2)), invFun := fun q => ((q.1, q.2.2), q.2.1),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let e' : Y × J ≃ J × Y := Equiv.prodComm Y J
  set Bl := blockDiagonal fun j => (w j : ℂ) • ω j
  set τ := reindex e e Bl
  have hBl : Bl.PosSemidef := blk_psd _ fun j => psd_smul (hω j).1 (hw j)
  have hτ : τ.PosSemidef := by simp only [τ, reindex_apply]; exact hBl.submatrix _
  have hτt : trace τ = 1 := by
    simp only [τ]
    rw [trace_reind, trace_blockDiagonal]
    simp only [trace_smul, (hω _).2, smul_eq_mul, mul_one]
    exact_mod_cast hw1
  have h := ssa τ hτ hτt
  have e1 : trB τ = ∑ j, (w j : ℂ) • ω j := by
    ext p q
    simp only [trB, τ, reindex_apply, submatrix_apply, of_apply, Bl, blockDiagonal_apply, e,
      Equiv.coe_fn_symm_mk, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simp
  have e2 : trF τ = reindex e' e' (blockDiagonal fun j => (w j : ℂ) • trF (ω j)) := by
    ext p q
    simp only [trF, τ, reindex_apply, submatrix_apply, of_apply, Bl, blockDiagonal_apply, e, e',
      Equiv.coe_fn_symm_mk, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
      Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [Finset.mul_sum]
  have e3 : trF (trF τ) = trF (∑ j, (w j : ℂ) • ω j) := by
    rw [← e1, trF_trB]
  have hT : vnEntropy τ = ∑ j, negMulLog (w j) / log 2 + ∑ j, w j * vnEntropy (ω j) := by
    simp only [τ]
    rw [vn_reind _ _ hBl.1, blk_ent w hw ω (fun j => (hω j).1) fun j => (hω j).2]
  have hT2 : vnEntropy (trF τ) =
      ∑ j, negMulLog (w j) / log 2 + ∑ j, w j * vnEntropy (trF (ω j)) := by
    rw [e2, vn_reind _ _ (blk_psd _ fun j => psd_smul (trF_psd (hω j).1) (hw j)).1,
      blk_ent w hw _ (fun j => trF_psd (hω j).1) fun j => by rw [trace_trF, (hω j).2]]
  rw [e1, e3, hT, hT2] at h
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

/-- concavity of the entropy. -/
theorem ent_concave {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (σ : J → Matrix Z Z ℂ)
    (hσ : ∀ j, IsDensityMatrix (σ j)) :
    ∑ j, w j * vnEntropy (σ j) ≤ vnEntropy (∑ j, (w j : ℂ) • σ j) := by
  let e : Z ≃ Z × Unit := addU1
  have h := cond_concave (X := Z) (Y := Unit) w hw hw1 (fun j => reindex e e (σ j)) fun j =>
    ⟨by rw [reindex_apply]; exact (hσ j).1.submatrix _, by rw [trace_reind, (hσ j).2]⟩
  have t1 : ∀ M : Matrix Z Z ℂ, trace M = 1 → trF (reindex e e M) = 1 := by
    intro M hM
    ext i j
    have : trF (reindex e e M) i j = trace M := by
      simp [trF, e, addU1, trace, reindex_apply]
    rw [this, hM]; simp
  have hsum : ∑ j, (w j : ℂ) • reindex e e (σ j) = reindex e e (∑ j, (w j : ℂ) • σ j) := by
    ext a b; simp [reindex_apply, Matrix.sum_apply]
  have htr : trace (∑ j, (w j : ℂ) • σ j) = 1 := by
    rw [trace_sum]; simp only [trace_smul, (hσ _).2, smul_eq_mul, mul_one]; exact_mod_cast hw1
  have hH : (∑ j, (w j : ℂ) • σ j).IsHermitian :=
    (Matrix.posSemidef_sum _ fun j _ => psd_smul (hσ j).1 (hw j)).1
  rw [hsum, t1 _ htr, vn_one, vn_reind _ _ hH] at h
  have r1 : ∀ j, vnEntropy (reindex e e (σ j)) = vnEntropy (σ j) := fun j => vn_reind _ _ (hσ j).1.1
  have r2 : ∀ j, vnEntropy (trF (reindex e e (σ j))) = 0 := fun j => by rw [t1 _ (hσ j).2, vn_one]
  simp only [r1, r2, sub_zero] at h
  exact h

end concave
end X6CH


/-! X6: additivity of the von Neumann entropy on Kronecker products of density matrices. -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6KR
open Matrix X6SSA X6CH QAlgorithms Real

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  conv_lhs => rw [hX.spectral_theorem]
  rfl

lemma unit_iso (U : Matrix.unitaryGroup ι ℂ) : (U : Matrix ι ι ℂ)ᴴ * U = 1 :=
  (Matrix.mem_unitaryGroup_iff'.1 U.2)

theorem vn_kron {X : Matrix ι ι ℂ} {Y : Matrix κ κ ℂ} (hX : IsDensityMatrix X)
    (hY : IsDensityMatrix Y) : vnEntropy (X ⊗ₖ Y) = vnEntropy X + vnEntropy Y := by
  set U := hX.1.1.eigenvectorUnitary
  set V := hY.1.1.eigenvectorUnitary
  set lam := hX.1.1.eigenvalues
  set μ := hY.1.1.eigenvalues
  set W : Matrix (ι × κ) (ι × κ) ℂ := (U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ)
  have hW : Wᴴ * W = 1 := by
    simp only [W, conjTranspose_kronecker, ← mul_kronecker_mul, unit_iso, one_kronecker_one]
  have hXY : X ⊗ₖ Y = W * (diagonal fun p : ι × κ => ((lam p.1 * μ p.2 : ℝ) : ℂ)) * Wᴴ := by
    conv_lhs => rw [spec hX.1.1, spec hY.1.1]
    rw [mul_kronecker_mul, mul_kronecker_mul, diagonal_kronecker_diagonal]
    simp only [W, conjTranspose_kronecker]
    push_cast
    rfl
  have hl : ∀ i, 0 ≤ lam i := hX.1.eigenvalues_nonneg
  have hm : ∀ j, 0 ≤ μ j := hY.1.eigenvalues_nonneg
  have hD : (diagonal fun p : ι × κ => ((lam p.1 * μ p.2 : ℝ) : ℂ)).PosSemidef :=
    PosSemidef.diagonal fun p => by
      simp only [Pi.zero_apply]
      exact_mod_cast mul_nonneg (hl p.1) (hm p.2)
  rw [hXY, vn_iso W hW _ hD, vn_diag', vn_eig' hX.1.1, vn_eig' hY.1.1, Fintype.sum_prod_type]
  have s1 := eig_sum hX.1.1 hX.2
  have s2 := eig_sum hY.1.1 hY.2
  simp only [Real.negMulLog_mul, add_div, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y => lam x * negMulLog (μ y) / log 2)]
  simp only [mul_div_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [← Finset.sum_div] at *
  rw [s2]
  have : ∑ x, lam x = 1 := s1
  simp only [Finset.sum_mul, Finset.mul_sum] at *
  rw [← Finset.sum_mul, this]
  ring

end X6KR


/-! X6 CEMI library, part 1: entropies of `registerMarginal`s in the Claimed50.P33 register
framework as entropies of marginals along abstract splittings. -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33 X6SSA

section reg
variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]

/-- the canonical splitting of the register basis along `s`. -/
def spl (D : Fin n → Type) (s : Finset (Fin n)) :
    RegisterBasis D ≃ SubBasis D s × ((i : {i : Fin n // ¬ i ∈ s}) → D i.val) :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) D

lemma spl_symm_apply (s : Finset (Fin n)) (a : SubBasis D s)
    (z : (i : {i : Fin n // ¬ i ∈ s}) → D i.val) (i : Fin n) :
    (spl D s).symm (a, z) i = if h : i ∈ s then a ⟨i, h⟩ else z ⟨i, h⟩ := rfl

lemma cond_iff (s : Finset (Fin n)) (a b : SubBasis D s)
    (z : (i : {i : Fin n // ¬ i ∈ s}) → D i.val) (x y : RegisterBasis D) :
    (x = (spl D s).symm (a, z) ∧ y = (spl D s).symm (b, z)) ↔
      (((∀ i (hi : i ∈ s), x i = a ⟨i, hi⟩ ∧ y i = b ⟨i, hi⟩) ∧ (∀ i, i ∉ s → x i = y i)) ∧
        z = ((spl D s) x).2) := by
  constructor
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
    · simp [spl_symm_apply, hi]
    · simp [spl_symm_apply, hi]
    · funext i
      simp [spl, Equiv.piEquivPiSubtypeProd, i.2]
  · rintro ⟨⟨h1, h2⟩, rfl⟩
    constructor
    · funext i
      rw [spl_symm_apply]
      split_ifs with hi
      · exact (h1 i hi).1
      · rfl
    · funext i
      rw [spl_symm_apply]
      split_ifs with hi
      · exact (h1 i hi).2
      · exact (h2 i hi).symm

lemma rm_eq (ω : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (s : Finset (Fin n)) :
    registerMarginal (trivialExtension ω) s =
      reindex (Equiv.prodPUnit _).symm (Equiv.prodPUnit _).symm (marg (spl D s) ω) := by
  classical
  ext ⟨a, u⟩ ⟨b, v⟩
  simp only [registerMarginal, trivialExtension, reindex_apply, submatrix_apply,
    Equiv.symm_symm, Equiv.prodPUnit_apply, marg, trR, of_apply]
  symm
  calc ∑ z, ω ((spl D s).symm (a, z)) ((spl D s).symm (b, z))
      = ∑ z, ∑ x, ∑ y, if x = (spl D s).symm (a, z) ∧ y = (spl D s).symm (b, z)
          then ω x y else 0 := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Fintype.sum_eq_single ((spl D s).symm (a, z))]
        · rw [Fintype.sum_eq_single ((spl D s).symm (b, z))]
          · simp
          · intro y hy; simp [hy]
        · intro x hx
          refine Finset.sum_eq_zero fun y _ => ?_
          simp [hx]
    _ = ∑ x, ∑ y, ∑ z, if x = (spl D s).symm (a, z) ∧ y = (spl D s).symm (b, z)
          then ω x y else 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        simp_rw [cond_iff s a b _ x y]
        rw [Fintype.sum_eq_single ((spl D s) x).2]
        · simp only [and_true]
        · intro z hz; simp [hz]

lemma vn_inst {ι : Type*} [Fintype ι] (i1 i2 : DecidableEq ι) (M : Matrix ι ι ℂ) :
    @vnEntropy ι _ i1 M = @vnEntropy ι _ i2 M := by
  congr

/-- entropy of a register subset = entropy of the marginal along the canonical splitting. -/
lemma ent_spl [∀ i, Nonempty (D i)] (ω : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hω : ω.PosSemidef) (s : Finset (Fin n)) :
    entropyAt (trivialExtension ω) s = by classical exact vnEntropy (marg (spl D s) ω) := by
  classical
  unfold entropyAt
  rw [rm_eq]
  rw [vn_inst _ (instDecidableEqProd) _, vn_reind _ _ (marg_psd _ hω).1]

lemma spl_fst_iff (s : Finset (Fin n)) (x y : RegisterBasis D) :
    ((spl D s) x).1 = ((spl D s) y).1 ↔ ∀ i ∈ s, x i = y i := by
  constructor
  · intro h i hi; exact congrFun h ⟨i, hi⟩
  · intro h; funext i; exact h i.1 i.2

lemma spl_snd_iff (s : Finset (Fin n)) (x y : RegisterBasis D) :
    ((spl D s) x).2 = ((spl D s) y).2 ↔ ∀ i ∉ s, x i = y i := by
  constructor
  · intro h i hi; exact congrFun h ⟨i, hi⟩
  · intro h; funext i; exact h i.1 i.2

/-- entropy of a register subset via any splitting carrying the same information. -/
lemma ent_eq [∀ i, Nonempty (D i)] {K F : Type*} [Fintype K] [DecidableEq K] [Fintype F]
    (Φ : RegisterBasis D ≃ K × F) (ω : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hω : ω.PosSemidef) (s : Finset (Fin n))
    (h1 : ∀ x y, (Φ x).1 = (Φ y).1 ↔ ∀ i ∈ s, x i = y i)
    (h2 : ∀ x y, (Φ x).2 = (Φ y).2 ↔ ∀ i ∉ s, x i = y i) :
    entropyAt (trivialExtension ω) s = vnEntropy (marg Φ ω) := by
  classical
  rw [ent_spl ω hω s]
  exact (vn_marg_eq (spl D s) Φ (fun x y => by rw [spl_fst_iff, h1])
    (fun x y => by rw [spl_snd_iff, h2]) hω).symm

end reg

lemma marg_comp {Ω P K G F : Type*} [Fintype G] [Fintype F] (Φ : Ω ≃ P × F) (Ψ : P ≃ K × G)
    (ρ : Matrix Ω Ω ℂ) :
    marg Ψ (marg Φ ρ) =
      marg ((Φ.trans (Equiv.prodCongr Ψ (Equiv.refl F))).trans (Equiv.prodAssoc K G F)) ρ := by
  ext k k'
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type]
  rfl

section primed
variable {n : ℕ} {D F : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]

/-- primed/unprimed split of paired registers. -/
def pq (D F : Fin n → Type) : RegisterBasis (fun i => D i × F i) ≃ RegisterBasis F × RegisterBasis D where
  toFun x := (fun i => (x i).2, fun i => (x i).1)
  invFun p := fun i => (p.2 i, p.1 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- unprimed/primed split of paired registers. -/
def up (D F : Fin n → Type) : RegisterBasis (fun i => D i × F i) ≃ RegisterBasis D × RegisterBasis F where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

lemma pm_eq (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) :
    primedMarginal ω = marg (pq D F) ω := rfl

lemma um_eq (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) :
    unprimedMarginal ω = marg (up D F) ω := rfl

/-- entropy of primed registers `s` via any splitting of the paired space carrying the same
information. -/
lemma ent_pm [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)] {K G : Type*} [Fintype K] [DecidableEq K]
    [Fintype G] (Φ : RegisterBasis (fun i => D i × F i) ≃ K × G)
    (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hω : ω.PosSemidef) (s : Finset (Fin n))
    (h1 : ∀ x y, (Φ x).1 = (Φ y).1 ↔ ∀ i ∈ s, (x i).2 = (y i).2)
    (h2 : ∀ x y, (Φ x).2 = (Φ y).2 ↔ (∀ i ∉ s, (x i).2 = (y i).2) ∧ ∀ i, (x i).1 = (y i).1) :
    entropyAt (trivialExtension (primedMarginal ω)) s = vnEntropy (marg Φ ω) := by
  classical
  rw [ent_spl _ (by rw [pm_eq]; exact marg_psd _ hω) s, pm_eq, marg_comp]
  refine (vn_marg_eq _ Φ (fun x y => ?_) (fun x y => ?_) hω).symm
  · simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      Equiv.prodAssoc_apply]
    rw [spl_fst_iff, h1]; rfl
  · simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      Equiv.prodAssoc_apply, Prod.mk.injEq]
    rw [spl_snd_iff, h2]
    constructor
    · rintro ⟨h, h'⟩; exact ⟨h, fun i => congrFun h' i⟩
    · rintro ⟨h, h'⟩; exact ⟨h, funext h'⟩

end primed
end X6CE


/-! X6 CEMI library, part 5: embedding matrices of injective maps, partial traces through local
embeddings, and the entropy of a weighted direct sum of two states. -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms X6SSA Real

/-- the partial-isometry matrix of a map `f : α → β`. -/
def emb {α β : Type*} [DecidableEq β] (f : α → β) : Matrix β α ℂ :=
  of fun b a => if b = f a then 1 else 0

section emb
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma emb_iso {f : α → β} (hf : Function.Injective f) : (emb f)ᴴ * emb f = 1 := by
  ext a a'
  simp only [emb, mul_apply, conjTranspose_apply, of_apply, one_apply]
  rw [Fintype.sum_eq_single (f a)]
  · by_cases h : a = a'
    · subst h; simp
    · simp [h, hf.ne h, eq_comm]
  · intro b hb; simp [hb]

lemma conj_emb_apply (f : α → β) (X : Matrix α α ℂ) (b b' : β) :
    (emb f * X * (emb f)ᴴ) b b' = ∑ a, ∑ a', if b = f a ∧ b' = f a' then X a a' else 0 := by
  simp only [emb, mul_apply, conjTranspose_apply, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  by_cases h1 : b = f a <;> by_cases h2 : b' = f a' <;> simp [h1, h2]

lemma conj_emb_apply_ff {f : α → β} (hf : Function.Injective f) (X : Matrix α α ℂ) (a a' : α) :
    (emb f * X * (emb f)ᴴ) (f a) (f a') = X a a' := by
  rw [conj_emb_apply, Fintype.sum_eq_single a]
  · rw [Fintype.sum_eq_single a']
    · simp
    · intro x hx; rw [if_neg]; rintro ⟨-, h⟩; exact hx (hf h).symm
  · intro x hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg]; rintro ⟨h, -⟩; exact hx (hf h).symm

lemma conj_emb_apply_out {f : α → β} (X : Matrix α α ℂ) (b b' : β)
    (h : b ∉ Set.range f ∨ b' ∉ Set.range f) : (emb f * X * (emb f)ᴴ) b b' = 0 := by
  rw [conj_emb_apply]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun a' _ => ?_
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rcases h with h | h
  · exact h ⟨a, h1.symm⟩
  · exact h ⟨a', h2.symm⟩

lemma conj_emb_psd (f : α → β) {X : Matrix α α ℂ} (hX : X.PosSemidef) :
    (emb f * X * (emb f)ᴴ).PosSemidef :=
  hX.mul_mul_conjTranspose_same _

lemma conj_emb_trace {f : α → β} (hf : Function.Injective f) (X : Matrix α α ℂ) :
    trace (emb f * X * (emb f)ᴴ) = trace X := by
  rw [trace_mul_cycle, emb_iso hf, Matrix.one_mul]

end emb

/-- partial traces commute with local injective embeddings. -/
lemma marg_embed {Ω Ω1 K K1 F F1 : Type*} [Fintype Ω] [Fintype Ω1] [Fintype K] [Fintype K1]
    [Fintype F] [Fintype F1] [DecidableEq Ω] [DecidableEq K] [DecidableEq Ω1] [DecidableEq K1]
    (Φ : Ω ≃ K × F) (Φ1 : Ω1 ≃ K1 × F1) (ι : Ω1 → Ω) (κ : K1 → K) (ζ : F1 → F)
    (hι : Function.Injective ι) (hκ : Function.Injective κ) (hζ : Function.Injective ζ)
    (hc : ∀ x, Φ (ι x) = (κ (Φ1 x).1, ζ (Φ1 x).2)) (X : Matrix Ω1 Ω1 ℂ) :
    marg Φ (emb ι * X * (emb ι)ᴴ) = emb κ * marg Φ1 X * (emb κ)ᴴ := by
  have hc' : ∀ k1 f1, Φ.symm (κ k1, ζ f1) = ι (Φ1.symm (k1, f1)) := by
    intro k1 f1
    apply Φ.injective
    rw [Equiv.apply_symm_apply, hc, Equiv.apply_symm_apply]
  have hout : ∀ k f, (k ∉ Set.range κ ∨ f ∉ Set.range ζ) → Φ.symm (k, f) ∉ Set.range ι := by
    rintro k f h ⟨x, hx⟩
    have := hc x
    rw [hx, Equiv.apply_symm_apply, Prod.mk.injEq] at this
    rcases h with h | h
    · exact h ⟨_, this.1.symm⟩
    · exact h ⟨_, this.2.symm⟩
  ext k k'
  by_cases hk : k ∈ Set.range κ ∧ k' ∈ Set.range κ
  · obtain ⟨⟨k1, rfl⟩, ⟨k1', rfl⟩⟩ := hk
    rw [conj_emb_apply_ff hκ]
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Equiv.symm_symm]
    symm
    refine Fintype.sum_of_injective ζ hζ _ _ (fun f hf => ?_) (fun f1 => ?_)
    · exact conj_emb_apply_out X _ _ (Or.inl (hout _ _ (Or.inr hf)))
    · rw [hc', hc', conj_emb_apply_ff hι]
  · rw [conj_emb_apply_out _ _ _ (by tauto)]
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Equiv.symm_symm]
    refine Finset.sum_eq_zero fun f _ => conj_emb_apply_out X _ _ ?_
    by_cases h1 : k ∈ Set.range κ
    · exact Or.inr (hout _ _ (Or.inl (by tauto)))
    · exact Or.inl (hout _ _ (Or.inl h1))

section dsum
variable {K1 K2 : Type*} [Fintype K1] [Fintype K2] [DecidableEq K1] [DecidableEq K2]

lemma vn_herm_diag {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    vnEntropy A = vnEntropy (diagonal fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)) := by
  conv_lhs => rw [X6KR.spec hA.1]
  refine X6CH.vn_iso _ ?_ _ ?_
  · exact X6KR.unit_iso _
  · exact posSemidef_diagonal_iff.2 fun i => by
      exact_mod_cast hA.eigenvalues_nonneg i

lemma vn_fromBlocks {A : Matrix K1 K1 ℂ} {B : Matrix K2 K2 ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : vnEntropy (fromBlocks A 0 0 B) = vnEntropy A + vnEntropy B := by
  set U := (hA.1.eigenvectorUnitary : Matrix K1 K1 ℂ)
  set V := (hB.1.eigenvectorUnitary : Matrix K2 K2 ℂ)
  have hU : Uᴴ * U = 1 := X6KR.unit_iso _
  have hV : Vᴴ * V = 1 := X6KR.unit_iso _
  set dA : Matrix K1 K1 ℂ := diagonal fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)
  set dB : Matrix K2 K2 ℂ := diagonal fun i => ((hB.1.eigenvalues i : ℝ) : ℂ)
  have hM : fromBlocks A 0 0 B = fromBlocks U 0 0 V * fromBlocks dA 0 0 dB *
      (fromBlocks U 0 0 V)ᴴ := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_zero]
    rw [← X6KR.spec hA.1, ← X6KR.spec hB.1]
  have hW : (fromBlocks U 0 0 V)ᴴ * fromBlocks U 0 0 V = 1 := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_zero, hU, hV]
    exact fromBlocks_one
  have hD : fromBlocks dA 0 0 dB = diagonal (Sum.elim (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ))
      fun i => ((hB.1.eigenvalues i : ℝ) : ℂ)) := fromBlocks_diagonal _ _
  have hDpsd : (fromBlocks dA 0 0 dB).PosSemidef := by
    rw [hD]
    refine posSemidef_diagonal_iff.2 fun i => ?_
    rcases i with i | i
    · simp only [Sum.elim_inl]; exact_mod_cast hA.eigenvalues_nonneg i
    · simp only [Sum.elim_inr]; exact_mod_cast hB.eigenvalues_nonneg i
  rw [hM, X6CH.vn_iso _ hW _ hDpsd, vn_herm_diag hA, vn_herm_diag hB, hD]
  have e : (Sum.elim (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)) fun i => ((hB.1.eigenvalues i : ℝ) : ℂ))
      = fun i => ((Sum.elim (fun i => hA.1.eigenvalues i) (fun i => hB.1.eigenvalues i) i : ℝ) : ℂ) := by
    funext i; rcases i with i | i <;> rfl
  rw [e, X6CH.vn_diag', X6CH.vn_diag', X6CH.vn_diag', Fintype.sum_sum_type]
  rfl

lemma vn_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.PosSemidef)
    (htr : trace X = 1) {c : ℝ} (hc : 0 ≤ c) :
    vnEntropy ((c : ℂ) • X) = negMulLog c / log 2 + c * vnEntropy X := by
  have h := X6CH.blk_ent (J := Unit) (fun _ => c) (fun _ => hc) (fun _ => X) (fun _ => hX)
    (fun _ => htr)
  have hr : blockDiagonal (fun _ : Unit => (c : ℂ) • X) =
      reindex (Equiv.prodPUnit ι).symm (Equiv.prodPUnit ι).symm ((c : ℂ) • X) := by
    ext ⟨a, u⟩ ⟨b, v⟩
    simp [blockDiagonal_apply]
  rw [hr, vn_reind _ _ (X6CH.psd_smul hX hc).1] at h
  simpa using h

lemma fc_conj {K : Type*} [Fintype K] (A : Matrix K K1 ℂ) (B : Matrix K K2 ℂ)
    (P : Matrix K1 K1 ℂ) (Q : Matrix K2 K2 ℂ) :
    fromCols A B * fromBlocks P 0 0 Q * (fromCols A B)ᴴ = A * P * Aᴴ + B * Q * Bᴴ := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromBlocks,
    fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, add_zero, zero_add]

/-- entropy of a weighted direct sum of two embedded states. -/
theorem vn_dsum {K : Type*} [Fintype K] [DecidableEq K] (κ1 : K1 → K) (κ2 : K2 → K)
    (h1 : Function.Injective κ1) (h2 : Function.Injective κ2)
    (hd : ∀ a b, κ1 a ≠ κ2 b) {X : Matrix K1 K1 ℂ} {Y : Matrix K2 K2 ℂ}
    (hX : X.PosSemidef) (hXt : trace X = 1) (hY : Y.PosSemidef) (hYt : trace Y = 1)
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    vnEntropy ((l : ℂ) • (emb κ1 * X * (emb κ1)ᴴ) + ((1 - l : ℝ) : ℂ) • (emb κ2 * Y * (emb κ2)ᴴ))
      = (negMulLog l + negMulLog (1 - l)) / log 2 + l * vnEntropy X +
        (1 - l) * vnEntropy Y := by
  have hinj : Function.Injective (Sum.elim κ1 κ2) := by
    rintro (a | a) (b | b) h
    · simp only [Sum.elim_inl] at h; rw [h1 h]
    · exact absurd h (hd a b)
    · exact absurd h.symm (hd b a)
    · simp only [Sum.elim_inr] at h; rw [h2 h]
  have hM : (l : ℂ) • (emb κ1 * X * (emb κ1)ᴴ) + ((1 - l : ℝ) : ℂ) • (emb κ2 * Y * (emb κ2)ᴴ) =
      emb (Sum.elim κ1 κ2) * fromBlocks ((l : ℂ) • X) 0 0 (((1 - l : ℝ) : ℂ) • Y) *
        (emb (Sum.elim κ1 κ2))ᴴ := by
    have hE : emb (Sum.elim κ1 κ2) = fromCols (emb κ1) (emb κ2) := by
      ext b (a | a) <;> rfl
    rw [hE, fc_conj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hP1 := X6CH.psd_smul hX hl0
  have hP2 := X6CH.psd_smul hY (show (0 : ℝ) ≤ 1 - l by linarith)
  have hFB : (fromBlocks ((l : ℂ) • X) 0 0 (((1 - l : ℝ) : ℂ) • Y)).PosSemidef := by
    have h1 : fromCols (emb (Sum.inl : K1 → K1 ⊕ K2)) (emb (Sum.inr : K2 → K1 ⊕ K2)) = 1 := by
      ext (i | i) (j | j) <;> simp [emb, one_apply]
    have := fc_conj (emb (Sum.inl : K1 → K1 ⊕ K2)) (emb (Sum.inr : K2 → K1 ⊕ K2))
      ((l : ℂ) • X) (((1 - l : ℝ) : ℂ) • Y)
    rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at this
    rw [this]
    exact (conj_emb_psd _ hP1).add (conj_emb_psd _ hP2)
  rw [hM, X6CH.vn_iso _ (emb_iso hinj) _ hFB, vn_fromBlocks hP1 hP2, vn_smul hX hXt hl0,
    vn_smul hY hYt (by linarith)]
  ring

end dsum
end X6CE

noncomputable section
namespace X6CE
open QAlgorithms.Papers.Independent.Claimed50.P33

/-- trivial splitting `PUnit × Ω`. -/
def Φ0 (Ω : Type) : Ω ≃ PUnit.{1} × Ω where
  toFun x := (PUnit.unit, x)
  invFun p := p.2
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma Φ0_apply {Ω : Type} (x : Ω) : Φ0 Ω x = (PUnit.unit, x) := rfl

end X6CE


/-! X6 CEMI library, part 6: register entropies of a flagged mixture of two register states
embedded through local injections with disjoint ranges. -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33 X6SSA Real

lemma marg_lin {Ω K F : Type*} [Fintype F] (Φ : Ω ≃ K × F) (a b : ℂ) (M N : Matrix Ω Ω ℂ) :
    marg Φ (a • M + b • N) = a • marg Φ M + b • marg Φ N := by
  ext k k'
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]

lemma emb_id {α : Type*} [Fintype α] [DecidableEq α] (X : Matrix α α ℂ) :
    emb (id : α → α) * X * (emb (id : α → α))ᴴ = X := by
  have h : emb (id : α → α) = 1 := by
    ext a b; simp [emb, one_apply]
  rw [h, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

lemma ent_empty {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    entropyAt (trivialExtension ρ) ∅ = 0 := by
  classical
  rw [ent_eq (Φ0 _) ρ hρ ∅ (fun x y => by simp) (fun x y => by simp [funext_iff])]
  have h : marg (Φ0 _) ρ = 1 := by
    ext u v
    rw [Subsingleton.elim u v, one_apply_eq, ← htr]
    simp [marg, trR, trace]
    rfl
  rw [h, vn_one]

lemma ent_spl' {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (ω : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hω : ω.PosSemidef) (s : Finset (Fin n))
    [DecidableEq (SubBasis D s)] :
    entropyAt (trivialExtension ω) s = vnEntropy (marg (spl D s) ω) := by
  rw [ent_spl ω hω s]; exact vn_inst _ _ _

/-- the local embedding of register bases. -/
def regMap {n : ℕ} {D1 D : Fin n → Type} (f : ∀ i, D1 i → D i) :
    RegisterBasis D1 → RegisterBasis D := fun x i => f i (x i)

lemma regMap_inj {n : ℕ} {D1 D : Fin n → Type} {f : ∀ i, D1 i → D i}
    (hf : ∀ i, Function.Injective (f i)) : Function.Injective (regMap f) := by
  intro x y h
  funext i
  exact hf i (congrFun h i)

/-- flagged mixture of two register states. -/
def flagMix {n : ℕ} {D D1 D2 : Fin n → Type} [∀ i, Fintype (D1 i)] [∀ i, Fintype (D2 i)]
    [∀ i, DecidableEq (D i)] (f1 : ∀ i, D1 i → D i) (f2 : ∀ i, D2 i → D i) (l : ℝ)
    (ρ1 : Matrix (RegisterBasis D1) (RegisterBasis D1) ℂ)
    (ρ2 : Matrix (RegisterBasis D2) (RegisterBasis D2) ℂ) :
    Matrix (RegisterBasis D) (RegisterBasis D) ℂ :=
  (l : ℂ) • (emb (regMap f1) * ρ1 * (emb (regMap f1))ᴴ) +
    ((1 - l : ℝ) : ℂ) • (emb (regMap f2) * ρ2 * (emb (regMap f2))ᴴ)

section mix
variable {n : ℕ} {D D1 D2 : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (D1 i)]
  [∀ i, Fintype (D2 i)] [∀ i, DecidableEq (D i)] [∀ i, DecidableEq (D1 i)]
  [∀ i, DecidableEq (D2 i)]
  {f1 : ∀ i, D1 i → D i} {f2 : ∀ i, D2 i → D i} {l : ℝ}
  {ρ1 : Matrix (RegisterBasis D1) (RegisterBasis D1) ℂ}
  {ρ2 : Matrix (RegisterBasis D2) (RegisterBasis D2) ℂ}

lemma flagMix_psd (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hρ1 : ρ1.PosSemidef) (hρ2 : ρ2.PosSemidef) :
    (flagMix f1 f2 l ρ1 ρ2).PosSemidef :=
  (X6CH.psd_smul (conj_emb_psd _ hρ1) hl0).add
    (X6CH.psd_smul (conj_emb_psd _ hρ2) (by linarith))

lemma flagMix_trace (h1 : ∀ i, Function.Injective (f1 i)) (h2 : ∀ i, Function.Injective (f2 i))
    (ht1 : trace ρ1 = 1) (ht2 : trace ρ2 = 1) : trace (flagMix f1 f2 l ρ1 ρ2) = 1 := by
  unfold flagMix
  rw [trace_add, trace_smul, trace_smul]
  rw [conj_emb_trace (regMap_inj h1) ρ1]
  rw [conj_emb_trace (regMap_inj h2) ρ2, ht1, ht2]
  simp only [smul_eq_mul, mul_one, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- register entropies of a flagged mixture, for a nonempty register set. -/
theorem flagMix_ent [∀ i, Nonempty (D i)] [∀ i, Nonempty (D1 i)] [∀ i, Nonempty (D2 i)]
    (h1 : ∀ i, Function.Injective (f1 i)) (h2 : ∀ i, Function.Injective (f2 i))
    (hd : ∀ i a b, f1 i a ≠ f2 i b) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hρ1 : ρ1.PosSemidef) (ht1 : trace ρ1 = 1) (hρ2 : ρ2.PosSemidef) (ht2 : trace ρ2 = 1)
    (s : Finset (Fin n)) (hs : s.Nonempty) :
    entropyAt (trivialExtension (flagMix f1 f2 l ρ1 ρ2)) s =
      (negMulLog l + negMulLog (1 - l)) / log 2 + l * entropyAt (trivialExtension ρ1) s +
        (1 - l) * entropyAt (trivialExtension ρ2) s := by
  obtain ⟨i0, hi0⟩ := hs
  rw [ent_spl' _ (flagMix_psd hl0 hl1 hρ1 hρ2) s, ent_spl' _ hρ1 s, ent_spl' _ hρ2 s]
  let κ1 : SubBasis D1 s → SubBasis D s := fun k i => f1 i.1 (k i)
  let κ2 : SubBasis D2 s → SubBasis D s := fun k i => f2 i.1 (k i)
  let ζ1 : ((i : {i : Fin n // ¬ i ∈ s}) → D1 i.val) → ((i : {i : Fin n // ¬ i ∈ s}) → D i.val) :=
    fun k i => f1 i.1 (k i)
  let ζ2 : ((i : {i : Fin n // ¬ i ∈ s}) → D2 i.val) → ((i : {i : Fin n // ¬ i ∈ s}) → D i.val) :=
    fun k i => f2 i.1 (k i)
  have hκ1 : Function.Injective κ1 := fun x y h => funext fun i => h1 i.1 (congrFun h i)
  have hκ2 : Function.Injective κ2 := fun x y h => funext fun i => h2 i.1 (congrFun h i)
  have hζ1 : Function.Injective ζ1 := fun x y h => funext fun i => h1 i.1 (congrFun h i)
  have hζ2 : Function.Injective ζ2 := fun x y h => funext fun i => h2 i.1 (congrFun h i)
  have e1 := marg_embed (spl D s) (spl D1 s) (regMap f1) κ1 ζ1 (regMap_inj h1) hκ1 hζ1
    (fun x => rfl) ρ1
  have e2 := marg_embed (spl D s) (spl D2 s) (regMap f2) κ2 ζ2 (regMap_inj h2) hκ2 hζ2
    (fun x => rfl) ρ2
  rw [flagMix, marg_lin, e1, e2]
  refine vn_dsum κ1 κ2 hκ1 hκ2 (fun a b h => hd i0 (a ⟨i0, hi0⟩) (b ⟨i0, hi0⟩)
    (congrFun h ⟨i0, hi0⟩)) (marg_psd _ hρ1) (by rw [marg_trace, ht1]) (marg_psd _ hρ2)
    (by rw [marg_trace, ht2]) hl0 hl1

end mix
end X6CE


/-! X6 CEMI library, part 14: honest/primed coordinates of paired registers, a generic SSA for
disjoint coordinate sets, and nonnegativity of the n-party paired increment. -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
  QAlgorithms.Papers.Independent.Gap20.P10 X6SSA

section fourway
variable {T : Type*} [DecidableEq T] {E : T → Type*}

/-- split a pi type along three disjoint index sets and the rest. -/
def four (a b c : Finset T) (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c) :
    ((t : T) → E t) ≃ (((t : {t // t ∈ a}) → E t) × (((t : {t // t ∈ b}) → E t) ×
      ((t : {t // t ∈ c}) → E t))) × ((t : {t // t ∉ a ∧ t ∉ b ∧ t ∉ c}) → E t) where
  toFun x := ((fun t => x t, (fun t => x t, fun t => x t)), fun t => x t)
  invFun y t := if ha : t ∈ a then y.1.1 ⟨t, ha⟩ else if hb : t ∈ b then y.1.2.1 ⟨t, hb⟩ else
    if hc : t ∈ c then y.1.2.2 ⟨t, hc⟩ else y.2 ⟨t, ha, hb, hc⟩
  left_inv x := by
    funext t
    simp only
    split_ifs <;> rfl
  right_inv y := by
    obtain ⟨⟨ya, yb, yc⟩, yr⟩ := y
    have nb : ∀ t, t ∈ b → t ∉ a := fun t h h' => Finset.disjoint_left.1 hab h' h
    have nc : ∀ t, t ∈ c → t ∉ a := fun t h h' => Finset.disjoint_left.1 hac h' h
    have nc' : ∀ t, t ∈ c → t ∉ b := fun t h h' => Finset.disjoint_left.1 hbc h' h
    refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) ?_
    · funext ⟨t, ht⟩; simp [ht]
    · funext ⟨t, ht⟩; simp [ht, nb t ht]
    · funext ⟨t, ht⟩; simp [ht, nc t ht, nc' t ht]
    · funext ⟨t, ht⟩; simp [ht.1, ht.2.1, ht.2.2]

end fourway

section coords
variable {n : ℕ} {D F : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
  [∀ i, DecidableEq (D i)] [∀ i, DecidableEq (F i)]

/-- coordinates: `(i, false)` honest, `(i, true)` primed. -/
def Cb (D F : Fin n → Type) : Fin n × Bool → Type
  | (i, false) => D i
  | (i, true) => F i

instance Cb_ft : ∀ t, Fintype (Cb D F t)
  | (i, false) => (inferInstance : Fintype (D i))
  | (i, true) => (inferInstance : Fintype (F i))

instance Cb_de : ∀ t, DecidableEq (Cb D F t)
  | (i, false) => (inferInstance : DecidableEq (D i))
  | (i, true) => (inferInstance : DecidableEq (F i))

lemma Cb_ne [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)] : ∀ t, Nonempty (Cb D F t)
  | (i, false) => (inferInstance : Nonempty (D i))
  | (i, true) => (inferInstance : Nonempty (F i))

def toB (D F : Fin n → Type) : RegisterBasis (fun i => D i × F i) ≃ ((t : Fin n × Bool) → Cb D F t) where
  toFun x t := match t with
    | (i, false) => (x i).1
    | (i, true) => (x i).2
  invFun y i := (y (i, false), y (i, true))
  left_inv x := rfl
  right_inv y := by
    funext t
    match t with
    | (i, false) => rfl
    | (i, true) => rfl

@[simp] lemma toB_f (x : RegisterBasis (fun i => D i × F i)) (i : Fin n) :
    toB D F x (i, false) = (x i).1 := rfl
@[simp] lemma toB_t (x : RegisterBasis (fun i => D i × F i)) (i : Fin n) :
    toB D F x (i, true) = (x i).2 := rfl

lemma toB_eq_iff (x y : RegisterBasis (fun i => D i × F i)) (P : Finset (Fin n × Bool)) :
    (∀ t ∈ P, toB D F x t = toB D F y t) ↔
      (∀ i, (i, false) ∈ P → (x i).1 = (y i).1) ∧ (∀ i, (i, true) ∈ P → (x i).2 = (y i).2) := by
  constructor
  · intro h; exact ⟨fun i hi => h _ hi, fun i hi => h _ hi⟩
  · rintro ⟨h1, h2⟩ ⟨i, b⟩ hb
    cases b
    · exact h1 i hb
    · exact h2 i hb

lemma toB_ne_iff (x y : RegisterBasis (fun i => D i × F i)) (P : Finset (Fin n × Bool)) :
    (∀ t, t ∉ P → toB D F x t = toB D F y t) ↔
      (∀ i, (i, false) ∉ P → (x i).1 = (y i).1) ∧ (∀ i, (i, true) ∉ P → (x i).2 = (y i).2) := by
  constructor
  · intro h; exact ⟨fun i hi => h _ hi, fun i hi => h _ hi⟩
  · rintro ⟨h1, h2⟩ ⟨i, b⟩ hb
    cases b
    · exact h1 i hb
    · exact h2 i hb

/-- the coordinate splitting along `P`. -/
def spB (D F : Fin n → Type) (P : Finset (Fin n × Bool)) :=
  (toB D F).trans (Equiv.piEquivPiSubtypeProd (fun t => t ∈ P) (Cb D F))

/-- entropy of a set of coordinates. -/
def S2 (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (P : Finset (Fin n × Bool)) : ℝ := vnEntropy (marg (spB D F P) ω)

lemma spB_fst (P : Finset (Fin n × Bool)) (x y : RegisterBasis (fun i => D i × F i)) :
    (spB D F P x).1 = (spB D F P y).1 ↔ ∀ t ∈ P, toB D F x t = toB D F y t := by
  constructor
  · intro h t ht; exact congrFun h ⟨t, ht⟩
  · intro h; funext t; exact h t.1 t.2

lemma spB_snd (P : Finset (Fin n × Bool)) (x y : RegisterBasis (fun i => D i × F i)) :
    (spB D F P x).2 = (spB D F P y).2 ↔ ∀ t, t ∉ P → toB D F x t = toB D F y t := by
  constructor
  · intro h t ht; exact congrFun h ⟨t, ht⟩
  · intro h; funext t; exact h t.1 t.2

variable [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]

/-- any splitting carrying the information of the coordinates `P`. -/
lemma S2_eq {K G : Type*} [Fintype K] [DecidableEq K] [Fintype G]
    (Φ : RegisterBasis (fun i => D i × F i) ≃ K × G)
    (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hω : ω.PosSemidef) (P : Finset (Fin n × Bool))
    (h1 : ∀ x y, (Φ x).1 = (Φ y).1 ↔ ∀ t ∈ P, toB D F x t = toB D F y t)
    (h2 : ∀ x y, (Φ x).2 = (Φ y).2 ↔ ∀ t, t ∉ P → toB D F x t = toB D F y t) :
    vnEntropy (marg Φ ω) = S2 ω P := by
  classical
  have := Cb_ne (D := D) (F := F)
  unfold S2
  exact vn_marg_eq (spB D F P) Φ (fun x y => by rw [spB_fst, h1]) (fun x y => by rw [spB_snd, h2]) hω

lemma ent_reg (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hω : ω.PosSemidef) (s : Finset (Fin n)) :
    entropyAt (trivialExtension ω) s = S2 ω (s ×ˢ Finset.univ) := by
  classical
  have := Cb_ne (D := D) (F := F)
  rw [ent_eq (spB D F (s ×ˢ Finset.univ)) ω hω s]
  · unfold S2; exact vn_inst _ _ _
  · intro x y
    rw [spB_fst, toB_eq_iff]
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩ i hi; exact Prod.ext (h1 i hi) (h2 i hi)
    · intro h; exact ⟨fun i hi => congrArg Prod.fst (h i hi), fun i hi => congrArg Prod.snd (h i hi)⟩
  · intro x y
    rw [spB_snd, toB_ne_iff]
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩ i hi; exact Prod.ext (h1 i hi) (h2 i hi)
    · intro h; exact ⟨fun i hi => congrArg Prod.fst (h i hi), fun i hi => congrArg Prod.snd (h i hi)⟩

lemma ent_pmB (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hω : ω.PosSemidef) (s : Finset (Fin n)) :
    entropyAt (trivialExtension (primedMarginal ω)) s = S2 ω (s ×ˢ {true}) := by
  classical
  have := Cb_ne (D := D) (F := F)
  rw [ent_pm (spB D F (s ×ˢ {true})) ω hω s]
  · unfold S2; exact vn_inst _ _ _
  · intro x y
    rw [spB_fst, toB_eq_iff]
    simp
  · intro x y
    rw [spB_snd, toB_ne_iff]
    simp [and_comm]

set_option maxHeartbeats 2000000 in
lemma ssa2 (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hω : ω.PosSemidef) (htr : trace ω = 1) (a b c : Finset (Fin n × Bool))
    (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c) :
    S2 ω (a ∪ b ∪ c) + S2 ω c ≤ S2 ω (a ∪ c) + S2 ω (b ∪ c) := by
  classical
  have := Cb_ne (D := D) (F := F)
  have nb : ∀ t, t ∈ b → t ∉ a := fun t h h' => Finset.disjoint_left.1 hab h' h
  have nc : ∀ t, t ∈ c → t ∉ a := fun t h h' => Finset.disjoint_left.1 hac h' h
  have nc' : ∀ t, t ∈ c → t ∉ b := fun t h h' => Finset.disjoint_left.1 hbc h' h
  let Φ := (toB D F).trans (four (E := Cb D F) a b c hab hac hbc)
  have h := ssa_split Φ ω hω htr
  rw [S2_eq (Φ.trans r21) ω hω (a ∪ c), S2_eq (Φ.trans r31) ω hω (b ∪ c),
    S2_eq (Φ.trans r1) ω hω c, S2_eq Φ ω hω (a ∪ b ∪ c)] at h
  · linarith
  all_goals intro x y
  all_goals simp only [Φ, Equiv.trans_apply, four, r21, r31, r1, Equiv.coe_fn_mk, Prod.mk.injEq,
    funext_iff, Subtype.forall, Finset.mem_union]
  all_goals
    constructor
    all_goals
      intro h
      repeat' apply And.intro
      all_goals
        intro t ht
        by_cases ha : t ∈ a <;> by_cases hb : t ∈ b <;> by_cases hc : t ∈ c <;> simp_all [-Prod.forall, -Bool.forall_bool, -toB_f, -toB_t]

lemma pd_nonneg_n
    (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hω : ω.PosSemidef) (htr : trace ω = 1) : 0 ≤ pairedDifference ω := by
  classical
  have hall : allParties (singleParties n) = Finset.univ := by
    ext i; simp [allParties, singleParties]
  unfold pairedDifference info conditionalMultipartiteInformation
  simp only [hall, Finset.union_empty, singleParties]
  simp_rw [ent_reg ω hω, ent_pmB ω hω]
  simp only [Finset.empty_product]
  let Q : ℕ → Finset (Fin n × Bool) := fun k => Finset.univ.filter (fun t => t.2 = true ∨ t.1.val < k)
  have step : ∀ i : Fin n, S2 ω (Q (i.val + 1)) - S2 ω (Q i.val) ≤
      S2 ω ({i} ×ˢ Finset.univ) - S2 ω ({i} ×ˢ {true}) := by
    intro i
    have h := ssa2 ω hω htr ({(i, false)} : Finset (Fin n × Bool)) ((Q i.val).erase (i, true))
      ({(i, true)} : Finset (Fin n × Bool))
      (by simp [Q]) (by simp) (by simp)
    have e1 : ({(i, false)} : Finset (Fin n × Bool)) ∪ (Q i.val).erase (i, true) ∪ {(i, true)} =
        Q (i.val + 1) := by
      ext ⟨j, β⟩; cases β <;> simp [Q, Fin.ext_iff] <;> omega
    have e2 : ({(i, false)} : Finset (Fin n × Bool)) ∪ {(i, true)} = {i} ×ˢ Finset.univ := by
      ext ⟨j, β⟩; cases β <;> simp
    have e3 : (Q i.val).erase (i, true) ∪ {(i, true)} = Q i.val := by
      ext ⟨j, β⟩; cases β <;> simp [Q, Fin.ext_iff] <;> omega
    have e4 : ({(i, true)} : Finset (Fin n × Bool)) = ({i} : Finset (Fin n)) ×ˢ ({true} : Finset Bool) := by simp
    rw [e1, e2, e3, e4] at h
    linarith
  have tele : ∑ i : Fin n, (S2 ω (Q (i.val + 1)) - S2 ω (Q i.val)) = S2 ω (Q n) - S2 ω (Q 0) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => S2 ω (Q (k + 1)) - S2 ω (Q k)), Finset.sum_range_sub (fun k => S2 ω (Q k)) n]
  have hQn : Q n = Finset.univ ×ˢ Finset.univ := by
    ext ⟨j, β⟩; simp [Q, j.2]
  have hQ0 : Q 0 = Finset.univ ×ˢ {true} := by
    ext ⟨j, β⟩; cases β <;> simp [Q]
  rw [hQn, hQ0] at tele
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => step i)
  rw [tele, Finset.sum_sub_distrib] at hs
  linarith

end coords
end X6CE


/-! X6 CEMI library, part 15: the exact n-party splitting of the paired increment of an
extension of a product-structured honest system `(U i × W i)` into the increments of its
`U`-reduction (with primes `W i × F i`) and its `W`-reduction (tracing `U`). -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
  QAlgorithms.Papers.Independent.Gap20.P10 X6SSA

/-- the n-party information expansion. -/
lemma info_n {n : ℕ} {E : Fin n → Type} [∀ i, Fintype (E i)]
    (X : Matrix (RegisterBasis E) (RegisterBasis E) ℂ) :
    info .total X (singleParties n) ∅ =
      ∑ i, entropyAt (trivialExtension X) {i} - entropyAt (trivialExtension X) Finset.univ -
        ((n - 1 : ℕ) : ℝ) * entropyAt (trivialExtension X) ∅ := by
  have h : allParties (singleParties n) = Finset.univ := by
    ext i; simp [allParties, singleParties]
  simp only [info, conditionalMultipartiteInformation, singleParties, Finset.union_empty, h]

end X6CE


/-! X6 CEMI library, part 17: register entropies of paired products add; multipartite
additivity of CEMI. -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
  QAlgorithms.Papers.Independent.Gap20.P10 X6SSA

section main
variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]

lemma triv_dens_n (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hrho : IsDensityMatrix rho) : IsDensityMatrix (trivialPairedExtension rho) := by
  classical
  let f : RegisterBasis (fun i => D i × Fin 1) ≃ RegisterBasis D :=
    Equiv.piCongrRight fun i => Equiv.prodUnique (D i) (Fin 1)
  have h : trivialPairedExtension rho = rho.submatrix f f := rfl
  refine ⟨?_, ?_⟩
  · rw [h]; exact hrho.1.submatrix _
  · rw [h, ← hrho.2]
    simp only [trace, diag_apply, submatrix_apply]
    exact Equiv.sum_comp f (fun x => rho x x)

lemma vals_ne_n (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho) :
    (cemiValues rho).Nonempty :=
  ⟨_, fun _ => 1, fun _ => Nat.one_pos, trivialPairedExtension rho, triv_dens_n rho hrho,
    by ext x y; simp [unprimedMarginal, trivialPairedExtension], rfl⟩

lemma vals_nonneg_n (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    ∀ v ∈ cemiValues rho, 0 ≤ v := by
  classical
  rintro _ ⟨d, hd, ω, hω, -, rfl⟩
  have : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, hd i⟩⟩
  have := pd_nonneg_n ω hω.1 hω.2
  linarith

end main

end X6CE


/-! X6 CEMI library, part 18: entropy of a classical-quantum block state
`⊕_j p_j ρ_j` (block diagonal over a classical label). -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms X6SSA X6CH Real

variable {K J : Type*} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]

/-- `S(⊕_j p_j ρ_j) = H(p) + Σ_j p_j S(ρ_j)`. -/
theorem vn_blk (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (ρ : J → Matrix K K ℂ)
    (hρ : ∀ j, IsDensityMatrix (ρ j)) :
    vnEntropy (blockDiagonal fun j => ((p j : ℝ) : ℂ) • ρ j) =
      ∑ j, negMulLog (p j) / log 2 + ∑ j, p j * vnEntropy (ρ j) := by
  set U : J → Matrix K K ℂ := fun j => ((hρ j).1.1.eigenvectorUnitary : Matrix K K ℂ)
  set lam : J → K → ℝ := fun j => (hρ j).1.1.eigenvalues
  set W : Matrix (K × J) (K × J) ℂ := blockDiagonal U
  have hW : Wᴴ * W = 1 := by
    simp only [W, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    have : (fun j => (U j)ᴴ * U j) = (1 : J → Matrix K K ℂ) := by
      funext j; exact X6KR.unit_iso _
    rw [this, blockDiagonal_one]
  have hX : (blockDiagonal fun j => ((p j : ℝ) : ℂ) • ρ j) =
      W * (diagonal fun q : K × J => ((p q.2 * lam q.2 q.1 : ℝ) : ℂ)) * Wᴴ := by
    have e : ∀ j, ((p j : ℝ) : ℂ) • ρ j =
        U j * diagonal (fun k => ((p j * lam j k : ℝ) : ℂ)) * (U j)ᴴ := by
      intro j
      conv_lhs => rw [X6KR.spec (hρ j).1.1]
      have : diagonal (fun k => ((p j * lam j k : ℝ) : ℂ)) =
          ((p j : ℝ) : ℂ) • diagonal (fun k => ((lam j k : ℝ) : ℂ)) := by
        ext a b; by_cases h : a = b <;> simp [diagonal_apply, h]
      rw [this, Matrix.mul_smul, Matrix.smul_mul]
    simp only [e, W, blockDiagonal_conjTranspose, blockDiagonal_mul]
    rw [blockDiagonal_diagonal]
  have hl : ∀ j k, 0 ≤ lam j k := fun j => (hρ j).1.eigenvalues_nonneg
  have hD : (diagonal fun q : K × J => ((p q.2 * lam q.2 q.1 : ℝ) : ℂ)).PosSemidef :=
    PosSemidef.diagonal fun q => by
      simp only [Pi.zero_apply]
      exact_mod_cast mul_nonneg (hp q.2) (hl q.2 q.1)
  rw [hX, vn_iso W hW _ hD, vn_diag', Fintype.sum_prod_type, Finset.sum_comm]
  simp only [fun j => vn_eig' (hρ j).1.1]
  have s : ∀ j, ∑ k, lam j k = 1 := fun j => eig_sum (hρ j).1.1 (hρ j).2
  simp only [Real.negMulLog_mul, add_div, Finset.sum_add_distrib, mul_div_assoc,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [s j, one_mul]

end X6CE


/-! X6 CEMI library, part 20: entropy of a classical-quantum block state with
label-dependent block types (sigma-indexed block diagonal). -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms X6SSA X6CH Real

variable {J : Type*} [Fintype J] [DecidableEq J] {K : J → Type*} [∀ j, Fintype (K j)]
  [∀ j, DecidableEq (K j)]

/-- `S(⊕_j p_j ρ_j) = H(p) + Σ_j p_j S(ρ_j)` for blocks of different types. -/
theorem vn_blk' (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (ρ : (j : J) → Matrix (K j) (K j) ℂ)
    (hρ : ∀ j, IsDensityMatrix (ρ j)) :
    vnEntropy (blockDiagonal' fun j => ((p j : ℝ) : ℂ) • ρ j) =
      ∑ j, negMulLog (p j) / log 2 + ∑ j, p j * vnEntropy (ρ j) := by
  set U : (j : J) → Matrix (K j) (K j) ℂ := fun j => ((hρ j).1.1.eigenvectorUnitary : Matrix _ _ ℂ)
  set lam : (j : J) → K j → ℝ := fun j => (hρ j).1.1.eigenvalues
  set W : Matrix (Σ j, K j) (Σ j, K j) ℂ := blockDiagonal' U
  have hW : Wᴴ * W = 1 := by
    simp only [W, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
    have : (fun j => (U j)ᴴ * U j) = (1 : (j : J) → Matrix (K j) (K j) ℂ) := by
      funext j; exact X6KR.unit_iso _
    rw [this, blockDiagonal'_one]
  have hX : (blockDiagonal' fun j => ((p j : ℝ) : ℂ) • ρ j) =
      W * (diagonal fun q : Σ j, K j => ((p q.1 * lam q.1 q.2 : ℝ) : ℂ)) * Wᴴ := by
    have e : ∀ j, ((p j : ℝ) : ℂ) • ρ j =
        U j * diagonal (fun k => ((p j * lam j k : ℝ) : ℂ)) * (U j)ᴴ := by
      intro j
      conv_lhs => rw [X6KR.spec (hρ j).1.1]
      have : diagonal (fun k => ((p j * lam j k : ℝ) : ℂ)) =
          ((p j : ℝ) : ℂ) • diagonal (fun k => ((lam j k : ℝ) : ℂ)) := by
        ext a b; by_cases h : a = b <;> simp [diagonal_apply, h]
      rw [this, Matrix.mul_smul, Matrix.smul_mul]
    simp only [e, W, blockDiagonal'_conjTranspose, blockDiagonal'_mul]
    rw [blockDiagonal'_diagonal]
  have hl : ∀ j k, 0 ≤ lam j k := fun j => (hρ j).1.eigenvalues_nonneg
  have hD : (diagonal fun q : Σ j, K j => ((p q.1 * lam q.1 q.2 : ℝ) : ℂ)).PosSemidef :=
    PosSemidef.diagonal fun q => by
      simp only [Pi.zero_apply]
      exact_mod_cast mul_nonneg (hp q.1) (hl q.1 q.2)
  rw [hX, vn_iso W hW _ hD, vn_diag', Fintype.sum_sigma]
  simp only [fun j => vn_eig' (hρ j).1.1]
  have s : ∀ j, ∑ k, lam j k = 1 := fun j => eig_sum (hρ j).1.1 (hρ j).2
  simp only [Real.negMulLog_mul, add_div, Finset.sum_add_distrib, mul_div_assoc,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [s j, one_mul]

end X6CE


/-! X6 CEMI library, part 21: local Kraus operators acting on the honest registers of a paired
extension, and the per-outcome extensions of a local instrument. -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
  QAlgorithms.Papers.Independent.Gap20.P10 X6SSA

section lift
variable {n : ℕ} {D E F : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (E i)]
  [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]

/-- an operator on the honest registers, identity on the primes. -/
def liftP (F : Fin n → Type) [∀ i, DecidableEq (F i)] (L : Matrix (RegisterBasis E) (RegisterBasis D) ℂ) :
    Matrix (RegisterBasis (fun i => E i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ :=
  fun x y => (if ∀ i, (x i).2 = (y i).2 then 1 else 0) * L (fun i => (x i).1) (fun i => (y i).1)

lemma sum_liftP (L : Matrix (RegisterBasis E) (RegisterBasis D) ℂ)
    (u : RegisterBasis (fun i => E i × F i)) (f : RegisterBasis (fun i => D i × F i) → ℂ) :
    ∑ x, liftP F L u x * f x = ∑ x' : RegisterBasis D, L (fun i => (u i).1) x' *
      f (fun i => (x' i, (u i).2)) := by
  classical
  rw [← Equiv.sum_comp (up D F).symm (fun x => liftP F L u x * f x), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x' _ => ?_
  have : ∀ w : RegisterBasis F, (∀ i, (u i).2 = ((up D F).symm (x', w) i).2) ↔
      (fun i => (u i).2) = w := by
    intro w; rw [funext_iff]; rfl
  simp only [liftP, this, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rfl

lemma sum_liftP' (L : Matrix (RegisterBasis E) (RegisterBasis D) ℂ)
    (v : RegisterBasis (fun i => E i × F i)) (f : RegisterBasis (fun i => D i × F i) → ℂ) :
    ∑ y, f y * star (liftP F L v y) = ∑ y' : RegisterBasis D, f (fun i => (y' i, (v i).2)) *
      star (L (fun i => (v i).1) y') := by
  have h := sum_liftP (Lᴴᴴ) v (fun y => star (f y))
  simp only [conjTranspose_conjTranspose] at h
  have h2 := congrArg star h
  simp only [star_sum, star_mul', star_star] at h2
  simpa [mul_comm] using h2

lemma liftP_conj_apply (L : Matrix (RegisterBasis E) (RegisterBasis D) ℂ)
    (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (u v : RegisterBasis (fun i => E i × F i)) :
    (liftP F L * ω * (liftP F L)ᴴ) u v = ∑ x' : RegisterBasis D, ∑ y' : RegisterBasis D,
      L (fun i => (u i).1) x' * ω (fun i => (x' i, (u i).2)) (fun i => (y' i, (v i).2)) *
        star (L (fun i => (v i).1) y') := by
  simp only [mul_apply, conjTranspose_apply]
  rw [sum_liftP' L v (fun y => ∑ x, liftP F L u x * ω x y)]
  simp only [sum_liftP L u, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma um_liftP (L : Matrix (RegisterBasis E) (RegisterBasis D) ℂ)
    (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) :
    unprimedMarginal (liftP F L * ω * (liftP F L)ᴴ) = L * unprimedMarginal ω * Lᴴ := by
  ext a b
  simp only [unprimedMarginal]
  simp only [liftP_conj_apply]
  simp only [mul_apply, conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp only [unprimedMarginal, Finset.mul_sum, Finset.sum_mul]

end lift
end X6CE


/-! X6 CEMI library, part 22: the extension of one outcome of a local instrument. -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
  QAlgorithms.Papers.Independent.Gap20.P10 X6SSA

section outExt
variable {n : ℕ} {D E F : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (E i)]
  [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]

lemma um_add (X Y : Matrix (RegisterBasis (fun i => E i × F i))
    (RegisterBasis (fun i => E i × F i)) ℂ) :
    unprimedMarginal (X + Y) = unprimedMarginal X + unprimedMarginal Y := by
  ext a b; simp [unprimedMarginal, Finset.sum_add_distrib]

lemma um_smul (c : ℂ) (X : Matrix (RegisterBasis (fun i => E i × F i))
    (RegisterBasis (fun i => E i × F i)) ℂ) :
    unprimedMarginal (c • X) = c • unprimedMarginal X := by
  ext a b; simp [unprimedMarginal, Finset.mul_sum]

lemma um_sum {c : ℕ} (X : Fin c → Matrix (RegisterBasis (fun i => E i × F i))
    (RegisterBasis (fun i => E i × F i)) ℂ) :
    unprimedMarginal (∑ z, X z) = ∑ z, unprimedMarginal (X z) := by
  ext a b; simp only [unprimedMarginal, Matrix.sum_apply]; rw [Finset.sum_comm]

/-- the (normalized) extension of one outcome with Kraus operators `L z` and weight `q`. -/
def outExt (F : Fin n → Type) [∀ i, DecidableEq (F i)] [∀ i, Fintype (F i)] {c : ℕ} (q : ℝ)
    (L : Fin c → Matrix (RegisterBasis E) (RegisterBasis D) ℂ)
    (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) :
    Matrix (RegisterBasis (fun i => E i × F i)) (RegisterBasis (fun i => E i × F i)) ℂ :=
  ((q⁻¹ : ℝ) : ℂ) • ∑ z, liftP F (L z) * ω * (liftP F (L z))ᴴ

lemma um_outExt {c : ℕ} (q : ℝ) (L : Fin c → Matrix (RegisterBasis E) (RegisterBasis D) ℂ)
    (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) :
    unprimedMarginal (outExt F q L ω) =
      ((q⁻¹ : ℝ) : ℂ) • ∑ z, L z * unprimedMarginal ω * (L z)ᴴ := by
  unfold outExt
  rw [um_smul, um_sum]
  simp only [um_liftP]

lemma outExt_um {c : ℕ} {q : ℝ} (hq : q ≠ 0)
    (L : Fin c → Matrix (RegisterBasis E) (RegisterBasis D) ℂ)
    {ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ}
    {ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ} (hu : unprimedMarginal ω = ρ)
    {τ : Matrix (RegisterBasis E) (RegisterBasis E) ℂ}
    (hrel : ((q : ℝ) : ℂ) • τ = ∑ z, L z * ρ * (L z)ᴴ) :
    unprimedMarginal (outExt F q L ω) = τ := by
  rw [um_outExt, hu, ← hrel, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hq,
    Complex.ofReal_one, one_smul]

lemma outExt_dens [∀ i, DecidableEq (E i)] {c : ℕ} {q : ℝ} (hq : 0 < q)
    (L : Fin c → Matrix (RegisterBasis E) (RegisterBasis D) ℂ)
    {ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ}
    (hω : ω.PosSemidef) {ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ}
    (hu : unprimedMarginal ω = ρ) {τ : Matrix (RegisterBasis E) (RegisterBasis E) ℂ}
    (hτ : IsDensityMatrix τ) (hrel : ((q : ℝ) : ℂ) • τ = ∑ z, L z * ρ * (L z)ᴴ) :
    IsDensityMatrix (outExt F q L ω) := by
  classical
  refine ⟨?_, ?_⟩
  · unfold outExt
    refine PosSemidef.smul ?_ (by exact_mod_cast (inv_pos.2 hq).le)
    exact Matrix.posSemidef_sum _ fun z _ => hω.mul_mul_conjTranspose_same _
  · have h := outExt_um (F := F) hq.ne' L hu hrel
    rw [← hτ.2, ← h, um_eq, marg_trace]

end outExt
end X6CE


/-! X6 CEMI library, part 23: monotonicity of the Holevo quantity of an ensemble under
partial trace, `χ(B) ≤ χ(AB)`, via SSA on the classical-quantum block state. -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms X6SSA Real

section holevo
variable {Ω A B E : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B] [Fintype E] [DecidableEq E] {k : ℕ}

/-- move the `B` part to the front. -/
def swAB : (A × B) × E ≃ B × (A × E) where
  toFun x := (x.1.2, (x.1.1, x.2))
  invFun y := ((y.2.1, y.1), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- the splitting of the block state used for SSA. -/
def hvΦ (Ψ : Ω ≃ (A × B) × E) : Ω × Fin k ≃ (A × (Fin k × B)) × E where
  toFun x := (((Ψ x.1).1.1, (x.2, (Ψ x.1).1.2)), (Ψ x.1).2)
  invFun y := (Ψ.symm ((y.1.1, y.1.2.2), y.2), y.1.2.1)
  left_inv x := by simp
  right_inv y := by simp

lemma hv_lin (Φ : Ω ≃ A × E) (p : Fin k → ℝ) (μ : Fin k → Matrix Ω Ω ℂ) :
    marg Φ (∑ j, ((p j : ℝ) : ℂ) • μ j) = ∑ j, ((p j : ℝ) : ℂ) • marg Φ (μ j) := by
  ext a b
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma hv_dens {K F : Type*} [Fintype K] [DecidableEq K] [Fintype F] [DecidableEq F]
    (Φ : Ω ≃ K × F) {μ : Matrix Ω Ω ℂ} (h : IsDensityMatrix μ) : IsDensityMatrix (marg Φ μ) :=
  ⟨marg_psd Φ h.1, by rw [marg_trace, h.2]⟩

set_option maxHeartbeats 1000000 in
theorem holevo (Ψ : Ω ≃ (A × B) × E) (p : Fin k → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1)
    (μ : Fin k → Matrix Ω Ω ℂ) (hμ : ∀ j, IsDensityMatrix (μ j)) :
    vnEntropy (marg (Ψ.trans swAB) (∑ j, ((p j : ℝ) : ℂ) • μ j)) -
        ∑ j, p j * vnEntropy (marg (Ψ.trans swAB) (μ j)) ≤
      vnEntropy (marg Ψ (∑ j, ((p j : ℝ) : ℂ) • μ j)) - ∑ j, p j * vnEntropy (marg Ψ (μ j)) := by
  have hk : Nonempty (Fin k) := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hs
    · exact ⟨⟨0, h⟩⟩
  set κ : Matrix (Ω × Fin k) (Ω × Fin k) ℂ := blockDiagonal fun j => ((p j : ℝ) : ℂ) • μ j
  have hκ : κ.PosSemidef :=
    X6CH.blk_psd _ fun j => X6CH.psd_smul (hμ j).1 (hp j)
  have htr : trace κ = 1 := by
    simp only [κ, trace_blockDiagonal, trace_smul, (hμ _).2, smul_eq_mul, mul_one]
    exact_mod_cast hs
  have h := ssa_split (hvΦ (k := k) Ψ) κ hκ htr
  -- the four marginals
  have e21 : marg ((hvΦ Ψ).trans r21) κ = marg Ψ (∑ j, ((p j : ℝ) : ℂ) • μ j) := by
    rw [hv_lin]
    ext a b
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, κ, Fintype.sum_prod_type, Equiv.symm_trans_apply, hvΦ, r21, Equiv.coe_fn_symm_mk,
      blockDiagonal_apply, if_true]
    simp [Finset.mul_sum]
  have e1 : marg ((hvΦ Ψ).trans r1) κ = marg (Ψ.trans swAB) (∑ j, ((p j : ℝ) : ℂ) • μ j) := by
    rw [hv_lin]
    ext a b
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, κ, Fintype.sum_prod_type, Equiv.symm_trans_apply, hvΦ, r1, swAB,
      Equiv.coe_fn_symm_mk, blockDiagonal_apply, if_true]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]; simp [Finset.mul_sum]; exact Finset.sum_comm
  have e31 : reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (marg ((hvΦ Ψ).trans r31) κ) =
      blockDiagonal fun j => ((p j : ℝ) : ℂ) • marg (Ψ.trans swAB) (μ j) := by
    ext ⟨a, j⟩ ⟨b, j'⟩
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Matrix.smul_apply,
      smul_eq_mul, κ, Fintype.sum_prod_type, Equiv.symm_trans_apply, hvΦ, r31, swAB,
      Equiv.coe_fn_symm_mk, blockDiagonal_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
      Prod.swap_prod_mk]
    split_ifs <;> simp [Finset.mul_sum]
  have eΦ : reindex (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
        (reindex (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm _ _))
          (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm _ _)) (marg (hvΦ Ψ) κ)) =
      blockDiagonal fun j => ((p j : ℝ) : ℂ) • marg Ψ (μ j) := by
    ext ⟨⟨a, b⟩, j⟩ ⟨⟨a', b'⟩, j'⟩
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Matrix.smul_apply,
      smul_eq_mul, κ, Fintype.sum_prod_type, hvΦ,
      Equiv.coe_fn_symm_mk, blockDiagonal_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
      Prod.swap_prod_mk, Equiv.prodAssoc_symm_apply, Equiv.symm_symm, Equiv.prodAssoc_apply,
      Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Prod.map,
      id]
    split_ifs <;> simp [Finset.mul_sum]
  have d31 : vnEntropy (marg ((hvΦ Ψ).trans r31) κ) =
      ∑ j, negMulLog (p j) / log 2 + ∑ j, p j * vnEntropy (marg (Ψ.trans swAB) (μ j)) := by
    rw [← vn_reind (Equiv.prodComm _ _) _ (marg_psd _ hκ).1, e31,
      vn_blk p hp _ fun j => hv_dens _ (hμ j)]
  have dΦ : vnEntropy (marg (hvΦ Ψ) κ) =
      ∑ j, negMulLog (p j) / log 2 + ∑ j, p j * vnEntropy (marg Ψ (μ j)) := by
    rw [← vn_reind (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm _ _)) _ (marg_psd _ hκ).1,
      ← vn_reind (Equiv.prodAssoc _ _ _).symm
        (reindex (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm _ _))
          (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm _ _)) (marg (hvΦ Ψ) κ))
        ((marg_psd _ hκ).1.submatrix _), eΦ,
      vn_blk p hp _ fun j => hv_dens _ (hμ j)]
  rw [e21, e1, d31, dΦ] at h
  linarith

end holevo
end X6CE


/-! X6 CEMI library, part 24: a local instrument on `X` does not decrease the conditional
entropy `S(H | X G)` on average: for `p_j σ_j = Σ_z (A_jz ⊗ 1) ρ (A_jz ⊗ 1)†`,
`Σ_j p_j (S(Y_j G) - S(Y_j G H))_{σ_j} ≤ S(X G)_ρ - S(X G H)_ρ`. -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms X6SSA Real

section lt
variable {M N X Q : Type*} [Fintype N] [Fintype Q] [DecidableEq Q] [Fintype X]

def lt (Q : Type*) [DecidableEq Q] (B : Matrix M N ℂ) : Matrix (M × Q) (N × Q) ℂ :=
  of fun a b => if a.2 = b.2 then B a.1 b.1 else 0

@[simp] lemma lt_apply (B : Matrix M N ℂ) (a : M × Q) (b : N × Q) :
    lt Q B a b = if a.2 = b.2 then B a.1 b.1 else 0 := rfl

lemma st_ite (c : Prop) [Decidable c] (u : ℂ) : star (if c then u else 0) = if c then star u else 0 := by
  split_ifs <;> simp

lemma lt_conjTranspose (B : Matrix M N ℂ) : (lt Q B)ᴴ = lt Q Bᴴ := by
  ext a b
  simp only [lt, conjTranspose_apply, of_apply]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

lemma lt_mul (B : Matrix M N ℂ) (C : Matrix N X ℂ) : lt Q B * lt Q C = lt Q (B * C) := by
  ext a b
  simp only [lt, mul_apply, of_apply, Fintype.sum_prod_type, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

lemma lt_one [DecidableEq N] : lt Q (1 : Matrix N N ℂ) = 1 := by
  ext a b
  simp only [lt, of_apply, one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

lemma lt_conj_apply (B : Matrix M N ℂ) (C : Matrix X N ℂ) (ρ : Matrix (N × Q) (N × Q) ℂ)
    (a : M × Q) (b : X × Q) :
    (lt Q B * ρ * (lt Q C)ᴴ) a b = ∑ x, ∑ x', B a.1 x * ρ (x, a.2) (x', b.2) * star (C b.1 x') := by
  rw [lt_conjTranspose]
  simp only [mul_apply, lt, of_apply, Fintype.sum_prod_type, conjTranspose_apply, ite_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_mul]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  rw [Finset.sum_comm]

lemma trR_lt [Fintype M] (B : Matrix M N ℂ) (C : Matrix M N ℂ) (ρ : Matrix (N × Q) (N × Q) ℂ) :
    trR (lt Q B * ρ * (lt Q C)ᴴ) = B * trR ρ * Cᴴ := by
  ext m x
  show ∑ q, (lt Q B * ρ * (lt Q C)ᴴ) (m, q) (x, q) = _
  rw [Finset.sum_congr rfl fun q _ => lt_conj_apply B C ρ (m, q) (x, q)]
  simp only [mul_apply, conjTranspose_apply, trR, of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Finset.sum_comm
end lt

section instr
variable {k : ℕ} {X G H Z : Type*} [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G]
  [Fintype H] [DecidableEq H] [Fintype Z] [DecidableEq Z]
  {Y : Fin k → Type*} [∀ j, Fintype (Y j)] [∀ j, DecidableEq (Y j)]

/-- the local Kraus operator `B ⊗ 1_G ⊗ 1_H`. -/
abbrev kA (G H : Type*) [DecidableEq G] [DecidableEq H] {M N : Type*} (B : Matrix M N ℂ) :
    Matrix ((M × G) × H) ((N × G) × H) ℂ := lt H (lt G B)

lemma kA_conj_apply {M N : Type*} [Fintype M] [Fintype N] (B C : Matrix M N ℂ)
    (ρ : Matrix ((N × G) × H) ((N × G) × H) ℂ) (a b : (M × G) × H) :
    (kA G H B * ρ * (kA G H C)ᴴ) a b =
      ∑ x, ∑ x', B a.1.1 x * ρ ((x, a.1.2), a.2) ((x', b.1.2), b.2) * star (C b.1.1 x') := by
  rw [lt_conj_apply]
  simp only [Fintype.sum_prod_type, lt_apply, st_ite, ite_mul, zero_mul, mul_ite, mul_zero]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

/-- the Stinespring isometry `X → (Σ_j Y_j) × (Fin k × Z)` of the instrument. -/
def stB (A : (j : Fin k) → Z → Matrix (Y j) X ℂ) : Matrix ((Σ j, Y j) × (Fin k × Z)) X ℂ :=
  of fun a x => if a.2.1 = a.1.1 then A a.1.1 a.2.2 a.1.2 x else 0

lemma stB_iso (A : (j : Fin k) → Z → Matrix (Y j) X ℂ)
    (hA : ∑ j, ∑ z, (A j z)ᴴ * A j z = 1) : (stB A)ᴴ * stB A = 1 := by
  rw [← hA]
  ext x x'
  simp only [mul_apply, conjTranspose_apply, stB, of_apply, Fintype.sum_prod_type,
    Fintype.sum_sigma, Matrix.sum_apply, st_ite, ite_mul, zero_mul, mul_ite, mul_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Finset.sum_ite_eq']
  exact Finset.sum_comm

/-- the splitting of the dilated state used for SSA. -/
def stΦ : ((((Σ j, Y j) × (Fin k × Z)) × G) × H) ≃ ((Fin k × Z) × (H × ((Σ j, Y j) × G))) × Unit where
  toFun a := ((a.1.1.2, (a.2, (a.1.1.1, a.1.2))), ())
  invFun b := (((b.1.2.2.1, b.1.1), b.1.2.2.2), b.1.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- blocks `Σ_j (Y_j × G) × H`. -/
def stE : H × ((Σ j, Y j) × G) ≃ Σ j, (Y j × G) × H where
  toFun a := ⟨a.2.1.1, ((a.2.1.2, a.2.2), a.1)⟩
  invFun b := (b.2.2, (⟨b.1, b.2.1.1⟩, b.2.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def stE' : (Σ j, Y j) × G ≃ Σ j, Y j × G where
  toFun a := ⟨a.1.1, (a.1.2, a.2)⟩
  invFun b := (⟨b.1, b.2.1⟩, b.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Nonempty X] [Nonempty G] [Nonempty H] [Nonempty Z] [∀ j, Nonempty (Y j)]

set_option maxHeartbeats 2000000 in
theorem instr_cond (hk : 0 < k) (ρ : Matrix ((X × G) × H) ((X × G) × H) ℂ) (hρ : IsDensityMatrix ρ)
    (A : (j : Fin k) → Z → Matrix (Y j) X ℂ) (hA : ∑ j, ∑ z, (A j z)ᴴ * A j z = 1)
    (p : Fin k → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : (j : Fin k) → Matrix ((Y j × G) × H) ((Y j × G) × H) ℂ)
    (hσ : ∀ j, IsDensityMatrix (σ j))
    (hW : ∀ j, ((p j : ℝ) : ℂ) • σ j = ∑ z, kA G H (A j z) * ρ * (kA G H (A j z))ᴴ) :
    ∑ j, p j * (vnEntropy (trR (σ j)) - vnEntropy (σ j)) ≤ vnEntropy (trR ρ) - vnEntropy ρ := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : Nonempty (Σ j, Y j) := ⟨⟨⟨0, hk⟩, Classical.arbitrary _⟩⟩
  set V := kA G H (stB A)
  have hV : Vᴴ * V = 1 := by
    simp only [V, kA, lt_conjTranspose, lt_mul, stB_iso A hA, lt_one]
  set Θ := V * ρ * Vᴴ
  have hΘ : Θ.PosSemidef := hρ.1.mul_mul_conjTranspose_same V
  have htr : trace Θ = 1 := by
    simp only [Θ]; rw [trace_mul_cycle, hV, Matrix.one_mul, hρ.2]
  have h := ssa_split (stΦ (k := k) (Y := Y) (Z := Z) (G := G) (H := H)) Θ hΘ htr
  -- entry formula for Θ
  have hΘe : ∀ a b, Θ a b = if a.1.1.2.1 = a.1.1.1.1 ∧ b.1.1.2.1 = b.1.1.1.1 then
      ∑ x, ∑ x', A a.1.1.1.1 a.1.1.2.2 a.1.1.1.2 x * ρ ((x, a.1.2), a.2) ((x', b.1.2), b.2) *
        star (A b.1.1.1.1 b.1.1.2.2 b.1.1.1.2 x') else 0 := by
    intro a b
    simp only [Θ, V, kA_conj_apply, stB, of_apply]
    split_ifs <;> simp_all
  have hWe : ∀ j a b, ((p j : ℝ) : ℂ) * σ j a b =
      ∑ z, ∑ x, ∑ x', A j z a.1.1 x * ρ ((x, a.1.2), a.2) ((x', b.1.2), b.2) *
        star (A j z b.1.1 x') := by
    intro j a b
    have := congrFun (congrFun (hW j) a) b
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, kA_conj_apply] at this
    exact this
  -- (1) the A ∪ C marginal: `S(X G)` by the isometry
  have e21 : vnEntropy (marg ((stΦ (k := k) (Y := Y) (Z := Z) (G := G) (H := H)).trans r21) Θ) =
      vnEntropy (trR ρ) := by
    have m1 : marg (Equiv.refl _) Θ = trR Θ := by ext; rfl
    rw [vn_marg_eq (Equiv.refl _) _ (fun a b => ?_) (fun a b => ?_) hΘ, m1]
    · simp only [Θ, V, kA, trR_lt]
      have hi : (lt G (stB A))ᴴ * lt G (stB A) = 1 := by
        rw [lt_conjTranspose, lt_mul, stB_iso A hA, lt_one]
      exact X6CH.vn_iso _ hi (trR ρ) (marg_psd (Equiv.refl ((X × G) × H)) hρ.1)
    · simp [stΦ, r21, Prod.ext_iff]; tauto
    · simp [stΦ, r21, Prod.ext_iff]
  -- (2) the whole dilated state
  have eΦ : vnEntropy (marg (stΦ (k := k) (Y := Y) (Z := Z) (G := G) (H := H)) Θ) = vnEntropy ρ := by
    have m : marg (stΦ (k := k) (Y := Y) (Z := Z) (G := G) (H := H)) Θ =
        reindex ((stΦ (k := k) (Y := Y) (Z := Z) (G := G) (H := H)).trans (Equiv.prodPUnit _))
          ((stΦ (k := k) (Y := Y) (Z := Z) (G := G) (H := H)).trans (Equiv.prodPUnit _)) Θ := by
      ext a b; simp [marg, trR]
    rw [m, vn_reind _ _ hΘ.1]
    exact X6CH.vn_iso V hV ρ hρ.1
  -- (3) tracing the environment: the block state `⊕_j p_j σ_j`
  have e31 : vnEntropy (marg ((stΦ (k := k) (Y := Y) (Z := Z) (G := G) (H := H)).trans r31) Θ) =
      ∑ j, negMulLog (p j) / log 2 + ∑ j, p j * vnEntropy (σ j) := by
    have m : reindex stE stE (marg ((stΦ (k := k) (Y := Y) (Z := Z) (G := G) (H := H)).trans r31) Θ) =
        blockDiagonal' fun j => ((p j : ℝ) : ℂ) • σ j := by
      ext ⟨j, a⟩ ⟨j', b⟩
      simp only [reindex_apply, submatrix_apply, marg, trR, of_apply, Fintype.sum_prod_type,
        Fintype.sum_unique, Equiv.symm_trans_apply, stΦ, r31, stE, Equiv.coe_fn_symm_mk, hΘe]
      by_cases hj : j = j'
      · subst hj
        rw [blockDiagonal'_apply_eq, Matrix.smul_apply, smul_eq_mul, hWe]
        rw [Finset.sum_comm]
        simp [Finset.sum_ite_eq']
      · rw [blockDiagonal'_apply_ne _ _ _ hj]
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun z _ => ?_
        rw [if_neg]
        rintro ⟨h1, h2⟩; exact hj (h1.symm.trans h2)
    rw [← vn_reind stE _ (marg_psd _ hΘ).1, m, vn_blk' p hp σ hσ]
  -- (4) the `Y G` marginal: the block state `⊕_j p_j (σ_j)_{YG}`
  have e1 : vnEntropy (marg ((stΦ (k := k) (Y := Y) (Z := Z) (G := G) (H := H)).trans r1) Θ) =
      ∑ j, negMulLog (p j) / log 2 + ∑ j, p j * vnEntropy (trR (σ j)) := by
    have m : reindex stE' stE' (marg ((stΦ (k := k) (Y := Y) (Z := Z) (G := G) (H := H)).trans r1) Θ) =
        blockDiagonal' fun j => ((p j : ℝ) : ℂ) • trR (σ j) := by
      ext ⟨j, a⟩ ⟨j', b⟩
      simp only [reindex_apply, submatrix_apply, marg, trR, of_apply, Fintype.sum_prod_type,
        Fintype.sum_unique, Equiv.symm_trans_apply, stΦ, r1, stE', Equiv.coe_fn_symm_mk, hΘe]
      by_cases hj : j = j'
      · subst hj
        rw [blockDiagonal'_apply_eq, Matrix.smul_apply, smul_eq_mul]
        simp only [of_apply, Finset.mul_sum, hWe]
        rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
        simp only [and_self, if_true]
        exact Finset.sum_comm
      · rw [blockDiagonal'_apply_ne _ _ _ hj]
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun z _ =>
          Finset.sum_eq_zero fun h _ => ?_
        rw [if_neg]
        rintro ⟨h1, h2⟩; exact hj (h1.symm.trans h2)
    have hd : ∀ j, IsDensityMatrix (trR (σ j)) := fun j => hv_dens (Equiv.refl _) (hσ j)
    rw [← vn_reind stE' _ (marg_psd _ hΘ).1, m, vn_blk' p hp _ hd]
  rw [e21, e31, e1, eΦ] at h
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

end instr
end X6CE


/-! X6 CEMI library, part 25: splitting a paired register state at one party `P`
(`(E_P × F_P) × Π_{i ≠ P} (D_i × F_i)`, the other honest registers relabelled by equivalences
`E_i ≃ D_i`) and the bridges between register entropies and marginals of the split state. -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
  QAlgorithms.Papers.Independent.Gap20.P10 X6SSA

section bridge
variable {n : ℕ} (P : Fin n) {D E F : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
  [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
  (e : ∀ i, i ≠ P → E i ≃ D i)

/-- the other parties' paired registers, in the base labels `D`. -/
abbrev KK (P : Fin n) (D F : Fin n → Type) := (i : {i // i ≠ P}) → D i × F i

/-- the splitting at party `P`. -/
def Γs : RegisterBasis (fun i => E i × F i) ≃ (E P × F P) × KK P D F :=
  (Equiv.piSplitAt P (fun i => E i × F i)).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight fun i => (e i.1 i.2).prodCongr (Equiv.refl _)))

@[simp] lemma Γs_fst (x : RegisterBasis (fun i => E i × F i)) : (Γs P e x).1 = x P := rfl
@[simp] lemma Γs_snd (x : RegisterBasis (fun i => E i × F i)) (i : {i // i ≠ P}) :
    (Γs P e x).2 i = (e i.1 i.2 (x i).1, (x i).2) := rfl

/-- trace out the honest register of `P`. -/
def tX {M G H : Type*} : (M × G) × H ≃ (G × H) × M where
  toFun x := ((x.1.2, x.2), x.1.1)
  invFun y := ((y.2, y.1.1), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- the state of all registers except the honest register of `P`. -/
def μs (u : Matrix (RegisterBasis (fun i => E i × F i)) (RegisterBasis (fun i => E i × F i)) ℂ) :
    Matrix (F P × KK P D F) (F P × KK P D F) ℂ :=
  marg ((Γs P e).trans tX) u

/-- the remaining registers after removing party `i ≠ P`. -/
abbrev KR (P : Fin n) (D F : Fin n → Type) (i : Fin n) (hi : i ≠ P) :=
  (t : {t : {t // t ≠ P} // t ≠ ⟨i, hi⟩}) → D t × F t

def shf {G R S : Type*} : G × (R × S) ≃ R × (G × S) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun y := (y.2.1, (y.1, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- the honest-and-primed register of party `i ≠ P` in front. -/
def Ψi (i : Fin n) (hi : i ≠ P) : F P × KK P D F ≃ (D i × F i) × (F P × KR P D F i hi) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.piSplitAt ⟨i, hi⟩ (fun t : {t // t ≠ P} => D t × F t))).trans shf

/-- all primes in front. -/
def ΨF : F P × KK P D F ≃ (((t : {t // t ≠ P}) → F t) × F P) × ((t : {t // t ≠ P}) → D t) where
  toFun x := ((fun t => (x.2 t).2, x.1), fun t => (x.2 t).1)
  invFun y := (y.1.2, fun t => (y.2 t, y.1.1 t))
  left_inv _ := rfl
  right_inv _ := rfl

lemma forall_sub2 {i : Fin n} (hi : i ≠ P) (q : Fin n → Prop) :
    (∀ t : {t : {t // t ≠ P} // t ≠ ⟨i, hi⟩}, q t.1.1) ↔ ∀ i', i' ≠ i → i' ≠ P → q i' := by
  constructor
  · intro h i' h1 h2; exact h ⟨⟨i', h2⟩, fun h' => h1 (congrArg Subtype.val h')⟩
  · intro h t; exact h _ (fun h' => t.2 (Subtype.ext h')) t.1.2

lemma forall_sub1 (q : Fin n → Prop) : (∀ t : {t // t ≠ P}, q t.1) ↔ ∀ i', i' ≠ P → q i' :=
  ⟨fun h i' h' => h ⟨i', h'⟩, fun h t => h t.1 t.2⟩

variable [∀ i, Nonempty (D i)] [∀ i, Nonempty (E i)] [∀ i, Nonempty (F i)]
variable (u : Matrix (RegisterBasis (fun i => E i × F i)) (RegisterBasis (fun i => E i × F i)) ℂ)
  (hu : u.PosSemidef)
include hu

lemma br_P : S2 u ({P} ×ˢ Finset.univ) = vnEntropy (marg (Γs P e) u) := by
  refine (S2_eq _ u hu _ (fun x y => ?_) (fun x y => ?_)).symm
  · rw [toB_eq_iff]; simp [Prod.ext_iff]
  · rw [toB_ne_iff]
    simp only [Γs_snd, funext_iff, Prod.ext_iff, Equiv.apply_eq_iff_eq, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_univ, and_true]
    rw [forall_sub1 P (fun i => (x i).1 = (y i).1 ∧ (x i).2 = (y i).2)]
    constructor
    · intro h; exact ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩
    · intro h i hi; exact ⟨h.1 i hi, h.2 i hi⟩

lemma br_i (i : Fin n) (hi : i ≠ P) :
    S2 u ({i} ×ˢ Finset.univ) = vnEntropy (marg (Ψi P i hi) (μs P e u)) := by
  unfold μs; rw [marg_comp]
  refine (S2_eq _ u hu _ (fun x y => ?_) (fun x y => ?_)).symm
  · rw [toB_eq_iff]
    simp [Ψi, shf, tX, Prod.ext_iff]
  · rw [toB_ne_iff]
    simp only [Ψi, shf, tX, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
      id, Equiv.coe_fn_mk, Equiv.piSplitAt_apply, Equiv.prodAssoc_apply, Γs_fst, Γs_snd,
      funext_iff, Prod.ext_iff, Equiv.apply_eq_iff_eq, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_univ, and_true]
    rw [forall_sub2 P hi (fun i => (x i).1 = (y i).1 ∧ (x i).2 = (y i).2)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun i' hi' => ?_, fun i' hi' => ?_⟩
      · by_cases hP : i' = P
        · subst hP; exact h3
        · exact (h2 i' hi' hP).1
      · by_cases hP : i' = P
        · subst hP; exact h1
        · exact (h2 i' hi' hP).2
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h2 P hi.symm, fun i' a b => ⟨h1 i' a, h2 i' a⟩⟩, h1 P hi.symm⟩

lemma br_it (i : Fin n) (hi : i ≠ P) :
    S2 u ({i} ×ˢ {true}) = vnEntropy (marg ((Ψi P i hi).trans swAB) (μs P e u)) := by
  unfold μs; rw [marg_comp]
  refine (S2_eq _ u hu _ (fun x y => ?_) (fun x y => ?_)).symm
  · rw [toB_eq_iff]
    simp [Ψi, shf, tX, swAB, Prod.ext_iff]
  · rw [toB_ne_iff]
    simp only [Ψi, shf, tX, swAB, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
      id, Equiv.coe_fn_mk, Equiv.piSplitAt_apply, Equiv.prodAssoc_apply, Γs_fst, Γs_snd,
      funext_iff, Prod.ext_iff, Equiv.apply_eq_iff_eq, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_univ, and_true, true_and]
    rw [forall_sub2 P hi (fun i => (x i).1 = (y i).1 ∧ (x i).2 = (y i).2)]
    constructor
    · rintro ⟨⟨h0, h1, h2⟩, h3⟩
      refine ⟨fun i' _ => ?_, fun i' hi' => ?_⟩
      · by_cases hP : i' = P
        · subst hP; exact h3
        · by_cases hii : i' = i
          · subst hii; exact h0
          · exact (h2 i' hii hP).1
      · by_cases hP : i' = P
        · subst hP; exact h1
        · exact (h2 i' hi' hP).2
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1 i (by simp), h2 P hi.symm, fun i' a b => ⟨h1 i' (by simp), h2 i' a⟩⟩, h1 P (by simp)⟩

lemma br_Pt : S2 u ({P} ×ˢ {true}) = vnEntropy (marg ((ΨF P).trans swAB) (μs P e u)) := by
  unfold μs; rw [marg_comp]
  refine (S2_eq _ u hu _ (fun x y => ?_) (fun x y => ?_)).symm
  · rw [toB_eq_iff]
    simp [ΨF, tX, swAB, Prod.ext_iff]
  · rw [toB_ne_iff]
    simp only [ΨF, tX, swAB, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
      id, Equiv.coe_fn_mk, Equiv.prodAssoc_apply, Γs_fst, Γs_snd,
      funext_iff, Prod.ext_iff, Equiv.apply_eq_iff_eq, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_univ, and_true, true_and]
    rw [forall_sub1 P (fun i => (x i).2 = (y i).2), forall_sub1 P (fun i => (x i).1 = (y i).1)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun i' _ => ?_, fun i' hi' => h1 i' hi'⟩
      by_cases hP : i' = P
      · subst hP; exact h3
      · exact h2 i' hP
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h2, fun i' _ => h1 i' (by simp)⟩, h1 P (by simp)⟩

lemma br_Ft : S2 u (Finset.univ ×ˢ {true}) = vnEntropy (marg (ΨF P) (μs P e u)) := by
  unfold μs; rw [marg_comp]
  refine (S2_eq _ u hu _ (fun x y => ?_) (fun x y => ?_)).symm
  · rw [toB_eq_iff]
    simp only [ΨF, tX, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
      id, Equiv.coe_fn_mk, Equiv.prodAssoc_apply, Γs_fst, Γs_snd,
      funext_iff, Prod.ext_iff, Equiv.apply_eq_iff_eq, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_univ, true_and]
    rw [forall_sub1 P (fun i => (x i).2 = (y i).2)]
    simp only [Bool.false_eq_true, imp_false, not_true_eq_false, IsEmpty.forall_iff, implies_true,
      true_and, forall_const]
    constructor
    · rintro ⟨h1, h2⟩ i'
      by_cases hP : i' = P
      · subst hP; exact h2
      · exact h1 i' hP
    · intro h; exact ⟨fun i' _ => h i', h P⟩
  · rw [toB_ne_iff]
    simp only [ΨF, tX, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
      id, Equiv.coe_fn_mk, Equiv.prodAssoc_apply, Γs_fst, Γs_snd,
      funext_iff, Prod.ext_iff, Equiv.apply_eq_iff_eq, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_univ, true_and]
    rw [forall_sub1 P (fun i => (x i).1 = (y i).1)]
    simp only [Bool.false_eq_true, not_false_eq_true, forall_const, not_true_eq_false,
      IsEmpty.forall_iff, implies_true, and_true]
    constructor
    · rintro ⟨h1, h2⟩ i'
      by_cases hP : i' = P
      · subst hP; exact h2
      · exact h1 i' hP
    · intro h; exact ⟨fun i' _ => h i', h P⟩

end bridge
end X6CE


/-! X6 CEMI library, part 26: local Kraus operators of a `LocalInstrument` become `B ⊗ 1` in the
split coordinates; completeness of the local Kraus family; the paired increment split at a party;
trace preservation of the instrument on the other registers. -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
  QAlgorithms.Papers.Independent.Gap20.P10 X6SSA

section kraus
variable {n : ℕ} (P : Fin n) {D E : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
  [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

/-- splitting of a honest register basis at `P`. -/
def Γh (e : ∀ i, i ≠ P → E i ≃ D i) : RegisterBasis E ≃ E P × ((i : {i // i ≠ P}) → D i) :=
  (Equiv.piSplitAt P E).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight fun i => e i.1 i.2))

@[simp] lemma Γh_fst (e : ∀ i, i ≠ P → E i ≃ D i) (x : RegisterBasis E) : (Γh P e x).1 = x P := rfl
@[simp] lemma Γh_snd (e : ∀ i, i ≠ P → E i ≃ D i) (x : RegisterBasis E) (i : {i // i ≠ P}) :
    (Γh P e x).2 i = e i.1 i.2 (x i) := rfl

end kraus

section fs
variable {n : ℕ} (s t : FiniteState n) (P : Fin n) (hd : ∀ i, i ≠ P → t.dims i = s.dims i)

/-- the relabelling of the unchanged registers. -/
def eF : ∀ i, i ≠ P → Fin (t.dims i) ≃ Fin (s.dims i) := fun i hi => finCongr (hd i hi)

lemma kr_h (B : Matrix (Fin (t.dims P)) (Fin (s.dims P)) ℂ) :
    reindex (Γh P (eF s t P hd)) (Γh P (fun i _ => Equiv.refl (Fin (s.dims i))))
      (liftLocalKraus s t P B) = lt _ B := by
  ext a b
  obtain ⟨x, rfl⟩ := (Γh P (eF s t P hd)).surjective a
  obtain ⟨y, rfl⟩ := (Γh P (fun i _ => Equiv.refl (Fin (s.dims i)))).surjective b
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, lt_apply, Γh_fst,
    liftLocalKraus, funext_iff, Γh_snd, eF, Equiv.refl_apply]
  have : (∀ i, i ≠ P → (x i).val = (y i).val) ↔
      ∀ i : {i // i ≠ P}, (finCongr (hd i.1 i.2)) (x i) = y i := by
    constructor
    · intro h i; exact Fin.ext (by simp [h i.1 i.2])
    · intro h i hi; have := congrArg Fin.val (h ⟨i, hi⟩); simpa using this
  simp only [this]

variable (F : Fin n → Type) [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]

lemma kr_p (B : Matrix (Fin (t.dims P)) (Fin (s.dims P)) ℂ) :
    reindex (Γs P (eF s t P hd) (F := F)) (Γs P (fun i _ => Equiv.refl (Fin (s.dims i))) (F := F))
      (liftP F (liftLocalKraus s t P B)) = kA (F P) (KK P (fun i => Fin (s.dims i)) F) B := by
  ext a b
  obtain ⟨x, rfl⟩ := (Γs P (eF s t P hd) (F := F)).surjective a
  obtain ⟨y, rfl⟩ := (Γs P (fun i _ => Equiv.refl (Fin (s.dims i))) (F := F)).surjective b
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, kA, lt_apply, Γs_fst,
    liftP, liftLocalKraus, funext_iff, Γs_snd, eF, Equiv.refl_apply, Prod.ext_iff]
  by_cases h1 : ∀ i, (x i).2 = (y i).2
  · by_cases h2 : ∀ i, i ≠ P → (x i).1.val = (y i).1.val
    · rw [if_pos h1, if_pos h2, if_pos, if_pos (h1 P), one_mul]
      intro i
      exact ⟨Fin.ext (by simp [h2 i.1 i.2]), h1 i⟩
    · rw [if_pos h1, if_neg h2, mul_zero, if_neg]
      intro h; apply h2; intro i hi
      have := congrArg Fin.val (h ⟨i, hi⟩).1; simpa using this
  · rw [if_neg h1, zero_mul]
    split_ifs with h3 h4
    · exfalso; apply h1; intro i
      by_cases hi : i = P
      · subst hi; exact h4
      · exact (h3 ⟨i, hi⟩).2
    · rfl
    · rfl

end fs

section complete
variable {k : ℕ} {N K : Type*} [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K]

lemma lt_sum {M : Type*} {ι : Type*} (S : Finset ι) (f : ι → Matrix M N ℂ) :
    lt K (∑ i ∈ S, f i) = ∑ i ∈ S, lt K (f i) := by
  ext a b
  simp only [lt_apply, Matrix.sum_apply]
  split_ifs <;> simp_all

lemma lt_inj_one [Nonempty K] {c : Fin k → ℕ} {M : Fin k → Type*} [∀ j, Fintype (M j)]
    [∀ j, DecidableEq (M j)] (B : (j : Fin k) → Fin (c j) → Matrix (M j) N ℂ)
    (h : ∑ j, ∑ z, (lt K (B j z))ᴴ * lt K (B j z) = 1) : ∑ j, ∑ z, (B j z)ᴴ * B j z = 1 := by
  simp only [lt_conjTranspose, lt_mul] at h
  simp only [← lt_sum] at h
  ext x x'
  have := congrFun (congrFun h (x, Classical.arbitrary K)) (x', Classical.arbitrary K)
  simpa [lt_apply, one_apply, Prod.ext_iff] using this

lemma reindex_conj_mul {A B : Type*} [Fintype A] [Fintype B] {A' B' : Type*} [Fintype A'] [Fintype B']
    (f : A ≃ A') (g : B ≃ B') (L : Matrix A B ℂ) :
    reindex g g (Lᴴ * L) = (reindex f g L)ᴴ * reindex f g L := by
  simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]

end complete

section tp
variable {k : ℕ} {X G H Z : Type*} [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G]
  [Fintype H] [DecidableEq H] [Fintype Z] [DecidableEq Z]
  {Y : Fin k → Type*} [∀ j, Fintype (Y j)] [∀ j, DecidableEq (Y j)]

lemma sum4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- trace preservation of the instrument on the registers it does not act on. -/
lemma instr_tp (A : (j : Fin k) → Z → Matrix (Y j) X ℂ) (hA : ∑ j, ∑ z, (A j z)ᴴ * A j z = 1)
    (ρ : Matrix ((X × G) × H) ((X × G) × H) ℂ) :
    ∑ j, ∑ z, marg tX (kA G H (A j z) * ρ * (kA G H (A j z))ᴴ) = marg tX ρ := by
  ext a b
  have e1 : ∀ j z, marg tX (kA G H (A j z) * ρ * (kA G H (A j z))ᴴ) a b =
      ∑ y, ∑ x, ∑ x', A j z y x * ρ ((x, a.1), a.2) ((x', b.1), b.2) * star (A j z y x') := by
    intro j z
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, tX, Equiv.coe_fn_symm_mk]
    exact Finset.sum_congr rfl fun y _ => kA_conj_apply _ _ _ _ _
  simp only [Matrix.sum_apply, e1]
  have e2 : marg tX ρ a b = ∑ x, ∑ x', (1 : Matrix X X ℂ) x' x * ρ ((x, a.1), a.2) ((x', b.1), b.2) := by
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, tX, Equiv.coe_fn_symm_mk,
      one_apply]
    simp [Finset.sum_ite_eq]
  rw [e2, ← hA]
  simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, Finset.sum_mul]
  have e3 : ∀ j z, ∑ y, ∑ x, ∑ x', A j z y x * ρ ((x, a.1), a.2) ((x', b.1), b.2) * star (A j z y x') =
      ∑ x, ∑ x', ∑ y, star (A j z y x') * A j z y x * ρ ((x, a.1), a.2) ((x', b.1), b.2) := by
    intro j z
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y _ => by ring
  simp only [e3]
  exact sum4 _

end tp

section split
variable {n : ℕ} (P : Fin n) {D E F : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
  [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
  (e : ∀ i, i ≠ P → E i ≃ D i)
  [∀ i, Nonempty (D i)] [∀ i, Nonempty (E i)] [∀ i, Nonempty (F i)]

lemma S2_univ (u : Matrix (RegisterBasis (fun i => E i × F i)) (RegisterBasis (fun i => E i × F i)) ℂ)
    (hu : u.PosSemidef) : S2 u (Finset.univ ×ˢ Finset.univ) = vnEntropy u := by
  have m : marg (Equiv.prodUnique (RegisterBasis (fun i => E i × F i)) Unit).symm u = u := by
    ext a b; simp [marg, trR]
  rw [← S2_eq (Equiv.prodUnique (RegisterBasis (fun i => E i × F i)) Unit).symm u hu _
    (fun x y => ?_) (fun x y => ?_), m]
  · rw [toB_eq_iff]
    simp only [Equiv.prodUnique_symm_apply, Finset.mem_product, Finset.mem_univ, and_self,
      forall_const, funext_iff, Prod.ext_iff]
    constructor
    · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
    · intro h i; exact ⟨h.1 i, h.2 i⟩
  · simp

lemma pd_S2 (u : Matrix (RegisterBasis (fun i => E i × F i)) (RegisterBasis (fun i => E i × F i)) ℂ)
    (hu : u.PosSemidef) :
    pairedDifference u = ∑ i, S2 u ({i} ×ˢ Finset.univ) - S2 u (Finset.univ ×ˢ Finset.univ) -
      (∑ i, S2 u ({i} ×ˢ {true}) - S2 u (Finset.univ ×ˢ {true})) := by
  have hall : allParties (singleParties n) = Finset.univ := by
    ext i; simp [allParties, singleParties]
  unfold pairedDifference info conditionalMultipartiteInformation
  simp only [hall, Finset.union_empty, singleParties]
  simp_rw [ent_reg u hu, ent_pmB u hu]
  simp only [Finset.empty_product]
  ring

/-- the `i`-th Holevo-type term. -/
def bq (u : Matrix (RegisterBasis (fun i => E i × F i)) (RegisterBasis (fun i => E i × F i)) ℂ)
    (i : Fin n) : ℝ :=
  if h : i = P then 0 else
    vnEntropy (marg (Ψi P i h) (μs P e u)) - vnEntropy (marg ((Ψi P i h).trans swAB) (μs P e u))

lemma pd_split (u : Matrix (RegisterBasis (fun i => E i × F i)) (RegisterBasis (fun i => E i × F i)) ℂ)
    (hu : u.PosSemidef) :
    pairedDifference u = (vnEntropy (marg (Γs P e) u) - vnEntropy u) +
      ∑ i ∈ Finset.univ.erase P, bq P e u i +
      (vnEntropy (marg (ΨF P) (μs P e u)) - vnEntropy (marg ((ΨF P).trans swAB) (μs P e u))) := by
  rw [pd_S2 u hu, S2_univ u hu, br_Ft P e u hu,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ P), ← Finset.add_sum_erase _ _ (Finset.mem_univ P),
    br_P P e u hu, br_Pt P e u hu]
  have : ∑ i ∈ Finset.univ.erase P, S2 u ({i} ×ˢ Finset.univ) -
      ∑ i ∈ Finset.univ.erase P, S2 u ({i} ×ˢ {true}) = ∑ i ∈ Finset.univ.erase P, bq P e u i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiP : i ≠ P := Finset.ne_of_mem_erase hi
    rw [bq, dif_neg hiP, br_i P e u hu i hiP, br_it P e u hu i hiP]
  linarith

end split
end X6CE


/-! X6 CEMI library, part 27: the paired increment does not increase on average under a
local instrument: for every extension `ω` of `s` there are extensions `ω_j` of the outcomes with
`Σ_j p_j Δ(ω_j) ≤ Δ(ω)`. -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
  QAlgorithms.Papers.Independent.Gap20.P10 X6SSA

lemma bdens {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (x0 : Ω) :
    IsDensityMatrix (diagonal fun x => if x = x0 then (1 : ℂ) else 0) := by
  refine ⟨PosSemidef.diagonal fun x => ?_, ?_⟩
  · split_ifs <;> simp
  · simp [trace_diagonal]

lemma sum_hat {k : ℕ} {c : Fin k → ℕ} {β : Type*} [AddCommMonoid β] (j : Fin k)
    (f : Fin (c j) → β) :
    ∑ w : (Σ j', Fin (c j')), (if h : w.1 = j then f ⟨w.2.val, h ▸ w.2.isLt⟩ else 0) = ∑ z, f z := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma reindex_sum {A B A' B' : Type*} {ι : Type*} (S : Finset ι) (f : A ≃ A') (g : B ≃ B')
    (X : ι → Matrix A B ℂ) : reindex f g (∑ i ∈ S, X i) = ∑ i ∈ S, reindex f g (X i) := by
  ext a b; simp [Matrix.sum_apply]

lemma marg_smul {Ω K F : Type*} [Fintype F] (Φ : Ω ≃ K × F) (c : ℂ) (M : Matrix Ω Ω ℂ) :
    marg Φ (c • M) = c • marg Φ M := by
  ext a b; simp [marg, trR, Finset.mul_sum]

lemma marg_sum {Ω K F : Type*} [Fintype F] {ι : Type*} (S : Finset ι) (Φ : Ω ≃ K × F)
    (M : ι → Matrix Ω Ω ℂ) : marg Φ (∑ i ∈ S, M i) = ∑ i ∈ S, marg Φ (M i) := by
  ext a b; simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Matrix.sum_apply]
  rw [Finset.sum_comm]

lemma lt_zero {M N Q : Type*} [DecidableEq Q] : lt Q (0 : Matrix M N ℂ) = 0 := by
  ext a b; simp

lemma dens_reindex {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (e : Ω ≃ Ω') {M : Matrix Ω Ω ℂ}
    (h : IsDensityMatrix M) : IsDensityMatrix (reindex e e M) := by
  refine ⟨h.1.submatrix _, ?_⟩
  rw [← h.2]
  simp only [trace, reindex_apply, submatrix_apply, diag_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

section KI
variable {n k : ℕ}

set_option maxHeartbeats 4000000 in
theorem KI (s : FiniteState n) (p : Fin k → ℝ) (r : Fin k → FiniteState n)
    (hI : LocalInstrument s p r) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (ω : Matrix (RegisterBasis (fun i => Fin (s.dims i) × Fin (d i)))
      (RegisterBasis (fun i => Fin (s.dims i) × Fin (d i))) ℂ)
    (hω : IsDensityMatrix ω) (hu : unprimedMarginal ω = s.rho) :
    ∃ ω' : (j : Fin k) → Matrix (RegisterBasis (fun i => Fin ((r j).dims i) × Fin (d i)))
      (RegisterBasis (fun i => Fin ((r j).dims i) × Fin (d i))) ℂ,
      (∀ j, IsDensityMatrix (ω' j)) ∧ (∀ j, 0 < p j → unprimedMarginal (ω' j) = (r j).rho) ∧
      ∑ j, p j * pairedDifference (ω' j) ≤ pairedDifference ω := by
  obtain ⟨hp, hs, P, cnt, A, hdim, hK, hrel⟩ := hI
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hs
    · exact h
  have hne_s : ∀ i, Nonempty (Fin (s.dims i)) := fun i => ⟨⟨0, s.positive i⟩⟩
  have hne_r : ∀ j i, Nonempty (Fin ((r j).dims i)) := fun j i => ⟨⟨0, (r j).positive i⟩⟩
  have hne_d : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, hd i⟩⟩
  let F : Fin n → Type := fun i => Fin (d i)
  let L : (j : Fin k) → Fin (cnt j) → Matrix (RegisterBasis (fun i => Fin ((r j).dims i)))
      (RegisterBasis (fun i => Fin (s.dims i))) ℂ := fun j z => liftLocalKraus s (r j) P (A j z)
  let x0 : (j : Fin k) → RegisterBasis (fun i => Fin ((r j).dims i) × Fin (d i)) :=
    fun j i => (⟨0, (r j).positive i⟩, ⟨0, hd i⟩)
  let ω' : (j : Fin k) → Matrix (RegisterBasis (fun i => Fin ((r j).dims i) × Fin (d i)))
      (RegisterBasis (fun i => Fin ((r j).dims i) × Fin (d i))) ℂ := fun j =>
    if p j = 0 then diagonal (fun x => if x = x0 j then 1 else 0) else outExt F (p j) (L j) ω
  have hω' : ∀ j, IsDensityMatrix (ω' j) := by
    intro j
    by_cases h : p j = 0
    · simp only [ω', if_pos h]; exact bdens _
    · simp only [ω', if_neg h]
      exact outExt_dens (lt_of_le_of_ne (hp j) (Ne.symm h)) (L j) hω.1 hu (r j).normalized (hrel j)
  have hu' : ∀ j, 0 < p j → unprimedMarginal (ω' j) = (r j).rho := by
    intro j hj
    simp only [ω', if_neg hj.ne']
    exact outExt_um hj.ne' (L j) hu (hrel j)
  refine ⟨ω', hω', hu', ?_⟩
  -- split coordinates
  let e0 : ∀ i, i ≠ P → Fin (s.dims i) ≃ Fin (s.dims i) := fun i _ => Equiv.refl _
  let ej : (j : Fin k) → ∀ i, i ≠ P → Fin ((r j).dims i) ≃ Fin (s.dims i) :=
    fun j => eF s (r j) P (hdim j)
  let Γ0 := Γs P e0 (F := F)
  let Γj := fun j => Γs P (ej j) (F := F)
  let ρh := reindex Γ0 Γ0 ω
  let σ := fun j => reindex (Γj j) (Γj j) (ω' j)
  let Ah : (j : Fin k) → (Σ j', Fin (cnt j')) → Matrix (Fin ((r j).dims P)) (Fin (s.dims P)) ℂ :=
    fun j w => if h : w.1 = j then A j ⟨w.2.val, h ▸ w.2.isLt⟩ else 0
  -- completeness of the local Kraus family
  have hA0 : ∑ j, ∑ z, (A j z)ᴴ * A j z = 1 := by
    have h1 : ∀ j z, reindex (Γh P (fun i _ => Equiv.refl (Fin (s.dims i))))
        (Γh P (fun i _ => Equiv.refl (Fin (s.dims i))))
        ((liftLocalKraus s (r j) P (A j z))ᴴ * liftLocalKraus s (r j) P (A j z)) =
        (lt _ (A j z))ᴴ * lt _ (A j z) := by
      intro j z
      rw [reindex_conj_mul (Γh P (eF s (r j) P (hdim j))), kr_h]; rfl
    have h2 := congrArg (reindex (Γh P (fun i _ => Equiv.refl (Fin (s.dims i))))
      (Γh P (fun i _ => Equiv.refl (Fin (s.dims i))))) hK
    rw [reindex_sum, Finset.sum_congr rfl fun j _ => reindex_sum _ _ _ _] at h2
    simp only [h1] at h2
    rw [reindex_apply, submatrix_one_equiv] at h2
    exact lt_inj_one A h2
  have hA : ∑ j, ∑ w, (Ah j w)ᴴ * Ah j w = 1 := by
    rw [← hA0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_hat (c := cnt) j (fun z => (A j z)ᴴ * A j z)]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Ah]; split_ifs <;> simp
  have hZ : Nonempty (Σ j, Fin (cnt j)) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    have h0 : ∑ j, ∑ w, (Ah j w)ᴴ * Ah j w = 0 := by simp [Finset.univ_eq_empty]
    rw [hA] at h0
    have := congrFun (congrFun h0 ⟨0, s.positive P⟩) ⟨0, s.positive P⟩
    simp at this
  -- the outcome blocks
  have hW : ∀ j, ((p j : ℝ) : ℂ) • σ j =
      ∑ w, kA (F P) (KK P (fun i => Fin (s.dims i)) F) (Ah j w) * ρh *
        (kA (F P) (KK P (fun i => Fin (s.dims i)) F) (Ah j w))ᴴ := by
    intro j
    have e1 : ∑ w, kA (F P) (KK P (fun i => Fin (s.dims i)) F) (Ah j w) * ρh *
        (kA (F P) (KK P (fun i => Fin (s.dims i)) F) (Ah j w))ᴴ =
        ∑ z, kA (F P) (KK P (fun i => Fin (s.dims i)) F) (A j z) * ρh *
          (kA (F P) (KK P (fun i => Fin (s.dims i)) F) (A j z))ᴴ := by
      rw [← sum_hat (c := cnt) j (fun z => kA (F P) (KK P (fun i => Fin (s.dims i)) F) (A j z) * ρh *
          (kA (F P) (KK P (fun i => Fin (s.dims i)) F) (A j z))ᴴ)]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [Ah]; split_ifs
      · rfl
      · simp only [kA, lt_zero, Matrix.zero_mul, conjTranspose_zero, Matrix.mul_zero]
    have e2 : ∀ z, kA (F P) (KK P (fun i => Fin (s.dims i)) F) (A j z) * ρh *
        (kA (F P) (KK P (fun i => Fin (s.dims i)) F) (A j z))ᴴ =
        reindex (Γj j) (Γj j) (liftP F (L j z) * ω * (liftP F (L j z))ᴴ) := by
      intro z
      rw [← kr_p s (r j) P (hdim j) F (A j z)]
      simp only [reindex_apply, ρh, conjTranspose_submatrix, submatrix_mul_equiv, Γj, Γ0, ej, L, e0]
    rw [e1, Finset.sum_congr rfl fun z _ => e2 z, ← reindex_sum]
    by_cases h : p j = 0
    · have hpsd : (∑ z, liftP F (L j z) * ω * (liftP F (L j z))ᴴ).PosSemidef :=
        Matrix.posSemidef_sum _ fun z _ => hω.1.mul_mul_conjTranspose_same _
      have hz : ∑ z, liftP F (L j z) * ω * (liftP F (L j z))ᴴ = 0 := by
        apply hpsd.trace_eq_zero_iff.1
        rw [← marg_trace (up _ F), ← um_eq, um_sum]
        simp only [um_liftP, hu]
        rw [← hrel j, h]; simp
      rw [hz, h]; simp
    · simp only [σ, ω', if_neg h, outExt]
      ext a b
      simp only [reindex_apply, submatrix_apply, Matrix.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h, Complex.ofReal_one, one_mul]
  -- (I) the instrument term
  have hσd : ∀ j, IsDensityMatrix (σ j) := fun j => dens_reindex _ (hω' j)
  have hIC := instr_cond hk ρh (dens_reindex _ hω) Ah hA p hp σ hσd hW
  have hI1 : ∑ j, p j * (vnEntropy (marg (Γj j) (ω' j)) - vnEntropy (ω' j)) ≤
      vnEntropy (marg Γ0 ω) - vnEntropy ω := by
    have a1 : ∀ j, vnEntropy (σ j) = vnEntropy (ω' j) := fun j => vn_reind _ _ (hω' j).1.1
    have a2 : vnEntropy ρh = vnEntropy ω := vn_reind _ _ hω.1.1
    simp only [a1, a2] at hIC
    exact hIC
  -- (II) the Holevo terms
  let μ := fun j => μs P (ej j) (F := F) (ω' j)
  have hμd : ∀ j, IsDensityMatrix (μ j) := fun j => hv_dens _ (hω' j)
  have hmix : (∑ j, ((p j : ℝ) : ℂ) • μ j) = μs P e0 (F := F) ω := by
    have h1 : ∀ j, ((p j : ℝ) : ℂ) • μ j = ∑ w, marg tX
        (kA (F P) (KK P (fun i => Fin (s.dims i)) F) (Ah j w) * ρh *
          (kA (F P) (KK P (fun i => Fin (s.dims i)) F) (Ah j w))ᴴ) := by
      intro j
      rw [← marg_sum, ← hW j, marg_smul]
      rfl
    simp only [h1]
    rw [instr_tp Ah hA ρh]
    rfl
  have hb : ∀ i ∈ Finset.univ.erase P, ∑ j, p j * bq P (ej j) (ω' j) i ≤ bq P e0 ω i := by
    intro i hi
    have hiP : i ≠ P := Finset.ne_of_mem_erase hi
    simp only [bq, dif_neg hiP]
    have := holevo (Ψi P i hiP) p hp hs μ hμd
    rw [hmix] at this
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  have hc : ∑ j, p j * (vnEntropy (marg (ΨF P) (μs P (ej j) (ω' j))) -
      vnEntropy (marg ((ΨF P).trans swAB) (μs P (ej j) (ω' j)))) ≤
      vnEntropy (marg (ΨF P) (μs P e0 ω)) - vnEntropy (marg ((ΨF P).trans swAB) (μs P e0 ω)) := by
    have := holevo (ΨF P) p hp hs μ hμd
    rw [hmix] at this
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  -- assemble
  rw [pd_split P e0 ω hω.1]
  have hsplit : ∀ j, pairedDifference (ω' j) = (vnEntropy (marg (Γj j) (ω' j)) - vnEntropy (ω' j)) +
      ∑ i ∈ Finset.univ.erase P, bq P (ej j) (ω' j) i +
      (vnEntropy (marg (ΨF P) (μs P (ej j) (ω' j))) -
        vnEntropy (marg ((ΨF P).trans swAB) (μs P (ej j) (ω' j)))) :=
    fun j => pd_split P (ej j) (ω' j) (hω' j).1
  simp only [hsplit, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ.erase P)]
  have := Finset.sum_le_sum hb
  linarith

end KI
end X6CE


/-! X6 CEMI library, part 28: the n-party flagged paired extension of two extensions and the
convexity of CEMI over arbitrary finite mixtures (n ≥ 1 parties). -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
  QAlgorithms.Papers.Independent.Gap20.P10 X6SSA Real

section pairedN
variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
  {d1 d2 : Fin n → ℕ} (l : ℝ)
  (ω1 : Matrix (RegisterBasis (fun i => D i × Fin (d1 i)))
    (RegisterBasis (fun i => D i × Fin (d1 i))) ℂ)
  (ω2 : Matrix (RegisterBasis (fun i => D i × Fin (d2 i)))
    (RegisterBasis (fun i => D i × Fin (d2 i))) ℂ)

/-- left label embedding. -/
def gLN (d1 d2 : Fin n → ℕ) (i : Fin n) : D i × Fin (d1 i) → D i × Fin (d1 i + d2 i) :=
  fun p => (p.1, Fin.castAdd (d2 i) p.2)

/-- right label embedding. -/
def gRN (d1 d2 : Fin n → ℕ) (i : Fin n) : D i × Fin (d2 i) → D i × Fin (d1 i + d2 i) :=
  fun p => (p.1, Fin.natAdd (d1 i) p.2)

lemma gLN_inj (i : Fin n) : Function.Injective (gLN (D := D) d1 d2 i) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  simp only [gLN, Prod.mk.injEq] at h
  rw [h.1, Fin.castAdd_inj.1 h.2]

lemma gRN_inj (i : Fin n) : Function.Injective (gRN (D := D) d1 d2 i) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  simp only [gRN, Prod.mk.injEq] at h
  rw [h.1, (Fin.natAdd_inj _).1 h.2]

lemma cast_ne_natN (i : Fin n) (x : Fin (d1 i)) (y : Fin (d2 i)) :
    Fin.castAdd (d2 i) x ≠ Fin.natAdd (d1 i) y := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

lemma gLRN_ne (i : Fin n) (a : D i × Fin (d1 i)) (b : D i × Fin (d2 i)) :
    gLN d1 d2 i a ≠ gRN d1 d2 i b := by
  intro h
  exact cast_ne_natN i a.2 b.2 (congrArg Prod.snd h)

/-- the flagged paired extension. -/
def pairMixN : Matrix (RegisterBasis (fun i => D i × Fin (d1 i + d2 i)))
    (RegisterBasis (fun i => D i × Fin (d1 i + d2 i))) ℂ :=
  flagMix (gLN d1 d2) (gRN d1 d2) l ω1 ω2

lemma pairMixN_um : unprimedMarginal (pairMixN l ω1 ω2) =
    (l : ℂ) • unprimedMarginal ω1 + ((1 - l : ℝ) : ℂ) • unprimedMarginal ω2 := by
  rw [um_eq, um_eq, um_eq, pairMixN, flagMix, marg_lin]
  have e1 := marg_embed (up D (fun i => Fin (d1 i + d2 i))) (up D (fun i => Fin (d1 i)))
    (regMap (gLN d1 d2)) id (regMap fun i => Fin.castAdd (d2 i)) (regMap_inj gLN_inj)
    Function.injective_id (regMap_inj fun i => Fin.castAdd_injective _ _) (fun x => rfl) ω1
  have e2 := marg_embed (up D (fun i => Fin (d1 i + d2 i))) (up D (fun i => Fin (d2 i)))
    (regMap (gRN d1 d2)) id (regMap fun i => Fin.natAdd (d1 i)) (regMap_inj gRN_inj)
    Function.injective_id (regMap_inj fun i => Fin.natAdd_injective _ _) (fun x => rfl) ω2
  rw [e1, e2, emb_id, emb_id]

lemma pairMixN_pm : primedMarginal (pairMixN l ω1 ω2) =
    flagMix (D := fun i => Fin (d1 i + d2 i)) (fun i => Fin.castAdd (d2 i))
      (fun i => Fin.natAdd (d1 i)) l (primedMarginal ω1) (primedMarginal ω2) := by
  rw [pm_eq, pm_eq, pm_eq, pairMixN, flagMix, flagMix, marg_lin]
  have e1 := marg_embed (pq D (fun i => Fin (d1 i + d2 i))) (pq D (fun i => Fin (d1 i)))
    (regMap (gLN d1 d2)) (regMap fun i => Fin.castAdd (d2 i)) id (regMap_inj gLN_inj)
    (regMap_inj fun i => Fin.castAdd_injective _ _) Function.injective_id (fun x => rfl) ω1
  have e2 := marg_embed (pq D (fun i => Fin (d1 i + d2 i))) (pq D (fun i => Fin (d2 i)))
    (regMap (gRN d1 d2)) (regMap fun i => Fin.natAdd (d1 i)) id (regMap_inj gRN_inj)
    (regMap_inj fun i => Fin.natAdd_injective _ _) Function.injective_id (fun x => rfl) ω2
  rw [e1, e2]

theorem pairMixN_pd [NeZero n] (hd1 : ∀ i, 0 < d1 i) (hd2 : ∀ i, 0 < d2 i) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (h1 : ω1.PosSemidef) (ht1 : trace ω1 = 1) (h2 : ω2.PosSemidef) (ht2 : trace ω2 = 1) :
    pairedDifference (pairMixN l ω1 ω2) = l * pairedDifference ω1 + (1 - l) * pairedDifference ω2 := by
  have : ∀ i, Nonempty (Fin (d1 i)) := fun i => ⟨⟨0, hd1 i⟩⟩
  have : ∀ i, Nonempty (Fin (d2 i)) := fun i => ⟨⟨0, hd2 i⟩⟩
  have : ∀ i, Nonempty (Fin (d1 i + d2 i)) := fun i => ⟨⟨0, by have := hd1 i; omega⟩⟩
  have hp1 : (primedMarginal ω1).PosSemidef := by rw [pm_eq]; exact marg_psd _ h1
  have hp2 : (primedMarginal ω2).PosSemidef := by rw [pm_eq]; exact marg_psd _ h2
  have hq1 : trace (primedMarginal ω1) = 1 := by rw [pm_eq, marg_trace, ht1]
  have hq2 : trace (primedMarginal ω2) = 1 := by rw [pm_eq, marg_trace, ht2]
  have hm := flagMix_psd (f1 := gLN d1 d2) (f2 := gRN d1 d2) hl0 hl1 h1 h2
  have hmt := flagMix_trace (f1 := gLN d1 d2) (f2 := gRN d1 d2) (l := l) gLN_inj gRN_inj ht1 ht2
  have hpm : (primedMarginal (pairMixN l ω1 ω2)).PosSemidef := by rw [pm_eq]; exact marg_psd _ hm
  have hpt : trace (primedMarginal (pairMixN l ω1 ω2)) = 1 := by rw [pm_eq, marg_trace]; exact hmt
  have E := fun s hs => flagMix_ent (f1 := gLN d1 d2) (f2 := gRN d1 d2) gLN_inj gRN_inj gLRN_ne hl0 hl1
    h1 ht1 h2 ht2 s hs
  have P := fun s hs => flagMix_ent (D := fun i => Fin (d1 i + d2 i))
    (f1 := fun i => Fin.castAdd (d2 i)) (f2 := fun i => Fin.natAdd (d1 i))
    (fun i => Fin.castAdd_injective _ _) (fun i => Fin.natAdd_injective _ _) cast_ne_natN hl0 hl1
    hp1 hq1 hp2 hq2 s hs
  unfold pairedDifference
  rw [info_n, info_n, info_n, info_n, info_n, info_n, pairMixN_pm]
  rw [ent_empty _ h1 ht1, ent_empty _ h2 ht2, ent_empty _ hp1 hq1, ent_empty _ hp2 hq2]
  rw [← pairMixN_pm, ent_empty _ hpm hpt, pairMixN_pm]
  have hm' : (pairMixN l ω1 ω2).PosSemidef := hm
  have hmt' : trace (pairMixN l ω1 ω2) = 1 := hmt
  rw [ent_empty _ hm' hmt']
  unfold pairMixN
  rw [Finset.sum_congr rfl fun i _ => E {i} (by simp), E Finset.univ Finset.univ_nonempty,
    Finset.sum_congr rfl fun i _ => P {i} (by simp), P Finset.univ Finset.univ_nonempty]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

end pairedN
end X6CE


/-! X6 CEMI library, part 29: convexity of CEMI over finite mixtures, average monotonicity under
local instruments, and monotonicity under finite adaptive LOCC (n ≥ 1 parties). -/

open scoped Matrix ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CE
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
  QAlgorithms.Papers.Independent.Gap20.P10 X6SSA Real

lemma inf_auxN {S : Set ℝ} (hS : S.Nonempty) {a t b : ℝ} (ht : 0 ≤ t)
    (h : ∀ v ∈ S, a ≤ t * v + b) : a ≤ t * sInf S + b := by
  rcases ht.eq_or_lt with rfl | ht
  · obtain ⟨v, hv⟩ := hS
    simpa using h v hv
  · have : (a - b) / t ≤ sInf S := le_csInf hS fun v hv => by
      rw [div_le_iff₀ ht]; linarith [h v hv]
    rw [div_le_iff₀ ht] at this
    linarith

section conv
variable {n : ℕ} [NeZero n] {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
  [∀ i, Nonempty (D i)]

theorem convexN (ρ σ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    cemi ((l : ℂ) • ρ + ((1 - l : ℝ) : ℂ) • σ) ≤ l * cemi ρ + (1 - l) * cemi σ := by
  have hmem : ∀ v1 ∈ cemiValues ρ, ∀ v2 ∈ cemiValues σ,
      l * v1 + (1 - l) * v2 ∈ cemiValues ((l : ℂ) • ρ + ((1 - l : ℝ) : ℂ) • σ) := by
    rintro v1 ⟨d1, hd1, ω1, hω1, hu1, rfl⟩ v2 ⟨d2, hd2, ω2, hω2, hu2, rfl⟩
    refine ⟨fun i => d1 i + d2 i, fun i => by show 0 < d1 i + d2 i; have := hd1 i; omega,
      pairMixN l ω1 ω2,
      ⟨flagMix_psd hl0 hl1 hω1.1 hω2.1, flagMix_trace gLN_inj gRN_inj hω1.2 hω2.2⟩, ?_, ?_⟩
    · rw [pairMixN_um, hu1, hu2]
    · rw [pairMixN_pd l ω1 ω2 hd1 hd2 hl0 hl1 hω1.1 hω1.2 hω2.1 hω2.2]
      ring
  have hc : ∀ v1 ∈ cemiValues ρ, ∀ v2 ∈ cemiValues σ,
      cemi ((l : ℂ) • ρ + ((1 - l : ℝ) : ℂ) • σ) ≤ l * v1 + (1 - l) * v2 :=
    fun v1 h1 v2 h2 => csInf_le ⟨0, vals_nonneg_n _⟩ (hmem v1 h1 v2 h2)
  have h2 : ∀ v2 ∈ cemiValues σ,
      cemi ((l : ℂ) • ρ + ((1 - l : ℝ) : ℂ) • σ) ≤ l * cemi ρ + (1 - l) * v2 :=
    fun v2 hv2 => inf_auxN (vals_ne_n ρ hρ) hl0 fun v1 hv1 => hc v1 hv1 v2 hv2
  have := inf_auxN (vals_ne_n σ hσ) (b := l * cemi ρ)
    (by linarith : 0 ≤ 1 - l) fun v2 hv2 => (h2 v2 hv2).trans (le_of_eq (by ring))
  have hs : cemi σ = sInf (cemiValues σ) := rfl
  rw [hs]
  linarith

theorem convexK : ∀ (k : ℕ) (p : Fin k → ℝ) (τ : Fin k → Matrix (RegisterBasis D) (RegisterBasis D) ℂ),
    (∀ j, 0 ≤ p j) → ∑ j, p j = 1 → (∀ j, IsDensityMatrix (τ j)) →
      cemi (∑ j, ((p j : ℝ) : ℂ) • τ j) ≤ ∑ j, p j * cemi (τ j) := by
  intro k
  induction k with
  | zero => intro p τ _ hs _; simp at hs
  | succ k ih =>
    intro p τ hp hs hτ
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ] at hs
    set q := ∑ j : Fin k, p j.succ with hq
    have hq0 : 0 ≤ q := Finset.sum_nonneg fun j _ => hp _
    by_cases hqz : q = 0
    · have hz : ∀ j : Fin k, p j.succ = 0 := fun j =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp j.succ)).1 hqz j (Finset.mem_univ _)
      have h0 : p 0 = 1 := by linarith
      simp only [hz, h0, Complex.ofReal_zero, Complex.ofReal_one, zero_smul, Finset.sum_const_zero,
        add_zero, one_smul, zero_mul, one_mul, le_refl]
    · have hqp : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
      set ρ' := ∑ j : Fin k, (((p j.succ / q : ℝ)) : ℂ) • τ j.succ
      have hρ' : IsDensityMatrix ρ' := by
        refine ⟨Matrix.posSemidef_sum _ fun j _ => X6CH.psd_smul (hτ _).1 (div_nonneg (hp _) hq0), ?_⟩
        simp only [ρ', trace_sum, trace_smul, (hτ _).2, smul_eq_mul, mul_one]
        rw [← Complex.ofReal_sum, ← Finset.sum_div, ← hq, div_self hqz, Complex.ofReal_one]
      have e1 : ∑ j : Fin k, ((p j.succ : ℝ) : ℂ) • τ j.succ = ((1 - p 0 : ℝ) : ℂ) • ρ' := by
        have : 1 - p 0 = q := by linarith
        rw [this, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, ← Complex.ofReal_mul, mul_div_cancel₀ _ hqz]
      rw [e1]
      have hc := convexN (τ 0) ρ' (hτ 0) hρ' (p 0) (hp 0) (by linarith)
      have hi := ih (fun j => p j.succ / q) (fun j => τ j.succ) (fun j => div_nonneg (hp _) hq0)
        (by rw [← Finset.sum_div, ← hq, div_self hqz]) (fun j => hτ _)
      have e2 : (1 - p 0) * ∑ j : Fin k, p j.succ / q * cemi (τ j.succ) =
          ∑ j : Fin k, p j.succ * cemi (τ j.succ) := by
        have : 1 - p 0 = q := by linarith
        rw [this, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp
      have h1p : 0 ≤ 1 - p 0 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hi h1p]

end conv

/-- transport a bundled state along an equality of dimension vectors. -/
lemma transp {n : ℕ} (t : FiniteState n) {dm : Fin n → ℕ} (h : t.dims = dm) :
    ∃ τ : Matrix (RegisterBasis (fun i => Fin (dm i))) (RegisterBasis (fun i => Fin (dm i))) ℂ,
      IsDensityMatrix τ ∧ cemi τ = cemiFunctional t ∧
      ∀ x y, τ x y = stateEntry t (fun i => (x i).val) (fun i => (y i).val) := by
  obtain ⟨dims, pos, rho, nm⟩ := t
  subst h
  refine ⟨rho, nm, rfl, fun x y => ?_⟩
  simp [stateEntry]

lemma stateEntry_val {n : ℕ} (s : FiniteState n) (x y : RegisterBasis (fun i => Fin (s.dims i))) :
    stateEntry s (fun i => (x i).val) (fun i => (y i).val) = s.rho x y := by
  simp [stateEntry]

theorem convexF {n : ℕ} [NeZero n] : IsConvexFunctional (cemiFunctional (n := n)) := by
  intro k s p r ⟨hp, hs, hdims, hent⟩
  have : ∀ i, Nonempty (Fin (s.dims i)) := fun i => ⟨⟨0, s.positive i⟩⟩
  choose τ hτd hτc hτe using fun j => transp (r j) (hdims j)
  have hmix : s.rho = ∑ j, ((p j : ℝ) : ℂ) • τ j := by
    ext x y
    rw [← stateEntry_val s x y, hent]
    simp [Matrix.sum_apply, hτe]
  unfold cemiFunctional
  rw [hmix]
  calc cemi (∑ j, ((p j : ℝ) : ℂ) • τ j) ≤ ∑ j, p j * cemi (τ j) := convexK k p τ hp hs hτd
    _ = ∑ j, p j * cemiFunctional (r j) := by simp only [hτc]

theorem almF {n : ℕ} : IsAverageLocalMonotone (cemiFunctional (n := n)) := by
  intro s k p r hI
  have hp := hI.1
  have : ∀ i, Nonempty (Fin (s.dims i)) := fun i => ⟨⟨0, s.positive i⟩⟩
  unfold cemiFunctional cemi
  apply le_csInf (vals_ne_n s.rho s.normalized)
  rintro v ⟨d, hd, ω, hω, hu, rfl⟩
  obtain ⟨ω', hω', hu', hle⟩ := KI s p r hI d hd ω hω hu
  have hj : ∀ j, p j * sInf (cemiValues (r j).rho) ≤ p j * (pairedDifference (ω' j) / 2) := by
    intro j
    have : ∀ i, Nonempty (Fin ((r j).dims i)) := fun i => ⟨⟨0, (r j).positive i⟩⟩
    rcases (hp j).eq_or_lt with h | h
    · rw [← h]; simp
    · exact mul_le_mul_of_nonneg_left
        (csInf_le ⟨0, vals_nonneg_n _⟩ ⟨d, hd, ω' j, hω' j, hu' j h, rfl⟩) (hp j)
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hj j
  have e : ∑ j, p j * (pairedDifference (ω' j) / 2) = (∑ j, p j * pairedDifference (ω' j)) / 2 := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun j _ => by ring
  linarith

theorem locc_aux {n : ℕ} [NeZero n] {s : FiniteState n} {out : List (ℝ × FiniteState n)}
    (h : LOCC s out) :
    (out.map fun w => w.1 * cemiFunctional w.2).sum ≤ cemiFunctional s ∧
      (∀ w ∈ out, 0 ≤ w.1) ∧ (out.map Prod.fst).sum = 1 := by
  induction h with
  | stop s => simp
  | step s k p r hI next hn ih =>
    have hp := hI.1
    have hs := hI.2.1
    refine ⟨?_, ?_, ?_⟩
    · rw [List.map_flatMap]
      simp only [List.flatMap_def, List.sum_flatten, List.map_map]
      rw [← Fin.sum_univ_def]
      simp only [Function.comp_def, List.map_map]
      have e : ∀ j, ((next j).map fun w => p j * w.1 * cemiFunctional w.2).sum =
          p j * ((next j).map fun w => w.1 * cemiFunctional w.2).sum := by
        intro j
        rw [← List.sum_map_mul_left]
        congr 1; apply List.map_congr_left; intro w _; ring
      simp only [e]
      calc ∑ j, p j * ((next j).map fun w => w.1 * cemiFunctional w.2).sum ≤
          ∑ j, p j * cemiFunctional (r j) :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j).1 (hp j)
        _ ≤ cemiFunctional s := almF s k p r hI
    · intro w hw
      simp only [List.mem_flatMap, List.mem_map] at hw
      obtain ⟨j, -, w', hw', rfl⟩ := hw
      exact mul_nonneg (hp j) ((ih j).2.1 w' hw')
    · rw [List.map_flatMap]
      simp only [List.flatMap_def, List.sum_flatten, List.map_map]
      rw [← Fin.sum_univ_def]
      simp only [Function.comp_def, List.map_map]
      have e : ∀ j, ((next j).map fun w => p j * w.1).sum = p j := by
        intro j
        rw [List.sum_map_mul_left,
          show (next j).map (fun w => w.1) = (next j).map Prod.fst from rfl, (ih j).2.2, mul_one]
      simp only [e, hs]
  | forget s t out h hd hmix ih =>
    refine ⟨?_, by simp, by simp⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    have hmx : IsMixture t (fun i : Fin out.length => out[i.1].1) (fun i => out[i.1].2) := by
      refine ⟨fun i => ih.2.1 _ (List.getElem_mem _), ?_, fun i => hd _ (List.getElem_mem _), ?_⟩
      · rw [Fin.sum_univ_fun_getElem out Prod.fst]; exact ih.2.2
      · intro x y
        rw [hmix x y, ← Fin.sum_univ_fun_getElem out (fun w => (w.1 : ℂ) * stateEntry w.2 x y)]
    have hc := convexF out.length t _ _ hmx
    calc cemiFunctional t ≤ ∑ i : Fin out.length, out[i.1].1 * cemiFunctional out[i.1].2 := hc
      _ = (out.map fun w => w.1 * cemiFunctional w.2).sum :=
          Fin.sum_univ_fun_getElem out (fun w => w.1 * cemiFunctional w.2)
      _ ≤ cemiFunctional s := ih.1

end X6CE


open QAlgorithms.Papers.Independent.Claimed50.P33 QAlgorithms.Papers.Independent.Gap20.P10 in
theorem solution :
    (∀ s t : FiniteState 2, LOCC s [(1, t)] →
      cemiFunctional t ≤ cemiFunctional s) ∧
    IsAdaptiveLOCCMonotone (cemiFunctional (n := 2)) := by
  have hm : IsAdaptiveLOCCMonotone (cemiFunctional (n := 2)) := fun s out h => (X6CE.locc_aux h).1
  exact ⟨fun s t h => by simpa using hm s _ h, hm⟩
