-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P43.projectionDenseCoding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:41:00.619858+00:00
-- url     : https://prove2.me/submissions/cb4d38f4-cb5a-4ef8-8c80-c8365677da95

import Theorems.Thm_TroppMatrixConcentration_ch8_entropy_joint_convex
import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43
import Definitions.Def_QAlgorithms_Defs_Measurement
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_denseCodingIdentities


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


/-! X6 channel library, part 7: convexity of the input mutual information under mixing of
channels and concavity in the input. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)
open QAlgorithms.Papers.Independent.Information100.P27 (average)
open QAlgorithms.Papers.Independent.Gap48.P33

variable {A B J : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype J] [DecidableEq J]

lemma trF_sum {P Q : Type*} [Fintype P] [Fintype Q] (c : J → ℂ) (ω : J → Matrix (P × Q) (P × Q) ℂ) :
    trF (∑ j, c j • ω j) = ∑ j, c j • trF (ω j) := by
  ext a b
  simp only [trF, of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma kraus_lin {K : Type*} [Fintype K] (E : K → Matrix B A ℂ) (c : J → ℂ)
    (σ : J → Matrix A A ℂ) : krausApply E (∑ j, c j • σ j) = ∑ j, c j • krausApply E (σ j) := by
  rw [kraus_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ∑ k, E k * (c j • σ j) * (E k)ᴴ = c j • ∑ k, E k * σ j * (E k)ᴴ
  simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- the output-reference state of a Kraus channel: its `B` marginal and density. -/
lemma out_facts [Nonempty A] [Nonempty B] {m : ℕ} [NeZero m] (E : Fin m → Matrix B A ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = 1) (s : Matrix A A ℂ) (hs : trace (s * sᴴ) = 1) :
    trF (idTensorSuperop (krausApply E) (pureDensity (vecOf s))) = krausApply E (s * sᴴ) ∧
    IsDensityMatrix (idTensorSuperop (krausApply E) (pureDensity (vecOf s))) := by
  have h := m_RC s E (F0 (B := B))
  rw [idT_F0] at h
  have hP : (pureDensity (lam s E (F0 (B := B)))).PosSemidef := pd_psd _
  have hPt := tr_one s E F0 hE F0_kraus hs
  refine ⟨?_, ?_, ?_⟩
  · rw [← h, ← kraus_F0 (krausApply E (s * sᴴ)), ← m_C]
    ext i j
    simp only [trF, marg, trR, reindex_apply, submatrix_apply, of_apply, sRC, sC,
      Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
  · rw [← h]; exact marg_psd _ hP
  · rw [← h, marg_trace, hPt]

lemma idT_mixed {R : Type*} (w : J → ℝ) (N : J → Superop A B) (X : Matrix (R × A) (R × A) ℂ) :
    idTensorSuperop (mixedChannel w N) X = ∑ j, (w j : ℂ) • idTensorSuperop (N j) X := by
  ext p q
  simp [idTensorSuperop, mixedChannel, average, Matrix.sum_apply]

theorem mixing [Nonempty A] [Nonempty B]
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho)
    (w : J → ℝ) (hw : ProbabilityWeights w)
    (N : J → Superop A B) (hN : ∀ j, IsChannel (N j)) :
    inputMutualInfo (mixedChannel w N) rho ≤ ∑ j, w j * inputMutualInfo (N j) rho := by
  choose m E hm hE hNE using fun j => kraus_of_channel (hN j)
  set s := cfc Real.sqrt rho
  have hs : s * sᴴ = rho := sqrt_sq hrho.1
  have hΨ : trace (s * sᴴ) = 1 := by rw [hs, hrho.2]
  let ω : J → Matrix (A × B) (A × B) ℂ := fun j => idTensorSuperop (N j) (pureDensity (vecOf s))
  have hfacts : ∀ j, trF (ω j) = N j rho ∧ IsDensityMatrix (ω j) := by
    intro j
    haveI : NeZero (m j) := ⟨(hm j).ne'⟩
    have := out_facts (E j) (hE j) s hΨ
    simp only [ω, hNE j]
    rw [← hs]
    exact this
  have hEE : ∀ j, entropyExchange (N j) rho = vnEntropy (ω j) := fun j =>
    ee_eq _ hrho.1.isHermitian
  have hEEm : entropyExchange (mixedChannel w N) rho = vnEntropy (∑ j, (w j : ℂ) • ω j) := by
    rw [ee_eq _ hrho.1.isHermitian, idT_mixed]
  have hmix : mixedChannel w N rho = trF (∑ j, (w j : ℂ) • ω j) := by
    rw [trF_sum]
    simp only [mixedChannel, average, fun j => (hfacts j).1]
  have hc := cond_concave w hw.1 hw.2 ω fun j => (hfacts j).2
  unfold inputMutualInfo
  rw [hEEm, hmix]
  simp only [hEE, ← fun j => (hfacts j).1]
  have e : ∑ j, w j * (vnEntropy rho + vnEntropy (trF (ω j)) - vnEntropy (ω j)) =
      vnEntropy rho - ∑ j, w j * (vnEntropy (ω j) - vnEntropy (trF (ω j))) := by
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      hw.2, one_mul]
    ring
  rw [e]
  linarith

lemma stV_conj_apply {K : Type*} [Fintype K] (E : K → Matrix B A ℂ) (σ : Matrix A A ℂ)
    (p q : B × K) :
    (stV E * σ * (stV E)ᴴ) p q = (E p.2 * σ * (E q.2)ᴴ) p.1 q.1 := by
  simp [stV, mul_apply, conjTranspose_apply]

lemma trF_stV {K : Type*} [Fintype K] [DecidableEq K] (E : K → Matrix B A ℂ) (σ : Matrix A A ℂ) :
    trF (stV E * σ * (stV E)ᴴ) = comp E σ := by
  ext k k'
  simp only [trF, of_apply, stV_conj_apply, comp, trace, diag_apply]

theorem concavity [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (w : J → ℝ) (hw : ProbabilityWeights w)
    (rho : J → Matrix A A ℂ) (hrho : ∀ j, IsDensityMatrix (rho j)) :
    (∑ j, w j * inputMutualInfo N (rho j)) ≤ inputMutualInfo N (average w rho) := by
  obtain ⟨m, E, hm, hE, rfl⟩ := kraus_of_channel hN
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set V := stV E
  have hV : Vᴴ * V = 1 := stV_iso E hE
  -- input mutual information of a density in terms of the Stinespring image
  have key : ∀ σ : Matrix A A ℂ, IsDensityMatrix σ →
      inputMutualInfo (krausApply E) σ =
        vnEntropy (krausApply E σ) + (vnEntropy (V * σ * Vᴴ) - vnEntropy (trF (V * σ * Vᴴ))) := by
    intro σ hσ
    unfold inputMutualInfo
    rw [ee_eq _ hσ.1.isHermitian, sc, sqrt_sq hσ.1, vn_iso _ hV _ hσ.1, trF_stV]
    ring
  have dens : ∀ σ : Matrix A A ℂ, IsDensityMatrix σ → IsDensityMatrix (V * σ * Vᴴ) := by
    intro σ hσ
    refine ⟨hσ.1.mul_mul_conjTranspose_same V, ?_⟩
    rw [trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, hσ.2]
  have densN : ∀ σ : Matrix A A ℂ, IsDensityMatrix σ → IsDensityMatrix (krausApply E σ) :=
    fun σ hσ => ⟨kraus_psd E hσ.1, by rw [kraus_trace E hE, hσ.2]⟩
  have hav : IsDensityMatrix (average w rho) := by
    refine ⟨Matrix.posSemidef_sum _ fun j _ => psd_smul (hrho j).1 (hw.1 j), ?_⟩
    simp only [average, trace_sum, trace_smul, (hrho _).2, smul_eq_mul, mul_one]
    exact_mod_cast hw.2
  have hlinV : V * average w rho * Vᴴ = ∑ j, (w j : ℂ) • (V * rho j * Vᴴ) := by
    simp only [average, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hlinN : krausApply E (average w rho) = ∑ j, (w j : ℂ) • krausApply E (rho j) :=
    kraus_lin E _ _
  have h1 := cond_concave w hw.1 hw.2 (fun j => V * rho j * Vᴴ) fun j => dens _ (hrho j)
  have h2 := ent_concave w hw.1 hw.2 (fun j => krausApply E (rho j)) fun j => densN _ (hrho j)
  rw [key _ hav, hlinV, hlinN]
  simp only [fun j => key _ (hrho j), mul_add, Finset.sum_add_distrib]
  linarith

end X6CH


/-! X6 channel library, part 8: classical-quantum states and the measured-input Holevo balance. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms Real
open QAlgorithms.Papers.Independent.Information100.P27 (shannon average labelInformation)
open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)
open QAlgorithms.Papers.Independent.Gap48.P33

variable {A B K J : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]

lemma vn_any {ι : Type*} [Fintype ι] (d d' : DecidableEq ι) (M : Matrix ι ι ℂ) :
    @vnEntropy ι _ d M = @vnEntropy ι _ d' M := by
  cases Subsingleton.elim d d'; rfl

lemma shannon_eq (w : J → ℝ) : shannon w = ∑ j, negMulLog (w j) / log 2 := by
  unfold shannon
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Real.logb, negMulLog]; ring

lemma cq_eq {H : Type} [Fintype H] [DecidableEq H] (w : J → ℝ) (ρ : J → Matrix H H ℂ) :
    cqState w ρ = reindex (Equiv.prodComm H J) (Equiv.prodComm H J)
      (blockDiagonal fun j => (w j : ℂ) • ρ j) := by
  ext p q
  simp [cqState, blockDiagonal_apply, reindex_apply, eq_comm]

lemma cq_ent {H : Type} [Fintype H] [DecidableEq H] (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (ρ : J → Matrix H H ℂ) (hρ : ∀ j, IsDensityMatrix (ρ j)) :
    vnEntropy (cqState w ρ) = shannon w + ∑ j, w j * vnEntropy (ρ j) := by
  rw [cq_eq, vn_reind _ _ (blk_psd _ fun j => psd_smul (hρ j).1 (hw j)).1,
    blk_ent w hw ρ (fun j => (hρ j).1) fun j => (hρ j).2, shannon_eq]

lemma diag_ent (w : J → ℝ) : vnEntropy (diagonal fun j => (w j : ℂ)) = shannon w := by
  rw [vn_diag', shannon_eq]

lemma sqrt_mul_self' {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x : ℂ) * (Real.sqrt x : ℂ) = x := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]

/-- an orthonormal mixture has the Shannon entropy of its weights. -/
lemma ortho_ent (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (ψ : J → EuclideanSpace ℂ A)
    (hψ : Orthonormal ℂ ψ) : vnEntropy (average w fun j => pureDensity (ψ j)) = shannon w := by
  let M : Matrix A J ℂ := of fun a j => (Real.sqrt (w j) : ℂ) * ψ j a
  have h1 : average w (fun j => pureDensity (ψ j)) = M * Mᴴ := by
    ext a b
    simp only [average, Matrix.sum_apply, Matrix.smul_apply, pureDensity, of_apply, smul_eq_mul,
      mul_apply, conjTranspose_apply, M, star_mul', Complex.star_def, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := sqrt_mul_self' (hw j)
    linear_combination (ψ j a * (starRingEnd ℂ) (ψ j b)) * this.symm
  have h2 : Mᴴ * M = diagonal fun j => (w j : ℂ) := by
    ext i j
    have hin := orthonormal_iff_ite.mp hψ i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hin
    simp only [mul_apply, conjTranspose_apply, M, of_apply, star_mul', Complex.star_def,
      Complex.conj_ofReal, diagonal_apply]
    have : ∑ a, (Real.sqrt (w i) : ℂ) * (starRingEnd ℂ) (ψ i a) * ((Real.sqrt (w j) : ℂ) * ψ j a) =
        (Real.sqrt (w i) : ℂ) * (Real.sqrt (w j) : ℂ) * dotProduct (star (ψ i : A → ℂ)) (ψ j : A → ℂ) := by
      simp only [dotProduct, Finset.mul_sum, Pi.star_apply, Complex.star_def]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [this]
    have hin' : dotProduct (star (ψ i : A → ℂ)) (ψ j : A → ℂ) = if i = j then 1 else 0 := by
      rw [dotProduct_comm]; exact hin
    rw [hin']
    by_cases hij : i = j
    · subst hij; simp [sqrt_mul_self' (hw i)]
    · simp [hij]
  rw [h1, vn_mul_conj, h2, diag_ent]

lemma dil_pd (E : K → Matrix B A ℂ) (ψ : EuclideanSpace ℂ A) :
    pureDensity (dilationVector E ψ) = stV E * pureDensity ψ * (stV E)ᴴ := by
  ext p q
  simp only [pureDensity, dilationVector, stV, of_apply, mul_apply, conjTranspose_apply,
    PiLp.toLp_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, Complex.star_def]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  ring

lemma dil_out (E : K → Matrix B A ℂ) (ψ : EuclideanSpace ℂ A) :
    trR (pureDensity (dilationVector E ψ)) = krausApply E (pureDensity ψ) := by
  have : pureDensity ψ = vecMulVec (ψ : A → ℂ) (star (ψ : A → ℂ)) := by
    ext a b; simp [pureDensity, vecMulVec_apply]
  rw [this, kraus_rank1]
  ext b b'
  simp [trR, pureDensity, dilationVector, Matrix.sum_apply, vecMulVec_apply, mulVec, dotProduct]

theorem measured [Nonempty A] [Nonempty B] [Nonempty K]
    (E : K → Matrix B A ℂ) (hE : IsKrausFamily E)
    (w : J → ℝ) (hw : ProbabilityWeights w)
    (psi : J → EuclideanSpace ℂ A) (hpsi : Orthonormal ℂ psi) :
    let output := fun j => krausApply E (pureDensity (psi j))
    let joint := cqState w (fun j => pureDensity (dilationVector E (psi j)))
    QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation (cqState w output) =
      labelInformation w output ∧
    vnEntropy (average w (fun j => pureDensity (psi j))) = shannon w ∧
    shannon w = labelInformation w output + middleConditionalInformation joint ∧
    classicalLoss w output = middleConditionalInformation joint := by
  intro output joint
  have hE' : ∑ k, (E k)ᴴ * E k = 1 := hE
  have hV := stV_iso E hE'
  have hpd : ∀ j, IsDensityMatrix (pureDensity (psi j)) := fun j =>
    ⟨pd_psd _, pd_trace _ (hpsi.1 j)⟩
  have hout : ∀ j, IsDensityMatrix (output j) := fun j =>
    ⟨kraus_psd E (hpd j).1, by simp only [output]; rw [kraus_trace E hE', (hpd j).2]⟩
  have hdil : ∀ j, IsDensityMatrix (pureDensity (dilationVector E (psi j))) := fun j => by
    rw [dil_pd]
    exact ⟨(hpd j).1.mul_mul_conjTranspose_same _, by
      rw [trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, (hpd j).2]⟩
  have hS0 : ∀ j, vnEntropy (pureDensity (dilationVector E (psi j))) = 0 := fun j =>
    vn_pd_zero _ (hdil j).2
  have hcq := cq_ent w hw.1 output hout
  have hjoint : vnEntropy joint = shannon w := by
    simp only [joint]; rw [cq_ent w hw.1 _ hdil]; simp [hS0]
  have hortho := ortho_ent w hw.1 psi hpsi
  have havg_out : average w output = traceLeft (cqState w output) := by
    ext b b'
    simp [average, traceLeft, cqState, Matrix.sum_apply]
  have hJ : traceRight (cqState w output) = diagonal fun j => (w j : ℂ) := by
    ext i j
    simp only [traceRight, cqState, of_apply, diagonal_apply]
    by_cases h : i = j
    · subst h
      simp only [if_true]
      rw [← Finset.mul_sum]
      have : ∑ x, output i x x = trace (output i) := rfl
      rw [this, (hout i).2, mul_one]
    · simp [h]
  -- the four marginals of the reordered joint state
  have hMCI : middleConditionalInformation joint =
      (shannon w + ∑ j, w j * vnEntropy (output j)) + shannon w -
        vnEntropy (average w output) - shannon w := by
    show vnEntropy (fun i j : J × B => ∑ k : K, joint (i.1, (i.2, k)) (j.1, (j.2, k))) +
      vnEntropy (fun i j : K × B => ∑ a : J, joint (a, (i.2, i.1)) (a, (j.2, j.1))) -
      vnEntropy (traceLeft (fun x y : (J × K) × B => joint (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2)))) -
      vnEntropy (fun x y : (J × K) × B => joint (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2))) = _
    have e1 : (fun i j : J × B => ∑ k : K, joint (i.1, (i.2, k)) (j.1, (j.2, k))) = cqState w output := by
      ext p q
      simp only [joint, output, cqState, ← dil_out]
      split_ifs with h
      · simp [trR, Finset.mul_sum]
      · simp
    have e2 : (fun i j : K × B => ∑ a : J, joint (a, (i.2, i.1)) (a, (j.2, j.1))) =
        reindex (Equiv.prodComm B K) (Equiv.prodComm B K)
          (stV E * average w (fun j => pureDensity (psi j)) * (stV E)ᴴ) := by
      ext p q
      simp only [joint, cqState, if_true, reindex_apply, submatrix_apply, Equiv.prodComm_symm,
        Equiv.prodComm_apply, Prod.swap_prod_mk, average, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, dil_pd]
      rfl
    have e3 : traceLeft (fun x y : (J × K) × B => joint (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2))) =
        average w output := by
      rw [havg_out]
      ext b b'
      simp only [traceLeft, joint, output, cqState, of_apply, Fintype.sum_prod_type, ← dil_out]
      simp [trR, Finset.mul_sum]
    have e4 : vnEntropy (fun x y : (J × K) × B => joint (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2))) =
        vnEntropy joint := by
      have := vn_reind (show J × (B × K) ≃ (J × K) × B from
        { toFun := fun x => ((x.1, x.2.2), x.2.1), invFun := fun y => (y.1.1, (y.2, y.1.2)),
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }) joint
        (by simp only [joint]; rw [cq_eq]; rw [reindex_apply]
            exact ((blk_psd _ fun j => psd_smul (hdil j).1 (hw.1 j)).submatrix _).1)
      exact this
    have hav : (average w fun j => pureDensity (psi j)).PosSemidef :=
      Matrix.posSemidef_sum _ fun j _ => psd_smul (hpd j).1 (hw.1 j)
    rw [e1, e2, e3, e4, hjoint, hcq, vn_reind _ _ (hav.mul_mul_conjTranspose_same _).1,
      vn_iso _ hV _ hav, hortho]
  refine ⟨?_, hortho, ?_, ?_⟩
  · unfold QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation labelInformation
    rw [vn_any (Classical.decEq B) inferInstance (average w output)]
    have hsum : ∀ j, @vnEntropy B _ (Classical.decEq B) (output j) = vnEntropy (output j) :=
      fun j => vn_any (Classical.decEq B) inferInstance (output j)
    simp only [hsum]
    rw [hJ, diag_ent, ← havg_out, hcq]; ring
  · rw [hMCI]; unfold labelInformation
    rw [vn_any (Classical.decEq B) inferInstance (average w output)]
    have hsum : ∀ j, @vnEntropy B _ (Classical.decEq B) (output j) = vnEntropy (output j) :=
      fun j => vn_any (Classical.decEq B) inferInstance (output j)
    simp only [hsum]
    ring
  · rw [hMCI]; unfold classicalLoss; rw [hcq]; ring

end X6CH


/-! X6 channel library, part 9: covariance invariance of the input mutual information and the
Pauli twirl bound for qubit channels. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms Real
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)
open QAlgorithms.Papers.Independent.Information100.P27 (average)
open QAlgorithms.Papers.Independent.Gap48.P33

variable {A K : Type} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]

lemma comp_psd (E : K → Matrix A A ℂ) {σ : Matrix A A ℂ} (hσ : σ.PosSemidef) :
    (comp E σ).PosSemidef := by
  rw [← trF_stV]; exact trF_psd (hσ.mul_mul_conjTranspose_same _)

/-- input mutual information is invariant under a covariance unitary. -/
theorem cov_inv [Nonempty A] [Nonempty K] (E : K → Matrix A A ℂ) (U : Matrix A A ℂ)
    (hU1 : Uᴴ * U = 1) (s : K → ℂ) (hs : ∀ k, s k * star (s k) = 1)
    (hc : ∀ k, E k * U = s k • (U * E k)) (σ : Matrix A A ℂ) (hσ : IsDensityMatrix σ) :
    inputMutualInfo (krausApply E) (U * σ * Uᴴ) = inputMutualInfo (krausApply E) σ := by
  have hd : IsDensityMatrix (U * σ * Uᴴ) := ⟨hσ.1.mul_mul_conjTranspose_same U, by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul, hσ.2]⟩
  have hterm : ∀ k k', E k * (U * σ * Uᴴ) * (E k')ᴴ = (s k * star (s k')) • (U * (E k * σ * (E k')ᴴ) * Uᴴ) := by
    intro k k'
    have h1 : E k * (U * σ * Uᴴ) * (E k')ᴴ = (E k * U) * σ * (E k' * U)ᴴ := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [h1, hc k, hc k']
    simp only [conjTranspose_smul, conjTranspose_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.mul_assoc]
    rw [mul_comm (star (s k')) (s k)]
  have hN : krausApply E (U * σ * Uᴴ) = U * krausApply E σ * Uᴴ := by
    show ∑ k, E k * (U * σ * Uᴴ) * (E k)ᴴ = U * (∑ k, E k * σ * (E k)ᴴ) * Uᴴ
    simp only [hterm, hs, one_smul, Matrix.mul_sum, Matrix.sum_mul]
  have hC : comp E (U * σ * Uᴴ) = diagonal s * comp E σ * (diagonal s)ᴴ := by
    ext k k'
    simp only [comp, of_apply, hterm, trace_smul, smul_eq_mul, diagonal_conjTranspose, mul_diagonal,
      diagonal_mul]
    rw [trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
    simp [Pi.star_apply]; ring
  have hD : (diagonal s)ᴴ * diagonal s = 1 := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp only [diagonal_apply_eq, Pi.mul_apply, Pi.star_apply, one_apply_eq]
      rw [mul_comm]; exact hs i
    · simp [h, one_apply]
  unfold inputMutualInfo
  rw [ee_eq _ hd.1.isHermitian, sc, sqrt_sq hd.1, ee_eq _ hσ.1.isHermitian, sc, sqrt_sq hσ.1,
    vn_iso U hU1 σ hσ.1, hN, vn_iso U hU1 _ (kraus_psd E hσ.1), hC,
    vn_iso _ hD _ (comp_psd E hσ.1)]

/-- the four Paulis. -/
def pauli : Fin 4 → Matrix Bool Bool ℂ := ![1, pauliX, pauliY, pauliZ]

lemma pauli_unitary (j : Fin 4) : (pauli j)ᴴ * pauli j = 1 := by
  fin_cases j <;> ext a b <;> cases a <;> cases b <;>
    simp [pauli, pauliX, pauliY, pauliZ, mul_apply, Fintype.sum_bool, conjTranspose_apply]

lemma pauli_herm (j : Fin 4) : (pauli j)ᴴ = pauli j := by
  fin_cases j <;> ext a b <;> cases a <;> cases b <;>
    simp [pauli, pauliX, pauliY, pauliZ, conjTranspose_apply]

lemma twirl_avg (ρ : Matrix Bool Bool ℂ) (hρ : trace ρ = 1) :
    average (fun _ : Fin 4 => (1 / 4 : ℝ)) (fun j => pauli j * ρ * (pauli j)ᴴ) =
      diagonalSource (1 / 2) := by
  have ht : ρ false false + ρ true true = 1 := by
    rw [← hρ]; simp [trace, Fintype.sum_bool]; ring
  ext a b
  cases a <;> cases b <;>
    simp [average, pauli, pauliX, pauliY, pauliZ, mul_apply, Fintype.sum_bool, conjTranspose_apply,
      Fin.sum_univ_four, diagonalSource, Matrix.sum_apply, Complex.I_sq]
  all_goals ring_nf
  all_goals (try simp only [Complex.I_sq])
  all_goals first | ring1 | linear_combination (1/2 : ℂ) * ht | linear_combination (-1/2 : ℂ) * ht

/-- for a Pauli-covariant qubit Kraus channel, the maximally mixed input maximises `I`. -/
theorem twirl_max {m : ℕ} (E : Fin m → Matrix Bool Bool ℂ) (hm : 0 < m)
    (hE : ∑ k, (E k)ᴴ * E k = 1)
    (hcov : ∀ j : Fin 4, ∃ s : Fin m → ℂ, (∀ k, s k * star (s k) = 1) ∧
      ∀ k, E k * pauli j = s k • (pauli j * E k))
    (ρ : Matrix Bool Bool ℂ) (hρ : IsDensityMatrix ρ) :
    inputMutualInfo (krausApply E) ρ ≤ inputMutualInfo (krausApply E) (diagonalSource (1 / 2)) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hch : IsChannel (krausApply E) := ⟨m, E, hE, fun _ => rfl⟩
  have hw : ProbabilityWeights (fun _ : Fin 4 => (1 / 4 : ℝ)) := ⟨fun _ => by norm_num, by
    simp [Fin.sum_univ_four]⟩
  have hdens : ∀ j, IsDensityMatrix (pauli j * ρ * (pauli j)ᴴ) := fun j =>
    ⟨hρ.1.mul_mul_conjTranspose_same _, by
      rw [trace_mul_comm, ← Matrix.mul_assoc, pauli_unitary, Matrix.one_mul, hρ.2]⟩
  have h := concavity (krausApply E) hch _ hw (fun j => pauli j * ρ * (pauli j)ᴴ) hdens
  rw [twirl_avg ρ hρ.2] at h
  have hinv : ∀ j, inputMutualInfo (krausApply E) (pauli j * ρ * (pauli j)ᴴ) =
      inputMutualInfo (krausApply E) ρ := by
    intro j
    obtain ⟨s, hs, hc⟩ := hcov j
    exact cov_inv E (pauli j) (pauli_unitary j) s hs hc ρ hρ
  simp only [hinv, Fin.sum_univ_four] at h
  linarith

end X6CH


/-! X6: concavity of `S(ρ) - S_e(N, ρ)` and the entropy exchange of a pure ensemble average. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6EX
open Matrix X6SSA X6CH QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)

lemma trF_stV' {A B K : Type*} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
    (E : K → Matrix B A ℂ) (σ : Matrix A A ℂ) :
    trF (stV E * σ * (stV E)ᴴ) = X6CH.comp E σ := by
  ext k k'
  simp [trF, stV, mul_apply, conjTranspose_apply, X6CH.comp, trace]

/-- `S(σ) - S_e(N, σ)` as a conditional entropy of the Stinespring image. -/
lemma cond_form {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B] {m : ℕ} [NeZero m] (E : Fin m → Matrix B A ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = 1) {σ : Matrix A A ℂ} (hσ : σ.PosSemidef) :
    vnEntropy σ - entropyExchange (krausApply E) σ =
      vnEntropy (stV E * σ * (stV E)ᴴ) - vnEntropy (trF (stV E * σ * (stV E)ᴴ)) := by
  rw [ee_eq _ hσ.isHermitian, sc, sqrt_sq hσ, vn_iso _ (stV_iso E hE) _ hσ, trF_stV']

theorem concave2 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (rho0 rho1 : Matrix A A ℂ)
    (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    vnEntropy ((p : ℂ) • rho0 + ((1 - p : ℝ) : ℂ) • rho1) -
      entropyExchange N ((p : ℂ) • rho0 + ((1 - p : ℝ) : ℂ) • rho1) ≥
      p * (vnEntropy rho0 - entropyExchange N rho0) +
        (1 - p) * (vnEntropy rho1 - entropyExchange N rho1) := by
  obtain ⟨m, E, hm, hE, rfl⟩ := kraus_of_channel hN
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set V := stV E
  have hV := stV_iso E hE
  set w : Fin 2 → ℝ := ![p, 1 - p]
  set ρ : Fin 2 → Matrix A A ℂ := ![rho0, rho1]
  have hρ : ∀ j, IsDensityMatrix (ρ j) := fun j => by fin_cases j <;> simp [ρ, h0, h1]
  have dens : ∀ j, IsDensityMatrix (V * ρ j * Vᴴ) := fun j =>
    ⟨(hρ j).1.mul_mul_conjTranspose_same V, by
      rw [trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, (hρ j).2]⟩
  have hw : ∀ j, 0 ≤ w j := fun j => by fin_cases j <;> simp [w, hp0, hp1]
  have hw1 : ∑ j, w j = 1 := by simp [w, Fin.sum_univ_two]
  have hc := cond_concave w hw hw1 (fun j => V * ρ j * Vᴴ) dens
  have hmix : (p : ℂ) • rho0 + ((1 - p : ℝ) : ℂ) • rho1 = ∑ j, (w j : ℂ) • ρ j := by
    simp only [w, ρ, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  have hmixV : ∑ j, (w j : ℂ) • (V * ρ j * Vᴴ) = V * (∑ j, (w j : ℂ) • ρ j) * Vᴴ := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hmixd : (∑ j, (w j : ℂ) • ρ j).PosSemidef :=
    Matrix.posSemidef_sum _ fun j _ => psd_smul (hρ j).1 (hw j)
  rw [hmixV] at hc
  rw [hmix, ge_iff_le, cond_form E hE hmixd, cond_form E hE h0.1, cond_form E hE h1.1]
  simpa [Fin.sum_univ_two, w, ρ] using hc

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble pureAverage) in
theorem pure_ensemble {d : ℕ} (hd : 0 < d) (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (e : PureEnsemble (Fin d)) :
    ∑ j, e.prob j * vnEntropy (Phi (pureDensity (e.vector j))) ≤
      entropyExchange Phi (pureAverage e) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨m, E, hm, hE, rfl⟩ := kraus_of_channel hPhi
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hpd : ∀ j, IsDensityMatrix (pureDensity (e.vector j)) := fun j =>
    ⟨pd_psd _, pd_trace _ (e.normalized j)⟩
  have hav : pureAverage e = ∑ j, (e.prob j : ℂ) • pureDensity (e.vector j) := by
    unfold pureAverage
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.coe_smul]
  have havd : (pureAverage e).PosSemidef := by
    rw [hav]; exact Matrix.posSemidef_sum _ fun j _ => psd_smul (hpd j).1 (e.nonneg j)
  -- output entropy of a pure input equals the entropy of the complementary output
  have hpure : ∀ j, vnEntropy (krausApply E (pureDensity (e.vector j))) =
      vnEntropy (X6CH.comp E (pureDensity (e.vector j))) := by
    intro j
    rw [← dil_out, vn_pure_marginals, dil_pd, trF_stV']
  have hcd : ∀ j, IsDensityMatrix (X6CH.comp E (pureDensity (e.vector j))) := fun j =>
    ⟨comp_psd E (hpd j).1, by
      rw [← trF_stV', trace_trF, trace_mul_comm, ← Matrix.mul_assoc, stV_iso E hE, Matrix.one_mul,
        (hpd j).2]⟩
  have hlin : X6CH.comp E (∑ j, (e.prob j : ℂ) • pureDensity (e.vector j)) =
      ∑ j, (e.prob j : ℂ) • X6CH.comp E (pureDensity (e.vector j)) := by
    simp only [← trF_stV', Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    exact X6CH.trF_sum _ _
  have h := ent_concave e.prob e.nonneg e.total _ hcd
  rw [ee_eq _ havd.isHermitian, sc, sqrt_sq havd, hav, hlin]
  simpa only [hpure] using h

end X6EX


/-! X6: discarding an input ancilla cannot increase the maximal input mutual information. -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6DA
open Matrix X6SSA X6CH X6EX QAlgorithms Real
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo maximalMutualInfo)

variable {A B K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype K] [DecidableEq K]

/-- entropy is at most `|A| / ln 2`. -/
lemma vn_le_card {σ : Matrix A A ℂ} (hσ : σ.PosSemidef) :
    vnEntropy σ ≤ Fintype.card A / log 2 := by
  rw [vn_eig' hσ.1, ← Finset.sum_div]
  have hl : 0 < log 2 := Real.log_pos one_lt_two
  refine div_le_div_of_nonneg_right ?_ hl.le
  calc ∑ i, negMulLog (hσ.1.eigenvalues i) ≤ ∑ _i : A, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => (negMulLog_le_one_sub_self (hσ.eigenvalues_nonneg i)).trans
          (by linarith [hσ.eigenvalues_nonneg i])
    _ = Fintype.card A := by simp

/-- `⟨k|` on the second factor. -/
def Pk (k : K) : Matrix A (A × K) ℂ := of fun x y => if y = (x, k) then 1 else 0

lemma Pk_sum (ρ : Matrix (A × K) (A × K) ℂ) : ∑ k : K, (Pk (A := A) k * ρ * (Pk (A := A) k)ᴴ : Matrix A A ℂ) = trR ρ := by
  ext x x'
  simp [Pk, mul_apply, conjTranspose_apply, Matrix.sum_apply, trR]

lemma Pk_iso : ∑ k, (Pk (A := A) (K := K) k)ᴴ * Pk (A := A) k = 1 := by
  ext p q
  obtain ⟨x, k⟩ := p
  obtain ⟨x', k'⟩ := q
  simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, Pk, of_apply, one_apply, Prod.ext_iff]
  by_cases h1 : x = x' <;> by_cases h2 : k = k' <;> simp [h1, h2, Finset.sum_ite_eq', ite_and]

/-- Kraus family of `N ∘ Tr_K`. -/
def Gk {m : ℕ} (E : Fin m → Matrix B A ℂ) : Fin m × K → Matrix B (A × K) ℂ :=
  fun p => E p.1 * Pk (A := A) p.2

lemma Gk_kraus {m : ℕ} (E : Fin m → Matrix B A ℂ) (hE : ∑ a, (E a)ᴴ * E a = 1) :
    ∑ p, (Gk (K := K) E p)ᴴ * Gk E p = 1 := by
  have h : ∀ p : Fin m × K, (Gk (K := K) E p)ᴴ * Gk E p = (Pk (A := A) p.2)ᴴ * ((E p.1)ᴴ * E p.1) * Pk (A := A) p.2 := by
    intro p; simp only [Gk, conjTranspose_mul, Matrix.mul_assoc]
  simp only [h, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [← Matrix.sum_mul, ← Matrix.mul_sum, hE, Matrix.mul_one]
  exact Pk_iso

lemma Gk_eq {m : ℕ} (E : Fin m → Matrix B A ℂ) :
    (fun ρ : Matrix (A × K) (A × K) ℂ => krausApply E (traceRight ρ)) = krausApply (Gk (K := K) E) := by
  funext ρ
  show _ = ∑ p, Gk E p * ρ * (Gk E p)ᴴ
  have : traceRight ρ = trR ρ := rfl
  rw [this, ← Pk_sum]
  show ∑ a, E a * (∑ k : K, (Pk (A := A) k * ρ * (Pk (A := A) k)ᴴ : Matrix A A ℂ)) * (E a)ᴴ =
    ∑ p : Fin m × K, (E p.1 * Pk (A := A) p.2) * ρ * (E p.1 * Pk (A := A) p.2)ᴴ
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [conjTranspose_mul, Matrix.mul_assoc]

/-- identity Kraus family (any universe). -/
def F1 {B : Type*} [DecidableEq B] : Unit → Matrix B B ℂ := fun _ => 1

lemma F1_kraus : ∑ l, (F1 (B := B) l)ᴴ * F1 l = 1 := by simp [F1]

section main
variable {m : ℕ} (E : Fin m → Matrix B A ℂ) (Ψ : Matrix (A × K) (A × K) ℂ)

def sBE : (A × K) × (B × (Unit × (Fin m × K))) ≃ (B × Fin m) × ((A × K) × (Unit × K)) where
  toFun x := ((x.2.1, x.2.2.2.1), (x.1, (x.2.2.1, x.2.2.2.2)))
  invFun y := (y.2.1, (y.1.1, (y.2.2.1, (y.1.2, y.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl

def sE : (A × K) × (B × (Unit × (Fin m × K))) ≃ Fin m × ((A × K) × (B × (Unit × K))) where
  toFun x := (x.2.2.2.1, (x.1, (x.2.1, (x.2.2.1, x.2.2.2.2))))
  invFun y := (y.2.1, (y.2.2.1, (y.2.2.2.1, (y.1, y.2.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl

lemma lam_entry (r : A × K) (b : B) (e : Fin m) (kd : K) :
    (lam Ψ (Gk (K := K) E) (F1 (B := B))) (r, (b, ((), (e, kd)))) =
      (stV E * (Pk (A := A) kd * Ψ)) (b, e) r := by
  simp [lam, Gk, F1, stV, mul_apply, Matrix.mul_assoc]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

lemma m_BE : marg (sBE (m := m)) (pureDensity (lam Ψ (Gk (K := K) E) (F1 (B := B)))) =
    stV E * trR (Ψ * Ψᴴ) * (stV E)ᴴ := by
  have e1 : trR (Ψ * Ψᴴ) = ∑ kd : K, ((Pk (A := A) kd * Ψ) * (Pk (A := A) kd * Ψ)ᴴ : Matrix A A ℂ) := by
    rw [← Pk_sum]
    refine Finset.sum_congr rfl fun kd _ => ?_
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have e2 : stV E * trR (Ψ * Ψᴴ) * (stV E)ᴴ =
      ∑ kd : K, (stV E * (Pk (A := A) kd * Ψ)) * (stV E * (Pk (A := A) kd * Ψ))ᴴ := by
    rw [e1, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun kd _ => ?_
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e2]
  ext p q
  simp only [Matrix.sum_apply, mul_conjT_apply]
  have hent : ∀ (y : (A × K) × (Unit × K)), (lam Ψ (Gk (K := K) E) (F1 (B := B)))
      ((sBE (m := m)).symm (p, y)) = (stV E * (Pk (A := A) y.2.2 * Ψ)) p y.1 := by
    rintro ⟨r, ⟨⟨⟩, kd⟩⟩
    exact lam_entry E Ψ r p.1 p.2 kd
  have hent' : ∀ (y : (A × K) × (Unit × K)), (lam Ψ (Gk (K := K) E) (F1 (B := B)))
      ((sBE (m := m)).symm (q, y)) = (stV E * (Pk (A := A) y.2.2 * Ψ)) q y.1 := by
    rintro ⟨r, ⟨⟨⟩, kd⟩⟩
    exact lam_entry E Ψ r q.1 q.2 kd
  show ∑ y, (lam Ψ (Gk (K := K) E) (F1 (B := B))) ((sBE (m := m)).symm (p, y)) *
      conj ((lam Ψ (Gk (K := K) E) (F1 (B := B))) ((sBE (m := m)).symm (q, y))) = _
  simp only [hent, hent']
  rw [Fintype.sum_prod_type (α₁ := A × K) (α₂ := Unit × K)]
  simp only [Fintype.sum_prod_type (α₁ := Unit) (α₂ := K), Finset.univ_unique, Finset.sum_singleton]
  exact Finset.sum_comm

lemma m_E : marg (sE (m := m)) (pureDensity (lam Ψ (Gk (K := K) E) (F1 (B := B)))) =
    trF (marg (sBE (m := m)) (pureDensity (lam Ψ (Gk (K := K) E) (F1 (B := B))))) := by
  ext e e'
  simp only [marg, trR, trF, reindex_apply, submatrix_apply, of_apply, sE, sBE,
    Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

def Φ4 : (A × K) × (B × (Unit × (Fin m × K))) ≃ (K × (B × (A × K))) × (Unit × Fin m) where
  toFun x := ((x.2.2.2.2, (x.2.1, x.1)), (x.2.2.1, x.2.2.2.1))
  invFun y := (y.1.2.2, (y.1.2.1, (y.2.1, (y.2.2, y.1.1))))
  left_inv _ := rfl
  right_inv _ := rfl

end main

lemma trR_dens {ρ : Matrix (A × K) (A × K) ℂ} (hρ : IsDensityMatrix ρ) : IsDensityMatrix (trR ρ) := by
  have h2 : trR ρ = trF (reindex (Equiv.prodComm A K) (Equiv.prodComm A K) ρ) := by ext; rfl
  refine ⟨?_, ?_⟩
  · rw [h2]; exact trF_psd (by rw [reindex_apply]; exact hρ.1.submatrix _)
  · rw [h2, trace_trF, trace_reind, hρ.2]

/-- the key inequality `I(N ∘ Tr_K, ρ) ≤ I(N, Tr_K ρ)` (weak monotonicity). -/
theorem key [Nonempty A] [Nonempty B] [Nonempty K] {m : ℕ} [NeZero m] (E : Fin m → Matrix B A ℂ)
    (hE : ∑ a, (E a)ᴴ * E a = 1) (ρ : Matrix (A × K) (A × K) ℂ) (hρ : IsDensityMatrix ρ) :
    inputMutualInfo (fun ρ : Matrix (A × K) (A × K) ℂ => krausApply E (traceRight ρ)) ρ ≤
      inputMutualInfo (krausApply E) (traceRight ρ) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  have hA := trR_dens hρ
  have htr : traceRight ρ = trR ρ := rfl
  rw [Gk_eq, htr]
  set Ψ := cfc Real.sqrt ρ
  have hs : Ψ * Ψᴴ = ρ := sqrt_sq hρ.1
  have hΨ : trace (Ψ * Ψᴴ) = 1 := by rw [hs, hρ.2]
  have hG := Gk_kraus (K := K) E hE
  set P := pureDensity (lam Ψ (Gk (K := K) E) (F1 (B := B)))
  have hP : P.PosSemidef := pd_psd _
  have hPt : trace P = 1 := tr_one Ψ _ _ hG F1_kraus hΨ
  have eR : vnEntropy (marg (Equiv.refl _) P) = vnEntropy ρ := by
    rw [m_R Ψ _ _ hG F1_kraus, vn_transpose (isHermitian_conjTranspose_mul_self Ψ), ← vn_mul_conj, hs]
  have eK : vnEntropy (marg sK P) = vnEntropy (X6CH.comp (Gk (K := K) E) ρ) := by
    rw [m_K Ψ _ _ F1_kraus, hs]
  have eBE : vnEntropy (marg (sBE (m := m)) P) = vnEntropy (trR ρ) := by
    rw [m_BE, hs, vn_iso _ (stV_iso E hE) _ hA.1]
  have eE : vnEntropy (marg (sE (m := m)) P) = vnEntropy (X6CH.comp E (trR ρ)) := by
    rw [m_E, m_BE, hs, trF_stV']
  have h := ssa_split (Φ4 (m := m)) P hP hPt
  rw [pure_comp ((Φ4 (m := m)).trans r21), pure_comp ((Φ4 (m := m)).trans r31),
    pure_comp (Φ4 (m := m))] at h
  rw [vn_marg_eq (sBE (m := m)) (((Φ4 (m := m)).trans r21).trans (Equiv.prodComm _ _)) ?_ ?_ hP,
    vn_marg_eq sK (((Φ4 (m := m)).trans r31).trans (Equiv.prodComm _ _)) ?_ ?_ hP,
    vn_marg_eq (Equiv.refl _) ((Φ4 (m := m)).trans r1) ?_ ?_ hP,
    vn_marg_eq (sE (m := m)) ((Φ4 (m := m)).trans (Equiv.prodComm _ _)) ?_ ?_ hP,
    eBE, eK, eR, eE] at h
  · have hNρ : krausApply (Gk (K := K) E) ρ = krausApply E (trR ρ) := by
      rw [← Gk_eq]; rfl
    unfold inputMutualInfo
    rw [ee_eq _ hρ.1.isHermitian, sc, sqrt_sq hρ.1, ee_eq _ hA.1.isHermitian, sc, sqrt_sq hA.1, hNρ]
    linarith
  all_goals intro ω ω'
  all_goals simp only [sBE, sE, sK, Φ4, r21, r31, r1, Equiv.coe_fn_mk, Equiv.trans_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Prod.ext_iff, Equiv.refl_apply]
  all_goals (try simp)
  all_goals (try tauto)

theorem discard [Nonempty A] [Nonempty B] [Nonempty K] (N : Superop A B) (hN : IsChannel N) :
    maximalMutualInfo (fun rho : Matrix (A × K) (A × K) ℂ => N (traceRight rho)) ≤
      maximalMutualInfo N := by
  obtain ⟨m, E, hm, hE, rfl⟩ := kraus_of_channel hN
  haveI : NeZero m := ⟨hm.ne'⟩
  unfold maximalMutualInfo
  -- the target set is bounded above
  set M : Superop B B := krausApply (fun _ : Fin 1 => (1 : Matrix B B ℂ))
  have hM : IsChannel M := ⟨1, fun _ => 1, by
    show ∑ _j : Fin 1, (1 : Matrix B B ℂ)ᴴ * 1 = 1
    simp, fun _ => rfl⟩
  have hbdd : BddAbove {v | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧
      v = inputMutualInfo (krausApply E) rho} := by
    refine ⟨2 * (Fintype.card A / log 2), ?_⟩
    rintro v ⟨σ, hσ, rfl⟩
    have h := (dpi (krausApply E) M hN hM σ hσ).2.1
    have := vn_le_card hσ.1
    linarith
  have hne : {v | ∃ rho : Matrix (A × K) (A × K) ℂ, IsDensityMatrix rho ∧
      v = inputMutualInfo (fun rho : Matrix (A × K) (A × K) ℂ => krausApply E (traceRight rho)) rho}.Nonempty := by
    obtain ⟨x⟩ : Nonempty (A × K) := inferInstance
    exact ⟨_, ⟨pureDensity (EuclideanSpace.single x (1 : ℂ)), ⟨pd_psd _, pd_trace _ (by simp)⟩, rfl⟩⟩
  refine csSup_le hne ?_
  rintro v ⟨ρ, hρ, rfl⟩
  exact (key E hE ρ hρ).trans (le_csSup hbdd ⟨_, trR_dens hρ, rfl⟩)

end X6DA


/-! X6: nonnegativity of the input mutual information (via the complementary channel), general
concavity of `S(ρ) - S_e(N, ρ)`, and the Holevo bound `χ(N(ρ_j)) ≤ I(N, Σ w_j ρ_j)`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6ZC
open Matrix X6SSA X6CH QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)
open QAlgorithms.Papers.Independent.Information100.P27 (average labelInformation)

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Kraus family of the complementary channel. -/
def cK {K : Type} (E : K → Matrix B A ℂ) : B → Matrix K A ℂ := fun b => of fun k a => E k b a

lemma cK_kraus {K : Type} [Fintype K] (E : K → Matrix B A ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) :
    ∑ b, (cK E b)ᴴ * cK E b = 1 := by
  rw [← hE]
  ext a a'
  simp only [cK, Matrix.sum_apply, mul_apply, conjTranspose_apply, of_apply]
  exact Finset.sum_comm

lemma cK_apply {K : Type} [Fintype K] (E : K → Matrix B A ℂ) (σ : Matrix A A ℂ) :
    krausApply (cK E) σ = X6CH.comp E σ := by
  ext k k'
  simp only [krausApply, cK, X6CH.comp, Matrix.sum_apply, mul_apply, conjTranspose_apply, of_apply,
    trace, diag_apply, Finset.sum_mul]

lemma cK_comp {K : Type} [Fintype K] (E : K → Matrix B A ℂ) (σ : Matrix A A ℂ) :
    X6CH.comp (cK E) σ = krausApply E σ := by
  ext b b'
  simp only [krausApply, cK, X6CH.comp, Matrix.sum_apply, mul_apply, conjTranspose_apply, of_apply,
    trace, diag_apply, Finset.sum_mul]

/-- `I(N, ρ) ≥ 0`. -/
theorem mi_nonneg [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (ρ : Matrix A A ℂ) (hρ : IsDensityMatrix ρ) : 0 ≤ inputMutualInfo N ρ := by
  obtain ⟨m, E, hm, hE, rfl⟩ := kraus_of_channel hN
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set s := cfc Real.sqrt ρ
  have hs : s * sᴴ = ρ := sqrt_sq hρ.1
  have hΨ : trace (s * sᴴ) = 1 := by rw [hs, hρ.2]
  obtain ⟨-, -, -, i4⟩ := ineqs (R := A) s (cK E) (F0 (B := Fin m)) (cK_kraus E hE) F0_kraus hΨ
  simp only [hs, kraus_F0, cK_apply, cK_comp] at i4
  have eN : entropyExchange (krausApply E) ρ = vnEntropy (X6CH.comp E ρ) := by
    rw [ee_eq _ hρ.1.isHermitian, sc, hs]
  unfold inputMutualInfo
  rw [eN]
  linarith

/-- concavity of `S(σ) - S_e(N, σ)` for finite mixtures. -/
theorem concave_fin [Nonempty A] [Nonempty B] {J : Type} [Fintype J] [DecidableEq J]
    (N : Superop A B) (hN : IsChannel N) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (ρ : J → Matrix A A ℂ) (hρ : ∀ j, IsDensityMatrix (ρ j)) :
    ∑ j, w j * (vnEntropy (ρ j) - entropyExchange N (ρ j)) ≤
      vnEntropy (∑ j, (w j : ℂ) • ρ j) - entropyExchange N (∑ j, (w j : ℂ) • ρ j) := by
  obtain ⟨m, E, hm, hE, rfl⟩ := kraus_of_channel hN
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set V := stV E
  have hV := stV_iso E hE
  have dens : ∀ j, IsDensityMatrix (V * ρ j * Vᴴ) := fun j =>
    ⟨(hρ j).1.mul_mul_conjTranspose_same V, by
      rw [trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, (hρ j).2]⟩
  have hc := cond_concave w hw hw1 (fun j => V * ρ j * Vᴴ) dens
  have hmixV : ∑ j, (w j : ℂ) • (V * ρ j * Vᴴ) = V * (∑ j, (w j : ℂ) • ρ j) * Vᴴ := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hmixd : (∑ j, (w j : ℂ) • ρ j).PosSemidef :=
    Matrix.posSemidef_sum _ fun j _ => psd_smul (hρ j).1 (hw j)
  rw [hmixV] at hc
  rw [X6EX.cond_form E hE hmixd]
  simpa only [X6EX.cond_form E hE (hρ _).1] using hc

lemma chan_dens [Nonempty A] (N : Superop A B) (hN : IsChannel N) (ρ : Matrix A A ℂ)
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (N ρ) := by
  obtain ⟨m, E, hm, hE, rfl⟩ := kraus_of_channel hN
  exact ⟨kraus_psd E hρ.1, by rw [kraus_trace E hE, hρ.2]⟩

lemma li_eq {J : Type} [Fintype J] (w : J → ℝ) (τ : J → Matrix B B ℂ) :
    labelInformation w τ = vnEntropy (∑ j, (w j : ℂ) • τ j) - ∑ j, w j * vnEntropy (τ j) := by
  unfold labelInformation average
  rw [X6CH.vn_any _ inferInstance]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [X6CH.vn_any _ inferInstance]

/-- Holevo bound: `0 ≤ χ({w_j, N ρ_j}) ≤ I(N, Σ w_j ρ_j)`. -/
theorem holevo_le [Nonempty A] [Nonempty B] {J : Type} [Fintype J] [DecidableEq J]
    (N : Superop A B) (hN : IsChannel N) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (ρ : J → Matrix A A ℂ) (hρ : ∀ j, IsDensityMatrix (ρ j)) :
    0 ≤ labelInformation w (fun j => N (ρ j)) ∧
      labelInformation w (fun j => N (ρ j)) ≤ inputMutualInfo N (average w ρ) := by
  have hlin : N (average w ρ) = average w (fun j => N (ρ j)) := by
    obtain ⟨m, E, hm, hE, rfl⟩ := kraus_of_channel hN
    exact kraus_lin E _ ρ
  have hNd := fun j => chan_dens N hN (ρ j) (hρ j)
  constructor
  · rw [li_eq]
    have := ent_concave w hw hw1 _ hNd
    linarith
  · have h1 := concave_fin N hN w hw hw1 ρ hρ
    have h2 : ∀ j, 0 ≤ inputMutualInfo N (ρ j) := fun j => mi_nonneg N hN (ρ j) (hρ j)
    have h3 : 0 ≤ ∑ j, w j * inputMutualInfo N (ρ j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (h2 j)
    rw [li_eq]
    unfold inputMutualInfo at *
    rw [hlin]
    unfold average at *
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h1 h3
    linarith

end X6ZC


/-! Claimed50.P43, eq.(17): the entanglement-assisted Holevo converse. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6AH
open Matrix X6SSA X6CH QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo
  maximalMutualInfo)
open QAlgorithms.Papers.Independent.Claimed50.P43

/-! ### tensor powers of Kraus channels -/

section pi
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def piK {k m : ℕ} (E : Fin m → Matrix κ ι ℂ) (j : Fin k → Fin m) :
    Matrix (Fin k → κ) (Fin k → ι) ℂ :=
  of fun y x => ∏ i, E (j i) (y i) (x i)

lemma prod_one {k : ℕ} (x x' : Fin k → ι) :
    ∏ i, (1 : Matrix ι ι ℂ) (x i) (x' i) = (1 : Matrix (Fin k → ι) (Fin k → ι) ℂ) x x' := by
  by_cases h : x = x'
  · subst h; simp
  · rw [Matrix.one_apply_ne h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

lemma piK_iso {k m : ℕ} (E : Fin m → Matrix κ ι ℂ) (hE : ∑ l, (E l)ᴴ * E l = 1) :
    ∑ j : Fin k → Fin m, (piK E j)ᴴ * piK E j = 1 := by
  ext x x'
  rw [← prod_one, ← hE]
  simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, piK, of_apply, star_prod,
    ← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.prod_sum]

lemma pi_kraus {k m : ℕ} (E : Fin m → Matrix κ ι ℂ) :
    piSuperop (fun _ : Fin k => krausApply E) = krausApply (piK (k := k) E) := by
  funext X
  ext y y'
  have h1 : ∀ (a a' : ι) (b b' : κ), krausApply E (Matrix.single a a' 1) b b' =
      ∑ l, E l b a * star (E l b' a') := by
    intro a a' b b'
    simp only [krausApply, Matrix.sum_apply, mul_apply, conjTranspose_apply, Matrix.single_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single a']
    · rw [Finset.sum_eq_single a]
      · simp
      · intro c _ hc; simp [Ne.symm hc]
      · simp
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  simp only [piSuperop, of_apply]
  simp only [h1, Fintype.prod_sum, Finset.mul_sum]
  simp only [krausApply, Matrix.sum_apply, mul_apply, conjTranspose_apply, piK, of_apply, star_prod,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext x'; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x' _ =>
    Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib]; ring

lemma pi_channel {k : ℕ} [Nonempty ι] (N : Superop ι κ) (hN : IsChannel N) :
    IsChannel (piSuperop (fun _ : Fin k => N)) := by
  obtain ⟨m, E, -, hE, rfl⟩ := kraus_of_channel hN
  let e := (Fintype.equivFin (Fin k → Fin m)).symm
  refine ⟨Fintype.card (Fin k → Fin m), fun t => piK E (e t), ?_, fun X => ?_⟩
  · show ∑ t, (piK E (e t))ᴴ * piK E (e t) = 1
    rw [Equiv.sum_comp e (fun j => (piK E j)ᴴ * piK E j)]
    exact piK_iso E hE
  · rw [pi_kraus]
    show ∑ j, piK E j * X * (piK E j)ᴴ = ∑ t, piK E (e t) * X * (piK E (e t))ᴴ
    rw [Equiv.sum_comp e (fun j => piK E j * X * (piK E j)ᴴ)]

end pi

/-! ### marginals of `id ⊗ Φ` -/

section marg
variable {R A B : Type*} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B]

lemma idT_trR {K : Type*} [Fintype K] (E : K → Matrix B A ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1)
    (X : Matrix (R × A) (R × A) ℂ) :
    traceRight (idTensorSuperop (krausApply E) X) = traceRight X := by
  ext r r'
  show trace (krausApply E (of fun i i' => X (r, i) (r', i'))) = ∑ a, X (r, a) (r', a)
  rw [kraus_trace E hE]; try rfl

lemma idT_trL {K : Type*} [Fintype K] (E : K → Matrix B A ℂ) (X : Matrix (R × A) (R × A) ℂ) :
    traceLeft (idTensorSuperop (krausApply E) X) = krausApply E (traceLeft X) := by
  ext b b'
  simp only [traceLeft, idTensorSuperop, krausApply, of_apply, Matrix.sum_apply, mul_apply,
    conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

end marg

/-! ### the one-encoder inequality -/

lemma vn_nonneg' {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) : 0 ≤ vnEntropy ρ := by
  rw [X6CH.vn_eig' hρ.1.1]
  refine Finset.sum_nonneg fun i _ => div_nonneg (Real.negMulLog_nonneg (hρ.1.eigenvalues_nonneg i)
    ?_) (Real.log_nonneg (by norm_num))
  rw [← X6CH.eig_sum hρ.1.1 hρ.2]
  exact Finset.single_le_sum (fun j _ => hρ.1.eigenvalues_nonneg j) (Finset.mem_univ i)

variable {A C : Type} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]
  [Nonempty A] [Nonempty C]

lemma ee_nonneg (N : Superop A C) (hN : IsChannel N) {ρ : Matrix A A ℂ} (hρ : IsDensityMatrix ρ) :
    0 ≤ entropyExchange N ρ := by
  obtain ⟨m, E, hm, hE, rfl⟩ := kraus_of_channel hN
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [ee_eq _ hρ.1.isHermitian, sc, sqrt_sq hρ.1]
  refine vn_nonneg' ⟨?_, ?_⟩
  · rw [← X6EX.trF_stV']; exact trF_psd (hρ.1.mul_mul_conjTranspose_same _)
  · rw [← X6EX.trF_stV']
    refine (trace_trF _).trans ?_
    rw [trace_mul_comm, ← Matrix.mul_assoc, stV_iso E hE, Matrix.one_mul, hρ.2]

/-- `S(B) - S(BC) ≤ S(ρ_i) - S_e(N, ρ_i)` for one encoder. -/
lemma one_enc (N : Superop A C) (hN : IsChannel N) (Φ : Superop A A) (hΦ : IsChannel Φ)
    (ψ : EuclideanSpace ℂ (A × A)) (hψ : ‖ψ‖ = 1) :
    vnEntropy (traceRight (pureDensity ψ)) -
        vnEntropy (idTensorSuperop N (idTensorSuperop Φ (pureDensity ψ))) ≤
      vnEntropy (traceLeft (idTensorSuperop Φ (pureDensity ψ))) -
        entropyExchange N (traceLeft (idTensorSuperop Φ (pureDensity ψ))) := by
  obtain ⟨m, F, hm, hF, rfl⟩ := kraus_of_channel hN
  obtain ⟨m', E, hm', hE, hΦE⟩ := kraus_of_channel hΦ
  subst hΦE
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nonempty (Fin m') := ⟨⟨0, hm'⟩⟩
  let Ψ : Matrix A A ℂ := of fun a r => ψ (r, a)
  have hvec : vecOf Ψ = ψ := by ext p; rfl
  have hσ : Ψ * Ψᴴ = traceLeft (pureDensity ψ) := by
    ext a a'
    simp [Ψ, mul_apply, traceLeft, pureDensity, conjTranspose_apply]
  have hψd : IsDensityMatrix (pureDensity ψ) := ⟨pd_psd ψ, pd_trace ψ hψ⟩
  have hΨ : trace (Ψ * Ψᴴ) = 1 := by
    rw [hσ]; exact (trace_trF (pureDensity ψ)).trans hψd.2
  obtain ⟨-, i2, -, -⟩ := ineqs Ψ E F hE hF hΨ
  rw [hvec, hσ] at i2
  have hρ : (krausApply E (traceLeft (pureDensity ψ))).PosSemidef :=
    kraus_psd E (trF_psd hψd.1)
  have eL : entropyExchange (krausApply F) (krausApply E (traceLeft (pureDensity ψ))) =
      vnEntropy (comp F (krausApply E (traceLeft (pureDensity ψ)))) := by
    rw [ee_eq _ hρ.isHermitian, sc, sqrt_sq hρ]
  rw [idT_trL, eL]
  have eR : vnEntropy (traceRight (pureDensity ψ)) = vnEntropy (traceLeft (pureDensity ψ)) :=
    vn_pure_marginals ψ
  rw [eR]
  linarith

end X6AH


/-! Claimed50.P43, eq.(17): the entanglement-assisted Holevo converse, main argument. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6AH
open Matrix X6SSA X6CH QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo
  maximalMutualInfo)
open QAlgorithms.Papers.Independent.Claimed50.P43

section gen
variable {R A B : Type*} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B]

lemma idT_kraus' {K : Type*} [Fintype K] (E : K → Matrix B A ℂ) :
    idTensorSuperop (R := R) (krausApply E) = krausApply (fun k => (1 : Matrix R R ℂ) ⊗ₖ E k) := by
  funext M
  ext p q
  show (∑ k, E k * (of fun i i' => M (p.1, i) (q.1, i')) * (E k)ᴴ) p.2 q.2 =
    (∑ k, ((1 : Matrix R R ℂ) ⊗ₖ E k) * M * ((1 : Matrix R R ℂ) ⊗ₖ E k)ᴴ) p q
  simp only [conjTranspose_kronecker, conjTranspose_one]
  simp only [idTensorSuperop, krausApply, of_apply, Matrix.sum_apply, mul_apply, conjTranspose_apply,
    kroneckerMap_apply, Fintype.sum_prod_type, one_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single q.1 (fun b _ hb => by simp [hb]) (by simp)]
  simp only [if_true]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single p.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

lemma idT_psd {K : Type*} [Fintype K] (E : K → Matrix B A ℂ) {Y : Matrix (R × A) (R × A) ℂ}
    (hY : Y.PosSemidef) : (idTensorSuperop (R := R) (krausApply E) Y).PosSemidef := by
  rw [idT_kraus']; exact kraus_psd _ hY

lemma chan_idT_trR (Φ : Superop A B) (hΦ : IsChannel Φ) (X : Matrix (R × A) (R × A) ℂ)
    [Nonempty A] : traceRight (idTensorSuperop Φ X) = traceRight X := by
  obtain ⟨m, E, -, hE, hΦE⟩ := kraus_of_channel hΦ
  rw [hΦE]; exact idT_trR E hE X

lemma chan_idT_trL (Φ : Superop A B) (hΦ : IsChannel Φ) (X : Matrix (R × A) (R × A) ℂ)
    [Nonempty A] : traceLeft (idTensorSuperop Φ X) = Φ (traceLeft X) := by
  obtain ⟨m, E, -, hE, hΦE⟩ := kraus_of_channel hΦ
  rw [hΦE]; exact idT_trL E X

lemma trace_trR' {P Q : Type*} [Fintype P] [Fintype Q] (M : Matrix (P × Q) (P × Q) ℂ) :
    trace (trR M) = trace M := by
  simp [Matrix.trace, trR, Fintype.sum_prod_type]

lemma chan_idT_dens (Φ : Superop A B) (hΦ : IsChannel Φ) {X : Matrix (R × A) (R × A) ℂ}
    [Nonempty A] (hX : IsDensityMatrix X) : IsDensityMatrix (idTensorSuperop Φ X) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨m, E, -, hE, hΦE⟩ := kraus_of_channel hΦ
    rw [hΦE]; exact idT_psd E hX.1
  · have h := trace_trR' (idTensorSuperop Φ X)
    have h2 := trace_trR' X
    have e : trR (idTensorSuperop Φ X) = trR X := chan_idT_trR Φ hΦ X
    rw [← h, e, h2, hX.2]

lemma dens_mix {ι : Type*} [Fintype ι] {J : Type*} [Fintype J] (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (ρ : J → Matrix ι ι ℂ) (hρ : ∀ j, IsDensityMatrix (ρ j)) :
    IsDensityMatrix (∑ j, (w j : ℂ) • ρ j) := by
  refine ⟨Matrix.posSemidef_sum _ fun j _ => (hρ j).1.smul (by exact_mod_cast hw j), ?_⟩
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, (hρ _).2, smul_eq_mul, mul_one]
  exact_mod_cast hw1

lemma trR_mix {J : Type*} [Fintype J] (c : J → ℂ) (M : J → Matrix (R × A) (R × A) ℂ) :
    traceRight (∑ j, c j • M j) = ∑ j, c j • traceRight (M j) := by
  ext r r'
  simp only [traceRight, of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma trL_mix {J : Type*} [Fintype J] (c : J → ℂ) (M : J → Matrix (R × A) (R × A) ℂ) :
    traceLeft (∑ j, c j • M j) = ∑ j, c j • traceLeft (M j) := by
  ext a a'
  simp only [traceLeft, of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

end gen

variable {A C : Type} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]
  [Nonempty A] [Nonempty C]

theorem score_le (N : Superop A C) (hN : IsChannel N) {m : ℕ} (e : AssistedEnsemble A m) :
    assistedScore N e ≤
      inputMutualInfo N (∑ i, (e.prob i : ℂ) • traceLeft (encodedAssistedState e i)) := by
  have hψd : IsDensityMatrix (pureDensity e.resource) :=
    ⟨pd_psd _, pd_trace _ e.normalized⟩
  set ω := fun i => idTensorSuperop N (encodedAssistedState e i) with hω
  set ρ := fun i => traceLeft (encodedAssistedState e i) with hρdef
  set ρB := traceRight (pureDensity e.resource) with hρB
  have henc : ∀ i, IsDensityMatrix (encodedAssistedState e i) := fun i =>
    chan_idT_dens _ (e.channel i) hψd
  have hωd : ∀ i, IsDensityMatrix (ω i) := fun i => chan_idT_dens N hN (henc i)
  have hρd : ∀ i, IsDensityMatrix (ρ i) := fun i => by
    show IsDensityMatrix (traceLeft (idTensorSuperop (e.encode i) (pureDensity e.resource)))
    rw [chan_idT_trL _ (e.channel i)]
    exact X6ZC.chan_dens _ (e.channel i) _ ⟨trF_psd hψd.1, (trace_trF _).trans hψd.2⟩
  have hR : ∀ i, traceRight (ω i) = ρB := fun i => by
    show traceRight (idTensorSuperop N (idTensorSuperop (e.encode i) (pureDensity e.resource))) = _
    rw [chan_idT_trR N hN, chan_idT_trR _ (e.channel i)]
  have hF : ∀ i, traceLeft (ω i) = N (ρ i) := fun i => chan_idT_trL N hN _
  have hΩ := dens_mix e.prob e.nonneg e.total ω hωd
  have hsub := subadd (∑ i, (e.prob i : ℂ) • ω i) hΩ.1 hΩ.2
  have e1 : trR (∑ i, (e.prob i : ℂ) • ω i) = ρB := by
    show traceRight (∑ i, (e.prob i : ℂ) • ω i) = ρB
    rw [trR_mix]
    simp only [hR, ← Finset.sum_smul]
    rw [← Complex.ofReal_sum, e.total]; simp
  have hlin : N (∑ i, (e.prob i : ℂ) • ρ i) = ∑ i, (e.prob i : ℂ) • N (ρ i) := by
    obtain ⟨m', E, -, -, hNE⟩ := kraus_of_channel hN
    rw [hNE]; exact kraus_lin E _ _
  have e2 : trF (∑ i, (e.prob i : ℂ) • ω i) = N (∑ i, (e.prob i : ℂ) • ρ i) := by
    show traceLeft (∑ i, (e.prob i : ℂ) • ω i) = _
    rw [trL_mix, hlin]
    simp only [hF]
  rw [e1, e2] at hsub
  have hone : ∀ i, vnEntropy ρB - vnEntropy (ω i) ≤ vnEntropy (ρ i) - entropyExchange N (ρ i) :=
    fun i => one_enc N hN (e.encode i) (e.channel i) e.resource e.normalized
  have hconc := X6ZC.concave_fin N hN e.prob e.nonneg e.total ρ hρd
  have hsum : ∑ i, e.prob i * (vnEntropy ρB - vnEntropy (ω i)) ≤
      ∑ i, e.prob i * (vnEntropy (ρ i) - entropyExchange N (ρ i)) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hone i) (e.nonneg i)
  have hB : ∑ i, e.prob i * (vnEntropy ρB - vnEntropy (ω i)) =
      vnEntropy ρB - ∑ i, e.prob i * vnEntropy (ω i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, e.total, one_mul]
  unfold assistedScore inputMutualInfo
  show vnEntropy (∑ i, (e.prob i : ℂ) • ω i) - ∑ i, e.prob i * vnEntropy (ω i) ≤ _
  linarith

lemma mmi_bdd (N : Superop A C) (hN : IsChannel N) :
    BddAbove {v | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧ v = inputMutualInfo N rho} := by
  refine ⟨Fintype.card A / Real.log 2 + Fintype.card C / Real.log 2, ?_⟩
  rintro v ⟨ρ, hρ, rfl⟩
  unfold inputMutualInfo
  have h1 := X6DA.vn_le_card hρ.1
  have h2 := X6DA.vn_le_card (X6ZC.chan_dens N hN ρ hρ).1
  have h3 := ee_nonneg N hN hρ
  linarith

/-- a trivial assisted ensemble. -/
def triv (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] : AssistedEnsemble A 1 where
  prob := fun _ => 1
  nonneg := fun _ => zero_le_one
  total := by simp
  resource := EuclideanSpace.single (Classical.arbitrary A, Classical.arbitrary A) 1
  normalized := by simp
  encode := fun _ => id
  channel := fun _ => ⟨1, fun _ => 1, by simp [IsKrausFamily], fun ρ => by simp [krausApply]⟩

theorem oneShot_le (N : Superop A C) (hN : IsChannel N) :
    assistedOneShot N ≤ maximalMutualInfo N := by
  unfold assistedOneShot maximalMutualInfo
  refine csSup_le ⟨_, 1, triv A, rfl⟩ ?_
  rintro v ⟨m, e, rfl⟩
  refine (score_le N hN e).trans (le_csSup (mmi_bdd N hN) ⟨_, ?_, rfl⟩)
  have hψd : IsDensityMatrix (pureDensity e.resource) :=
    ⟨pd_psd _, pd_trace _ e.normalized⟩
  refine dens_mix e.prob e.nonneg e.total _ fun i => ?_
  show IsDensityMatrix (traceLeft (idTensorSuperop (e.encode i) (pureDensity e.resource)))
  rw [chan_idT_trL _ (e.channel i)]
  exact X6ZC.chan_dens _ (e.channel i) _ ⟨trF_psd hψd.1, (trace_trF _).trans hψd.2⟩

theorem main (N : Superop A C) (hN : IsChannel N) :
    (∀ (m : ℕ) (e : AssistedEnsemble A m), assistedScore N e ≤
      inputMutualInfo N (∑ i, (e.prob i : ℂ) • traceLeft (encodedAssistedState e i))) ∧
    assistedOneShot N ≤ maximalMutualInfo N ∧
    (∀ n : ℕ, 0 < n → assistedOneShot (piSuperop (fun _ : Fin n => N)) ≤
      maximalMutualInfo (piSuperop (fun _ : Fin n => N))) :=
  ⟨fun m e => score_le N hN e, oneShot_le N hN, fun n _ => oneShot_le _ (pi_channel N hN)⟩

end X6AH


/-! X6: two matrices with the same Gram matrix `X Xᴴ = Y Yᴴ` differ by a unitary on the right. -/

open scoped Matrix ComplexConjugate InnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6GU
open Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

lemma nsq (X : Matrix m n ℂ) (u : m → ℂ) :
    star (Xᴴ *ᵥ u) ⬝ᵥ (Xᴴ *ᵥ u) = star u ⬝ᵥ ((X * Xᴴ) *ᵥ u) := by
  rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec, mulVec_mulVec]

lemma norm_sq_eq_dot (v : EuclideanSpace ℂ n) : (‖v‖ ^ 2 : ℝ) = (star (v : n → ℂ) ⬝ᵥ (v : n → ℂ)).re := by
  rw [EuclideanSpace.norm_sq_eq, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply, Complex.star_def]
  rw [mul_comm, Complex.mul_conj']; norm_cast

theorem gram_unitary (X Y : Matrix m n ℂ) (h : X * Xᴴ = Y * Yᴴ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ X = Y * U := by
  let TX : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ n := toEuclideanLin Xᴴ
  let TY : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ n := toEuclideanLin Yᴴ
  have hTX : ∀ u, (TX u : n → ℂ) = Xᴴ *ᵥ (u : m → ℂ) := fun u => rfl
  have hTY : ∀ u, (TY u : n → ℂ) = Yᴴ *ᵥ (u : m → ℂ) := fun u => rfl
  have hn : ∀ u, ‖TX u‖ = ‖TY u‖ := fun u => by
    have h1 := norm_sq_eq_dot (TX u)
    have h2 := norm_sq_eq_dot (TY u)
    rw [hTX, nsq, h] at h1
    rw [hTY, nsq] at h2
    have : ‖TX u‖ ^ 2 = ‖TY u‖ ^ 2 := by rw [h1, h2]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  have hker : LinearMap.ker TY ≤ LinearMap.ker TX := fun u hu => by
    rw [LinearMap.mem_ker] at hu ⊢
    rw [← norm_eq_zero, hn, hu, norm_zero]
  let L0 : LinearMap.range TY →ₗ[ℂ] EuclideanSpace ℂ n :=
    (Submodule.liftQ _ TX hker).comp (TY.quotKerEquivRange.symm : _ →ₗ[ℂ] _)
  have hL0 : ∀ u, L0 ⟨TY u, LinearMap.mem_range_self _ _⟩ = TX u := fun u => by
    simp only [L0, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let L : LinearMap.range TY →ₗᵢ[ℂ] EuclideanSpace ℂ n :=
    { L0 with
      norm_map' := by
        rintro ⟨_, u, rfl⟩
        change ‖L0 ⟨TY u, _⟩‖ = _
        rw [hL0, hn]; rfl }
  let G := L.extend
  have hG : ∀ u, G (TY u) = TX u := fun u => by
    have := LinearIsometry.extend_apply L ⟨TY u, LinearMap.mem_range_self _ _⟩
    exact this.trans (hL0 u)
  let Gm : Matrix n n ℂ := Matrix.of fun i j => (G (EuclideanSpace.single j 1)) i
  have hGv : ∀ v : EuclideanSpace ℂ n, ∀ i, (G v) i = ∑ j, Gm i j * v j := fun v i => by
    have hv : v = ∑ j, v j • EuclideanSpace.single j (1 : ℂ) := by
      ext k; simp [Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, Gm, of_apply]
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
  have h1 : Gm * Yᴴ = Xᴴ := by
    ext i k
    have := congrArg (fun w : EuclideanSpace ℂ n => w i) (hG (EuclideanSpace.single k 1))
    simp only at this
    rw [hGv, hTX] at this
    have e : ∀ j, (TY (EuclideanSpace.single k 1)) j = Yᴴ j k := fun j => by
      rw [hTY]; simp [mulVec, dotProduct, PiLp.single_apply]
    simp only [e] at this
    rw [Matrix.mul_apply, this]
    simp [mulVec, dotProduct, PiLp.single_apply]
  have h2 : Gmᴴ * Gm = 1 := by
    ext j j'
    have := G.inner_map_map (EuclideanSpace.single j 1) (EuclideanSpace.single j' 1)
    rw [EuclideanSpace.inner_single_left] at this
    simp only [map_one, one_mul, PiLp.single_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    have e : ⟪G (EuclideanSpace.single j 1), G (EuclideanSpace.single j' 1)⟫_ℂ =
        ∑ i, conj (Gm i j) * Gm i j' := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, Gm, mul_comm]
    rw [e] at this
    simp only [conjTranspose_apply, Complex.star_def]
    rw [this]
  refine ⟨Gmᴴ, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.1 h2
  · have := congrArg conjTranspose h1
    rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose] at this
    exact this.symm

end X6GU


/-! X6: every bipartite density with first marginal `s` is obtained from one fixed
purification of `s` by a channel on the second factor. -/

open scoped Matrix ComplexConjugate ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
namespace X6CM
open Matrix QAlgorithms

variable {A : Type} [Fintype A] [DecidableEq A]

lemma sqrt_herm {n : Type*} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) : (cfc Real.sqrt ρ)ᴴ = cfc Real.sqrt ρ := by
  have : IsSelfAdjoint (cfc Real.sqrt ρ) := cfc_predicate _ _
  exact this

lemma sqrt_sq {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    cfc Real.sqrt ρ * (cfc Real.sqrt ρ)ᴴ = ρ := by
  open scoped MatrixOrder in
  have h0 : (0 : Matrix n n ℂ) ≤ ρ := Matrix.nonneg_iff_posSemidef.mpr hρ
  rw [sqrt_herm, ← cfc_mul Real.sqrt Real.sqrt ρ]
  conv_rhs => rw [← cfc_id ℝ ρ]
  open scoped MatrixOrder in
  exact cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg h0 hx)

/-- the purification vector of `S Sᴴ`. -/
def vec (S : Matrix A A ℂ) : EuclideanSpace ℂ (A × A) := WithLp.toLp 2 fun p => S p.1 p.2

lemma vec_marg (S : Matrix A A ℂ) : traceRight (pureDensity (vec S)) = S * Sᴴ := by
  ext a a'
  simp [traceRight, pureDensity, vec, mul_apply, conjTranspose_apply]

theorem realize [Nonempty A] (S : Matrix A A ℂ) (ρ : Matrix (A × A) (A × A) ℂ)
    (hρ : ρ.PosSemidef) (hm : traceRight ρ = S * Sᴴ) :
    ∃ (m : ℕ) (F : Fin m → Matrix A A ℂ), IsKrausFamily F ∧
      ρ = idTensorSuperop (krausApply F) (pureDensity (vec S)) := by
  set W : Matrix (A × A) (A × A) ℂ := cfc Real.sqrt ρ with hW
  have hρW : ρ = W * Wᴴ := (sqrt_sq hρ).symm
  let k0 : A × A := Classical.arbitrary _
  let X : Matrix A (A × (A × A)) ℂ := of fun a p => W (a, p.1) p.2
  let Y : Matrix A (A × (A × A)) ℂ := of fun a p => if p.2 = k0 then S a p.1 else 0
  have hX : X * Xᴴ = S * Sᴴ := by
    rw [← hm, hρW]
    ext a a'
    simp [X, traceRight, mul_apply, conjTranspose_apply, Fintype.sum_prod_type]
  have hY : Y * Yᴴ = S * Sᴴ := by
    ext a a'
    simp [Y, mul_apply, conjTranspose_apply, Fintype.sum_prod_type]
  obtain ⟨U, hU, hXY⟩ := X6GU.gram_unitary X Y (by rw [hX, hY])
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  -- Kraus operators indexed by `A × A`
  let G : (A × A) → Matrix A A ℂ := fun k => of fun b c => U (c, k0) (b, k)
  have hXe : ∀ a b k, W (a, b) k = ∑ c, S a c * U (c, k0) (b, k) := by
    intro a b k
    have := congrFun (congrFun hXY a) (b, k)
    simp only [X, Y, of_apply, mul_apply, Fintype.sum_prod_type, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  have hG : ∑ k, (G k)ᴴ * G k = 1 := by
    ext c c'
    have h1 := congrFun (congrFun hU' (c', k0)) (c, k0)
    rw [mul_apply, Fintype.sum_prod_type] at h1
    simp only [conjTranspose_apply] at h1
    simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, G, of_apply]
    rw [Finset.sum_comm]
    have e1 : (1 : Matrix (A × (A × A)) (A × (A × A)) ℂ) (c', k0) (c, k0) = (1 : Matrix A A ℂ) c c' := by
      by_cases h : c = c'
      · subst h; simp
      · rw [one_apply_ne (by simpa [eq_comm] using h), one_apply_ne h]
    rw [← e1, ← h1]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  let e := Fintype.equivFin (A × A)
  refine ⟨Fintype.card (A × A), fun j => G (e.symm j), ?_, ?_⟩
  · show ∑ j, (G (e.symm j))ᴴ * G (e.symm j) = 1
    rw [Equiv.sum_comp e.symm (fun k => (G k)ᴴ * G k), hG]
  ext p q
  rw [hρW]
  simp only [idTensorSuperop, krausApply, of_apply, Matrix.sum_apply, mul_apply, conjTranspose_apply]
  rw [Equiv.sum_comp e.symm (fun k => ∑ x, (∑ x_1, G k p.2 x_1 *
    pureDensity (vec S) (p.1, x_1) (q.1, x)) * star (G k q.2 x))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hXe, hXe, star_sum, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  simp only [G, of_apply, pureDensity, vec, star_mul', RCLike.star_def]
  ring

theorem cmr {I : Type*} [Nonempty A] (s : Matrix A A ℂ) (hs : IsDensityMatrix s)
    (rho : I → Matrix (A × A) (A × A) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (hmarg : ∀ i, traceRight (rho i) = s) :
    ∃ psi : EuclideanSpace ℂ (A × A), ‖psi‖ = 1 ∧ traceRight (pureDensity psi) = s ∧
      ∃ E : I → Superop A A, ∀ i, IsChannel (E i) ∧
        rho i = idTensorSuperop (E i) (pureDensity psi) := by
  set S := cfc Real.sqrt s
  have hS : S * Sᴴ = s := sqrt_sq hs.1
  have hr : ∀ i, ∃ (m : ℕ) (F : Fin m → Matrix A A ℂ), IsKrausFamily F ∧
      rho i = idTensorSuperop (krausApply F) (pureDensity (vec S)) := fun i =>
    realize S (rho i) (hrho i).1 (by rw [hmarg, hS])
  choose m F hF hρ using hr
  refine ⟨vec S, ?_, by rw [vec_marg, hS], fun i => krausApply (F i), fun i =>
    ⟨⟨m i, F i, hF i, fun _ => rfl⟩, hρ i⟩⟩
  have htr : trace (pureDensity (vec S)) = 1 := by
    rw [← hs.2, ← hS, ← vec_marg]
    simp [trace, traceRight, Fintype.sum_prod_type]
  have h2 := EuclideanSpace.norm_sq_eq (vec S)
  have h3 : ∑ p, ‖vec S p‖ ^ 2 = 1 := by
    have := congrArg Complex.re htr
    simp only [trace, diag_apply, pureDensity, of_apply, Complex.mul_conj, Complex.re_sum,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq] at this
    simpa using this
  rw [h3] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2

end X6CM


/-! Attainment of Holevo-type maxima over finite ensembles of density matrices
(Carathéodory reduction to a fixed ensemble size, then compactness). -/

open scoped ComplexOrder Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6AT

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- density matrices. -/
def Dens (I : Type*) [Fintype I] : Set (Matrix I I ℂ) := {ρ | ρ.PosSemidef ∧ ρ.trace = 1}

lemma isClosed_psd : IsClosed {P : Matrix I I ℂ | P.PosSemidef} := by
  have : {P : Matrix I I ℂ | P.PosSemidef} =
      {P | Pᴴ = P} ∩ ⋂ x : I → ℂ, {P | 0 ≤ star x ⬝ᵥ (P *ᵥ x)} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [this]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

lemma psd_decomp (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    ∃ B : Matrix I I ℂ, A = Bᴴ * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  open scoped MatrixOrder in
  have hB : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  open scoped MatrixOrder in
  have hAB : A = (CFC.sqrt A)ᴴ * CFC.sqrt A := by
    rw [hB.isHermitian.eq, CFC.sqrt_mul_sqrt_self A h0]
  exact ⟨_, hAB⟩

lemma entry_bound (A : Matrix I I ℂ) (hA : A.PosSemidef) (i j : I) :
    ‖A i j‖ ≤ 2 * (A.trace).re := by
  obtain ⟨B, rfl⟩ := psd_decomp A hA
  have hij : (Bᴴ * B) i j = ∑ k, star (B k i) * B k j := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have htr : ((Bᴴ * B).trace).re = ∑ l, ∑ k, ‖B k l‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [hij, htr, Finset.sum_comm]
  calc ‖∑ k, star (B k i) * B k j‖ ≤ ∑ k, ‖star (B k i) * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ k, (‖B k i‖ ^ 2 + ‖B k j‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_star]
        nlinarith [sq_nonneg (‖B k i‖ - ‖B k j‖), norm_nonneg (B k i), norm_nonneg (B k j)]
    _ ≤ ∑ k, (∑ l, ‖B k l‖ ^ 2 + ∑ l, ‖B k l‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => add_le_add ?_ ?_
        · exact Finset.single_le_sum (f := fun l => ‖B k l‖ ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_univ i)
        · exact Finset.single_le_sum (f := fun l => ‖B k l‖ ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_univ j)
    _ = 2 * ∑ k, ∑ l, ‖B k l‖ ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring

lemma dens_compact : IsCompact (Dens I) := by
  let Bs : Set (Matrix I I ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 2
  have hBs : IsCompact Bs :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hc : IsClosed (Dens I) :=
    isClosed_psd.inter (isClosed_eq (continuous_id.matrix_trace) continuous_const)
  refine hBs.of_isClosed_subset hc fun ρ hρ => ?_
  simp only [Bs, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i _ j _
  rw [Metric.mem_closedBall, dist_zero_right]
  have := entry_bound ρ hρ.1 i j
  rw [hρ.2] at this; simpa using this

lemma dens_avg {k : ℕ} (p : Fin k → ℝ) (ρ : Fin k → Matrix I I ℂ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hρ : ∀ i, ρ i ∈ Dens I) : ∑ i, p i • ρ i ∈ Dens I := by
  constructor
  · refine Matrix.posSemidef_sum _ fun i _ => ?_
    have := (hρ i).1.smul (show (0 : ℂ) ≤ (p i : ℂ) by exact_mod_cast hp i)
    rwa [Complex.coe_smul] at this
  · rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, (hρ _).2]
    simp only [Complex.real_smul, mul_one]
    exact_mod_cast hp1

/-- the fixed ensemble size supplied by Carathéodory's theorem. -/
abbrev KK (I : Type*) [Fintype I] : ℕ := Module.finrank ℝ (Matrix I I ℂ × ℝ) + 1

lemma red [Nonempty I] (h : Matrix I I ℂ → ℝ) {k : ℕ} (p : Fin k → ℝ) (ρ : Fin k → Matrix I I ℂ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (hρ : ∀ i, ρ i ∈ Dens I) :
    ∃ (q : Fin (KK I) → ℝ) (σ : Fin (KK I) → Matrix I I ℂ), (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧
      (∀ i, σ i ∈ Dens I) ∧ ∑ i, q i • σ i = ∑ i, p i • ρ i ∧
      ∑ i, q i * h (σ i) = ∑ i, p i * h (ρ i) := by
  set S : Set (Matrix I I ℂ × ℝ) := {z | ∃ r ∈ Dens I, z = (r, h r)}
  have hx : ∑ i, p i • ((ρ i, h (ρ i)) : Matrix I I ℂ × ℝ) ∈ convexHull ℝ S :=
    (convex_convexHull ℝ S).sum_mem (fun i _ => hp i) hp1
      (fun i _ => subset_convexHull ℝ S ⟨ρ i, hρ i, rfl⟩)
  obtain ⟨ι, hι, z, w, hzS, hai, hw, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ KK I := by
    have h1 := hai.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤
        Module.finrank ℝ (Matrix I I ℂ × ℝ) := Submodule.finrank_le _
    simp only [KK]; omega
  let e : ι ↪ Fin (KK I) := (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
  have hz : ∀ i, ∃ r ∈ Dens I, z i = (r, h r) := fun i => hzS ⟨i, rfl⟩
  choose r hr hrz using hz
  obtain ⟨ρ0⟩ : Nonempty (Dens I) := by
    obtain ⟨i0⟩ := ‹Nonempty I›
    refine ⟨⟨Matrix.diagonal (fun i => if i = i0 then (1 : ℂ) else 0), ?_, ?_⟩⟩
    · rw [Matrix.posSemidef_diagonal_iff]; intro i; split_ifs <;> norm_num
    · simp [Matrix.trace_diagonal]
  let q : Fin (KK I) → ℝ := Function.extend e w 0
  let σ : Fin (KK I) → Matrix I I ℂ := Function.extend e r (fun _ => ρ0.1)
  have hq : ∀ i, q (e i) = w i := fun i => e.injective.extend_apply _ _ _
  have hσ : ∀ i, σ (e i) = r i := fun i => e.injective.extend_apply _ _ _
  have hq0 : ∀ j ∉ Set.range e, q j = 0 := fun j hj => by
    simp only [q]; rw [Function.extend_apply' _ _ _ (by simpa using hj)]; rfl
  have hs1 : ∑ j, q j = ∑ i, q (e i) :=
    (Fintype.sum_of_injective e e.injective _ _ (fun j hj => hq0 j hj) (fun i => rfl)).symm
  have hs2 : ∑ j, q j • σ j = ∑ i, q (e i) • σ (e i) :=
    (Fintype.sum_of_injective e e.injective _ (fun j => q j • σ j)
      (fun j hj => by simp [hq0 j hj]) (fun i => rfl)).symm
  have hs3 : ∑ j, q j * h (σ j) = ∑ i, q (e i) * h (σ (e i)) :=
    (Fintype.sum_of_injective e e.injective _ (fun j => q j * h (σ j))
      (fun j hj => by simp [hq0 j hj]) (fun i => rfl)).symm
  have hfst := congrArg Prod.fst hwz
  have hsnd := congrArg Prod.snd hwz
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hfst hsnd
  refine ⟨q, σ, fun j => ?_, ?_, fun j => ?_, ?_, ?_⟩
  · by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj; rw [hq]; exact (hw i).le
    · rw [hq0 j hj]
  · rw [hs1]; simp only [hq]; exact hw1
  · by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj; rw [hσ]; exact hr i
    · simp only [σ]; rw [Function.extend_apply' _ _ _ (by simpa using hj)]; exact ρ0.2
  · rw [hs2]
    simp only [hq, hσ]
    rw [← hfst]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrz i]
  · rw [hs3]
    simp only [hq, hσ]
    rw [← hsnd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrz i]

/-- maxima of `g(Σ p ρ) - Σ p h(ρ)` over finite ensembles of densities are attained, with a
fixed number `KK I` of members. -/
theorem att [Nonempty I] (g h : Matrix I I ℂ → ℝ) (hg : ContinuousOn g (Dens I))
    (hh : ContinuousOn h (Dens I)) :
    ∃ (q : Fin (KK I) → ℝ) (σ : Fin (KK I) → Matrix I I ℂ), (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧
      (∀ i, σ i ∈ Dens I) ∧
      ∀ (k : ℕ) (p : Fin k → ℝ) (ρ : Fin k → Matrix I I ℂ), (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
        (∀ i, ρ i ∈ Dens I) →
        g (∑ i, p i • ρ i) - ∑ i, p i * h (ρ i) ≤ g (∑ i, q i • σ i) - ∑ i, q i * h (σ i) := by
  let Ω : Set ((Fin (KK I) → ℝ) × (Fin (KK I) → Matrix I I ℂ)) :=
    stdSimplex ℝ (Fin (KK I)) ×ˢ Set.pi Set.univ (fun _ => Dens I)
  have hΩ : IsCompact Ω := (isCompact_stdSimplex ℝ _).prod (isCompact_univ_pi fun _ => dens_compact)
  let F : ((Fin (KK I) → ℝ) × (Fin (KK I) → Matrix I I ℂ)) → ℝ :=
    fun x => g (∑ i, x.1 i • x.2 i) - ∑ i, x.1 i * h (x.2 i)
  have hmemΩ : ∀ x ∈ Ω, (∀ i, 0 ≤ x.1 i) ∧ ∑ i, x.1 i = 1 ∧ ∀ i, x.2 i ∈ Dens I := by
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun i => h3 i (Set.mem_univ i)⟩
  have hF : ContinuousOn F Ω := by
    refine ContinuousOn.sub ?_ ?_
    · refine hg.comp (by fun_prop) fun x hx => ?_
      obtain ⟨h1, h2, h3⟩ := hmemΩ x hx
      exact dens_avg _ _ h1 h2 h3
    · refine continuousOn_finset_sum _ fun i _ => ?_
      refine (continuous_apply i |>.comp continuous_fst).continuousOn.mul ?_
      refine hh.comp (continuous_apply i |>.comp continuous_snd).continuousOn fun x hx => ?_
      exact (hmemΩ x hx).2.2 i
  obtain ⟨ρ0, hρ0⟩ : ∃ ρ0 : Matrix I I ℂ, ρ0 ∈ Dens I := by
    obtain ⟨i0⟩ := ‹Nonempty I›
    refine ⟨Matrix.diagonal (fun i => if i = i0 then (1 : ℂ) else 0), ?_, ?_⟩
    · rw [Matrix.posSemidef_diagonal_iff]; intro i; split_ifs <;> norm_num
    · simp [Matrix.trace_diagonal]
  have hne : Ω.Nonempty := by
    refine ⟨(Pi.single 0 1, fun _ => ρ0), ⟨⟨fun i => ?_, ?_⟩, fun i _ => hρ0⟩⟩
    · by_cases hi : i = 0
      · subst hi; simp
      · simp [hi]
    · simp
  obtain ⟨x, hx, hmax⟩ := hΩ.exists_isMaxOn hne hF
  obtain ⟨h1, h2, h3⟩ := hmemΩ x hx
  refine ⟨x.1, x.2, h1, h2, h3, fun k p ρ hp hp1 hρ => ?_⟩
  obtain ⟨q, σ, hq, hq1, hσ, havg, hsum⟩ := red h p ρ hp hp1 hρ
  have hy : (q, σ) ∈ Ω := ⟨⟨hq, hq1⟩, fun i _ => hσ i⟩
  have := hmax hy
  simp only [Set.mem_setOf_eq, F] at this
  rw [havg, hsum] at this
  exact this

end X6AT


/-! Continuity of the von Neumann entropy on density matrices; partial traces of densities. -/

open scoped ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6AT
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Re tr (M log M)`. -/
def Hn' (M : Matrix n n ℂ) : ℝ := (trace (cfc (fun x : ℝ => x * Real.log x) M)).re

lemma vn_eq' (M : Matrix n n ℂ) : QAlgorithms.vnEntropy M = - Hn' M / Real.log 2 := by
  unfold QAlgorithms.vnEntropy Hn'
  have : (fun x : ℝ => x * Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * (x * Real.log x) := by
    funext x; rw [Real.logb]; ring
  rw [this, cfc_const_mul (Real.log 2)⁻¹ (fun x : ℝ => x * Real.log x) M
    Real.continuous_mul_log.continuousOn, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  ring

lemma spec_density' {M : Matrix n n ℂ} (hM : M.PosSemidef) (htr : M.trace = 1) :
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

lemma cont_tr_re' : Continuous fun M : Matrix n n ℂ => (trace M).re :=
  Complex.continuous_re.comp
    (LinearMap.continuous_of_finiteDimensional (traceLinearMap n ℂ ℂ))

lemma vn_contOn : ContinuousOn (QAlgorithms.vnEntropy : Matrix n n ℂ → ℝ) (Dens n) := by
  have h : ContinuousOn (Hn' : Matrix n n ℂ → ℝ)
      {a | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Icc 0 1} :=
    cont_tr_re'.comp_continuousOn
      (continuousOn_cfc (Matrix n n ℂ) isCompact_Icc _ Real.continuous_mul_log.continuousOn)
  have hsub : Dens n ⊆ {a : Matrix n n ℂ | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Icc 0 1} :=
    fun ρ hρ => ⟨hρ.1.1, spec_density' hρ.1 hρ.2⟩
  have h2 : ContinuousOn (fun ρ : Matrix n n ℂ => -Hn' ρ / Real.log 2) (Dens n) :=
    ((h.mono hsub).neg).div_const _
  exact h2.congr fun ρ _ => vn_eq' ρ

section ptr
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma traceRight_psd {M : Matrix (α × β) (α × β) ℂ} (hM : M.PosSemidef) :
    (QAlgorithms.traceRight M).PosSemidef := by
  let P : β → Matrix (α × β) α ℂ := fun h => of fun x a => if x = (a, h) then 1 else 0
  have : QAlgorithms.traceRight M = ∑ h, (P h)ᴴ * M * P h := by
    ext j k
    simp only [QAlgorithms.traceRight, of_apply, Matrix.sum_apply, mul_apply, conjTranspose_apply, P]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single (k, h)]
    · rw [Finset.sum_eq_single (j, h)] <;> simp (config := {contextual := true})
    · intro b _ hb; simp [hb]
    · simp
  rw [this]
  exact Matrix.posSemidef_sum _ fun h _ => hM.conjTranspose_mul_mul_same _

lemma trace_traceRight (M : Matrix (α × β) (α × β) ℂ) :
    (QAlgorithms.traceRight M).trace = M.trace := by
  simp only [QAlgorithms.traceRight, trace, diag, of_apply]
  rw [Fintype.sum_prod_type]

lemma traceRight_cont : Continuous (QAlgorithms.traceRight : Matrix (α × β) (α × β) ℂ → _) := by
  unfold QAlgorithms.traceRight
  refine continuous_pi fun j => continuous_pi fun k => ?_
  simp only [of_apply]
  exact continuous_finsetSum _ fun h _ =>
    (continuous_apply (k, h)).comp (continuous_apply (j, h))

end ptr

end X6AT


/-! X6 attainment library, part 3: two-level ensembles `Σ_x p_x Σ_y q_{xy} σ_{xy}`. -/

open scoped Matrix ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
namespace X6AT
open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Carathéodory, with the new members taken from the original family. -/
lemma redI {k : ℕ} (p : Fin k → ℝ) (ρ : Fin k → Matrix I I ℂ) (c : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    ∃ (q : Fin (KK I) → ℝ) (f : Fin (KK I) → Fin k), (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧
      ∑ i, q i • ρ (f i) = ∑ i, p i • ρ i ∧ ∑ i, q i * c (f i) = ∑ i, p i * c i := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hp1
    · exact h
  set S : Set (Matrix I I ℂ × ℝ) := Set.range (fun i => ((ρ i, c i) : Matrix I I ℂ × ℝ))
  have hx : ∑ i, p i • ((ρ i, c i) : Matrix I I ℂ × ℝ) ∈ convexHull ℝ S :=
    (convex_convexHull ℝ S).sum_mem (fun i _ => hp i) hp1
      (fun i _ => subset_convexHull ℝ S ⟨i, rfl⟩)
  obtain ⟨ι, hι, z, w, hzS, hai, hw, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ KK I := by
    have h1 := hai.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤
        Module.finrank ℝ (Matrix I I ℂ × ℝ) := Submodule.finrank_le _
    simp only [KK]; omega
  let e : ι ↪ Fin (KK I) := (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
  have hz : ∀ i, ∃ j, ((ρ j, c j) : Matrix I I ℂ × ℝ) = z i := fun i => hzS ⟨i, rfl⟩
  choose r hrz using hz
  let q : Fin (KK I) → ℝ := Function.extend e w 0
  let f : Fin (KK I) → Fin k := Function.extend e r (fun _ => ⟨0, hk⟩)
  have hq : ∀ i, q (e i) = w i := fun i => e.injective.extend_apply _ _ _
  have hf : ∀ i, f (e i) = r i := fun i => e.injective.extend_apply _ _ _
  have hq0 : ∀ j ∉ Set.range e, q j = 0 := fun j hj => by
    simp only [q]; rw [Function.extend_apply' _ _ _ (by simpa using hj)]; rfl
  have hs1 : ∑ j, q j = ∑ i, q (e i) :=
    (Fintype.sum_of_injective e e.injective _ _ (fun j hj => hq0 j hj) (fun i => rfl)).symm
  have hs2 : ∑ j, q j • ρ (f j) = ∑ i, q (e i) • ρ (f (e i)) :=
    (Fintype.sum_of_injective e e.injective _ (fun j => q j • ρ (f j))
      (fun j hj => by simp [hq0 j hj]) (fun i => rfl)).symm
  have hs3 : ∑ j, q j * c (f j) = ∑ i, q (e i) * c (f (e i)) :=
    (Fintype.sum_of_injective e e.injective _ (fun j => q j * c (f j))
      (fun j hj => by simp [hq0 j hj]) (fun i => rfl)).symm
  have hfst := congrArg Prod.fst hwz
  have hsnd := congrArg Prod.snd hwz
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hfst hsnd
  refine ⟨q, f, fun j => ?_, ?_, ?_, ?_⟩
  · by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj; rw [hq]; exact (hw i).le
    · rw [hq0 j hj]
  · rw [hs1]; simp only [hq]; exact hw1
  · rw [hs2]
    simp only [hq, hf]
    rw [← hfst]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hrz i]
  · rw [hs3]
    simp only [hq, hf]
    rw [← hsnd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hrz i]

/-- the two-level objective `g(avg) + Σ_x P_x a(ρ_x) - Σ_x P_x Σ_y Q_{xy} k(σ_{xy})`. -/
def F2 (g a k : Matrix I I ℂ → ℝ) {n m : ℕ} (P : Fin n → ℝ) (Q : Fin n → Fin m → ℝ)
    (S : Fin n → Fin m → Matrix I I ℂ) : ℝ :=
  g (∑ i, P i • ∑ j, Q i j • S i j) + ∑ i, P i * a (∑ j, Q i j • S i j) -
    ∑ i, P i * ∑ j, Q i j * k (S i j)

/-- every two-level objective value is matched by one with `KK × KK` members. -/
lemma red2 [Nonempty I] (g a k : Matrix I I ℂ → ℝ) {n m : ℕ} (P : Fin n → ℝ)
    (Q : Fin n → Fin m → ℝ) (S : Fin n → Fin m → Matrix I I ℂ) (hP : ∀ i, 0 ≤ P i)
    (hP1 : ∑ i, P i = 1) (hQ : ∀ i j, 0 ≤ Q i j) (hQ1 : ∀ i, ∑ j, Q i j = 1) :
    ∃ (p : Fin (KK I) → ℝ) (q : Fin (KK I) → Fin (KK I) → ℝ)
      (σ : Fin (KK I) → Fin (KK I) → Matrix I I ℂ),
      (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i j, 0 ≤ q i j) ∧ (∀ i, ∑ j, q i j = 1) ∧
      (∀ i j, ∃ x y, σ i j = S x y) ∧ F2 g a k p q σ = F2 g a k P Q S := by
  have hin : ∀ x, ∃ (q : Fin (KK I) → ℝ) (f : Fin (KK I) → Fin m), (∀ i, 0 ≤ q i) ∧
      ∑ i, q i = 1 ∧ ∑ i, q i • S x (f i) = ∑ j, Q x j • S x j ∧
      ∑ i, q i * k (S x (f i)) = ∑ j, Q x j * k (S x j) :=
    fun x => redI (Q x) (S x) (fun j => k (S x j)) (hQ x) (hQ1 x)
  choose q0 f0 hq0 hq01 hq0s hq0k using hin
  let ρ' : Fin n → Matrix I I ℂ := fun x => ∑ j, Q x j • S x j
  let c : Fin n → ℝ := fun x => a (ρ' x) - ∑ j, Q x j * k (S x j)
  obtain ⟨p, f, hp, hp1, hps, hpc⟩ := redI P ρ' c hP hP1
  refine ⟨p, fun i => q0 (f i), fun i j => S (f i) (f0 (f i) j), hp, hp1,
    fun i j => hq0 _ _, fun i => hq01 _, fun i j => ⟨_, _, rfl⟩, ?_⟩
  unfold F2
  simp only [hq0s, hq0k]
  have e1 : ∑ i, P i * a (∑ j, Q i j • S i j) - ∑ i, P i * ∑ j, Q i j * k (S i j) =
      ∑ i, P i * c i := by
    simp only [c, ρ', mul_sub, Finset.sum_sub_distrib]
  have e2 : ∑ i, p i * a (∑ j, Q (f i) j • S (f i) j) -
      ∑ i, p i * ∑ j, Q (f i) j * k (S (f i) j) = ∑ i, p i * c (f i) := by
    simp only [c, ρ', mul_sub, Finset.sum_sub_distrib]
  rw [add_sub_assoc, add_sub_assoc, e1, e2, hpc]
  congr 2

/-- maxima of two-level objectives are attained by `KK × KK` ensembles. -/
theorem att2 [Nonempty I] (g a k : Matrix I I ℂ → ℝ) (hg : ContinuousOn g (Dens I))
    (ha : ContinuousOn a (Dens I)) (hk : ContinuousOn k (Dens I)) :
    ∃ (p : Fin (KK I) → ℝ) (q : Fin (KK I) → Fin (KK I) → ℝ)
      (σ : Fin (KK I) → Fin (KK I) → Matrix I I ℂ),
      (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i j, 0 ≤ q i j) ∧ (∀ i, ∑ j, q i j = 1) ∧
      (∀ i j, σ i j ∈ Dens I) ∧
      ∀ (n m : ℕ) (P : Fin n → ℝ) (Q : Fin n → Fin m → ℝ) (S : Fin n → Fin m → Matrix I I ℂ),
        (∀ i, 0 ≤ P i) → ∑ i, P i = 1 → (∀ i j, 0 ≤ Q i j) → (∀ i, ∑ j, Q i j = 1) →
        (∀ i j, S i j ∈ Dens I) → F2 g a k P Q S ≤ F2 g a k p q σ := by
  let Ω : Set ((Fin (KK I) → ℝ) × (Fin (KK I) → Fin (KK I) → ℝ) ×
      (Fin (KK I) → Fin (KK I) → Matrix I I ℂ)) :=
    stdSimplex ℝ (Fin (KK I)) ×ˢ (Set.pi Set.univ (fun _ => stdSimplex ℝ (Fin (KK I))) ×ˢ
      Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Dens I)))
  have hΩ : IsCompact Ω := (isCompact_stdSimplex ℝ _).prod
    ((isCompact_univ_pi fun _ => isCompact_stdSimplex ℝ _).prod
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => dens_compact))
  have hmemΩ : ∀ x ∈ Ω, (∀ i, 0 ≤ x.1 i) ∧ ∑ i, x.1 i = 1 ∧ (∀ i j, 0 ≤ x.2.1 i j) ∧
      (∀ i, ∑ j, x.2.1 i j = 1) ∧ ∀ i j, x.2.2 i j ∈ Dens I := by
    rintro x ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, fun i => (h3 i (Set.mem_univ i)).1, fun i => (h3 i (Set.mem_univ i)).2,
      fun i j => h4 i (Set.mem_univ i) j (Set.mem_univ j)⟩
  have hinner : ∀ x ∈ Ω, ∀ i, ∑ j, x.2.1 i j • x.2.2 i j ∈ Dens I := by
    intro x hx i
    obtain ⟨-, -, h3, h4, h5⟩ := hmemΩ x hx
    exact dens_avg _ _ (h3 i) (h4 i) (h5 i)
  let F : ((Fin (KK I) → ℝ) × (Fin (KK I) → Fin (KK I) → ℝ) ×
      (Fin (KK I) → Fin (KK I) → Matrix I I ℂ)) → ℝ := fun x => F2 g a k x.1 x.2.1 x.2.2
  have hF : ContinuousOn F Ω := by
    refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) ?_
    · refine hg.comp (by fun_prop) fun x hx => ?_
      obtain ⟨h1, h2, -⟩ := hmemΩ x hx
      exact dens_avg _ _ h1 h2 (hinner x hx)
    · refine continuousOn_finsetSum _ fun i _ => ?_
      refine (continuous_apply i |>.comp continuous_fst).continuousOn.mul ?_
      exact ha.comp (by fun_prop) fun x hx => hinner x hx i
    · refine continuousOn_finsetSum _ fun i _ => ?_
      refine (continuous_apply i |>.comp continuous_fst).continuousOn.mul ?_
      refine continuousOn_finsetSum _ fun j _ => ?_
      refine (by fun_prop : Continuous fun x : ((Fin (KK I) → ℝ) × (Fin (KK I) → Fin (KK I) → ℝ) ×
        (Fin (KK I) → Fin (KK I) → Matrix I I ℂ)) => x.2.1 i j).continuousOn.mul ?_
      refine hk.comp (by fun_prop) fun x hx => (hmemΩ x hx).2.2.2.2 i j
  obtain ⟨ρ0, hρ0⟩ : ∃ ρ0 : Matrix I I ℂ, ρ0 ∈ Dens I := by
    obtain ⟨i0⟩ := ‹Nonempty I›
    refine ⟨Matrix.diagonal (fun i => if i = i0 then (1 : ℂ) else 0), ?_, ?_⟩
    · rw [Matrix.posSemidef_diagonal_iff]; intro i; split_ifs <;> norm_num
    · simp [Matrix.trace_diagonal]
  have hsimp : (Pi.single 0 1 : Fin (KK I) → ℝ) ∈ stdSimplex ℝ (Fin (KK I)) := by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases hi : i = 0
      · subst hi; simp
      · simp [hi]
    · simp
  have hne : Ω.Nonempty :=
    ⟨(Pi.single 0 1, fun _ => Pi.single 0 1, fun _ _ => ρ0),
      ⟨hsimp, fun _ _ => hsimp, fun _ _ _ _ => hρ0⟩⟩
  obtain ⟨x, hx, hmax⟩ := hΩ.exists_isMaxOn hne hF
  obtain ⟨h1, h2, h3, h4, h5⟩ := hmemΩ x hx
  refine ⟨x.1, x.2.1, x.2.2, h1, h2, h3, h4, h5, fun n m P Q S hP hP1 hQ hQ1 hS => ?_⟩
  obtain ⟨p, q, σ, hp, hp1, hq, hq1, hσ, heq⟩ := red2 g a k P Q S hP hP1 hQ hQ1
  have hy : (p, q, σ) ∈ Ω := ⟨⟨hp, hp1⟩, fun i _ => ⟨hq i, hq1 i⟩, fun i _ j _ => by
    obtain ⟨x', y', h⟩ := hσ i j; show σ i j ∈ Dens I; rw [h]; exact hS x' y'⟩
  have := hmax hy
  simp only [Set.mem_setOf_eq, F] at this
  rw [← heq]
  exact this

end X6AT


/-! X6 attainment library, part 4: ensembles whose members share a common first marginal. -/

open scoped Matrix ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
namespace X6AT
open Matrix

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- maxima of `g(Σ p ρ) - Σ p h(ρ)` over finite ensembles of densities with a common
`traceRight` are attained. -/
theorem attC [Nonempty P] [Nonempty Q] (g h : Matrix (P × Q) (P × Q) ℂ → ℝ)
    (hg : ContinuousOn g (Dens (P × Q))) (hh : ContinuousOn h (Dens (P × Q))) :
    ∃ (q : Fin (KK (P × Q)) → ℝ) (σ : Fin (KK (P × Q)) → Matrix (P × Q) (P × Q) ℂ),
      (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧ (∀ i, σ i ∈ Dens (P × Q)) ∧
      (∀ i j, QAlgorithms.traceRight (σ i) = QAlgorithms.traceRight (σ j)) ∧
      ∀ (k : ℕ) (p : Fin k → ℝ) (ρ : Fin k → Matrix (P × Q) (P × Q) ℂ), (∀ i, 0 ≤ p i) →
        ∑ i, p i = 1 → (∀ i, ρ i ∈ Dens (P × Q)) →
        (∀ i j, QAlgorithms.traceRight (ρ i) = QAlgorithms.traceRight (ρ j)) →
        g (∑ i, p i • ρ i) - ∑ i, p i * h (ρ i) ≤ g (∑ i, q i • σ i) - ∑ i, q i * h (σ i) := by
  let K := KK (P × Q)
  let C : Set (Fin K → Matrix (P × Q) (P × Q) ℂ) :=
    Set.pi Set.univ (fun _ => Dens (P × Q)) ∩
      ⋂ i, ⋂ j, {σ | QAlgorithms.traceRight (σ i) = QAlgorithms.traceRight (σ j)}
  have hC : IsCompact C := by
    refine (isCompact_univ_pi fun _ => dens_compact).inter_right ?_
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (traceRight_cont.comp (continuous_apply i))
        (traceRight_cont.comp (continuous_apply j))
  let Ω : Set ((Fin K → ℝ) × (Fin K → Matrix (P × Q) (P × Q) ℂ)) := stdSimplex ℝ (Fin K) ×ˢ C
  have hΩ : IsCompact Ω := (isCompact_stdSimplex ℝ _).prod hC
  let F : ((Fin K → ℝ) × (Fin K → Matrix (P × Q) (P × Q) ℂ)) → ℝ :=
    fun x => g (∑ i, x.1 i • x.2 i) - ∑ i, x.1 i * h (x.2 i)
  have hmemΩ : ∀ x ∈ Ω, (∀ i, 0 ≤ x.1 i) ∧ ∑ i, x.1 i = 1 ∧ (∀ i, x.2 i ∈ Dens (P × Q)) ∧
      ∀ i j, QAlgorithms.traceRight (x.2 i) = QAlgorithms.traceRight (x.2 j) := by
    rintro x ⟨⟨h1, h2⟩, h3, h4⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at h4
    exact ⟨h1, h2, fun i => h3 i (Set.mem_univ i), h4⟩
  have hF : ContinuousOn F Ω := by
    refine ContinuousOn.sub ?_ ?_
    · refine hg.comp (by fun_prop) fun x hx => ?_
      obtain ⟨h1, h2, h3, -⟩ := hmemΩ x hx
      exact dens_avg _ _ h1 h2 h3
    · refine continuousOn_finset_sum _ fun i _ => ?_
      refine (continuous_apply i |>.comp continuous_fst).continuousOn.mul ?_
      refine hh.comp (continuous_apply i |>.comp continuous_snd).continuousOn fun x hx => ?_
      exact (hmemΩ x hx).2.2.1 i
  obtain ⟨ρ0, hρ0⟩ : ∃ ρ0 : Matrix (P × Q) (P × Q) ℂ, ρ0 ∈ Dens (P × Q) := by
    obtain ⟨i0⟩ := (inferInstance : Nonempty (P × Q))
    refine ⟨Matrix.diagonal (fun i => if i = i0 then (1 : ℂ) else 0), ?_, ?_⟩
    · rw [Matrix.posSemidef_diagonal_iff]; intro i; split_ifs <;> norm_num
    · simp [Matrix.trace_diagonal]
  have hne : Ω.Nonempty := by
    refine ⟨(Pi.single 0 1, fun _ => ρ0), ⟨⟨fun i => ?_, ?_⟩, fun i _ => hρ0, ?_⟩⟩
    · by_cases hi : i = 0
      · subst hi; simp
      · simp [hi]
    · simp
    · simp
  obtain ⟨x, hx, hmax⟩ := hΩ.exists_isMaxOn hne hF
  obtain ⟨h1, h2, h3, h4⟩ := hmemΩ x hx
  refine ⟨x.1, x.2, h1, h2, h3, h4, fun k p ρ hp hp1 hρ hρm => ?_⟩
  obtain ⟨q, f, hq, hq1, havg, hsum⟩ := redI p ρ (fun i => h (ρ i)) hp hp1
  have hy : (q, fun i => ρ (f i)) ∈ Ω := by
    refine ⟨⟨hq, hq1⟩, fun i _ => hρ (f i), ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact fun i j => hρm _ _
  have := hmax hy
  simp only [Set.mem_setOf_eq, F] at this
  rw [havg, hsum] at this
  exact this

end X6AT


/-! Claimed50.P43, eq.(20): the common-Bob-marginal reformulation and attainment. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6AH
open Matrix X6SSA X6CH QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P43
open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage outputHolevo)

variable {A C : Type} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]
  [Nonempty A] [Nonempty C]

lemma idT_lin (N : Superop A C) (hN : IsChannel N) {J : Type} [Fintype J] [DecidableEq J] (c : J → ℂ)
    (M : J → Matrix (A × A) (A × A) ℂ) :
    idTensorSuperop (R := A) N (∑ j, c j • M j) = ∑ j, c j • idTensorSuperop (R := A) N (M j) := by
  obtain ⟨m', E, -, -, hNE⟩ := kraus_of_channel hN
  subst hNE
  have h1 := idT_kraus' (R := A) E
  rw [h1]
  exact kraus_lin (fun k => (1 : Matrix A A ℂ) ⊗ₖ E k) c M

lemma idT_cont (N : Superop A C) (hN : IsChannel N) :
    Continuous (idTensorSuperop (R := A) N) := by
  obtain ⟨m', E, -, -, hNE⟩ := kraus_of_channel hN
  rw [hNE, idT_kraus']
  unfold krausApply
  exact continuous_finsetSum _ fun k _ =>
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

lemma real_avg {I : Type*} [Fintype I] {k : ℕ} (p : Fin k → ℝ) (ρ : Fin k → Matrix I I ℂ) :
    ∑ i, p i • ρ i = ∑ i, (p i : ℂ) • ρ i := by
  simp only [Complex.coe_smul]

lemma idT_lin_real (N : Superop A C) (hN : IsChannel N) {k : ℕ} (p : Fin k → ℝ)
    (M : Fin k → Matrix (A × A) (A × A) ℂ) :
    idTensorSuperop (R := A) N (∑ j, p j • M j) = ∑ j, p j • idTensorSuperop (R := A) N (M j) := by
  rw [real_avg, real_avg, idT_lin N hN]

lemma vals_sub (N : Superop A C) (hN : IsChannel N) :
    assistedValues N ⊆ commonBobValues N := by
  rintro v ⟨m, e, rfl⟩
  have hψd : IsDensityMatrix (pureDensity e.resource) :=
    ⟨pd_psd _, pd_trace _ e.normalized⟩
  have henc : ∀ i, IsDensityMatrix (encodedAssistedState e i) := fun i =>
    chan_idT_dens _ (e.channel i) hψd
  let E : Ensemble (A × A) := ⟨m, e.prob, encodedAssistedState e, e.nonneg, e.total, henc⟩
  refine ⟨E, ⟨traceRight (pureDensity e.resource),
    ⟨X6AT.traceRight_psd hψd.1, (X6AT.trace_traceRight _).trans hψd.2⟩, fun i => ?_⟩, ?_⟩
  · exact chan_idT_trR _ (e.channel i) _
  · unfold assistedScore outputHolevo ensembleAverage
    simp only [E]
    rw [real_avg, idT_lin N hN]

lemma vals_sup (N : Superop A C) (hN : IsChannel N) :
    commonBobValues N ⊆ assistedValues N := by
  rintro v ⟨E, ⟨s, hs, hm⟩, rfl⟩
  obtain ⟨ψ, hψ, -, Φ, hΦ⟩ := X6CM.cmr s hs E.state E.density hm
  let e : AssistedEnsemble A E.size :=
    ⟨E.prob, E.nonneg, E.total, ψ, hψ, Φ, fun i => (hΦ i).1⟩
  refine ⟨E.size, e, ?_⟩
  have hst : ∀ i, encodedAssistedState e i = E.state i := fun i => ((hΦ i).2).symm
  show outputHolevo (idTensorSuperop (R := A) N) E = vnEntropy (∑ i, (E.prob i : ℂ) •
      idTensorSuperop (R := A) N (encodedAssistedState e i)) -
    ∑ i, E.prob i * vnEntropy (idTensorSuperop (R := A) N (encodedAssistedState e i))
  simp only [hst]
  unfold outputHolevo ensembleAverage
  rw [real_avg, idT_lin N hN]

lemma vals_eq (N : Superop A C) (hN : IsChannel N) :
    assistedValues N = commonBobValues N :=
  (vals_sub N hN).antisymm (vals_sup N hN)

theorem fixedBob (N : Superop A C) (hN : IsChannel N) :
    assistedOneShot N = sSup (commonBobValues N) ∧
    IsGreatest (commonBobValues N) (assistedOneShot N) ∧
    IsGreatest (assistedValues N) (assistedOneShot N) := by
  have hc := idT_cont N hN
  have hgc : ContinuousOn (fun ρ => vnEntropy (idTensorSuperop (R := A) N ρ))
      (X6AT.Dens (A × A)) :=
    X6AT.vn_contOn.comp hc.continuousOn fun ρ hρ => chan_idT_dens N hN hρ
  obtain ⟨q, σ, hq, hq1, hσ, hσm, hmax⟩ := X6AT.attC _ _ hgc hgc
  let E0 : Ensemble (A × A) := ⟨X6AT.KK (A × A), q, σ, hq, hq1, hσ⟩
  have h0 : 0 < X6AT.KK (A × A) := Nat.succ_pos _
  have hE0 : outputHolevo (idTensorSuperop (R := A) N) E0 ∈ commonBobValues N := by
    refine ⟨E0, ⟨traceRight (σ ⟨0, h0⟩),
      ⟨X6AT.traceRight_psd (hσ _).1, (X6AT.trace_traceRight _).trans (hσ _).2⟩,
      fun i => hσm i _⟩, rfl⟩
  have hG : IsGreatest (commonBobValues N) (outputHolevo (idTensorSuperop (R := A) N) E0) := by
    refine ⟨hE0, ?_⟩
    rintro v ⟨E, ⟨s, hs, hm⟩, rfl⟩
    have := hmax E.size E.prob E.state E.nonneg E.total E.density
      (fun i j => (hm i).trans (hm j).symm)
    exact this
  have hS : assistedOneShot N = outputHolevo (idTensorSuperop (R := A) N) E0 := by
    unfold assistedOneShot; rw [vals_eq N hN]; exact hG.csSup_eq
  rw [hS]
  refine ⟨hG.csSup_eq.symm, hG, ?_⟩
  rw [vals_eq N hN]; exact hG

end X6AH


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


/-! X6: faithfulness of quantum mutual information: `S(AB) = S(A) + S(B)` forces
`ρ_AB = ρ_A ⊗ ρ_B`. Proved in eigen-coordinates of the marginals. -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6MI
open Matrix X6SSA X6CH QAlgorithms Real

/-- pointwise Klein-type inequality with equality case. -/
lemma key (c p a b : ℝ) (hc : 0 ≤ c) (hp : 0 ≤ p) (ha : c * p ≤ a) (hb : c * p ≤ b)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    0 ≤ c * p * (log p - log a - log b) - c * (p - a * b) ∧
      (c * p * (log p - log a - log b) - c * (p - a * b) = 0 → c ≠ 0 → p = a * b) := by
  rcases hc.eq_or_lt with rfl | hc'
  · simp
  rcases hp.eq_or_lt with rfl | hp'
  · refine ⟨by simp; positivity, fun h hc0 => ?_⟩
    simp at h
    rcases h with h | h
    · exact absurd h hc0
    · rcases h with h | h <;> simp [h]
  have ha' : 0 < a := lt_of_lt_of_le (mul_pos hc' hp') ha
  have hb' : 0 < b := lt_of_lt_of_le (mul_pos hc' hp') hb
  have hab : 0 < a * b := mul_pos ha' hb'
  have hx : 0 < a * b / p := div_pos hab hp'
  have hlog : log (a * b / p) = log a + log b - log p := by
    rw [log_div hab.ne' hp'.ne', log_mul ha'.ne' hb'.ne']
  have e : c * p * (log p - log a - log b) - c * (p - a * b) =
      c * p * ((a * b / p - 1) - log (a * b / p)) := by
    rw [hlog]; field_simp; ring
  rw [e]
  have h1 := log_le_sub_one_of_pos hx
  refine ⟨mul_nonneg (mul_nonneg hc hp) (by linarith), fun h _ => ?_⟩
  by_contra hne
  have hx1 : a * b / p ≠ 1 := by
    intro h1; apply hne; field_simp at h1; linarith
  have h2 := log_lt_sub_one_of_pos hx hx1
  have : 0 < c * p * ((a * b / p - 1) - log (a * b / p)) :=
    mul_pos (mul_pos hc' hp') (by linarith)
  linarith

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma logb_eq (x : ℝ) : -(x * logb 2 x) = -(x * log x) / log 2 := by
  rw [logb]; ring

/-- the diagonal-marginal case. -/
theorem diag_case (N : Matrix (ι × κ) (ι × κ) ℂ) (hN : IsDensityMatrix N) (a : ι → ℝ) (b : κ → ℝ)
    (ha : trR N = diagonal (fun i => (a i : ℂ))) (hb : trF N = diagonal (fun k => (b k : ℂ)))
    (h : vnEntropy N = ∑ i, -(a i * logb 2 (a i)) + ∑ k, -(b k * logb 2 (b k))) :
    N = diagonal (fun x => ((a x.1 * b x.2 : ℝ) : ℂ)) := by
  have hH : N.IsHermitian := hN.1.1
  set V : Matrix (ι × κ) (ι × κ) ℂ := (hH.eigenvectorUnitary : Matrix (ι × κ) (ι × κ) ℂ) with hVdef
  set p := hH.eigenvalues with hpdef
  have hNe : ∀ y x, N y x = ∑ m, V y m * (p m : ℂ) * star (V x m) := by
    intro y x
    conv_lhs => rw [X6KR.spec hH]
    simp only [mul_apply, diagonal_apply, conjTranspose_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
    rfl
  have hVV : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hH.eigenvectorUnitary.2
  have hVV' : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hH.eigenvectorUnitary.2
  set c : (ι × κ) → (ι × κ) → ℝ := fun m x => Complex.normSq (V x m) with hcdef
  have hc0 : ∀ m x, 0 ≤ c m x := fun m x => Complex.normSq_nonneg _
  have hrow : ∀ x, ∑ m, c m x = 1 := by
    intro x
    have := congrFun (congrFun hVV x) x
    simp only [mul_apply, conjTranspose_apply, one_apply_eq] at this
    have h2 := congrArg Complex.re this
    simpa [c, Complex.normSq_apply, Complex.mul_conj, ← Complex.ofReal_sum] using h2
  have hcol : ∀ m, ∑ x, c m x = 1 := by
    intro m
    have := congrFun (congrFun hVV' m) m
    simp only [mul_apply, conjTranspose_apply, one_apply_eq] at this
    have h2 := congrArg Complex.re this
    simpa [c, Complex.normSq_apply, mul_comm, Complex.mul_conj, ← Complex.ofReal_sum] using h2
  have hp0 : ∀ m, 0 ≤ p m := hN.1.eigenvalues_nonneg
  have hdiag : ∀ x, (N x x).re = ∑ m, p m * c m x := by
    intro x
    rw [hNe, Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm (V x m), mul_assoc]
    simp [c, Complex.mul_conj]
  have hai : ∀ i, a i = ∑ k, ∑ m, p m * c m (i, k) := by
    intro i
    have := congrArg Complex.re (congrFun (congrFun ha i) i)
    simp only [trR, of_apply, diagonal_apply_eq, Complex.ofReal_re, Complex.re_sum] at this
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => hdiag _
  have hbk : ∀ k, b k = ∑ i, ∑ m, p m * c m (i, k) := by
    intro k
    have := congrArg Complex.re (congrFun (congrFun hb k) k)
    simp only [trF, of_apply, diagonal_apply_eq, Complex.ofReal_re, Complex.re_sum] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => hdiag _
  have htr : ∑ x, (N x x).re = 1 := by
    have := congrArg Complex.re hN.2
    simpa [trace, Complex.re_sum] using this
  have hsa : ∑ i, a i = 1 := by
    rw [← htr, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => by rw [hai]; exact Finset.sum_congr rfl fun k _ => (hdiag _).symm
  have hsb : ∑ k, b k = 1 := by
    rw [← htr, Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by rw [hbk]; exact Finset.sum_congr rfl fun i _ => (hdiag _).symm
  have hsp : ∑ m, p m = 1 := by
    rw [← htr]
    simp only [hdiag]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => by rw [← Finset.mul_sum, hcol, mul_one]
  have ha0 : ∀ i, 0 ≤ a i := fun i => by
    rw [hai]; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun m _ => mul_nonneg (hp0 m) (hc0 _ _)
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    rw [hbk]; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun m _ => mul_nonneg (hp0 m) (hc0 _ _)
  -- entropy identity in nats
  have hS : ∑ m, p m * log (p m) = ∑ i, a i * log (a i) + ∑ k, b k * log (b k) := by
    rw [vn_eig hH] at h
    simp only [logb_eq, ← Finset.sum_div] at h
    have hl : (0 : ℝ) < log 2 := log_pos (by norm_num)
    rw [← add_div, div_left_inj' hl.ne'] at h
    simp only [Finset.sum_neg_distrib] at h
    linarith
  set T : (ι × κ) → (ι × κ) → ℝ := fun x m =>
    c m x * p m * (log (p m) - log (a x.1) - log (b x.2)) - c m x * (p m - a x.1 * b x.2) with hT
  have hcpa : ∀ x m, c m x * p m ≤ a x.1 := by
    intro x m
    rw [hai]
    calc c m x * p m = p m * c m (x.1, x.2) := by ring
      _ ≤ ∑ m', p m' * c m' (x.1, x.2) :=
          Finset.single_le_sum (f := fun m' => p m' * c m' (x.1, x.2))
            (fun m' _ => mul_nonneg (hp0 m') (hc0 _ _)) (Finset.mem_univ m)
      _ ≤ ∑ k, ∑ m', p m' * c m' (x.1, k) :=
          Finset.single_le_sum (f := fun k => ∑ m', p m' * c m' (x.1, k))
            (fun k _ => Finset.sum_nonneg fun m' _ => mul_nonneg (hp0 m') (hc0 _ _))
            (Finset.mem_univ x.2)
  have hcpb : ∀ x m, c m x * p m ≤ b x.2 := by
    intro x m
    rw [hbk]
    calc c m x * p m = p m * c m (x.1, x.2) := by ring
      _ ≤ ∑ m', p m' * c m' (x.1, x.2) :=
          Finset.single_le_sum (f := fun m' => p m' * c m' (x.1, x.2))
            (fun m' _ => mul_nonneg (hp0 m') (hc0 _ _)) (Finset.mem_univ m)
      _ ≤ ∑ i, ∑ m', p m' * c m' (i, x.2) :=
          Finset.single_le_sum (f := fun i => ∑ m', p m' * c m' (i, x.2))
            (fun i _ => Finset.sum_nonneg fun m' _ => mul_nonneg (hp0 m') (hc0 _ _))
            (Finset.mem_univ x.1)
  have hT0 : ∀ x m, 0 ≤ T x m := fun x m =>
    (key _ _ _ _ (hc0 m x) (hp0 m) (hcpa x m) (hcpb x m) (ha0 _) (hb0 _)).1
  have hsum : ∑ x, ∑ m, T x m = 0 := by
    have e1 : ∑ x, ∑ m, c m x * p m * log (p m) = ∑ m, p m * log (p m) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hcol, one_mul]
    have e2 : ∑ x, ∑ m, c m x * p m * log (a x.1) = ∑ i, a i * log (a i) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show a i * log (a i) = (∑ k, ∑ m, p m * c m (i, k)) * log (a i) by rw [← hai],
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by dsimp only; ring
    have e3 : ∑ x, ∑ m, c m x * p m * log (b x.2) = ∑ k, b k * log (b k) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show b k * log (b k) = (∑ i, ∑ m, p m * c m (i, k)) * log (b k) by rw [← hbk],
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by dsimp only; ring
    have e4 : ∑ x, ∑ m, c m x * p m = 1 := by
      rw [Finset.sum_comm, ← hsp]
      exact Finset.sum_congr rfl fun m _ => by rw [← Finset.sum_mul, hcol, one_mul]
    have e5 : ∑ x, ∑ m, c m x * (a x.1 * b x.2) = 1 := by
      have : ∑ x : ι × κ, a x.1 * b x.2 = 1 := by
        rw [Fintype.sum_prod_type]; simp only [← Finset.mul_sum, ← Finset.sum_mul, hsb, hsa, mul_one]
      rw [← this]
      exact Finset.sum_congr rfl fun x _ => by rw [← Finset.sum_mul, hrow, one_mul]
    simp only [hT, mul_sub, Finset.sum_sub_distrib]
    rw [e1, e2, e3]
    have e4' : ∑ x, ∑ m, c m x * p m = ∑ x, ∑ m, c m x * p m := rfl
    simp only [e4, e5] at *
    linarith
  have hTz : ∀ x m, T x m = 0 := by
    intro x m
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Finset.sum_nonneg fun m _ => hT0 x m)).1
      hsum x (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => hT0 x m)).1 h1 m (Finset.mem_univ _)
  have hpq : ∀ x m, V x m ≠ 0 → p m = a x.1 * b x.2 := by
    intro x m hV
    refine (key _ _ _ _ (hc0 m x) (hp0 m) (hcpa x m) (hcpb x m) (ha0 _) (hb0 _)).2 (hTz x m) ?_
    simpa [c] using hV
  ext y x
  rw [hNe, diagonal_apply]
  have : ∑ m, V y m * (p m : ℂ) * star (V x m) =
      ((a x.1 * b x.2 : ℝ) : ℂ) * ∑ m, V y m * star (V x m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hV : V x m = 0
    · simp [hV]
    · rw [hpq x m hV]; ring
  rw [this]
  have h2 := congrFun (congrFun hVV y) x
  simp only [mul_apply, conjTranspose_apply, one_apply] at h2
  rw [h2]
  split_ifs with hyx
  · subst hyx; simp
  · simp

section kron
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma kron1_entry (X Y : Matrix I I ℂ) (M : Matrix (I × J) (I × J) ℂ) (p q : I × J) :
    ((X ⊗ₖ (1 : Matrix J J ℂ)) * M * (Y ⊗ₖ (1 : Matrix J J ℂ))ᴴ) p q =
      ∑ x, ∑ x', X p.1 x * M (x, p.2) (x', q.2) * star (Y q.1 x') := by
  rw [conjTranspose_kronecker, conjTranspose_one]
  simp only [mul_apply, kroneckerMap_apply, one_apply, conjTranspose_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma kron2_entry (X Y : Matrix J J ℂ) (M : Matrix (I × J) (I × J) ℂ) (p q : I × J) :
    (((1 : Matrix I I ℂ) ⊗ₖ X) * M * ((1 : Matrix I I ℂ) ⊗ₖ Y)ᴴ) p q =
      ∑ x, ∑ x', X p.2 x * M (p.1, x) (q.1, x') * star (Y q.2 x') := by
  rw [conjTranspose_kronecker, conjTranspose_one]
  simp only [mul_apply, kroneckerMap_apply, one_apply, conjTranspose_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, one_mul, mul_zero, zero_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Finset.sum_comm (γ := I), Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]

lemma mul3_entry {P Q : Type*} [Fintype Q] (X : Matrix P Q ℂ) (B : Matrix Q Q ℂ) (Y : Matrix P Q ℂ)
    (i j : P) : (X * B * Yᴴ) i j = ∑ x, ∑ x', X i x * B x x' * star (Y j x') := by
  simp only [mul_apply, conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma trR_k1 (X : Matrix I I ℂ) (ρ : Matrix (I × J) (I × J) ℂ) :
    trR ((X ⊗ₖ (1 : Matrix J J ℂ)) * ρ * (X ⊗ₖ (1 : Matrix J J ℂ))ᴴ) = X * trR ρ * Xᴴ := by
  ext i i'
  rw [mul3_entry]
  simp only [trR, of_apply, kron1_entry, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]

lemma trF_k2 (X : Matrix J J ℂ) (ρ : Matrix (I × J) (I × J) ℂ) :
    trF (((1 : Matrix I I ℂ) ⊗ₖ X) * ρ * ((1 : Matrix I I ℂ) ⊗ₖ X)ᴴ) = X * trF ρ * Xᴴ := by
  ext i i'
  rw [mul3_entry]
  simp only [trF, of_apply, kron2_entry, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]

lemma trR_k2 (B : Matrix J J ℂ) (hB : Bᴴ * B = 1) (ρ : Matrix (I × J) (I × J) ℂ) :
    trR (((1 : Matrix I I ℂ) ⊗ₖ B) * ρ * ((1 : Matrix I I ℂ) ⊗ₖ B)ᴴ) = trR ρ := by
  ext i i'
  simp only [trR, of_apply, kron2_entry]
  have hB' : ∀ x' x, ∑ k, star (B k x') * B k x = if x' = x then 1 else 0 := by
    intro x' x
    have := congrFun (congrFun hB x') x
    simpa [mul_apply, one_apply] using this
  calc ∑ k, ∑ x, ∑ x', B k x * ρ (i, x) (i', x') * star (B k x')
      = ∑ x, ∑ x', (∑ k, star (B k x') * B k x) * ρ (i, x) (i', x') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x' _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ x, ρ (i, x) (i', x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [hB', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma trF_k1 (A : Matrix I I ℂ) (hA : Aᴴ * A = 1) (ρ : Matrix (I × J) (I × J) ℂ) :
    trF ((A ⊗ₖ (1 : Matrix J J ℂ)) * ρ * (A ⊗ₖ (1 : Matrix J J ℂ))ᴴ) = trF ρ := by
  ext j j'
  simp only [trF, of_apply, kron1_entry]
  have hA' : ∀ x' x, ∑ k, star (A k x') * A k x = if x' = x then 1 else 0 := by
    intro x' x
    have := congrFun (congrFun hA x') x
    simpa [mul_apply, one_apply] using this
  calc ∑ k, ∑ x, ∑ x', A k x * ρ (x, j) (x', j') * star (A k x')
      = ∑ x, ∑ x', (∑ k, star (A k x') * A k x) * ρ (x, j) (x', j') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x' _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ x, ρ (x, j) (x, j') := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [hA', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma trR_psd' {ρ : Matrix (I × J) (I × J) ℂ} (h : ρ.PosSemidef) : (trR ρ).PosSemidef := by
  have := marg_psd (Equiv.refl (I × J)) h
  simpa [marg] using this

lemma conj_mul {n : Type*} [Fintype n] (A B M : Matrix n n ℂ) :
    (A * B) * M * (A * B)ᴴ = A * (B * M * Bᴴ) * Aᴴ := by
  rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]

end kron

/-- **Faithfulness of mutual information.** -/
theorem faithful (M : Matrix (ι × κ) (ι × κ) ℂ) (hM : IsDensityMatrix M)
    (h : vnEntropy M = vnEntropy (trR M) + vnEntropy (trF M)) : M = trR M ⊗ₖ trF M := by
  have hR : (trR M).PosSemidef := trR_psd' hM.1
  have hF : (trF M).PosSemidef := trF_psd hM.1
  set X : Matrix ι ι ℂ := (hR.1.eigenvectorUnitary : Matrix ι ι ℂ) with hXd
  set Y : Matrix κ κ ℂ := (hF.1.eigenvectorUnitary : Matrix κ κ ℂ) with hYd
  have hX : Xᴴ * X = 1 := X6KR.unit_iso _
  have hY : Yᴴ * Y = 1 := X6KR.unit_iso _
  have hX' : X * Xᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hR.1.eigenvectorUnitary.2
  have hY' : Y * Yᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hF.1.eigenvectorUnitary.2
  set Da : Matrix ι ι ℂ := diagonal (fun i => ((hR.1.eigenvalues i : ℝ) : ℂ))
  set Db : Matrix κ κ ℂ := diagonal (fun i => ((hF.1.eigenvalues i : ℝ) : ℂ))
  have sR : trR M = X * Da * Xᴴ := X6KR.spec hR.1
  have sF : trF M = Y * Db * Yᴴ := X6KR.spec hF.1
  set W : Matrix (ι × κ) (ι × κ) ℂ := Xᴴ ⊗ₖ Yᴴ with hWd
  have hW1 : W = (Xᴴ ⊗ₖ (1 : Matrix κ κ ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ Yᴴ) := by
    rw [hWd, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hW2 : W = ((1 : Matrix ι ι ℂ) ⊗ₖ Yᴴ) * (Xᴴ ⊗ₖ (1 : Matrix κ κ ℂ)) := by
    rw [hWd, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hWW : Wᴴ * W = 1 := by
    rw [hWd, conjTranspose_kronecker, conjTranspose_conjTranspose, conjTranspose_conjTranspose,
      ← mul_kronecker_mul, hX', hY', one_kronecker_one]
  have hWW' : W * Wᴴ = 1 := by
    rw [hWd, conjTranspose_kronecker, conjTranspose_conjTranspose, conjTranspose_conjTranspose,
      ← mul_kronecker_mul, hX, hY, one_kronecker_one]
  set N := W * M * Wᴴ with hNd
  have hNR : trR N = Da := by
    rw [hNd, hW1, conj_mul, trR_k1,
      trR_k2 _ (by rw [conjTranspose_conjTranspose]; exact hY'), sR]
    simp only [conjTranspose_conjTranspose, ← Matrix.mul_assoc, hX, Matrix.one_mul]
    rw [Matrix.mul_assoc, hX, Matrix.mul_one]
  have hNF : trF N = Db := by
    rw [hNd, hW2, conj_mul, trF_k2,
      trF_k1 _ (by rw [conjTranspose_conjTranspose]; exact hX'), sF]
    simp only [conjTranspose_conjTranspose, ← Matrix.mul_assoc, hY, Matrix.one_mul]
    rw [Matrix.mul_assoc, hY, Matrix.mul_one]
  have hNd' : IsDensityMatrix N := by
    refine ⟨hM.1.mul_mul_conjTranspose_same W, ?_⟩
    rw [hNd, Matrix.trace_mul_cycle, hWW, Matrix.one_mul, hM.2]
  have hSN : vnEntropy N = vnEntropy M := X6CH.vn_iso W hWW M hM.1
  have hdiag := diag_case N hNd' _ _ hNR hNF (by
    rw [hSN, h, vn_eig hR.1, vn_eig hF.1])
  have hND : N = Da ⊗ₖ Db := by
    rw [hdiag, diagonal_kronecker_diagonal]
    congr 1; funext x; push_cast; rfl
  have hMN : M = Wᴴ * N * W := by
    rw [hNd]; simp only [← Matrix.mul_assoc, hWW, Matrix.one_mul]
    rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
  conv_lhs => rw [hMN, hND]
  rw [sR, sF, hWd, conjTranspose_kronecker, conjTranspose_conjTranspose,
    conjTranspose_conjTranspose, ← mul_kronecker_mul, ← mul_kronecker_mul]

end X6MI


/-! X6: weak monotonicity `S(A) + S(E) ≤ S(AB) + S(BE)` for a density on `(A × B) × E`,
from SSA applied to the canonical purification. -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6WM
open Matrix X6SSA X6CH QAlgorithms

variable {A B E : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype E] [DecidableEq E]

lemma vn_any' {ι : Type*} [Fintype ι] (d d' : DecidableEq ι) (M : Matrix ι ι ℂ) :
    @vnEntropy ι _ d M = @vnEntropy ι _ d' M := by
  cases Subsingleton.elim d d'; rfl

/-- the purification vector `w (x, r) = √σ x r`. -/
def pv {X : Type*} [Fintype X] [DecidableEq X] (σ : Matrix X X ℂ) : EuclideanSpace ℂ (X × X) :=
  WithLp.toLp 2 fun p => cfc Real.sqrt σ p.1 p.2

lemma pv_sum {X : Type*} [Fintype X] [DecidableEq X] {σ : Matrix X X ℂ} (hσ : σ.PosSemidef)
    (x x' : X) : ∑ r, pureDensity (pv σ) (x, r) (x', r) = σ x x' := by
  have h := congrFun (congrFun (sqrt_sq hσ) x) x'
  rw [← h, mul_apply]
  simp [pureDensity, pv, conjTranspose_apply]

/-- the four splittings. -/
def Φ : ((A × B) × E) × ((A × B) × E) ≃ (((A × B) × E) × (B × E)) × A where
  toFun p := ((p.2, (p.1.1.2, p.1.2)), p.1.1.1)
  invFun q := (((q.2, q.1.2.1), q.1.2.2), q.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

def ΦAB : ((A × B) × E) × ((A × B) × E) ≃ (A × B) × (E × ((A × B) × E)) where
  toFun p := (p.1.1, (p.1.2, p.2))
  invFun q := ((q.1, q.2.1), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def ΦBE : ((A × B) × E) × ((A × B) × E) ≃ (B × E) × (A × ((A × B) × E)) where
  toFun p := ((p.1.1.2, p.1.2), (p.1.1.1, p.2))
  invFun q := (((q.2.1, q.1.1), q.1.2), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def ΦE : ((A × B) × E) × ((A × B) × E) ≃ E × ((A × B) × ((A × B) × E)) where
  toFun p := (p.1.2, (p.1.1, p.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def ΦA : ((A × B) × E) × ((A × B) × E) ≃ A × ((B × E) × ((A × B) × E)) where
  toFun p := (p.1.1.1, ((p.1.1.2, p.1.2), p.2))
  invFun q := (((q.1, q.2.1.1), q.2.1.2), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem wm [Nonempty A] [Nonempty B] [Nonempty E] (σ : Matrix ((A × B) × E) ((A × B) × E) ℂ)
    (hσ : σ.PosSemidef) (htr : trace σ = 1) :
    vnEntropy (traceRight (traceRight σ)) + vnEntropy (traceLeft σ) ≤
      vnEntropy (traceRight σ) +
        vnEntropy (Matrix.of fun p q : B × E => ∑ a, σ ((a, p.1), p.2) ((a, q.1), q.2)) := by
  have : Nonempty ((A × B) × E) := inferInstance
  set P := pureDensity (pv σ)
  have hP : P.PosSemidef := pd_psd _
  have hPt : trace P = 1 := by
    rw [← htr, trace, trace, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => pv_sum hσ x x
  have eAB : marg ΦAB P = traceRight σ := by
    ext x x'
    simp only [traceRight, traceLeft, of_apply]
    simp_rw [← pv_sum hσ]
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type, ΦAB, Equiv.coe_fn_symm_mk, P]
  have eBE : marg ΦBE P = Matrix.of fun p q : B × E => ∑ a, σ ((a, p.1), p.2) ((a, q.1), q.2) := by
    ext x x'
    simp only [traceRight, traceLeft, of_apply]
    simp_rw [← pv_sum hσ]
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type, ΦBE, Equiv.coe_fn_symm_mk, P]
  have eE : marg ΦE P = traceLeft σ := by
    ext x x'
    simp only [traceRight, traceLeft, of_apply]
    simp_rw [← pv_sum hσ]
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type, ΦE, Equiv.coe_fn_symm_mk, P]
  have eA : marg ΦA P = traceRight (traceRight σ) := by
    ext x x'
    simp only [traceRight, traceLeft, of_apply]
    simp_rw [← pv_sum hσ]
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type, ΦA, Equiv.coe_fn_symm_mk, P]
  have h := ssa_split (Φ (A := A) (B := B) (E := E)) P hP hPt
  rw [pure_comp ((Φ (A := A) (B := B) (E := E)).trans r21), pure_comp (Φ (A := A) (B := B) (E := E))] at h
  rw [vn_marg_eq ΦAB (((Φ (A := A) (B := B) (E := E)).trans r21).trans (Equiv.prodComm _ _)) ?_ ?_ hP,
    vn_marg_eq ΦBE ((Φ (A := A) (B := B) (E := E)).trans r31) ?_ ?_ hP,
    vn_marg_eq ΦE ((Φ (A := A) (B := B) (E := E)).trans r1) ?_ ?_ hP,
    vn_marg_eq ΦA ((Φ (A := A) (B := B) (E := E)).trans (Equiv.prodComm _ _)) ?_ ?_ hP,
    eAB, eBE, eE, eA] at h
  · linarith
  all_goals intro ω ω'
  all_goals simp only [Φ, ΦAB, ΦBE, ΦE, ΦA, r21, r31, r1, Equiv.coe_fn_mk, Equiv.trans_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Prod.ext_iff, Equiv.refl_apply]
  all_goals (try simp)
  all_goals (try tauto)

end X6WM


/-! X6: the pinching inequality `S(X) ≤ S(diag X)` and the entropies of a generalized
dephasing channel `X ↦ Σ_e D_e X D_eᴴ`, `D_e = diag(env · e)`, applied to a pure state. -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6DP
open Matrix X6SSA X6CH QAlgorithms

variable {A E R : Type*} [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E]
  [Fintype R] [DecidableEq R]

/-- sign diagonal unitary. -/
def Ds (s : A → Bool) : Matrix A A ℂ := diagonal fun a => sg (s a)

lemma Ds_iso (s : A → Bool) : (Ds s)ᴴ * Ds s = 1 := by
  rw [Ds, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext a
  simp [star_sg, sg_mul_self]

lemma Ds_conj_apply (s : A → Bool) (X : Matrix A A ℂ) (a b : A) :
    (Ds s * X * (Ds s)ᴴ) a b = X a b * (sg (s a) * sg (s b)) := by
  rw [Ds, diagonal_conjTranspose, mul_diagonal, diagonal_mul]
  simp [star_sg]; ring

/-- pinching: the entropy of a density does not exceed that of its diagonal. -/
theorem pinch [Nonempty A] {X : Matrix A A ℂ} (hX : IsDensityMatrix X) :
    vnEntropy X ≤ vnEntropy (diagonal fun a => X a a) := by
  set N := Fintype.card A
  set w : (A → Bool) → ℝ := fun _ => 1 / 2 ^ N
  have hw : ∀ s, 0 ≤ w s := fun _ => by positivity
  have hcard : (Fintype.card (A → Bool) : ℝ) = 2 ^ N := by
    simp [Fintype.card_fun, Fintype.card_bool, N]
  have hw1 : ∑ s, w s = 1 := by
    simp only [w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
  have hσ : ∀ s, IsDensityMatrix (Ds s * X * (Ds s)ᴴ) := fun s =>
    ⟨hX.1.mul_mul_conjTranspose_same _, by
      rw [trace_mul_comm, ← Matrix.mul_assoc, Ds_iso, Matrix.one_mul, hX.2]⟩
  have h := ent_concave w hw hw1 (fun s => Ds s * X * (Ds s)ᴴ) hσ
  have hmix : ∑ s, (w s : ℂ) • (Ds s * X * (Ds s)ᴴ) = diagonal fun a => X a a := by
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Ds_conj_apply]
    have : ∀ s : A → Bool, (w s : ℂ) * (X a b * (sg (s a) * sg (s b))) =
        ((1 / 2 ^ N : ℝ) : ℂ) * X a b * (sg (s a) * sg (s b)) := fun s => by ring
    rw [Finset.sum_congr rfl fun s _ => this s, ← Finset.mul_sum, sg_sum]
    by_cases hab : a = b
    · subst hab; simp only [if_true, diagonal_apply_eq]
      push_cast; field_simp; simp only [N]; ring
    · simp [hab]
  rw [hmix] at h
  have e : ∀ s, vnEntropy (Ds s * X * (Ds s)ᴴ) = vnEntropy X := fun s => vn_iso _ (Ds_iso s) _ hX.1
  simp only [e, ← Finset.sum_mul, hw1, one_mul] at h
  exact h

/-- Kraus operators of the generalized dephasing channel. -/
def Ek (env : A → EuclideanSpace ℂ E) (e : E) : Matrix A A ℂ := diagonal fun a => env a e

lemma Ek_kraus (env : A → EuclideanSpace ℂ E) (henv : ∀ a, ‖env a‖ = 1) :
    ∑ e, (Ek env e)ᴴ * Ek env e = 1 := by
  simp only [Ek, diagonal_conjTranspose, diagonal_mul_diagonal]
  rw [← diagonal_one]
  ext a b
  simp only [Matrix.sum_apply, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp only [if_true, Pi.star_apply]
    have h := EuclideanSpace.norm_sq_eq (env a)
    rw [henv a] at h
    have : ∑ e, star (env a e) * env a e = ((∑ e, ‖env a e‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj']
    rw [this, ← h]; simp
  · simp [hab]

lemma Ek_apply (env : A → EuclideanSpace ℂ E) (X : Matrix A A ℂ) (a b : A) :
    krausApply (Ek env) X a b = ∑ e, env a e * X a b * star (env b e) := by
  simp only [krausApply, Matrix.sum_apply, Ek, diagonal_conjTranspose, mul_diagonal, diagonal_mul,
    Pi.star_apply]

lemma Ek_diag (env : A → EuclideanSpace ℂ E) (henv : ∀ a, ‖env a‖ = 1) (X : Matrix A A ℂ) (a : A) :
    krausApply (Ek env) X a a = X a a := by
  have h := congrFun (congrFun (Ek_kraus env henv) a) a
  simp only [Matrix.sum_apply, Ek, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_apply_eq,
    one_apply_eq, Pi.star_apply] at h
  rw [Ek_apply]
  calc ∑ e, env a e * X a a * star (env a e) = X a a * ∑ e, star (env a e) * env a e := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring
    _ = X a a := by rw [h, mul_one]

/-- the channel only sees the diagonal through the complementary output. -/
lemma comp_Ek (env : A → EuclideanSpace ℂ E) (X : Matrix A A ℂ) :
    X6CH.comp (Ek env) X = ∑ a, X a a • pureDensity (env a) := by
  ext e e'
  simp only [X6CH.comp, of_apply, Ek, diagonal_conjTranspose, mul_diagonal, diagonal_mul, trace,
    diag_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pureDensity, Pi.star_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.smul_apply, of_apply, smul_eq_mul, Complex.star_def]; ring

lemma traceRight_idT (env : A → EuclideanSpace ℂ E) (henv : ∀ a, ‖env a‖ = 1)
    (Y : Matrix (R × A) (R × A) ℂ) :
    traceRight (idTensorSuperop (krausApply (Ek env)) Y) = traceRight Y := by
  ext r r'
  have h := kraus_trace (Ek env) (Ek_kraus env henv) (Matrix.of fun i i' => Y (r, i) (r', i'))
  simp only [trace, diag_apply, of_apply] at h
  simpa only [traceRight, idTensorSuperop, of_apply] using h

lemma traceLeft_idT (env : A → EuclideanSpace ℂ E) (Y : Matrix (R × A) (R × A) ℂ) :
    traceLeft (idTensorSuperop (krausApply (Ek env)) Y) = krausApply (Ek env) (traceLeft Y) := by
  ext a b
  simp only [traceLeft, idTensorSuperop, of_apply, Ek_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

/-- `ψ ↦ Ψ` with `vecOf Ψ = ψ`. -/
def mOf (v : EuclideanSpace ℂ (R × A)) : Matrix A R ℂ := of fun a r => v (r, a)

lemma vecOf_mOf (v : EuclideanSpace ℂ (R × A)) : vecOf (mOf v) = v := rfl

lemma mOf_mul (v : EuclideanSpace ℂ (R × A)) : mOf v * (mOf v)ᴴ = traceLeft (pureDensity v) := by
  ext a b
  simp [mOf, mul_apply, traceLeft, pureDensity, conjTranspose_apply]

/-- the three entropies of `(id ⊗ N)(vv*)`. -/
theorem entropies [Nonempty A] [Nonempty E] [Nonempty R] (env : A → EuclideanSpace ℂ E)
    (henv : ∀ a, ‖env a‖ = 1) (v : EuclideanSpace ℂ (R × A)) :
    vnEntropy (traceRight (idTensorSuperop (krausApply (Ek env)) (pureDensity v))) =
        vnEntropy (traceLeft (pureDensity v)) ∧
      traceLeft (idTensorSuperop (krausApply (Ek env)) (pureDensity v)) =
        krausApply (Ek env) (traceLeft (pureDensity v)) ∧
      vnEntropy (idTensorSuperop (krausApply (Ek env)) (pureDensity v)) =
        vnEntropy (∑ a, traceLeft (pureDensity v) a a • pureDensity (env a)) := by
  refine ⟨?_, traceLeft_idT env _, ?_⟩
  · rw [traceRight_idT env henv]
    exact vn_pure_marginals v
  · have h := sc (mOf v) (Ek env)
    rw [vecOf_mOf, mOf_mul, comp_Ek] at h
    exact h

end X6DP


/-! X6: classical and quantum Fano inequalities:
`S(σ) ≤ h₂(F) + (1 - F) log₂(d - 1)` with `F = ⟨ψ|σ|ψ⟩`. -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6FN
open Matrix X6SSA X6CH QAlgorithms Real

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- classical Fano bound. -/
lemma cfano (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) (i0 : Ω) :
    ∑ i, negMulLog (p i) ≤
      negMulLog (p i0) + negMulLog (1 - p i0) + (1 - p i0) * log (Fintype.card Ω - 1) := by
  set S := Finset.univ.erase i0
  have hsplit : ∀ f : Ω → ℝ, ∑ i, f i = f i0 + ∑ i ∈ S, f i := fun f =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ i0)).symm
  have hq : ∑ i ∈ S, p i = 1 - p i0 := by have := hsplit p; linarith
  have hn : ((S.card : ℕ) : ℝ) = Fintype.card Ω - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Nat.cast_sub (Fintype.card_pos_iff.2 ⟨i0⟩), Nat.cast_one]
  rw [hsplit, ← hn, ← hq]
  set q := ∑ i ∈ S, p i
  suffices h : ∑ i ∈ S, negMulLog (p i) ≤ negMulLog q + q * log (S.card : ℝ) by linarith
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [Finset.card_eq_zero] at h0
    simp [q, h0]
  have hnr : (0 : ℝ) < S.card := by exact_mod_cast hpos
  have hj := concaveOn_negMulLog.le_map_sum (t := S) (w := fun _ => (1 / S.card : ℝ)) (p := p)
    (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun i _ => Set.mem_Ici.2 (hp i))
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  have key : (S.card : ℝ) * negMulLog (1 / S.card * q) = negMulLog q + q * log S.card := by
    rcases (show 0 ≤ q from Finset.sum_nonneg fun i _ => hp i).eq_or_lt with hq0 | hq0
    · rw [← hq0]; simp
    · simp only [negMulLog, one_div]
      rw [Real.log_mul (inv_ne_zero hnr.ne') hq0.ne', Real.log_inv]
      field_simp
      ring
  rw [← key]
  have := mul_le_mul_of_nonneg_left hj hnr.le
  rwa [← mul_assoc, mul_one_div_cancel hnr.ne', one_mul] at this

/-- quantum Fano bound. -/
theorem qfano [Nonempty Ω] {σ : Matrix Ω Ω ℂ} (hσ : IsDensityMatrix σ) (ψ : EuclideanSpace ℂ Ω)
    (hψ : ‖ψ‖ = 1) :
    vnEntropy σ ≤ binEntropy2 (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re +
      (1 - (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re) * logb 2 (Fintype.card Ω - 1) := by
  obtain ⟨i0⟩ := ‹Nonempty Ω›
  have hv : Orthonormal ℂ (({i0} : Set Ω).domRestrict fun _ => ψ) := by
    refine ⟨fun _ => hψ, fun i j hij => ?_⟩
    exact absurd (Subtype.ext ((Set.mem_singleton_iff.1 i.2).trans
      (Set.mem_singleton_iff.1 j.2).symm)) hij
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b i0 = ψ := hb i0 rfl
  set W : Matrix Ω Ω ℂ := of fun a i => b i a
  have hW : Wᴴ * W = 1 := by
    ext i j
    have h := orthonormal_iff_ite.1 b.orthonormal i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [W, mul_apply, conjTranspose_apply, of_apply, one_apply]
    rw [← h]
    simp [dotProduct, mul_comm]
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.1 hW
  set σ' := Wᴴ * σ * W
  have hiso : vnEntropy σ' = vnEntropy σ := by
    have := vn_iso Wᴴ (by rw [conjTranspose_conjTranspose, hW']) σ hσ.1
    rwa [conjTranspose_conjTranspose] at this
  have hd : IsDensityMatrix σ' := ⟨hσ.1.conjTranspose_mul_mul_same W, by
    simp only [σ']
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hW', Matrix.mul_one, hσ.2]⟩
  set p : Ω → ℝ := fun a => (σ' a a).re
  have hpc : ∀ a, ((p a : ℝ) : ℂ) = σ' a a := fun a => hd.1.1.coe_re_apply_self a
  have hp : ∀ a, 0 ≤ p a := fun a => by
    have := hd.1.diag_nonneg (i := a)
    exact (Complex.nonneg_iff.1 this).1
  have hp1 : ∑ a, p a = 1 := by
    have := hd.2
    rw [trace] at this
    have h2 : ((∑ a, p a : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]; simp only [hpc]; exact this
    exact_mod_cast h2
  have hF : p i0 = (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re := by
    simp only [p, σ', W, mul_apply, conjTranspose_apply, of_apply, hb0, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    simp [RCLike.star_def]
  have hpin := X6DP.pinch hd
  have hdiag : (diagonal fun a => σ' a a) = diagonal fun a => ((p a : ℝ) : ℂ) := by
    simp only [hpc]
  rw [hdiag, vn_diag'] at hpin
  have hc := cfano p hp hp1 i0
  rw [← hiso, ← hF]
  refine hpin.trans ?_
  rw [← Finset.sum_div, binEntropy2, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, logb,
    ← mul_div_assoc, ← add_div]
  exact div_le_div_of_nonneg_right hc (Real.log_pos one_lt_two).le

end X6FN


/-! X6: loss/fidelity Fano bound for a channel composed with a decoder. -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6LF
open Matrix X6SSA X6CH QAlgorithms Real
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)
open QAlgorithms.Papers.Independent.Gap48.P33

variable {R A B : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

lemma refFid (Φ : Superop A A) (psi : EuclideanSpace ℂ (R × A)) :
    referenceFidelity Φ psi =
      (∑ x, ∑ y, conj (psi x) * idTensorSuperop Φ (pureDensity psi) x y * psi y).re := by
  unfold referenceFidelity
    QAlgorithms.Papers.Independent.Dependency50.P40.purificationFidelity
    QAlgorithms.Papers.Independent.Dependency50.P40.complexQuadraticForm
  simp only []
  congr 1
  set e := ((Fintype.equivFin R).prodCongr (Fintype.equivFin A)).symm
  refine Fintype.sum_equiv e _ _ fun x => Fintype.sum_equiv e _ _ fun y => ?_
  simp only [e, idTensorSuperop, pureDensity, of_apply, PiLp.toLp_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map, Equiv.symm_apply_apply]
  rfl

/-- composition of Kraus channels. -/
lemma kraus_comp {C K L : Type*} [Fintype C] [Fintype K] [Fintype L] (E : K → Matrix B A ℂ)
    (G : L → Matrix C B ℂ) (X : Matrix A A ℂ) :
    krausApply G (krausApply E X) = krausApply (fun p : L × K => G p.1 * E p.2) X := by
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, Fintype.sum_prod_type,
    conjTranspose_mul, Matrix.mul_assoc]

lemma kraus_comp_iso {C K L : Type*} [Fintype C] [Fintype K] [Fintype L] (E : K → Matrix B A ℂ)
    (G : L → Matrix C B ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (hG : ∑ l, (G l)ᴴ * G l = 1) :
    ∑ p : L × K, (G p.1 * E p.2)ᴴ * (G p.1 * E p.2) = 1 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, ← hE]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc _ = (E k)ᴴ * ((∑ l, (G l)ᴴ * G l) * E k) := by
        simp only [conjTranspose_mul, Matrix.sum_mul, Matrix.mul_sum, Matrix.mul_assoc]
    _ = _ := by rw [hG, Matrix.one_mul]

variable [Nonempty R] [Nonempty A] [Nonempty B]

/-- the entropy exchange is the output entropy of `id ⊗ Φ` on ANY purification. -/
lemma ee_psi {K : Type} [Fintype K] [DecidableEq K] [Nonempty K] (H : K → Matrix B A ℂ)
    (psi : EuclideanSpace ℂ (R × A)) (hρ : (traceLeft (pureDensity psi)).PosSemidef) :
    entropyExchange (krausApply H) (traceLeft (pureDensity psi)) =
      vnEntropy (idTensorSuperop (krausApply H) (pureDensity psi)) := by
  rw [ee_eq _ hρ.isHermitian, sc, sqrt_sq hρ, ← X6DP.mOf_mul psi]
  conv_rhs => rw [← X6DP.vecOf_mOf psi]
  rw [sc]

lemma idT_dens {K : Type} [Fintype K] [DecidableEq K] [Nonempty K] (H : K → Matrix B A ℂ)
    (hH : ∑ k, (H k)ᴴ * H k = 1) (psi : EuclideanSpace ℂ (R × A)) (hpsi : ‖psi‖ = 1) :
    IsDensityMatrix (idTensorSuperop (krausApply H) (pureDensity psi)) := by
  have h := m_RC (X6DP.mOf psi) H (F0 (B := B))
  rw [idT_F0, X6DP.vecOf_mOf] at h
  have hΨ : trace (X6DP.mOf psi * (X6DP.mOf psi)ᴴ) = 1 := by
    rw [X6DP.mOf_mul]
    have := pd_trace psi hpsi
    rw [← this]
    simp [trace, traceLeft, Fintype.sum_prod_type]
    exact Finset.sum_comm
  refine ⟨?_, ?_⟩
  · rw [← h]; exact marg_psd _ (pd_psd _)
  · rw [← h, marg_trace, tr_one _ H F0 hH F0_kraus hΨ]

/-- `S(ρ) ≤ S_e(Φ, ρ) + S(Φ ρ)`. -/
lemma araki {K : Type} [Fintype K] [DecidableEq K] [Nonempty K] (H : K → Matrix B A ℂ)
    (hH : ∑ k, (H k)ᴴ * H k = 1) {ρ : Matrix A A ℂ} (hρ : IsDensityMatrix ρ) :
    vnEntropy ρ ≤ entropyExchange (krausApply H) ρ + vnEntropy (krausApply H ρ) := by
  set s := cfc Real.sqrt ρ
  have hs : s * sᴴ = ρ := sqrt_sq hρ.1
  have hΨ : trace (s * sᴴ) = 1 := by rw [hs, hρ.2]
  obtain ⟨-, i2, -, -⟩ := ineqs (R := A) s H (F0 (B := B)) hH F0_kraus hΨ
  simp only [hs, idT_F0, kraus_F0] at i2
  rw [comp_F0 _ (by rw [kraus_trace H hH, hρ.2])] at i2
  rw [ee_eq _ hρ.1.isHermitian]
  linarith

end X6LF


/-! Claimed50.P43, eq.(7): the projection-state dense-coding lower bound. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6DC
open Matrix QAlgorithms

section frame
variable {X : Type} [Fintype X] [DecidableEq X]

lemma herm_exp {H : Matrix X X ℂ} (hH : H.IsHermitian) (a b : X) :
    H a b = ∑ i, (hH.eigenvectorUnitary : Matrix X X ℂ) a i * (hH.eigenvalues i : ℂ) *
      conj ((hH.eigenvectorUnitary : Matrix X X ℂ) b i) := by
  conv_lhs => rw [hH.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.star_apply, Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, RCLike.star_def]
  rfl

lemma eig_idem {P : Matrix X X ℂ} (hP : P.IsHermitian) (hidem : P * P = P) (i : X) :
    hP.eigenvalues i = 0 ∨ hP.eigenvalues i = 1 := by
  set U : Matrix X X ℂ := (hP.eigenvectorUnitary : Matrix X X ℂ)
  have hU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hP.eigenvectorUnitary.2
  have hD : star U * P * U = diagonal (fun i => (hP.eigenvalues i : ℂ)) := by
    have hs := hP.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    conv_lhs => rw [hs]
    simp only [U, Matrix.mul_assoc, hU, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]; rfl
  have h2 : (star U * P * U) * (star U * P * U) = star U * P * U := by
    have hU' : U * star U = 1 := mul_eq_one_comm.1 hU
    calc (star U * P * U) * (star U * P * U) = star U * (P * (U * star U) * P) * U := by
          simp only [Matrix.mul_assoc]
      _ = star U * P * U := by rw [hU', Matrix.mul_one, hidem, Matrix.mul_assoc]
  rw [hD, diagonal_mul_diagonal] at h2
  have := congrFun (congrFun h2 i) i
  simp only [diagonal_apply_eq] at this
  have h3 : (hP.eigenvalues i) * (hP.eigenvalues i) = hP.eigenvalues i := by exact_mod_cast this
  have h4 : hP.eigenvalues i * (hP.eigenvalues i - 1) = 0 := by rw [mul_sub, h3]; ring
  rcases mul_eq_zero.1 h4 with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

lemma frame_exists (P : Matrix X X ℂ) (hP : P.IsHermitian) (hidem : P * P = P)
    (hpos : 0 < P.trace.re) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) = P.trace.re ∧
      ∃ J : Matrix X (Fin m) ℂ, Jᴴ * J = 1 ∧ J * Jᴴ = P := by
  set U : Matrix X X ℂ := (hP.eigenvectorUnitary : Matrix X X ℂ)
  have hU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hP.eigenvectorUnitary.2
  set S : Finset X := Finset.univ.filter (fun i => hP.eigenvalues i = 1)
  have hlam : ∀ i, hP.eigenvalues i = if i ∈ S then 1 else 0 := fun i => by
    rcases eig_idem hP hidem i with h | h <;> simp [S, h]
  have htr : P.trace.re = S.card := by
    rw [hP.trace_eq_sum_eigenvalues]
    simp only [Complex.re_sum, Complex.ofReal_re, RCLike.ofReal_re]
    simp_rw [hlam]
    simp [apply_ite Complex.re, Finset.sum_boole]
  set m := S.card
  let e : Fin m ≃ S := S.equivFin.symm
  let J : Matrix X (Fin m) ℂ := of fun x k => U x (e k)
  have hsumS : ∀ f : X → ℂ, ∑ k : Fin m, f (e k) = ∑ i ∈ S, f i := fun f => by
    rw [Equiv.sum_comp e (fun i : S => f i), Finset.sum_coe_sort S f]
  refine ⟨m, ?_, htr.symm, J, ?_, ?_⟩
  · have : (0 : ℝ) < m := htr ▸ hpos
    exact_mod_cast this
  · ext k l
    have := congrFun (congrFun hU (e k)) (e l)
    simp only [Matrix.mul_apply, star_apply, RCLike.star_def] at this
    simp only [J, Matrix.mul_apply, conjTranspose_apply, of_apply, RCLike.star_def, this,
      one_apply, e.injective.eq_iff, Subtype.coe_inj]
  · ext x y
    rw [herm_exp hP x y]
    simp only [J, Matrix.mul_apply, conjTranspose_apply, of_apply, RCLike.star_def]
    rw [hsumS (fun i => U x i * conj (U y i))]
    simp_rw [hlam]
    simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, mul_ite,
      ite_mul, mul_one, mul_zero, zero_mul]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    simp [S, U]

end frame

section weyl
open QAlgorithms.Papers.Independent.Information100.P34 (weyl cyclicPhase)

lemma phase_mul (d : ℕ) (x : ZMod d) : cyclicPhase d x * star (cyclicPhase d x) = 1 := by
  unfold cyclicPhase
  rw [RCLike.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have : 2 * ↑Real.pi * Complex.I * (x.val : ℂ) / (d : ℂ) +
      (starRingEnd ℂ) (2 * ↑Real.pi * Complex.I * (x.val : ℂ) / (d : ℂ)) = 0 := by
    simp only [map_div₀, map_mul, map_natCast, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  rw [this, Complex.exp_zero]

lemma weyl_mem {d : ℕ} [NeZero d] (a b : ZMod d) :
    weyl a b ∈ Matrix.unitaryGroup (ZMod d) ℂ := by
  unfold weyl
  simp only
  refine Submonoid.mul_mem _ (Submonoid.pow_mem _ ?_ _) (Submonoid.pow_mem _ ?_ _)
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    simp only [mul_apply, star_apply, of_apply, one_apply]
    rw [Finset.sum_eq_single (i - 1)]
    · by_cases h : i = j
      · subst h; simp
      · have : ¬ j = i - 1 + 1 := by rw [sub_add_cancel]; exact Ne.symm h
        simp [this, h, Ne.symm h]
    · intro c _ hc
      have : ¬ i = c + 1 := fun h => hc (by rw [h]; ring)
      simp [this]
    · simp
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext x
    exact phase_mul d x

end weyl

section ext
variable {X K : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]

lemma ext_unitary (J : Matrix X K ℂ) (hJ : Jᴴ * J = 1) (W : Matrix K K ℂ) (hW : W * Wᴴ = 1) :
    extendEncodedUnitary J W * (extendEncodedUnitary J W)ᴴ = 1 := by
  unfold extendEncodedUnitary
  have h1 : ∀ Y : Matrix K X ℂ, Jᴴ * (J * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have h2 : ∀ Y : Matrix K X ℂ, W * (Wᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
  simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_one, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, h1, h2]
  abel

lemma ext_proj (J : Matrix X K ℂ) (hJ : Jᴴ * J = 1) (W : Matrix K K ℂ) (hW : W * Wᴴ = 1) :
    extendEncodedUnitary J W * (J * Jᴴ) * (extendEncodedUnitary J W)ᴴ = J * Jᴴ := by
  unfold extendEncodedUnitary
  have h1 : ∀ Y : Matrix K X ℂ, Jᴴ * (J * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have h2 : ∀ Y : Matrix K X ℂ, W * (Wᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
  have h3 : Jᴴ * J = 1 := hJ
  simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_one, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, h1, h2, h3]
  abel

end ext

section res
open QAlgorithms.Papers.Independent.Claimed50.P43
variable {X : Type} [Fintype X] [DecidableEq X]

lemma pd_act (K : Matrix X X ℂ) (ψ : EuclideanSpace ℂ X) :
    pureDensity (act K ψ) = K * pureDensity ψ * Kᴴ := by
  ext a b
  simp only [pureDensity, act, of_apply, mulVec, dotProduct, mul_apply, conjTranspose_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

variable {m : ℕ} [NeZero m]

lemma trL_res (J : Matrix X (ZMod m) ℂ) (hJ : Jᴴ * J = 1) :
    traceLeft (pureDensity (frameResource J)) = ((m : ℂ)⁻¹) • (J * Jᴴ) := by
  have hJ' : ∀ k l, ∑ x, J x k * conj (J x l) = if l = k then 1 else 0 := fun k l => by
    have := congrFun (congrFun hJ l) k
    simp only [mul_apply, conjTranspose_apply, RCLike.star_def, one_apply] at this
    rw [← this]; exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hc : ((Real.sqrt m)⁻¹ : ℂ) * conj ((Real.sqrt m)⁻¹ : ℂ) = (m : ℂ)⁻¹ := by
    have e : ((Real.sqrt m)⁻¹ : ℂ) = (((Real.sqrt m)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast; rfl
  ext a a'
  simp only [traceLeft, pureDensity, frameResource, of_apply, Matrix.smul_apply, mul_apply,
    conjTranspose_apply, map_mul, map_sum, RCLike.star_def, smul_eq_mul]
  have key : (m : ℂ)⁻¹ * ∑ k, J a k * conj (J a' k) = ((Real.sqrt m)⁻¹ : ℂ) * conj ((Real.sqrt m)⁻¹ : ℂ) *
      ∑ k, ∑ l, (∑ x, J x k * conj (J x l)) * (J a k * conj (J a' l)) := by
    simp_rw [hJ']
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, hc]
  rw [key]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma pd_trace_norm {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) (h : trace (pureDensity v) = 1) :
    ‖v‖ = 1 := by
  have h2 := EuclideanSpace.norm_sq_eq v
  have h3 : ∑ p, ‖v p‖ ^ 2 = 1 := by
    have := congrArg Complex.re h
    simp only [trace, diag_apply, pureDensity, of_apply, Complex.mul_conj, Complex.re_sum,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq] at this
    simpa using this
  rw [h3] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2

lemma res_trace (J : Matrix X (ZMod m) ℂ) (hJ : Jᴴ * J = 1) :
    trace (pureDensity (frameResource J)) = 1 := by
  rw [← X6SSA.trace_trF]
  show trace (traceLeft (pureDensity (frameResource J))) = 1
  rw [trL_res J hJ, trace_smul, trace_mul_comm, hJ, trace_one, ZMod.card, smul_eq_mul]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 (NeZero.ne m))

lemma res_norm (J : Matrix X (ZMod m) ℂ) (hJ : Jᴴ * J = 1) : ‖frameResource J‖ = 1 :=
  pd_trace_norm _ (res_trace J hJ)

end res

section kr
variable {R A B : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B]

lemma idT_kron (Φ : Superop A B) (hΦ : ∀ (c : ℂ) (Y : Matrix A A ℂ), Φ (c • Y) = c • Φ Y)
    (S : Matrix R R ℂ) (Y : Matrix A A ℂ) :
    idTensorSuperop Φ (S ⊗ₖ Y) = S ⊗ₖ Φ Y := by
  ext p q
  have e : (of fun i i' => (S ⊗ₖ Y) (p.1, i) (q.1, i')) = S p.1 q.1 • Y := by
    ext i i'; simp [kroneckerMap_apply]
  show Φ (of fun i i' => (S ⊗ₖ Y) (p.1, i) (q.1, i')) p.2 q.2 = _
  rw [e, hΦ]
  simp [kroneckerMap_apply]

lemma conj_kraus (V : Matrix A A ℂ) :
    conjSuperop V = krausApply (fun _ : Fin 1 => V) := by
  funext ρ; simp [conjSuperop, krausApply]

lemma enc_eq (V : Matrix A A ℂ) (ψ : EuclideanSpace ℂ (A × A)) :
    idTensorSuperop (R := A) (conjSuperop V) (pureDensity ψ) =
      pureDensity (act ((1 : Matrix A A ℂ) ⊗ₖ V) ψ) := by
  rw [conj_kraus, X6AH.idT_kraus', pd_act]
  simp [krausApply]

lemma conj_channel (V : Matrix A A ℂ) (hV : Vᴴ * V = 1) : IsChannel (conjSuperop V) :=
  ⟨1, fun _ => V, by simp [IsKrausFamily, hV], fun ρ => by rw [conj_kraus]⟩

end kr
section main
open QAlgorithms.Papers.Independent.Claimed50.P43
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty X]
  [Nonempty Y]

lemma bell_marg {k : ℕ} (J : Matrix X (ZMod (k + 1)) ℂ) (hJ : Jᴴ * J = 1)
    (x : ZMod (k + 1) × ZMod (k + 1)) :
    traceLeft (pureDensity (frameBell J x)) = traceLeft (pureDensity (frameResource J)) := by
  have hW := Matrix.mem_unitaryGroup_iff.1 (weyl_mem (d := k + 1) x.1 x.2)
  unfold frameBell
  rw [pd_act]
  change X6SSA.trF _ = _
  refine (X6MI.trF_k2 (I := X) (frameWeyl J x.1 x.2) _).trans ?_
  change frameWeyl J x.1 x.2 * traceLeft (pureDensity (frameResource J)) * _ = _
  rw [trL_res J hJ, Matrix.mul_smul, Matrix.smul_mul]
  unfold frameWeyl
  rw [ext_proj J hJ _ hW]

theorem dc_main (M : Superop X Y) (hM : IsChannel M) (k : ℕ) (J : Matrix X (ZMod (k + 1)) ℂ)
    (hJ : Jᴴ * J = 1) :
    ∃ e : AssistedEnsemble X ((k + 1) * (k + 1)),
      (∀ i, e.prob i = (((k + 1) * (k + 1) : ℕ) : ℝ)⁻¹) ∧
      (∀ i, ∃ V : Matrix.unitaryGroup X ℂ, e.encode i = conjSuperop (V : Matrix X X ℂ)) ∧
      assistedScore M e = inputMutualInfo M (traceLeft (pureDensity (frameResource J))) := by
  set ψ := frameResource J with hψ
  set ρ := traceLeft (pureDensity ψ) with hρ
  have hψd : IsDensityMatrix (pureDensity ψ) := ⟨X6CH.pd_psd _, res_trace J hJ⟩
  have hρd : IsDensityMatrix ρ := ⟨X6SSA.trF_psd hψd.1, (X6SSA.trace_trF _).trans hψd.2⟩
  let V : ZMod (k + 1) × ZMod (k + 1) → Matrix X X ℂ := fun x => frameWeyl J x.1 x.2
  have hVu : ∀ x, V x * (V x)ᴴ = 1 := fun x =>
    ext_unitary J hJ _ (Matrix.mem_unitaryGroup_iff.1 (weyl_mem (d := k + 1) x.1 x.2))
  have hVu' : ∀ x, (V x)ᴴ * V x = 1 := fun x => mul_eq_one_comm.1 (hVu x)
  have hcard : Fintype.card (Fin ((k + 1) * (k + 1))) =
      Fintype.card (ZMod (k + 1) × ZMod (k + 1)) := by simp [ZMod.card]
  let σ : Fin ((k + 1) * (k + 1)) ≃ ZMod (k + 1) × ZMod (k + 1) := Fintype.equivOfCardEq hcard
  set c : ℝ := (((k + 1) * (k + 1) : ℕ) : ℝ)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : ∑ _i : Fin ((k + 1) * (k + 1)), c = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
    exact mul_inv_cancel₀ (by positivity)
  let e : AssistedEnsemble X ((k + 1) * (k + 1)) :=
    ⟨fun _ => c, fun _ => hc0, hc1, ψ, res_norm J hJ, fun i => conjSuperop (V (σ i)),
      fun i => conj_channel _ (hVu' _)⟩
  refine ⟨e, fun _ => rfl, fun i => ⟨⟨V (σ i), Matrix.mem_unitaryGroup_iff.2 (hVu _)⟩, rfl⟩, ?_⟩
  have henc : ∀ i, encodedAssistedState e i = pureDensity (frameBell J (σ i)) := fun i =>
    enc_eq _ _
  obtain ⟨n', H, hn', hH, hMH⟩ := X6CH.kraus_of_channel hM
  have : Nonempty (Fin n') := ⟨⟨0, hn'⟩⟩
  have hlinM : ∀ (a : ℂ) (Z : Matrix X X ℂ), M (a • Z) = a • M Z := by
    intro a Z; rw [hMH]
    simp only [krausApply, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]
  have hterm : ∀ i, vnEntropy (idTensorSuperop (R := X) M (encodedAssistedState e i)) =
      entropyExchange M ρ := by
    intro i
    have hb : traceLeft (pureDensity (frameBell J (σ i))) = ρ := bell_marg J hJ _
    rw [henc, ← hb, hMH]
    exact (X6LF.ee_psi H _ (hb ▸ hρd.1)).symm
  have hsum : ∑ i, ((c : ℝ) : ℂ) • pureDensity (frameBell J (σ i)) = ρ ⊗ₖ ρ := by
    rw [← Finset.smul_sum, Equiv.sum_comp σ (fun x => pureDensity (frameBell J x)),
      (denseCodingIdentities J hJ).2.2, hρ, trL_res J hJ]
    unfold frameProjector
    rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
    congr 1
    rw [hc]; push_cast; rw [← mul_inv]
  have havg : ∑ i, ((c : ℝ) : ℂ) • idTensorSuperop (R := X) M (encodedAssistedState e i) =
      ρ ⊗ₖ M ρ := by
    rw [← X6AH.idT_lin M hM]
    simp only [henc]
    rw [hsum, idT_kron M hlinM]
  unfold assistedScore
  show vnEntropy (∑ i, ((c : ℝ) : ℂ) • idTensorSuperop (R := X) M (encodedAssistedState e i)) -
    ∑ i, c * vnEntropy (idTensorSuperop (R := X) M (encodedAssistedState e i)) = _
  rw [havg, X6KR.vn_kron hρd (X6ZC.chan_dens M hM ρ hρd)]
  simp only [hterm]
  rw [← Finset.sum_mul, hc1, one_mul]
  rfl

lemma vals_bdd (M : Superop X Y) (hM : IsChannel M) : BddAbove (assistedValues M) := by
  obtain ⟨B, hB⟩ := X6AH.mmi_bdd M hM
  refine ⟨B, ?_⟩
  rintro v ⟨m, e, rfl⟩
  refine (X6AH.score_le M hM e).trans (hB ⟨_, ?_, rfl⟩)
  have hψd : IsDensityMatrix (pureDensity e.resource) :=
    ⟨X6CH.pd_psd _, X6CH.pd_trace _ e.normalized⟩
  refine X6AH.dens_mix e.prob e.nonneg e.total _ fun i => ?_
  show IsDensityMatrix (traceLeft (idTensorSuperop (e.encode i) (pureDensity e.resource)))
  rw [X6AH.chan_idT_trL _ (e.channel i)]
  exact X6ZC.chan_dens _ (e.channel i) _ ⟨X6SSA.trF_psd hψd.1, (X6SSA.trace_trF _).trans hψd.2⟩

theorem dc_final (M : Superop X Y) (hM : IsChannel M) (P : Matrix X X ℂ)
    (hP : P.IsHermitian) (hidem : P * P = P) (hpos : 0 < P.trace.re) :
    inputMutualInfo M ((P.trace.re : ℂ)⁻¹ • P) ≤ assistedOneShot M ∧
    ∃ (m : ℕ) (e : AssistedEnsemble X (m * m)),
      0 < m ∧ (m : ℝ) = P.trace.re ∧
      (∀ i, e.prob i = ((m * m : ℕ) : ℝ)⁻¹) ∧
      (∀ i, ∃ V : Matrix.unitaryGroup X ℂ, e.encode i = conjSuperop (V : Matrix X X ℂ)) ∧
      assistedScore M e = inputMutualInfo M ((P.trace.re : ℂ)⁻¹ • P) := by
  obtain ⟨m, hm, hmtr, J0, hJ0, hJP⟩ := frame_exists P hP hidem hpos
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let J : Matrix X (ZMod (k + 1)) ℂ := J0
  have hJ : Jᴴ * J = 1 := hJ0
  have hJP' : J * Jᴴ = P := hJP
  obtain ⟨e, hp, hV, hs⟩ := dc_main M hM k J hJ
  have hρ : traceLeft (pureDensity (frameResource J)) = (P.trace.re : ℂ)⁻¹ • P := by
    rw [trL_res J hJ, hJP', ← hmtr]; push_cast; rfl
  rw [hρ] at hs
  refine ⟨?_, k + 1, e, Nat.succ_pos _, hmtr, hp, hV, hs⟩
  rw [← hs]
  exact le_csSup (vals_bdd M hM) ⟨_, e, rfl⟩

end main
end X6DC


section
open scoped Matrix ComplexConjugate
open Filter
open QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P43
open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

theorem solution {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] [Nonempty A] [Nonempty C]
    (N : Superop A C) (hN : IsChannel N) (n : ℕ) (hn : 0 < n)
    (P : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hP : P.IsHermitian) (hidem : P * P = P) (hpos : 0 < P.trace.re) :
    inputMutualInfo (piSuperop (fun _ : Fin n => N))
      ((P.trace.re : ℂ)⁻¹ • P) ≤ assistedOneShot (piSuperop (fun _ : Fin n => N)) ∧
    ∃ (m : ℕ) (e : AssistedEnsemble (Fin n → A) (m * m)),
      0 < m ∧ (m : ℝ) = P.trace.re ∧
      (∀ i, e.prob i = ((m * m : ℕ) : ℝ)⁻¹) ∧
      (∀ i, ∃ V : Matrix.unitaryGroup (Fin n → A) ℂ,
        e.encode i = conjSuperop (V : Matrix (Fin n → A) (Fin n → A) ℂ)) ∧
      assistedScore (piSuperop (fun _ : Fin n => N)) e =
        inputMutualInfo (piSuperop (fun _ : Fin n => N)) ((P.trace.re : ℂ)⁻¹ • P) :=
  X6DC.dc_final _ (X6AH.pi_channel N hN) P hP hidem hpos

end
