-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P33.loss_information_balance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:41:52.640162+00:00
-- url     : https://prove2.me/submissions/a9ea2abd-f9a5-4715-84a9-9a5d84a0c0a8

import Theorems.Thm_TroppMatrixConcentration_ch8_entropy_joint_convex
import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33


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

variable {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
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
lemma mi_pure [Nonempty A] {τ : Matrix A A ℂ} (hτ : IsDensityMatrix τ) :
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

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first both)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)

theorem solution {A B K : Type}
    [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] [DecidableEq K]
    [Nonempty A] [Nonempty B] [Nonempty K]
    (E : K → Matrix B A ℂ) (hE : IsKrausFamily E)
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    let N := krausApply E
    let omega := pureDensity (dilationReference E (canonicalPurification rho))
    loss N rho = middleConditionalInformation omega ∧
    loss N rho = mutualInformation (discardMiddle omega) ∧
    entropyExchange N rho = vnEntropy (traceLeft (traceLeft omega)) ∧
    0 ≤ loss N rho ∧ loss N rho ≤ 2 * min (vnEntropy rho) (entropyExchange N rho) ∧
    inputMutualInfo N rho + loss N rho = 2 * vnEntropy rho ∧
    0 ≤ inputMutualInfo N rho ∧ inputMutualInfo N rho ≤ 2 * vnEntropy rho :=
  X6CH.balance E hE rho hrho
