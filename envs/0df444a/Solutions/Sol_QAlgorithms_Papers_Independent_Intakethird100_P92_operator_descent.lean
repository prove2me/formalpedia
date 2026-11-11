-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P92.operator_descent
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T09:59:43.526266+00:00
-- url     : https://prove2.me/submissions/ffeba95e-0103-4933-8713-7162ebdf35ec

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.DenseEmbedding
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
noncomputable section

section
open scoped ComplexConjugate

namespace S05P086

/-- A bounded-above discrete convex sequence cannot have a positive first slope. -/
theorem bounded_convex_first_le (a : ℕ → ℝ) (M : ℝ)
    (hbound : ∀ n, a n ≤ M)
    (hconvex : ∀ n, 2 * a (n + 1) ≤ a n + a (n + 2)) :
    a 1 ≤ a 0 := by
  by_contra h
  have hd : 0 < a 1 - a 0 := sub_pos.mpr (lt_of_not_ge h)
  have hslope : ∀ n, a 1 - a 0 ≤ a (n + 1) - a n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      have hc := hconvex n
      nlinarith
  have hlower : ∀ n : ℕ, a 0 + (n : ℝ) * (a 1 - a 0) ≤ a n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hslope n
      rw [Nat.cast_succ]
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((M - a 0) / (a 1 - a 0))
  have hlarge : M - a 0 < (n : ℝ) * (a 1 - a 0) := (div_lt_iff₀ hd).mp hn
  linarith [hlower n, hbound n]

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- An ambient contraction symmetric for a contracted inner product is also
a contraction for that inner product. Completeness is not needed. -/
theorem norm_q_contraction (q : E →ₗ[ℂ] F)
    (hq : ∀ v, ‖q v‖ ≤ ‖v‖) (C : E →L[ℂ] E) (hC : ‖C‖ ≤ 1)
    (hSym : ∀ v w, inner ℂ (q (C v)) (q w) = inner ℂ (q v) (q (C w)))
    (v : E) : ‖q (C v)‖ ≤ ‖q v‖ := by
  let z : ℕ → E := fun n => (C : E → E)^[n] v
  have hzstep : ∀ n, z (n + 1) = C (z n) := by
    intro n
    exact Function.iterate_succ_apply' _ _ _
  have hzbound : ∀ n, ‖z n‖ ≤ ‖v‖ := by
    intro n
    induction n with
    | zero => simp [z]
    | succ n ih =>
      rw [hzstep]
      calc
        ‖C (z n)‖ ≤ ‖C‖ * ‖z n‖ := C.le_opNorm _
        _ ≤ 1 * ‖z n‖ := mul_le_mul_of_nonneg_right hC (norm_nonneg _)
        _ ≤ ‖v‖ := by simpa only [one_mul] using ih
  let a : ℕ → ℝ := fun n => ‖q (z n)‖ ^ 2
  have habound : ∀ n, a n ≤ ‖v‖ ^ 2 := by
    intro n
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr ((hq _).trans (hzbound n))
  have hpair : ∀ n,
      RCLike.re (inner ℂ (q (z (n + 2))) (q (z n))) = a (n + 1) := by
    intro n
    rw [hzstep (n + 1), hSym, ← hzstep n]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (q (z (n + 1)))
  have haconvex : ∀ n, 2 * a (n + 1) ≤ a n + a (n + 2) := by
    intro n
    have hnonneg := sq_nonneg ‖q (z (n + 2)) - q (z n)‖
    have hnorm := norm_sub_sq (𝕜 := ℂ) (q (z (n + 2))) (q (z n))
    rw [hpair n] at hnorm
    dsimp only [a] at *
    nlinarith
  have hfirst := bounded_convex_first_le a (‖v‖ ^ 2) habound haconvex
  have hsq : ‖q (C v)‖ ^ 2 ≤ ‖q v‖ ^ 2 := by simpa [a, z] using hfirst
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- A bounded operator symmetric for a contracted inner product has no larger
operator bound in that inner product. Completeness is not needed. -/
theorem norm_q_map_le (q : E →ₗ[ℂ] F) (hq : ∀ v, ‖q v‖ ≤ ‖v‖)
    (B : E →L[ℂ] E)
    (hSym : ∀ v w, inner ℂ (q (B v)) (q w) = inner ℂ (q v) (q (B w)))
    (v : E) : ‖q (B v)‖ ≤ ‖B‖ * ‖q v‖ := by
  by_cases hB : B = 0
  · simp [hB]
  have hBpos : 0 < ‖B‖ := (norm_pos_iff (a := B)).mpr hB
  let C : E →L[ℂ] E := ((‖B‖⁻¹ : ℝ) : ℂ) • B
  have hC : ‖C‖ ≤ 1 := by
    dsimp only [C]
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg B)),
      inv_mul_cancel₀ hBpos.ne']
  have hCsym : ∀ x y, inner ℂ (q (C x)) (q y) = inner ℂ (q x) (q (C y)) := by
    intro x y
    simp only [C, smul_apply, map_smul, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, hSym x y]
  have h := norm_q_contraction q hq C hC hCsym v
  change ‖q ((((‖B‖⁻¹ : ℝ) : ℂ) • B) v)‖ ≤ ‖q v‖ at h
  rw [smul_apply, map_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg B))] at h
  have hmul := mul_le_mul_of_nonneg_left h (norm_nonneg B)
  simpa only [← mul_assoc, mul_inv_cancel₀ hBpos.ne', one_mul] using hmul

end S05P086
end

section
open scoped ComplexConjugate NNReal ENNReal
open QAlgorithms.Papers.Independent.Intakethird100.P92

namespace S05P086
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The completion quotient has precisely the reflected inner product. -/
lemma osQ_inner (r : ReflectionData E) (v w : r.plus) :
    inner ℂ (osQ r v) (osQ r w) = inner ℂ (r.theta (v : E)) (w : E) := by
  change inner ℂ
    ((UniformSpace.Completion.toComplₗᵢ : OSPreSpace r →ₗᵢ[ℂ] OS r) (toOSPre r v))
    ((UniformSpace.Completion.toComplₗᵢ : OSPreSpace r →ₗᵢ[ℂ] OS r) (toOSPre r w)) = _
  rw [LinearIsometry.inner_map_map]
  rfl

/-- The quotient norm is the square root of the nonnegative reflected form. -/
lemma osQ_norm (r : ReflectionData E) (v : r.plus) :
    ‖osQ r v‖ = Real.sqrt (inner ℂ (r.theta (v : E)) (v : E)).re := by
  change ‖(UniformSpace.Completion.toComplₗᵢ : OSPreSpace r →ₗᵢ[ℂ] OS r)
    (toOSPre r v)‖ = _
  rw [LinearIsometry.norm_map]
  rfl

lemma osQ_norm_sq (r : ReflectionData E) (v : r.plus) :
    ‖osQ r v‖ ^ 2 = (inner ℂ (r.theta (v : E)) (v : E)).re := by
  rw [osQ_norm, Real.sq_sqrt (r.positive v)]

/-- The canonical quotient map is a contraction for the ambient subspace norm. -/
lemma osQ_norm_le (r : ReflectionData E) (v : r.plus) : ‖osQ r v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg (osQ r v)) (norm_nonneg v)).mp
  rw [osQ_norm_sq]
  calc
    _ ≤ ‖r.theta (v : E)‖ * ‖(v : E)‖ :=
      re_inner_le_norm (𝕜 := ℂ) (r.theta (v : E)) (v : E)
    _ = ‖v‖ ^ 2 := by rw [r.theta.norm_map, pow_two]; rfl

/-- Every point in the Hilbert completion is approximated by quotient images. -/
lemma osQ_denseRange (r : ReflectionData E) : DenseRange (osQ r) := by
  change Dense (Set.range (fun v : r.plus => osQ r v))
  apply (UniformSpace.Completion.denseRange_coe (α := OSPreSpace r)).mono
  rintro z ⟨x, rfl⟩
  exact ⟨x.value, rfl⟩

end S05P086
end

section
open scoped ComplexConjugate
open QAlgorithms.Papers.Independent.Intakethird100.P92

namespace S05P086

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The original domain quotient is a surjective linear map onto q(D). -/
def domainQL (r : ReflectionData E) (D : Submodule ℂ r.plus) :
    D →ₗ[ℂ] D.map (osQ r) :=
  ((osQ r).comp D.subtype).codRestrict (D.map (osQ r))
    (fun v => (domainQ r D v).property)

@[simp] lemma domainQL_apply (r : ReflectionData E) (D : Submodule ℂ r.plus)
    (v : D) : domainQL r D v = domainQ r D v := rfl

lemma domainQ_surjective (r : ReflectionData E) (D : Submodule ℂ r.plus) :
    Function.Surjective (domainQ r D) := by
  intro w
  obtain ⟨v, hv, hq⟩ := Submodule.mem_map.mp w.property
  exact ⟨⟨v, hv⟩, Subtype.ext hq⟩

lemma domainQL_surjective (r : ReflectionData E) (D : Submodule ℂ r.plus) :
    Function.Surjective (domainQL r D) := domainQ_surjective r D

/-- Linear maps that vanish on the kernel factor through a surjective linear map. -/
lemma linear_factor_exists {A B C : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C]
    (q : A →ₗ[ℂ] B) (f : A →ₗ[ℂ] C) (hsurj : Function.Surjective q)
    (hnull : ∀ v, q v = 0 → f v = 0) :
    ∃ fbar : B →ₗ[ℂ] C, ∀ v, fbar (q v) = f v := by
  have hk : q.ker ≤ f.ker := fun v hv => hnull v hv
  refine ⟨(q.ker.liftQ f hk).comp (q.quotKerEquivOfSurjective hsurj).symm.toLinearMap, ?_⟩
  intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- The pairing identity and density preserve both null kernels and descend both
operators to q(D), preserving their pairing and symmetry. -/
theorem operator_descent_algebra (r : ReflectionData E) (D : Submodule ℂ r.plus)
    (hDense : Dense ((D.map (osQ r) : Submodule ℂ (OS r)) : Set (OS r)))
    (T U : D →ₗ[ℂ] r.plus)
    (hPair : ∀ v w : D,
      inner ℂ (r.theta (T v : E)) (w : E) =
        inner ℂ (r.theta (v : E)) (U w : E)) :
    (∀ v : D, osQ r v = 0 → osQ r (T v) = 0 ∧ osQ r (U v) = 0) ∧
    ∃ Tq Uq : D.map (osQ r) →ₗ[ℂ] OS r,
      (∀ v, Tq (domainQ r D v) = osQ r (T v)) ∧
      (∀ v, Uq (domainQ r D v) = osQ r (U v)) ∧
      (∀ v w : D.map (osQ r),
        inner ℂ (Tq v) (w : OS r) = inner ℂ (v : OS r) (Uq w)) ∧
      (T = U → ∀ v w : D.map (osQ r),
        inner ℂ (Tq v) (w : OS r) = inner ℂ (v : OS r) (Tq w)) := by
  have hp (v w : D) :
      inner ℂ (osQ r (T v)) (osQ r w) = inner ℂ (osQ r v) (osQ r (U w)) := by
    simpa only [osQ_inner] using hPair v w
  have hnull : ∀ v : D, osQ r v = 0 → osQ r (T v) = 0 ∧ osQ r (U v) = 0 := by
    intro v hv
    constructor
    · apply hDense.eq_zero_of_inner_left ℂ
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
      rw [hp v ⟨w, hw⟩, hv, inner_zero_left]
    · apply hDense.eq_zero_of_inner_right ℂ
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
      rw [← hp ⟨w, hw⟩ v, hv, inner_zero_right]
  obtain ⟨Tq, hT⟩ := linear_factor_exists (domainQL r D) ((osQ r).comp T)
    (domainQL_surjective r D) (fun v hv => (hnull v (congrArg Subtype.val hv)).1)
  obtain ⟨Uq, hU⟩ := linear_factor_exists (domainQL r D) ((osQ r).comp U)
    (domainQL_surjective r D) (fun v hv => (hnull v (congrArg Subtype.val hv)).2)
  have hT' : ∀ v, Tq (domainQ r D v) = osQ r (T v) := hT
  have hU' : ∀ v, Uq (domainQ r D v) = osQ r (U v) := hU
  have hpairq : ∀ v w : D.map (osQ r),
      inner ℂ (Tq v) (w : OS r) = inner ℂ (v : OS r) (Uq w) := by
    intro v w
    obtain ⟨v', rfl⟩ := domainQ_surjective r D v
    obtain ⟨w', rfl⟩ := domainQ_surjective r D w
    rw [hT', hU']
    exact hp v' w'
  refine ⟨hnull, Tq, Uq, hT', hU', hpairq, ?_⟩
  intro hTU v w
  rw [hpairq]
  obtain ⟨w', rfl⟩ := domainQ_surjective r D w
  rw [hT', hU', hTU]

end S05P086
end

section
open QAlgorithms.Papers.Independent.Intakethird100.P92

namespace S05P086
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A bounded operator symmetric for the reflected form has the specified
canonical completion extension, with no increase in operator norm. -/
theorem osExtension_of_symmetric (r : ReflectionData E) (B : r.plus →L[ℂ] r.plus)
    (hSym : ∀ v w : r.plus,
      inner ℂ (r.theta (B v : E)) (w : E) =
        inner ℂ (r.theta (v : E)) (B w : E)) :
    (∀ v : r.plus, osExtension r B.toLinearMap (osQ r v) = osQ r (B v)) ∧
      ‖osExtension r B.toLinearMap‖ ≤ ‖B‖ := by
  have hqsym : ∀ v w : r.plus,
      inner ℂ (osQ r (B v)) (osQ r w) = inner ℂ (osQ r v) (osQ r (B w)) := by
    intro v w
    rw [osQ_inner, osQ_inner]
    exact hSym v w
  have hbound : ∀ v : r.plus, ‖osQ r (B v)‖ ≤ ‖B‖ * ‖osQ r v‖ :=
    norm_q_map_le (osQ r) (osQ_norm_le r) B hqsym
  let f : r.plus →ₗ[ℂ] OS r := (osQ r).comp B.toLinearMap
  let A : OS r →L[ℂ] OS r := f.extendOfNorm (osQ r)
  have hA : ∀ v : r.plus, A (osQ r v) = osQ r (B v) := by
    intro v
    exact LinearMap.extendOfNorm_eq (f := f) (e := osQ r)
      (osQ_denseRange r) ⟨‖B‖, hbound⟩ v
  have hAnorm : ‖A‖ ≤ ‖B‖ :=
    LinearMap.opNorm_extendOfNorm_le (f := f) (e := osQ r)
      (osQ_denseRange r) (norm_nonneg B) hbound
  have hex : ∃ C : OS r →L[ℂ] OS r,
      ∀ v : r.plus, C (osQ r v) = osQ r (B.toLinearMap v) := ⟨A, hA⟩
  have hchosen : ∀ v : r.plus,
      osExtension r B.toLinearMap (osQ r v) = osQ r (B v) := by
    unfold osExtension
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  have heq : osExtension r B.toLinearMap = A := by
    apply DFunLike.coe_injective
    apply (osQ_denseRange r).equalizer (osExtension r B.toLinearMap).continuous A.continuous
    funext v
    exact (hchosen v).trans (hA v).symm
  refine ⟨hchosen, ?_⟩
  rw [heq]
  exact hAnorm

end S05P086
end

section
open QAlgorithms.Papers.Independent.Intakethird100.P92

namespace S05P086

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- On the full domain, a bounded extension of the paired operator is symmetric
for the reflected form whenever the two paired operators are equal. -/
theorem reflected_symmetry_of_full_domain [hHilbert : CompleteSpace E]
    (r : ReflectionData E) (D : Submodule ℂ r.plus)
    (T U : D →ₗ[ℂ] r.plus)
    (hPair : ∀ v w : D,
      inner ℂ (r.theta (T v : E)) (w : E) =
        inner ℂ (r.theta (v : E)) (U w : E))
    (B : r.plus →L[ℂ] r.plus) (hBT : ∀ v : D, B v = T v)
    (hD : D = ⊤) (hTU : T = U) :
    ∀ v w : r.plus,
      inner ℂ (r.theta (B v : E)) (w : E) =
        inner ℂ (r.theta (v : E)) (B w : E) := by
  intro v w
  let vd : D := ⟨v, by rw [hD]; trivial⟩
  let wd : D := ⟨w, by rw [hD]; trivial⟩
  have hv : T vd = B v := (hBT vd).symm
  have hw : U wd = B w := by
    rw [← hTU]
    exact (hBT wd).symm
  simpa only [hv, hw] using hPair vd wd

end S05P086
end

section
open QAlgorithms.Papers.Independent.Intakethird100.P92



open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Lemma 2.2, PDF pp. 8--9, all four clauses. The adjoint inclusion is stated
by its defining pairing identity on the dense common domain q(D), so it does not
incorrectly treat unbounded adjoints as everywhere-defined bounded operators.
The printed Eplus domain in (i) is D, as explicitly used in equation (5). -/
theorem solution [hHilbert : CompleteSpace E] (r : ReflectionData E) (D : Submodule ℂ r.plus)
    (hDense : Dense ((D.map (osQ r) : Submodule ℂ (OS r)) : Set (OS r)))
    (T U : D →ₗ[ℂ] r.plus)
    (hPair : ∀ v w : D,
      inner ℂ (r.theta (T v : E)) (w : E) =
        inner ℂ (r.theta (v : E)) (U w : E)) :
    (∀ v : D, osQ r v = 0 → osQ r (T v) = 0 ∧ osQ r (U v) = 0) ∧
    ∃ Tq Uq : D.map (osQ r) →ₗ[ℂ] OS r,
      (∀ v, Tq (domainQ r D v) = osQ r (T v)) ∧
      (∀ v, Uq (domainQ r D v) = osQ r (U v)) ∧
      (∀ v w : D.map (osQ r),
        inner ℂ (Tq v) (w : OS r) = inner ℂ (v : OS r) (Uq w)) ∧
      (T = U → ∀ v w : D.map (osQ r),
        inner ℂ (Tq v) (w : OS r) = inner ℂ (v : OS r) (Tq w)) ∧
      (∀ B : r.plus →L[ℂ] r.plus, (∀ v : D, B v = T v) → D = ⊤ → T = U →
        (∀ v : r.plus, osExtension r B.toLinearMap (osQ r v) = osQ r (B v)) ∧
        (∀ v : D.map (osQ r), osExtension r B.toLinearMap v = Tq v) ∧
        ‖osExtension r B.toLinearMap‖ ≤ ‖B‖) := by
  obtain ⟨hn, Tq, Uq, hT, hU, hPairq, hSymq⟩ :=
    S05P086.operator_descent_algebra r D hDense T U hPair
  refine ⟨hn, Tq, Uq, hT, hU, hPairq, hSymq, ?_⟩
  intro B hBT hD hTU
  have hSym := S05P086.reflected_symmetry_of_full_domain r D T U hPair B hBT hD hTU
  obtain ⟨hExt, hNorm⟩ := S05P086.osExtension_of_symmetric r B hSym
  refine ⟨hExt, ?_, hNorm⟩
  intro v
  obtain ⟨w, rfl⟩ := S05P086.domainQ_surjective r D v
  change osExtension r B.toLinearMap (osQ r (w : r.plus)) = Tq (domainQ r D w)
  rw [hExt, hBT w, hT w]



end

end

#print axioms solution
#check @solution
