-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hint_lin_ae
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:04.743434+00:00
-- url     : https://prove2.me/submissions/c8468dfa-7b34-4158-a349-859f0f16673b

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {n : ℕ} (c : Fin n → ℂ) (hc : c ≠ 0) :
    ∀ᵐ s ∂(sphereProb n), ∑ j, c j * spherePoint s j ≠ 0 := by
  classical
  set Lc : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ :=
    ∑ j, c j • (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).toLinearMap with hLc
  have hL : ∀ x : EuclideanSpace ℂ (Fin n), Lc x = ∑ j, c j * WithLp.ofLp x j := by
    intro x
    simp [hLc]
  set H : Submodule ℝ (EuclideanSpace ℂ (Fin n)) := LinearMap.ker (Lc.restrictScalars ℝ) with hH
  have hHtop : H ≠ ⊤ := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    intro htop
    have hmem : EuclideanSpace.single j (1 : ℂ) ∈ H := htop ▸ Submodule.mem_top
    rw [hH, LinearMap.mem_ker, LinearMap.restrictScalars_apply, hL] at hmem
    simp at hmem
    exact hj hmem
  have hvol : (volume : Measure (EuclideanSpace ℂ (Fin n))) H = 0 :=
    Measure.addHaar_submodule _ H hHtop
  have hA : MeasurableSet {s : UnitSphereC n | ¬ (∑ j, c j * spherePoint s j ≠ 0)} := by
    simp only [not_not]
    exact (isClosed_eq (by unfold spherePoint; fun_prop) continuous_const).measurableSet
  rw [ae_iff]
  unfold sphereProb
  refine ProbabilityTheory.cond_absolutelyContinuous ?_
  rw [Measure.toSphere_apply' (μ := (volume : Measure (EuclideanSpace ℂ (Fin n)))) hA]
  apply mul_eq_zero_of_right
  refine measure_mono_null ?_ hvol
  rintro _ ⟨r, _, _, ⟨s, hs, rfl⟩, rfl⟩
  simp only [Set.mem_setOf_eq, not_not] at hs
  show r • (s : EuclideanSpace ℂ (Fin n)) ∈ H
  refine H.smul_mem r ?_
  rw [hH, LinearMap.mem_ker, LinearMap.restrictScalars_apply, hL]
  simpa [spherePoint] using hs
end ReciprocityTheory.ChartRestriction.G.T0
