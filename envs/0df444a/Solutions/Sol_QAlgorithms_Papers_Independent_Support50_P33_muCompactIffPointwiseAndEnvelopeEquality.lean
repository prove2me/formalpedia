-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P33.muCompactIffPointwiseAndEnvelopeEquality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:58:02.833305+00:00
-- url     : https://prove2.me/submissions/06d1cf14-3b12-4300-8d1d-3fc2fe00e943
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P33
import Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_continuousBoundedClosedHull
import Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_pointwiseObstruction

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open QAlgorithms.Papers.Independent.Frontier18.P10
open QAlgorithms.Papers.Independent.Dependency50.P25

private theorem closedEnvelope_lowerSemicontinuous
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (A : Set E) (f : E → EReal) :
    LowerSemicontinuous (fun x : A => closedConvexHullFunction A f x) := by
  let S : Set (E → EReal) := {g | extendedConvexOn A g ∧
    LowerSemicontinuous (fun x : A => g x) ∧ ∀ y ∈ A, g y ≤ f y}
  have hrepr (x : E) : closedConvexHullFunction A f x = ⨆ g : S, g.val x := by
    apply le_antisymm
    · apply sSup_le
      rintro r ⟨g, hgconv, hglsc, hgminor, rfl⟩
      exact le_iSup_of_le (⟨g, hgconv, hglsc, hgminor⟩ : S) le_rfl
    · apply iSup_le
      intro g
      exact le_sSup ⟨g.val, g.property.1, g.property.2.1, g.property.2.2, rfl⟩
  simp_rw [hrepr]
  exact lowerSemicontinuous_iSup (fun g : S => g.property.2.1)

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal

open QAlgorithms.Papers.Independent.Support50.P33

open QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P33.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P33.paperBorel

section LocallyConvexResults

variable {E : Type*} [UniformSpace E] [AddCommGroup E] [Module ℝ E]
    [hgroup : IsUniformAddGroup E] [hsmul : ContinuousSMul ℝ E]
    [hlc : LocallyConvexSpace ℝ E] [hhaus : T2Space E]

include hgroup hsmul hlc hhaus

/-- Remark 2 conclusion, arXiv:1004.3792v1, PDF p.6, displayed logical
identity. Equality of the ordinary and closed convex envelopes is required
only on A, for every bounded continuous real test function. -/
theorem solution (A : Set E)
    (hA : GeneralBarycenterSpace A) (hc : Convex ℝ A) :
    MuCompact A ↔ PointwiseMuCompact A ∧
      ∀ f : E → ℝ, BoundedContinuousOn A f → ∀ x ∈ A,
        convexHullFunction A (fun y => (f y : EReal)) x =
          closedConvexHullFunction A (fun y => (f y : EReal)) x := by
  constructor
  · intro hm
    refine ⟨?_, ?_⟩
    · intro x hx
      simpa only [Set.mem_singleton_iff] using
        hm {x} (singleton_subset_iff.mpr hx) isCompact_singleton
    · intro f hf x hx
      exact (continuousBoundedClosedHull A hA hc hm f hf).2 x hx |>.2
  · rintro ⟨hpoint, heq⟩
    by_contra hnot
    obtain ⟨f, hf, hnotlsc, _⟩ := pointwiseObstruction A hA hc hnot hpoint
    apply hnotlsc
    have heqfun : (fun x : A => convexHullFunction A (fun y => (f y : EReal)) x) =
        (fun x : A => closedConvexHullFunction A (fun y => (f y : EReal)) x) := by
      funext x
      exact heq f hf x x.property
    rw [heqfun]
    exact closedEnvelope_lowerSemicontinuous A (fun y => (f y : EReal))

end LocallyConvexResults



end
