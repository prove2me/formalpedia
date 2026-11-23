-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.integrableOn_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:43.346068+00:00
-- url     : https://prove2.me/submissions/7c45efa5-ea25-4d99-81c8-bbafc80641ec

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (g : X → ℝ) (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target := by
  set K := (A.chart j) '' tsupport (P.χ j)
  have hKc : IsCompact K := (isClosed_tsupport _).isCompact.image_of_continuousOn
    ((A.chart j).continuousOn.mono (P.tsupport_subset j))
  have hKt : K ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart j).map_source (P.tsupport_subset j hx)
  have hχc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have := (P.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at this
    exact this
  have h1 : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) K :=
    (hg j K hKt hKc).continuousOn_mul (hχc.mono hKt) hKc
  have h2 := h1.of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet (by
    rintro y ⟨hy, hyK⟩
    have : (A.chart j).symm y ∉ tsupport (P.χ j) := fun h =>
      hyK ⟨_, h, (A.chart j).right_inv hy⟩
    simp [image_eq_zero_of_notMem_tsupport this])
  simpa only [mul_assoc] using h2
end ReciprocityTheory.AnForm.M
