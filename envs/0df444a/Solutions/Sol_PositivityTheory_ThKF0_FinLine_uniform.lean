-- Prove2me | solution 1 for PositivityTheory.ThKF0.FinLine.uniform
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:41.373053+00:00
-- url     : https://prove2.me/submissions/ca3ead11-41b0-4e26-af80-d24980cae9d7

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Filter Topology
open scoped Classical
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.FinLine
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
namespace PositivityTheory.ThKF0.FinLine
theorem _root_.solution {φ : G → ℂ} (hφ : φ ∈ SB G) : ∃ U : OpenAddSubgroup G, ∀ u ∈ U, ∀ x, φ (x + u) = φ x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : G), ∀ z ∈ tsupport φ, φ (z + t) = φ z := by
    refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : G × G => (φ (q.2 + q.1), φ q.2) :=
      (hφ.1.comp_continuous (by fun_prop)).prodMk (hφ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h1
  refine ⟨U, fun u hu z => ?_⟩
  by_cases hz : z ∈ tsupport φ
  · exact hU hu z hz
  by_cases hz' : z + u ∈ tsupport φ
  · have := hU (U.neg_mem hu) _ hz'
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']
end PositivityTheory.ThKF0.FinLine
