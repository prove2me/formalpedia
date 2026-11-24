-- Prove2me | solution 1 for PositivityTheory.ThKF0.FinLine.ind_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:01.421954+00:00
-- url     : https://prove2.me/submissions/9cfa12d1-2b2b-4e40-a453-68ddee17555a

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
theorem _root_.solution {U₀ U : OpenAddSubgroup G} (h₀ : IsCompact (U₀ : Set G)) (hU : U ≤ U₀) (a : G) : ind U a ∈ SB G := by
  have hc : IsClopen ((fun x => x - a) ⁻¹' (U : Set G)) := U.isClopen.preimage (continuous_sub_right a)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_, ?_⟩
  · by_cases hx : x - a ∈ U
    · filter_upwards [hc.isOpen.mem_nhds hx] with z hz
      exact (if_pos hz).trans (if_pos hx).symm
    · filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with z hz
      exact (if_neg hz).trans (if_neg hx).symm
  · refine HasCompactSupport.intro (h₀.image (continuous_add_right a)) fun y hy => if_neg fun h => hy ?_
    exact ⟨y - a, hU h, sub_add_cancel y a⟩
end PositivityTheory.ThKF0.FinLine
