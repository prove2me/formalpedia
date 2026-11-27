-- Prove2me | solution 1 for PositivityTheory.RgJS.newton_identities_low_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:58.396031+00:00
-- url     : https://prove2.me/submissions/dafa1de9-811a-45fd-8430-03573478cf6d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLowerBounds_NewtonIdentitiesLowDegree
import Theorems.Thm_PositivityTheory_RgJS_NewtonIdentitiesAlt_ev_card
import Theorems.Thm_PositivityTheory_RgJS_NewtonIdentitiesAlt_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open PositivityTheory PositivityTheory.RgJS
open NewtonIdentitiesAlt
namespace PositivityTheory.RgJS
theorem _root_.solution : NewtonLow := by
  intro N hN
  refine ⟨1 / 4, by norm_num, fun A _ a hA hprod => ?_⟩
  classical
  by_contra hlt
  push_neg at hlt
  have hp : ∀ k, 1 ≤ k → k ≤ N → ‖∑ i, a i ^ k‖ ≤ 1 / 2 := by
    intro k hk1 hkN
    by_contra hk
    push_neg at hk
    have hle : ‖∑ i, a i ^ k‖ ^ 2 ≤ ∑ m ∈ range N, ‖∑ i, a i ^ (m + 1)‖ ^ 2 := by
      have hmem : k - 1 ∈ range N := by
        rw [Finset.mem_range]
        omega
      have h4 := Finset.single_le_sum (f := fun m => ‖∑ i, a i ^ (m + 1)‖ ^ 2) (fun m _ => by positivity) hmem
      simpa [Nat.sub_add_cancel hk1] using h4
    nlinarith
  have h5 := bound a N (1 / 2) (by norm_num) (by norm_num) hp N hN le_rfl
  rw [← hA, ev_card, hprod] at h5
  norm_num at h5
end PositivityTheory.RgJS
