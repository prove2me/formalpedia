-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.foldr_fderiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:30.552326+00:00
-- url     : https://prove2.me/submissions/7b0e8063-15ce-4a60-a485-cb476adde2ec

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Z
theorem _root_.solution (G : MC n → ℂ) (U : Set (MC n)) (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) :
    ∀ (m : ℕ) (v : Fin m → MC n),
      AnalyticOnNhd ℂ ((List.finRange m).foldr (fun k H => fun B => fderiv ℂ H B (v k)) G) U ∧
      ∀ B ∈ U, ((List.finRange m).foldr (fun k H => fun B => fderiv ℂ H B (v k)) G) B = iteratedFDeriv ℂ m G B v := by
  intro m
  induction m with
  | zero =>
    intro v
    refine ⟨by simpa [List.finRange_zero] using hG, fun B _ => ?_⟩
    simp [List.finRange_zero, iteratedFDeriv_zero_apply]
  | succ m ih =>
    intro v
    obtain ⟨ha, he⟩ := ih (Fin.tail v)
    have e : (List.finRange (m + 1)).foldr (fun k H => fun B => fderiv ℂ H B (v k)) G =
        fun B => fderiv ℂ ((List.finRange m).foldr (fun k H => fun B => fderiv ℂ H B (Fin.tail v k)) G) B (v 0) := by
      rw [List.finRange_succ, List.foldr_cons, List.foldr_map]
      rfl
    rw [e]
    refine ⟨fun B hB => ((ContinuousLinearMap.apply ℂ ℂ (v 0)).analyticAt _).comp ((ha.fderiv_of_isOpen hU) B hB),
      fun B hB => ?_⟩
    have hev : (List.finRange m).foldr (fun k H => fun B => fderiv ℂ H B (Fin.tail v k)) G =ᶠ[nhds B]
        fun B => iteratedFDeriv ℂ m G B (Fin.tail v) :=
      Filter.eventually_of_mem (hU.mem_nhds hB) fun B' hB' => he B' hB'
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ m G) B :=
      ((hG.iteratedFDeriv_of_isOpen hU m) B hB).differentiableAt
    beta_reduce
    rw [hev.fderiv_eq, fderiv_continuousMultilinear_apply_const_apply hd, iteratedFDeriv_succ_apply_left]
end PositivityTheory.Rg.Sw.WR.Z
