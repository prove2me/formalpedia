-- Prove2me | solution 1 for PI.ScPiFrameW.frame_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:37.555799+00:00
-- url     : https://prove2.me/submissions/cf6d7432-9d13-4453-a541-4eae6218a4ea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_FrameCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_Transfer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_FrameHolds
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScPiFrameW_frame_core
import Theorems.Thm_PI_ScPiFrameW_hJ_rv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.ScPiFrameW
open PI.ScPiExists
namespace PI.ScPiFrameW
theorem _root_.solution : PI.ScPiExists.Frame := by
  intro I r k e f z hn hfr ⟨t, ht, hzz⟩ hε v
  obtain ⟨hee, hff, hef, hz⟩ := hfr
  have hσ : ∃ σ : Fin (r + 1) → Fin I.n, ∀ i, I.ε v i = false → ∃ j, σ j = i := by
    refine ⟨fun j => ⟨min ((k - 1) + 2 * j.val + 1) (I.n - 1), by omega⟩, ?_⟩
    intro i hi
    rw [hε v i] at hi
    have h2 : ¬ i.val < k - 1 ∧ (i.val - (k - 1)) % 2 ≠ 0 := by
      by_cases h1 : i.val < k - 1
      · simp [h1] at hi
      · simp [h1] at hi
        exact ⟨h1, by omega⟩
    have hi' := i.isLt
    refine ⟨⟨(i.val - (k - 1)) / 2, by omega⟩, ?_⟩
    apply Fin.ext
    show min ((k - 1) + 2 * ((i.val - (k - 1)) / 2) + 1) (I.n - 1) = i.val
    omega
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨w, hw1, hw2⟩ := frame_core (I.ε v) hn σ hσ (fun a => rv I v (e a))
    (fun a => rv I v (f a)) (rv I v z) (t : ℝ) (by exact_mod_cast ht)
    (fun a b => by rw [hJ_rv, hee a b, map_zero]) (fun a b => by rw [hJ_rv, hff a b, map_zero])
    (fun a b => by rw [hJ_rv, hef a b]; split_ifs <;> simp)
    (fun a => by rw [hJ_rv, (hz a).1, map_zero]) (fun a => by rw [hJ_rv, (hz a).2, map_zero])
    (by rw [hJ_rv, hzz]; simp)
  exact ⟨w, hw1, hw2⟩
end PI.ScPiFrameW
