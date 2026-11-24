-- Prove2me | solution 1 for P2M_Formalism_IndefR_Fin_Four_integ_cmul__b92e15a955ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:13:25.933292+00:00
-- url     : https://prove2.me/submissions/88022d04-a305-4971-9382-53924265883f

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_eq
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_congr
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_cmul
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_cmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Finset
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W : Type*} [AddCommGroup W]
variable {H : AddSubgroup W} (hfin : ∀ k, 0 < k → Finite (Qt k H))
include hfin
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (g : W → ℂ) (c : ℂ) : integ H (fun t => c * g t) = c * integ H g := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    have h0 : IsInv 1 H (fun _ : W => (0 : ℂ)) := fun _ _ _ _ => rfl
    rw [integ_eq hfin Nat.one_pos h0]
    simp [avg]
  by_cases hg : ∃ k, 0 < k ∧ IsInv k H g
  · obtain ⟨k, hk, hgk⟩ := hg
    exact integ_cmul hfin hk hgk c
  · have hn : ¬ ∃ k, 0 < k ∧ IsInv k H (fun t => c * g t) := by
      rintro ⟨k, hk, hgk⟩
      refine hg ⟨k, hk, ?_⟩
      refine (hgk.cmul c⁻¹).congr fun t _ => ?_
      simp [hc]
    rw [integ, dif_neg hn, integ, dif_neg hg, mul_zero]
end Formalism.IndefR.Fin.Four
