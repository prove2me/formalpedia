-- Prove2me | solution 1 for PI.CharIdemW.scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:44.179395+00:00
-- url     : https://prove2.me/submissions/1d40f1f8-dee8-402f-9387-62512f35661e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
import Theorems.Thm_PI_CharIdemW_nontrivial_of_simple
import Theorems.Thm_PI_CharIdemW_act_charIdem_eq_smul
import Theorems.Thm_PI_CharIdemW_trace_act_charIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
namespace PI.CharIdemW
theorem _root_.solution : Scalar := by
  intro G _ _ V W hV hW
  have := hV
  have := hW
  obtain ⟨c, hc⟩ := act_charIdem_eq_smul V W
  have htr := trace_act_charIdem V W
  rw [hc, map_smul, LinearMap.trace_one, smul_eq_mul] at htr
  have hWpos : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    have := nontrivial_of_simple W
    exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  constructor
  · rintro ⟨e⟩
    have hWV : Nonempty (W ≅ V) := ⟨e.symm⟩
    have hdim : (Module.finrank ℂ V : ℂ) = Module.finrank ℂ W := by
      have := congr_fun (FDRep.char_iso e) 1
      rwa [FDRep.char_one, FDRep.char_one] at this
    rw [if_pos hWV, hdim, mul_one] at htr
    have hc1 : c = 1 := mul_right_cancel₀ hWpos (htr.trans (one_mul _).symm)
    rw [hc, hc1, one_smul]
  · intro hE
    have hn : ¬ Nonempty (W ≅ V) := fun ⟨e⟩ => hE.false e.symm
    rw [if_neg hn, mul_zero] at htr
    rw [hc, (mul_eq_zero.mp htr).resolve_right hWpos, zero_smul]
end PI.CharIdemW
