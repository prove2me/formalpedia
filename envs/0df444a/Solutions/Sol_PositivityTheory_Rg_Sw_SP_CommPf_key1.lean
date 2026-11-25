-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.CommPf.key1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:31.23226+00:00
-- url     : https://prove2.me/submissions/6ce682a5-3997-419f-bf33-2cde89548829

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DerivationConstantVanishes
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_CommPf_dl_other
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_CommPf_dl_C
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_CommPf_derivation_constant_vanishes
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_CommPf_dl_yv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
open PositivityTheory.Rg.Sw.SP.CommPf
namespace PositivityTheory.Rg.Sw.SP.CommPf
theorem _root_.solution (s : ℂ) (m : ℕ) (b b' : Bool) (k l k' l' : Fin n) :
    dl s b k l (mm s m b' k' l') = dl s b' k' l' (mm s m b k l) := by
  simp only [mm, Derivation.leibniz, derivation_constant_vanishes, dl_C, smul_zero, add_zero, smul_eq_mul]
  by_cases h : b = b'
  · subst h
    rw [dl_yv, dl_yv]; ring
  · rw [dl_other s b b' h, dl_other s b' b (Ne.symm h)]; ring
end PositivityTheory.Rg.Sw.SP.CommPf
