-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:22:25.976495+00:00
-- url     : https://prove2.me/submissions/529501b8-0c53-460b-b6b1-83b02d3abeca

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DerivationConstantVanishes
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_CommPf_opH_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_CommPf_key1
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_CommPf_key2

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
open CommPf
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution : Comm := by
  intro n s m b b' k l k' l'
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, opH_apply, Derivation.leibniz, map_add, smul_eq_mul]
  have h2 : dl s b k l (dl s b' k' l' p) = dl s b' k' l' (dl s b k l p) := by
    have := congrArg (fun D : Derivation (Polynomial ℂ) (Fm n) (Fm n) => D p) (key2 s b b' k l k' l')
    simpa [Derivation.commutator_apply, sub_eq_zero] using this
  rw [h2, key1 s m b b' k l k' l']
  ring
end PositivityTheory.Rg.Sw.SP
