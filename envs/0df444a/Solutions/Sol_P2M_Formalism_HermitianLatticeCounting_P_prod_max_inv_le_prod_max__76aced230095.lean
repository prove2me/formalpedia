-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_P_prod_max_inv_le_prod_max__76aced230095
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:43:46.423578+00:00
-- url     : https://prove2.me/submissions/04d7e087-0ff2-46d1-b941-c9dadd509749

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.ProdMaxInvLeProdMax := by
  intro ι _ G hG h1
  have h : ∀ v, max 1 (1 / G v) = max 1 (G v) / G v := by
    intro v
    have h0 := hG v
    rcases le_total 1 (G v) with h | h
    · rw [max_eq_left, max_eq_right h, div_self h0.ne']
      rw [div_le_one h0]; exact h
    · rw [max_eq_right, max_eq_left h]
      rw [le_div_iff₀ h0]; simpa using h
  simp_rw [h, Finset.prod_div_distrib]
  apply div_le_self
  · exact Finset.prod_nonneg fun v _ => by positivity
  · exact h1
end Formalism.HermitianLatticeCounting.P
