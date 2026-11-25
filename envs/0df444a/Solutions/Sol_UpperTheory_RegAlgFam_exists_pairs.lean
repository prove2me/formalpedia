-- Prove2me | solution 1 for UpperTheory.RegAlgFam.exists_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:58:33.314531+00:00
-- url     : https://prove2.me/submissions/08d4808f-b14b-4310-b5d2-23b0f4a56578

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_AlgebraicInfinityType_InfinityType
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_RegAlgFam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open UpperTheory UpperTheory.RegAlgFam
namespace UpperTheory.RegAlgFam
theorem _root_.solution {α : Type*} (s t : Multiset α) (h : s.card = t.card) :
    ∃ P : Multiset (α × α), P.map Prod.fst = s ∧ P.map Prod.snd = t := by
  induction s using Quotient.inductionOn with | _ l =>
  induction t using Quotient.inductionOn with | _ k =>
  have hl : l.length = k.length := by simpa using h
  refine ⟨(l.zip k : List (α × α)), ?_, ?_⟩
  · simp [List.map_fst_zip hl.le]
  · simp [List.map_snd_zip hl.ge]
end UpperTheory.RegAlgFam
