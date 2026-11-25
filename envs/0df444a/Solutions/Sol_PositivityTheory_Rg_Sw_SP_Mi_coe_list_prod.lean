-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.coe_list_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:24.332259+00:00
-- url     : https://prove2.me/submissions/c01a5820-b805-478c-8612-828791dec7e2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R]
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution {A : Type} [Ring A] [Algebra R A] (S : Subalgebra R A) (l : List S) :
    ((l.prod : S) : A) = (l.map Subtype.val).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, ih]
end PositivityTheory.Rg.Sw.SP.Mi
