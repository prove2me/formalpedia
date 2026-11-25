-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.gp_closure_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:58.224616+00:00
-- url     : https://prove2.me/submissions/c8eb323c-056e-4752-a2a9-322eb5a831ab

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution {x : W} (h : IsIrreducible (closure ({x} : Set W))) :
    h.genericPoint = x := by
  have hs : closure {h.genericPoint} = closure ({x} : Set W) :=
    h.isGenericPoint_genericPoint isClosed_closure
  exact (inseparable_iff_closure_eq.2 hs).eq
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
