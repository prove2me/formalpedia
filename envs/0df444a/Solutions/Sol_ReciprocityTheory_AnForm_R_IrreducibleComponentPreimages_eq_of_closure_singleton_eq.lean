-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.eq_of_closure_singleton_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:27.783838+00:00
-- url     : https://prove2.me/submissions/c1465c5b-0efb-4baa-8a1d-f7ea986cd080

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
theorem _root_.solution {x x' : W} (h : closure ({x} : Set W) = closure {x'}) : x = x' := by
  exact (inseparable_iff_closure_eq.2 h).eq
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
