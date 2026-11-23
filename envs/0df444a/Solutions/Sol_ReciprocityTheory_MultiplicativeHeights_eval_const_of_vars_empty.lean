-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.eval_const_of_vars_empty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:19.819528+00:00
-- url     : https://prove2.me/submissions/6e995223-ba85-4ce6-a493-231277d8c962

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (f : MvPolynomial ι ℂ) (hf : f.vars ⊆ ∅) (x : ι → ℂ) :
    MvPolynomial.eval x f = MvPolynomial.constantCoeff f := by
  have := MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars (RingHom.id ℂ) (g := x) (p := f)
    (fun i hi => absurd (hf hi) (by simp))
  simpa using this
end ReciprocityTheory.MultiplicativeHeights
