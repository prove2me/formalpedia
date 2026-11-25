-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.eIdx_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:39:25.009348+00:00
-- url     : https://prove2.me/submissions/dfcb8c02-dbdc-4623-b692-1bd3678268cb

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
theorem _root_.solution (D m : ℕ) : Function.Injective (eIdx D m) := by
  rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  induction j₁ using Fin.cases <;> induction j₂ using Fin.cases <;>
    induction i₁ using Fin.cases <;> induction i₂ using Fin.cases <;>
    simp_all [eIdx]
end ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
