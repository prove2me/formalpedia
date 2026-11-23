-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.coeffVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:59.322794+00:00
-- url     : https://prove2.me/submissions/9513743b-8a43-4961-9bee-e06b7146a6c6

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι : Type*} (T : Finset (ι →₀ ℕ)) (P : MvPolynomial ι ℂ) (t : T) :
    coeffVec T P t = P.coeff t := rfl
end ReciprocityTheory.MultiplicativeHeights
