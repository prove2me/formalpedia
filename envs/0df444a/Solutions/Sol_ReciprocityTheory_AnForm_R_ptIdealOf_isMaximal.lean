-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ptIdealOf_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:01:10.877164+00:00
-- url     : https://prove2.me/submissions/ba9c4c34-d475-4bbe-8116-73df5b1e2d99

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial Algebra
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {σ : Type} (z : σ → ℂ) : (ptIdealOf z).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun x => ⟨MvPolynomial.C x, MvPolynomial.eval_C x⟩
end ReciprocityTheory.AnForm.R
