-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ptIdeal_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:14.93634+00:00
-- url     : https://prove2.me/submissions/6392b380-356d-4df6-9642-2c4698eec39f

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineMultihomogClassify

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {n : ℕ} (p : Fin n → ℂ) : (ptIdeal p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩
end ReciprocityTheory.AnForm.R
