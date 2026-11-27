-- Prove2me | solution 1 for ReciprocityTheory.PGsh.convD_groupLike
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:32:48.900806+00:00
-- url     : https://prove2.me/submissions/acb6df5a-5d17-470c-b0f8-27147d1fdb46

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (δ : A →ₗ[R] R) {χ : A} (h : IsGroupLikeElem R χ) :
    convD δ χ = δ χ • χ := by
  simp [convD, h.comul_eq_tmul_self]
end ReciprocityTheory.PGsh
