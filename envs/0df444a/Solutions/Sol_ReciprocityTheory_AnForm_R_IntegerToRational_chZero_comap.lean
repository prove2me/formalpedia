-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IntegerToRational.chZero_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:58.403904+00:00
-- url     : https://prove2.me/submissions/995be6db-27df-4a24-87e9-8dce718efab1

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace ReciprocityTheory.AnForm.R.IntegerToRational
theorem _root_.solution (Q : Ideal (MvPolynomial σ ℚ)) [Q.IsPrime] :
    ChZero (Q.comap (MvPolynomial.map (Int.castRingHom ℚ))) := by
  intro m hm
  rw [Ideal.mem_comap, MvPolynomial.map_C] at hm
  by_contra h
  have hu : IsUnit (C (Int.castRingHom ℚ m) : MvPolynomial σ ℚ) :=
    (isUnit_iff_ne_zero.mpr (by simpa using h)).map C
  exact (‹Q.IsPrime›).ne_top (Ideal.eq_top_of_isUnit_mem Q hm hu)
end ReciprocityTheory.AnForm.R.IntegerToRational
