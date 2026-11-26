-- Prove2me | solution 1 for PalomarCrouzeixPalencia.crouzeix_palencia
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:26:54.037345+00:00
-- url     : https://prove2.me/submissions/d426a226-02b1-45dd-b76c-0a114fbd671e

import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_CrouzeixPalenciaSolution
import Theorems.Thm_crouzeix_palencia

section
open scoped InnerProductSpace Polynomial
namespace PalomarCrouzeixPalencia
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem root_crouzeix_palencia (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) :=
  _root_.crouzeix_palencia A
end PalomarCrouzeixPalencia
end

set_option autoImplicit false
open scoped InnerProductSpace Polynomial
open PalomarCrouzeixPalencia
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PalomarCrouzeixPalencia
theorem _root_.solution (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) :=
  root_crouzeix_palencia A
end PalomarCrouzeixPalencia
