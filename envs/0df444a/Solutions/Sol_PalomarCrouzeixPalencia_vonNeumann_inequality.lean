-- Prove2me | solution 1 for PalomarCrouzeixPalencia.vonNeumann_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:26:50.480856+00:00
-- url     : https://prove2.me/submissions/69f1a44b-8cc1-46ff-832b-a20745d64e68

import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_CrouzeixPalenciaSolution
import Theorems.Thm_vonNeumann_inequality

section
open scoped InnerProductSpace Polynomial
namespace PalomarCrouzeixPalencia
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem root_vonNeumann_inequality (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1)
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval T p‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) :=
  _root_.vonNeumann_inequality T hT p
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
theorem _root_.solution (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1)
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval T p‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) :=
  root_vonNeumann_inequality T hT p
end PalomarCrouzeixPalencia
