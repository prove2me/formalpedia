-- Prove2me | solution 1 for PalomarCrouzeixPalencia.exists_unitary_power_dilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:26:22.396677+00:00
-- url     : https://prove2.me/submissions/936370c1-df08-4e2e-8b0b-09ffe793d668

import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_CrouzeixPalenciaSolution
import Theorems.Thm_exists_unitary_power_dilation

section
open scoped InnerProductSpace Polynomial
namespace PalomarCrouzeixPalencia
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem root_exists_unitary_power_dilation (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (V : E →L[ℂ] H) (U : H →L[ℂ] H),
    (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    U ∈ unitary (H →L[ℂ] H) ∧
    (∀ (n : ℕ) (x : E),
      ContinuousLinearMap.adjoint V ((U ^ n) (V x)) = (T ^ n) x) :=
  _root_.exists_unitary_power_dilation T hT
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
theorem _root_.solution (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (V : E →L[ℂ] H) (U : H →L[ℂ] H),
    (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    U ∈ unitary (H →L[ℂ] H) ∧
    (∀ (n : ℕ) (x : E),
      ContinuousLinearMap.adjoint V ((U ^ n) (V x)) = (T ^ n) x) :=
  root_exists_unitary_power_dilation T hT
end PalomarCrouzeixPalencia
