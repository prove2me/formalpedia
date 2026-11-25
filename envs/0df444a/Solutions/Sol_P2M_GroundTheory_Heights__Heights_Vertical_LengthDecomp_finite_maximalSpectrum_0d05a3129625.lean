-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_finite_maximalSpectrum_0d05a3129625
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:16.040716+00:00
-- url     : https://prove2.me/submissions/b3d36432-f0f8-4604-8bb8-56a051a9b307

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open Module IsLocalRing LinearMap Submodule
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
open Classical
variable {B : Type*} [CommRing B]
variable {R : Type*} [CommRing R] [Algebra R B]
variable {N : Type*} [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
namespace GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
theorem _root_.solution [IsLocalRing R] [Module.Finite R B] :
    Finite (MaximalSpectrum B) := by
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := R) (S := B) (maximalIdeal R)
  have := hfin.to_subtype
  refine Finite.of_injective (β := (maximalIdeal R).primesOver B)
    (fun n => ⟨n.asIdeal, n.isMaximal.isPrime, ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) n.asIdeal)).symm⟩⟩) ?_
  intro n n' hnn'
  exact MaximalSpectrum.ext (congrArg Subtype.val hnn')
end GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
