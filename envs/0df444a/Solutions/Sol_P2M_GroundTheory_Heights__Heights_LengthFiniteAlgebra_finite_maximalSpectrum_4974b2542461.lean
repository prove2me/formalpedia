-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finite_maximalSpectrum_4974b2542461
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:47.942104+00:00
-- url     : https://prove2.me/submissions/14054afc-8d67-4ef0-8a87-45b9f9bcd543

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthFiniteAlgebra
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_comap_eq_maximalIdeal_cc86a5f9bf6a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]
namespace GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
theorem _root_.solution [Module.Finite O B] : Finite (MaximalSpectrum B) := by
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := O) (S := B) (maximalIdeal O)
  have := hfin.to_subtype
  refine Finite.of_injective (β := (maximalIdeal O).primesOver B)
    (fun P => ⟨P.asIdeal, P.isMaximal.isPrime, ⟨(comap_eq_maximalIdeal P.asIdeal).symm⟩⟩) ?_
  intro P Q h
  exact MaximalSpectrum.ext (congrArg Subtype.val h)
end GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
