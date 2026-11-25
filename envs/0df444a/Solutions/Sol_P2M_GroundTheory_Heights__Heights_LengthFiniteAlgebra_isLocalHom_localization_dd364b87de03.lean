-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_isLocalHom_localization_dd364b87de03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:02:48.646592+00:00
-- url     : https://prove2.me/submissions/2e00db3b-fa59-4df9-814e-e31a99a69ea4

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
theorem _root_.solution [Module.Finite O B] (P : Ideal B) [P.IsMaximal] :
    IsLocalHom (algebraMap O (Localization.AtPrime P)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : a ∈ P.comap (algebraMap O B) := by
    rw [comap_eq_maximalIdeal P]; exact hna
  have h2 : algebraMap B (Localization.AtPrime P) (algebraMap O B a) ∈
      maximalIdeal (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).mpr h1
  rw [← IsScalarTower.algebraMap_apply] at h2
  exact h2 ha
end GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
