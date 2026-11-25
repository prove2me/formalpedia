-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_proof_ccfdbd9abfa6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:20.955502+00:00
-- url     : https://prove2.me/submissions/532ff753-966e-44af-aece-210465893c30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerAtPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hf_single_incl_598849498d15
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hf_single_single_76068ab7bbd0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_embed_eich_0fac005eb313

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerAtPlace
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerAtPlace
theorem _root_.solution (hPM : PlaceMaps.Statement) : EichlerAtPlace.Statement := by
  intro F E _ _ _ _ _ c hF hc v N J
  obtain ⟨-, hv⟩ := hPM F E c hF hc
  obtain ⟨-, -, hmul, -, hsi, hsig, -⟩ := hv v
  have key := fun e u c' => embed_eich c v hsi hsig J e u c'
  refine ⟨key, fun _ e f _ _ _ g hg => ?_⟩
  have along : ∀ a b : Fin N → E,
      g ∈ eichAlong (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ a) (inclV E v ∘ b) →
      embed E v g ∈ eichAlong (sigA c) (J.map (inclA F E)) (inclA F E ∘ a) (inclA F E ∘ b) := by
    rintro a b ⟨u, c', hua, hub, hc', rfl⟩
    refine ⟨singleV E v ∘ u, singleV E v c', ?_, ?_, ?_, key a u c'⟩
    · rw [hf_single_incl c v hsi J, hua, map_zero]
    · rw [hf_single_incl c v hsi J, hub, map_zero]
    · rw [hf_single_single c v hsi hmul hsig J, hsig, ← map_add, ← map_add]
      exact (congrArg (singleV E v) hc').trans (map_zero _)
  rcases hg with hg | hg
  · exact Or.inl (along e f hg)
  · exact Or.inr (along f e hg)
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerAtPlace
