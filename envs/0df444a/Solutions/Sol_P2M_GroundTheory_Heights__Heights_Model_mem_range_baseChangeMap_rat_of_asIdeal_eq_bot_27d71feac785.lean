-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_mem_range_baseChangeMap_rat_of_asIdeal_eq_bot_27d71feac785
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:44.779307+00:00
-- url     : https://prove2.me/submissions/748065fa-5a24-4518-82ac-83b574415233

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsInvOpenInsideRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PInvOpenInsideRat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {X : Scheme.{0}} (f : X ⟶ SpecZ) (x : X)
    (hx : (f.base x).asIdeal = ⊥) : x ∈ Set.range (baseChangeMap f ℚ) := by
  let y : Spec (CommRingCat.of ℚ) := ⟨⊥, Ideal.isPrime_bot⟩
  have h : f.base x = (Spec.map (CommRingCat.ofHom (Int.castRingHom ℚ))).base y := by
    apply PrimeSpectrum.ext
    rw [hx]
    change ⊥ = Ideal.comap (Int.castRingHom ℚ) ⊥
    exact (Ideal.comap_bot_of_injective _ (Int.cast_injective (α := ℚ))).symm
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  exact ⟨z, hz⟩
end GroundTheory.Heights₂.Heights.Model
