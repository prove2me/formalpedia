-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_SerreVanish_equiv_789ceb8d773d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:40.707509+00:00
-- url     : https://prove2.me/submissions/f0e36fe6-a695-4efd-951c-ecfef90a3236

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealXgen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltMore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace SerreVanish
theorem _root_.solution (hC : GradedCech.Statement) :
    Kleiman.SerreVanish.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman.SerreVanish.Statement := by
  constructor
  · intro hA S _ _ N M _ _ _ _ G hfin
    obtain ⟨c₀, hc₀⟩ := hA S N M (gradedEquiv S N M G) hfin
    obtain ⟨e, -, -⟩ := hC S N
    refine ⟨c₀, fun i hi c hc => ?_⟩
    have := hc₀ i hi c hc
    exact (e M G i c).injective.subsingleton
  · intro hB S _ _ N M _ _ _ _ 𝓜 hfin
    obtain ⟨G, rfl⟩ := (gradedEquiv S N M).surjective 𝓜
    obtain ⟨c₀, hc₀⟩ := hB S N M G hfin
    obtain ⟨e, -, -⟩ := hC S N
    refine ⟨c₀, fun i hi c hc => ?_⟩
    have := hc₀ i hi c hc
    exact (e M G i c).symm.injective.subsingleton
end SerreVanish
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
