-- Prove2me | solution 1 for P2M_UpperTheory_Comparison__formB_6c7ebdcf2338
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:39:02.49677+00:00
-- url     : https://prove2.me/submissions/a26bafc0-4a13-46fd-90c0-70a8117afe69

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_LevelFamily
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ZeroFreeOfRpowWindow
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_Imports
import Theorems.Thm_Deduction_zeroFree_of_rpow_window
import Theorems.Thm_P2M_UpperTheory_Comparison__level_family_500f33f210e6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost
namespace UpperTheory.Comparison₂
theorem _root_.solution :
    ∀ Λ : Level, Λ.FormB := by
  intro Λ la hla θ hθ0 hθ1 hW
  obtain ⟨F, hG, hZ⟩ := UpperTheory.Comparison₂.level_family Λ
  rw [← hZ]
  refine Deduction.zeroFree_of_rpow_window F (δ := la - 1) (C := 1) hθ0 hθ1 (by linarith) fun Y₀ => ?_
  obtain ⟨Y, hY, hx⟩ := hW Y₀
  refine ⟨Y, hY, fun y hy => ?_⟩
  have h1 : (1 : ℝ) + (la - 1) = la := by ring
  rw [h1] at hy
  rw [hG, one_mul]
  exact hx y hy.1 hy.2
end UpperTheory.Comparison₂
