-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_ringHom_powerSeries_root__53a4dd468b91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:09.879646+00:00
-- url     : https://prove2.me/submissions/6a7ba785-b798-4144-bb74-93ce5ce20bde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingHomPowerSeriesRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingHomPowerSeriesRootStatement
import Theorems.Thm_GlobalTheory_exists_ringHom_powerSeries_root


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k → t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K, (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧ ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by
  first | exact @GlobalTheory.exists_ringHom_powerSeries_root | exact GlobalTheory.exists_ringHom_powerSeries_root | (intros; apply GlobalTheory.exists_ringHom_powerSeries_root <;> assumption)
end _root_.GlobalTheory.T
