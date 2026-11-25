-- Prove2me | solution 1 for P2M_Formalism_G0_TopsChoiceProbabilityLemmas_tile_sub__fbbb87d340ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:53.692969+00:00
-- url     : https://prove2.me/submissions/5e13fdb4-1bf4-4f9c-8c49-312bef7abd44

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsChoiceProbabilityLemmas
theorem _root_.solution {n r u s i₀ : ℕ} (hs : s < n / ((6 * r + 1) * u)) (hnot : i₀ ∉ tile r u s) :
    tile r u s ⊆ (range n).erase i₀ := by
  intro x hx
  have hx' := hx
  unfold tile at hx
  rw [mem_Ico] at hx
  have h2 := Nat.mul_le_mul_right ((6 * r + 1) * u) (show s + 1 ≤ n / ((6 * r + 1) * u) by omega)
  have h3 := Nat.div_mul_le_self n ((6 * r + 1) * u)
  rw [mem_erase, mem_range]
  refine ⟨fun hxi => hnot (hxi ▸ hx'), by omega⟩
end Formalism.G0.TopsChoiceProbabilityLemmas
