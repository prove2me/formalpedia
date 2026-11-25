-- Prove2me | solution 1 for P2M_GlobalTheory_SW_HaarAlg_hasLevel_map__fb46485b3230
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:38.847445+00:00
-- url     : https://prove2.me/submissions/e9f3ce3c-e287-48e0-91b6-947ce4012ae3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarAlg
variable {K : Type} [Field K] {κ ι : Type}
namespace GlobalTheory.SW.HaarAlg
theorem _root_.solution {R : ℕ} {φ ψ : Matrix κ ι K → ℂ} (h1 : HasLevel R φ) (h2 : HasLevel R ψ)
    (f : ℂ → ℂ → ℂ) (hf : f 0 0 = 0) : HasLevel R fun x => f (φ x) (ψ x) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · by_cases a : φ x = 0
    · by_cases b : ψ x = 0
      · exact (hx (by simp only [a, b, hf])).elim
      · exact h2.1 x b
    · exact h1.1 x a
  · simp only [h1.2 x y hy, h2.2 x y hy]
end GlobalTheory.SW.HaarAlg
