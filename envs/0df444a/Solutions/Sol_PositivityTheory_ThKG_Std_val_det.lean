-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.val_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:37:18.715843+00:00
-- url     : https://prove2.me/submissions/de9f525f-bbe7-49d5-9fc6-76362ff8d921

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_SplitProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d n₁ d₁ : ℕ} {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable {jr : Fin n₁ → Fin n} {jc : Fin d₁ → Fin d}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution {N : Matrix (Fin n) (Fin n) k} (h : ∀ i j, valuation k (N i j) ≤ 1) : valuation k N.det ≤ 1 := by
  have : N = (Matrix.of fun i j => (⟨N i j, h i j⟩ : 𝒪[k])).map (algebraMap 𝒪[k] k) := rfl
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (Matrix.det _ : 𝒪[k]).2
end PositivityTheory.ThKG.Std
