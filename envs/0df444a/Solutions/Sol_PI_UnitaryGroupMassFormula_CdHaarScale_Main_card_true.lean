-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CdHaarScale.Main.card_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:37:47.146452+00:00
-- url     : https://prove2.me/submissions/b3d34b80-fa79-43ab-865a-cf54888647ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CdHaarScale PI.UnitaryGroupMassFormula.CdHaarScale.Main
namespace PI.UnitaryGroupMassFormula.CdHaarScale.Main
theorem _root_.solution {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    (Finset.univ.filter (fun i : Fin n => ε i = true)).card = P := by
  have hset : Finset.univ.filter (fun i : Fin n => ε i = true) =
      (Finset.univ : Finset (Fin P)).map ⟨fun a => e (Sum.inl a), fun a b h => by simpa using h⟩ := by
    ext i
    obtain ⟨s, rfl⟩ := e.surjective i
    rcases s with a | a <;> simp [h1, h2]
    · exact ⟨a, rfl⟩
    · intro x hx
      exact Sum.inl_ne_inr (e.injective hx)
  rw [hset, Finset.card_map, Finset.card_univ, Fintype.card_fin]
end PI.UnitaryGroupMassFormula.CdHaarScale.Main
