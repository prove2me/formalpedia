-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CdHaarScale.Main.card_false
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:37:18.210696+00:00
-- url     : https://prove2.me/submissions/3945cdcd-0281-4271-bfb3-573eeca479f9

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
    (Finset.univ.filter (fun i : Fin n => ε i = false)).card = Q := by
  have hset : Finset.univ.filter (fun i : Fin n => ε i = false) =
      (Finset.univ : Finset (Fin Q)).map ⟨fun a => e (Sum.inr a), fun a b h => by simpa using h⟩ := by
    ext i
    obtain ⟨s, rfl⟩ := e.surjective i
    rcases s with a | a <;> simp [h1, h2]
    · intro x hx
      exact Sum.inr_ne_inl (e.injective hx)
    · exact ⟨a, rfl⟩
  rw [hset, Finset.card_map, Finset.card_univ, Fintype.card_fin]
end PI.UnitaryGroupMassFormula.CdHaarScale.Main
