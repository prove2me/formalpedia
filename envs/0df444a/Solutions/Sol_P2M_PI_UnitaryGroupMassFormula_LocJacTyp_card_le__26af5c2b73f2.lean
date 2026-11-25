-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_le__26af5c2b73f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:48:10.197047+00:00
-- url     : https://prove2.me/submissions/f9eabd75-32d0-4fc8-a698-4dd37da4b42c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (r : ℕ) (i : Fin (r + 1)) :
    ((Finset.univ.filter fun l : Fin r => (i : ℕ) ≤ (l : ℕ)).card : ℝ) = (r : ℝ) - (i : ℕ) := by
  have h : (Finset.univ.filter fun l : Fin r => (i : ℕ) ≤ (l : ℕ)).map Fin.valEmbedding =
      Finset.Ico (i : ℕ) r := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨hl, l.2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨n, h2⟩, h1, rfl⟩
  rw [← Finset.card_map, h, Nat.card_Ico, Nat.cast_sub i.is_le]
end PI.UnitaryGroupMassFormula.LocJacTyp
