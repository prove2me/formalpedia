-- Prove2me | solution 1 for PI.WeylForKWork.card_lt_eMi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:53.358385+00:00
-- url     : https://prove2.me/submissions/523ea751-c146-44e3-b8bb-ef1c730ebe47

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Formula
import Theorems.Thm_PI_WeylForKWork_eps_ePl
import Theorems.Thm_PI_WeylForKWork_eps_eMi
import Theorems.Thm_PI_WeylForKWork_eMi_lt_iff
import Theorems.Thm_PI_WeylForKWork_eMi_inj
import Theorems.Thm_PI_WeylForKWork_prod_split
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.WeylForKWork
open PI PI.UpqRep Matrix Finset
variable {N : ℕ}
private theorem exists_eMi_eq_of_false (ε : Fin N → Bool) (b : Fin N) (hb : ε b = false) :
    ∃ k, eMi ε k = b := by
  obtain ⟨x, rfl⟩ := (blk ε).surjective b
  rcases x with k | j
  · have h2 : ε (blk ε (Sum.inl k)) = true := eps_ePl ε k
    rw [h2] at hb
    exact absurd hb (by decide)
  · exact ⟨j, rfl⟩
end PI.WeylForKWork
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix Finset
variable {N : ℕ}
namespace PI.WeylForKWork
theorem _root_.solution (ε : Fin N → Bool) (i : Fin (nMi ε)) :
    (univ.filter fun b => b < eMi ε i ∧ ε b = ε (eMi ε i)).card = (i : ℕ) := by
  have hs : (univ.filter fun b => b < eMi ε i ∧ ε b = ε (eMi ε i)) =
      (Finset.Iio i).map ⟨eMi ε, show Function.Injective (eMi ε) from fun a b h => (eMi_inj ε a b).1 h⟩ := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_map, mem_Iio, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hb, he⟩
      rw [eps_eMi ε i] at he
      obtain ⟨k, rfl⟩ := exists_eMi_eq_of_false ε b he
      exact ⟨k, (eMi_lt_iff ε k i).1 hb, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(eMi_lt_iff ε k i).2 hk, by rw [eps_eMi ε i, eps_eMi ε k]⟩
  rw [hs, Finset.card_map, Fin.card_Iio]
end PI.WeylForKWork
