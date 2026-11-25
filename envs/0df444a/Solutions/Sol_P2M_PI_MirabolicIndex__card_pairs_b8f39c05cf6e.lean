-- Prove2me | solution 1 for P2M_PI_MirabolicIndex__card_pairs_b8f39c05cf6e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:53.636001+00:00
-- url     : https://prove2.me/submissions/107d3d1e-0619-4f58-a957-a3b0d3e5e018

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MirabIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicIndex_RowMulOfMirab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.MirabolicIndex₂
open Finset Matrix PI.MirabIndex
variable {k : Type} [Field k] [Fintype k]
namespace PI.MirabolicIndex₂
theorem _root_.solution (n : ℕ) : Fintype.card (Pairs n) = (n + 1) * n / 2 := by
  have e : Pairs n ≃ Σ j : Fin (n + 1), {i : Fin (n + 1) // i < j} :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun x => ⟨(x.2.1, x.1), x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hj : ∀ j : Fin (n + 1), Fintype.card {i : Fin (n + 1) // i < j} = (j : ℕ) := fun j =>
    (Fintype.card_congr
      { toFun := fun i => (⟨i.1.val, i.2⟩ : Fin j.val)
        invFun := fun x => ⟨⟨x.val, lt_trans x.2 j.2⟩, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }).trans (Fintype.card_fin _)
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [hj]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) (n + 1), Finset.sum_range_id, Nat.add_sub_cancel]
end PI.MirabolicIndex₂
