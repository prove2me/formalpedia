-- Prove2me | solution 1 for P2M_PI_MirabolicIndex__card_mirab_5807049d95f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:32:16.223675+00:00
-- url     : https://prove2.me/submissions/19ef7639-5d67-4215-ae5d-b33d631cf31d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MirabIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicIndex_RowMulOfMirab
import Theorems.Thm_P2M_PI_MirabolicIndex__prod_sub_pow_61c489d9da34
import Theorems.Thm_P2M_PI_MirabolicIndex__card_GL_eq_7b3d39d97820

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
theorem _root_.solution (n : ℕ) :
    Nat.card {h : GL (Fin (n + 1)) k // IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} =
      Fintype.card k ^ ((n + 1) * n / 2) *
        ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) := by
  have h1 := card_GL_eq (k := k) n
  rw [Matrix.card_GL_field, Fin.prod_univ_succ] at h1
  simp only [Fin.val_zero, pow_zero, Fin.val_succ] at h1
  rw [prod_sub_pow] at h1
  have hk : 1 < Fintype.card k := Fintype.one_lt_card
  have hp : Fintype.card k ^ 1 ≤ Fintype.card k ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_one] at hp
  exact (Nat.eq_of_mul_eq_mul_left (by omega) h1).symm
end PI.MirabolicIndex₂
