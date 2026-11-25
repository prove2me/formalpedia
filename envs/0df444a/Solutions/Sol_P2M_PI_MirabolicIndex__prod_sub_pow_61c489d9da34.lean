-- Prove2me | solution 1 for P2M_PI_MirabolicIndex__prod_sub_pow_61c489d9da34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:56.420483+00:00
-- url     : https://prove2.me/submissions/4e39ead4-c774-4e4a-bc3f-a2a0884eebeb

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
namespace PI.MirabolicIndex₂
theorem _root_.solution (q n : ℕ) :
    ∏ i : Fin n, (q ^ (n + 1) - q ^ ((i : ℕ) + 1)) =
      q ^ ((n + 1) * n / 2) * ∏ i ∈ Finset.Ico 1 (n + 1), (q ^ i - 1) := by
  have hfac : ∀ i : Fin n, q ^ (n + 1) - q ^ ((i : ℕ) + 1) = q ^ ((i : ℕ) + 1) * (q ^ (n - i) - 1) := by
    intro i
    have hi : (i : ℕ) + 1 + (n - i) = n + 1 := by omega
    rw [Nat.mul_sub_one, ← pow_add, hi]
  have h2 : ∑ i ∈ Finset.range n, (i + 1) = (n + 1) * n / 2 := by
    have h3 := Finset.sum_range_id (n + 1)
    rw [Finset.sum_range_succ'] at h3
    simpa using h3
  rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun i => i + 1) n, h2]
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ (n - i) - 1) n, Finset.prod_Ico_eq_prod_range,
    Nat.add_sub_cancel, ← Finset.prod_range_reflect (fun j => q ^ (1 + j) - 1) n]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  show q ^ (n - i) - 1 = q ^ (1 + (n - 1 - i)) - 1
  rw [show 1 + (n - 1 - i) = n - i by omega]
end PI.MirabolicIndex₂
