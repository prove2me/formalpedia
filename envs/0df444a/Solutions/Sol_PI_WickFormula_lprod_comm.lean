-- Prove2me | solution 1 for PI.WickFormula.lprod_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:35:13.672078+00:00
-- url     : https://prove2.me/submissions/be2ee56e-cf78-43bf-bc30-48d2802020a0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul
import Theorems.Thm_PI_WickFormula_comm_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
variable {k AA : Type} [CommRing k] [Ring AA] [Algebra k AA]
namespace PI.WickFormula
theorem _root_.solution {n : ℕ} (c : Fin n → AA) (hc : ∀ i i', Commute (c i) (c i')) (b : AA) (t : Fin n → k)
    (h : ∀ j, b * c j = c j * b + algebraMap k AA (t j)) (e : Fin n → ℕ) :
    b * lprod c e = lprod c e * b +
      ∑ j, ((e j : k) * t j) • lprod c (fun j' => e j' - if j = j' then 1 else 0) := by
  induction n with
  | zero => simp [lprod]
  | succ n ih =>
    have key : ∀ (e : Fin (n + 1) → ℕ), lprod c e = c 0 ^ e 0 * lprod (fun i => c i.succ) (fun i => e i.succ) := by
      intro e; simp [lprod, List.ofFn_succ]
    have ih' := ih (fun i => c i.succ) (fun i i' => hc _ _) (fun i => t i.succ) (fun j => h j.succ)
      (fun i => e i.succ)
    rw [key, ← mul_assoc, comm_pow b (c 0) (t 0) (h 0) (e 0), add_mul, mul_assoc, ih', Fin.sum_univ_succ]
    simp only [key, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm, Fin.succ_inj, if_true, if_false, tsub_zero,
      mul_add, Finset.mul_sum, mul_smul_comm, smul_mul_assoc, ← mul_assoc, ite_true, ite_false]
    abel
end PI.WickFormula
