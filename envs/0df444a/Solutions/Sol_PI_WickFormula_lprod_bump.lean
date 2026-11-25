-- Prove2me | solution 1 for PI.WickFormula.lprod_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:47.605359+00:00
-- url     : https://prove2.me/submissions/332ebcc9-dc50-4e68-8bcd-cf8d2354e9c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Theorems.Thm_PI_WickFormula_lprod_succ

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
variable {AA : Type} [Ring AA]
namespace PI.WickFormula
theorem _root_.solution {n : ℕ} (c : Fin n → AA) (hc : ∀ i i', Commute (c i) (c i'))
    (e e' : Fin n → ℕ) (i : Fin n) (h1 : e' i = e i + 1) (h2 : ∀ i', i' ≠ i → e' i' = e i') :
    lprod c e' = c i * lprod c e := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [lprod_succ c e', lprod_succ c e]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · have ht : (fun j : Fin n => e' j.succ) = fun j => e j.succ :=
        funext fun j => h2 _ (Fin.succ_ne_zero j)
      rw [ht, h1, pow_succ', mul_assoc]
    · have h0 : e' 0 = e 0 := h2 0 (Fin.succ_ne_zero j).symm
      have key := ih (fun i => c i.succ) (fun a b => hc _ _) (fun j => e j.succ) (fun j => e' j.succ) j h1
        (fun i' hi' => h2 _ (fun h => hi' (Fin.succ_injective _ h)))
      rw [h0, key]
      simp only [← mul_assoc, ((hc 0 j.succ).pow_left (e 0)).eq]
end PI.WickFormula
