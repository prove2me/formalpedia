-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.key_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:40.101007+00:00
-- url     : https://prove2.me/submissions/2e7f8e32-3ef7-40e3-b495-017628b44086

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Theorems.Thm_ReciprocityTheory_PGsh_Up_lam_pow
import Theorems.Thm_ReciprocityTheory_PGsh_Up_xc_eq
import Theorems.Thm_ReciprocityTheory_PGsh_Up_monF_split
import Theorems.Thm_ReciprocityTheory_PGsh_Up_prod_erase_update
import Theorems.Thm_ReciprocityTheory_PGsh_Up_sum_erase_update

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] {ι : Type} [Fintype ι]
  [DecidableEq ι]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) :
    ∀ (N : ℕ) (α : ι → ZMod p), ∑ j, (α j).val = N → ∀ l,
      (fun x => lam Cm l x * monF Cm α x) ∈
        Submodule.span k (Set.range (monF (p := p) Cm)) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro α hα l
  have hlt : (α l).val < p := ZMod.val_lt (α l)
  by_cases hcase : (α l).val + 1 < p
  ·
    have hv : (α l + 1).val = (α l).val + 1 := by
      rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < p),
        Nat.mod_eq_of_lt hcase]
    have hfun : (fun x => lam Cm l x * monF Cm α x) =
        monF Cm (Function.update α l (α l + 1)) := by
      funext x
      rw [monF_split Cm α l x, monF_split Cm (Function.update α l (α l + 1)) l x,
        prod_erase_update, Function.update_self, hv, pow_succ]
      ring
    rw [hfun]
    exact Submodule.subset_span ⟨_, rfl⟩
  ·
    have hval : (α l).val = p - 1 := by omega
    have hsplit : (α l).val + ∑ j ∈ univ.erase l, (α j).val = ∑ j, (α j).val :=
      Finset.add_sum_erase univ (fun j => (α j).val) (Finset.mem_univ l)
    have hsplitγ : (Function.update α l 0 l).val +
        ∑ j ∈ univ.erase l, (Function.update α l 0 j).val =
        ∑ j, (Function.update α l 0 j).val :=
      Finset.add_sum_erase univ (fun j => (Function.update α l 0 j).val) (Finset.mem_univ l)
    have hγl : (Function.update α l 0 l).val = 0 := by simp
    have hse := sum_erase_update α l 0
    have hlow : ∑ j, (Function.update α l 0 j).val < N := by omega
    have hfun : (fun x => lam Cm l x * monF Cm α x) =
        ∑ i, ∑ m, (Cm l i ^ p * Cinv i m) •
          (fun x => lam Cm m x * monF Cm (Function.update α l 0) x) := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have e1 : monF Cm α x = lam Cm l x ^ (p - 1) * monF Cm (Function.update α l 0) x := by
        rw [monF_split Cm α l x, monF_split Cm (Function.update α l 0) l x, prod_erase_update,
          Function.update_self, ZMod.val_zero, pow_zero, one_mul, hval]
      have e2 : lam Cm l x * lam Cm l x ^ (p - 1) = lam Cm l x ^ p := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
      rw [e1, ← mul_assoc, e2, lam_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [xc_eq Cm Cinv h i x, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hfun]
    refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ ?_))
    exact ih _ hlow _ rfl m
end ReciprocityTheory.PGsh.Up
