-- Prove2me | solution 1 for P2M_BandParity_T_eq__1be22a5fd3a8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:46.318845+00:00
-- url     : https://prove2.me/submissions/649a7056-6d30-4952-818b-2b5927db7dbe

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_cosetSum_eq_sum_ite
public import Theorems.Thm_BandParity_p_mul_S
public import Theorems.Thm_BandParity_distinct
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_quartic_values
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp5 : 5 < p) : T χ = (p : GaussianInt) * ((k χ : GaussianInt) + gi * (t χ)) := by
  have hsplit : T χ = (cosetSum χ 1 : GaussianInt) + gi * (cosetSum χ gi) -
      (cosetSum χ (-1)) - gi * (cosetSum χ (-gi)) := by
    unfold T
    simp only [cosetSum_eq_sum_ite, Int.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · rcases quartic_values χ hχ hn with h | h | h | h <;> rw [h] <;> simp [distinct]
  rw [hsplit, ← p_mul_S hχ hp5, ← p_mul_S hχ hp5, ← p_mul_S hχ hp5, ← p_mul_S hχ hp5, k, t]
  push_cast; ring
end BandParity
