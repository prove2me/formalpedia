-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_prod_sub_prod_le_sum_abs_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:04.489802+00:00
-- url     : https://prove2.me/submissions/ee484c50-0408-4ca3-b571-69b140b9a2a6

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {κ : Type*} (s : Finset κ) (a b : κ → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, sum_insert hj]
    have hP : |∏ i ∈ s, b i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact prod_le_one (fun i _ => abs_nonneg _) (fun i hi => hb i (mem_insert_of_mem hi))
    have ih' := ih (fun i hi => ha i (mem_insert_of_mem hi)) (fun i hi => hb i (mem_insert_of_mem hi))
    have haj := ha j (mem_insert_self j s)
    have hsum : 0 ≤ ∑ i ∈ s, |a i - b i| := sum_nonneg fun i _ => abs_nonneg _
    calc |a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i|
        = |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i| := by ring_nf
      _ ≤ |a j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a j - b j| * |∏ i ∈ s, b i| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * ∑ i ∈ s, |a i - b i| + |a j - b j| * 1 :=
        add_le_add (mul_le_mul haj ih' (abs_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
      _ = |a j - b j| + ∑ i ∈ s, |a i - b i| := by ring
end ReciprocityTheory.Cheb
