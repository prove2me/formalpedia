-- Prove2me | solution 1 for ReciprocityTheory.Cheb.fibre_sum_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:54.928471+00:00
-- url     : https://prove2.me/submissions/88b4d09d-79de-4ee1-866b-599d0d5a0f26

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {α β : Type*} (π : α → β) (f : α → ℝ) (g : β → ℝ) (k : ℕ) (hf0 : ∀ a, 0 ≤ f a)
    (hf : Summable f) (hg0 : ∀ b, 0 ≤ g b) (hg : Summable g) (S : Set β) (hS : S.Finite)
    (hfib : ∀ b ∉ S, k ≤ {a | π a = b ∧ f a = g b}.ncard) :
    (k : ℝ) * ∑' b, g b ≤ ∑' a, f a + k * ∑' b, S.indicator g b := by
  classical
  have hf0' : 0 ≤ ∑' a, f a := tsum_nonneg hf0
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hf0'
  have hfin : ∀ b ∉ S, {a | π a = b ∧ f a = g b}.Finite := fun b hb =>
    Set.finite_of_ncard_pos (lt_of_lt_of_le hk (hfib b hb))
  let A : β → Finset α := fun b => if hb : b ∉ S then (hfin b hb).toFinset else ∅
  have hA : ∀ b a, a ∈ A b → π a = b ∧ f a = g b := by
    intro b a ha
    simp only [A] at ha
    split_ifs at ha with hb
    all_goals simp at ha
    all_goals exact ha
  have hcard : ∀ b ∉ S, k ≤ (A b).card := by
    intro b hb
    simp only [A, dif_pos hb]
    rw [← Set.ncard_eq_toFinset_card _ (hfin b hb)]
    exact hfib b hb
  have hdisj : ∀ v : Finset β, (v : Set β).PairwiseDisjoint A := by
    intro v b _ b' _ hbb'
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha ha'
    exact hbb' ((hA b a ha).1.symm.trans (hA b' a ha').1)
  have hmain : ∀ v : Finset β, ∑ b ∈ v, (k : ℝ) * Sᶜ.indicator g b ≤ ∑' a, f a := by
    intro v
    calc ∑ b ∈ v, (k : ℝ) * Sᶜ.indicator g b ≤ ∑ b ∈ v, ∑ a ∈ A b, f a := by
          refine Finset.sum_le_sum fun b _ => ?_
          by_cases hb : b ∈ S
          · rw [Set.indicator_of_notMem (by simpa using hb), mul_zero]
            exact Finset.sum_nonneg fun a _ => hf0 a
          · rw [Set.indicator_of_mem (by simpa using hb)]
            have e : ∑ a ∈ A b, f a = ∑ a ∈ A b, g b :=
              Finset.sum_congr rfl fun a ha => (hA b a ha).2
            rw [e, Finset.sum_const, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard b hb) (hg0 b)
      _ = ∑ a ∈ v.biUnion A, f a := (Finset.sum_biUnion (hdisj v)).symm
      _ ≤ ∑' a, f a := hf.sum_le_tsum _ fun a _ => hf0 a
  have h1 : ∑' b, (k : ℝ) * Sᶜ.indicator g b ≤ ∑' a, f a := tsum_le_of_sum_le' hf0' hmain
  rw [Summable.tsum_mul_left _ (hg.indicator _)] at h1
  have h2 : ∑' b, g b = ∑' b, Sᶜ.indicator g b + ∑' b, S.indicator g b := by
    rw [← Summable.tsum_add (hg.indicator _) (hg.indicator _)]
    congr 1
    ext b
    rw [add_comm, Set.indicator_self_add_compl_apply]
  rw [h2, mul_add]
  linarith
end ReciprocityTheory.Cheb
