-- Prove2me | solution 1 for StrategyproofMinimax.Tree.mc_parent_vertex_eq
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:39:12.091733+00:00
-- url     : https://prove2.me/submissions/75025ebb-5813-4312-aa5f-619181f71243

import Mathlib
import Definitions.Def_StrategyproofMinimax_Tree_cost
import Definitions.Def_StrategyproofMinimax_Tree_HardTree
import Definitions.Def_StrategyproofMinimax_Tree_profileAlong

namespace Aux_SPM_mc

open StrategyproofMinimax.Tree

lemma normC {m : ℕ} {ι : Type*} (S : Finset ι) (key : ι → Edge m) (hk : Set.InjOn key S)
    (c : ι → ℝ) :
    ‖(∑ i ∈ S, lp.single 1 (key i) (c i) : Ambient m)‖ = ∑ i ∈ S, |c i| := by
  classical
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one]
  have hco : ∀ e, (∑ i ∈ S, lp.single 1 (key i) (c i) : Ambient m) e =
      ∑ i ∈ S, if key i = e then c i else 0 := by
    intro e
    rw [lp.coeFn_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : key i = e
    · subst h; rw [lp.single_apply_self, if_pos rfl]
    · rw [lp.single_apply_ne _ _ _ (Ne.symm h), if_neg h]
  rw [tsum_eq_sum (s := S.image key)]
  · rw [Finset.sum_image hk]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hco, Finset.sum_eq_single i]
    · rw [if_pos rfl, Real.norm_eq_abs]
    · intro j hj hji; rw [if_neg]; exact fun h => hji (hk hj hi h)
    · intro h; exact absurd hi h
  · intro e he
    rw [hco, Finset.sum_eq_zero, norm_zero]
    intro i hi; rw [if_neg]; intro h; exact he (Finset.mem_image.mpr ⟨i, hi, h⟩)

lemma hlen {m : ℕ} (x : List (Fin m)) (i : ℕ) (hi : i < x.length) :
    (x.take (i + 1)).length = i + 1 := by
  simp; omega

lemma distL {m : ℕ} (u w : List (Fin m)) (c : ℕ) (hu : c ≤ u.length) (hw : c ≤ w.length)
    (hpre : u.take c = w.take c)
    (hdiff : ∀ j, c ≤ j → j < u.length → j < w.length → u.take (j + 1) ≠ w.take (j + 1)) :
    ‖vpos .left u - vpos .left w‖ =
      ∑ j ∈ Finset.Ico c u.length, (2 : ℝ) ^ j + ∑ j ∈ Finset.Ico c w.length, (2 : ℝ) ^ j := by
  have hsplit : ∀ x : List (Fin m), c ≤ x.length → vpos .left x =
      ∑ j ∈ Finset.range c, lp.single 1 (some (Side.left, x.take (j + 1))) ((2 : ℝ) ^ j) +
      ∑ j ∈ Finset.Ico c x.length, lp.single 1 (some (Side.left, x.take (j + 1))) ((2 : ℝ) ^ j) := by
    intro x hx
    simp only [vpos, zero_add]
    rw [Finset.sum_range_add_sum_Ico _ hx]
  have e : ∑ j ∈ Finset.range c, lp.single 1 (some (Side.left, u.take (j + 1))) ((2 : ℝ) ^ j) =
      ∑ j ∈ Finset.range c, (lp.single 1 (some (Side.left, w.take (j + 1))) ((2 : ℝ) ^ j) :
        Ambient m) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have h1 : u.take (j + 1) = (u.take c).take (j + 1) := by
      rw [List.take_take, min_eq_left (by omega)]
    have h2 : w.take (j + 1) = (w.take c).take (j + 1) := by
      rw [List.take_take, min_eq_left (by omega)]
    rw [h1, h2, hpre]
  rw [hsplit u hu, hsplit w hw, e, add_sub_add_left_eq_sub]
  have hrw : (∑ j ∈ Finset.Ico c u.length,
        lp.single 1 (some (Side.left, u.take (j + 1))) ((2 : ℝ) ^ j) : Ambient m) -
      ∑ j ∈ Finset.Ico c w.length, lp.single 1 (some (Side.left, w.take (j + 1))) ((2 : ℝ) ^ j) =
      ∑ i ∈ (Finset.Ico c u.length).disjSum (Finset.Ico c w.length),
        lp.single 1 (Sum.elim (fun j => some (Side.left, u.take (j + 1)))
          (fun j => some (Side.left, w.take (j + 1))) i)
          (Sum.elim (fun j => (2 : ℝ) ^ j) (fun j => -(2 : ℝ) ^ j) i) := by
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr, lp.single_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hrw, normC]
  · rw [Finset.sum_disjSum]
    simp
  · rintro (i | i) hi (j | j) hj h <;>
      simp only [Finset.mem_coe, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum,
        Finset.mem_Ico, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, exists_false,
        or_false, false_or, exists_eq_right, Sum.elim_inl, Sum.elim_inr, Option.some.injEq,
        Prod.mk.injEq, true_and] at hi hj h ⊢
    · have := congrArg List.length h
      rw [hlen _ _ hi.2, hlen _ _ hj.2] at this; omega
    · have := congrArg List.length h
      rw [hlen _ _ hi.2, hlen _ _ hj.2] at this
      have hij : i = j := by omega
      subst hij
      exact hdiff i hi.1 hi.2 hj.2 h
    · have := congrArg List.length h
      rw [hlen _ _ hi.2, hlen _ _ hj.2] at this
      have hij : i = j := by omega
      subst hij
      exact hdiff i hi.1 hj.2 hi.2 h.symm
    · have := congrArg List.length h
      rw [hlen _ _ hi.2, hlen _ _ hj.2] at this; omega

lemma spread {m : ℕ} (v a : List (Fin m)) (ha : a.length = v.length + 1) :
    ∃ c ≤ v.length, (spreadPos v a).length = c + 1 ∧ v.take c = (spreadPos v a).take c ∧
      (c < v.length → v.take (c + 1) ≠ spreadPos v a) := by
  induction v generalizing a with
  | nil =>
    refine ⟨0, le_rfl, ?_, by simp, by simp⟩
    simp [spreadPos]; omega
  | cons c0 v ih =>
    cases a with
    | nil => simp at ha
    | cons b a' =>
      simp only [List.length_cons] at ha
      by_cases hb : b = c0
      · obtain ⟨c, hc, h1, h2, h3⟩ := ih a' (by omega)
        refine ⟨c + 1, by simp; omega, ?_, ?_, ?_⟩
        · simp [spreadPos, hb, h1]
        · simp [spreadPos, hb, h2]
        · intro hlt
          simp only [spreadPos, hb, if_true, List.take_succ_cons, ne_eq, List.cons.injEq,
            true_and]
          exact h3 (by simp at hlt; omega)
      · refine ⟨0, by simp, by simp [spreadPos, hb], by simp, ?_⟩
        intro _
        simp [spreadPos, hb]
        exact Ne.symm hb

lemma address_len {m k n : ℕ} (i : Fin n) (a : List (Fin m)) (h : address m k n i = some a) :
    a.length = k := by
  unfold address at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  rw [← h, List.length_ofFn]

end Aux_SPM_mc

open StrategyproofMinimax.Tree Aux_SPM_mc in
theorem solution {m k n : ℕ} (hk : 1 ≤ k) (hn : 0 < n) (hdiv : 2 * m ^ k ∣ n)
    (v : List (Fin m)) (hv : v.length = k - 1) :
    mc (diracPM (vertex .left v : HardTree m k)) (profileAlong m k n v) =
      (2 : ℝ) ^ (k - 1) := by
  have hvk : v.length + 1 = k := by omega
  have hvt : v.take k = v := List.take_of_length_le (by omega)
  have hall : ∀ i, dist (profileAlong m k n v i) (vertex .left v : HardTree m k) =
      (2 : ℝ) ^ (k - 1) := by
    intro i
    unfold profileAlong
    split
    · rename_i a heq
      have ha := address_len i a heq
      obtain ⟨c, hc, h1, h2, h3⟩ := spread v a (by omega)
      set w := spreadPos v a with hw
      have hwt : w.take k = w := List.take_of_length_le (by omega)
      have hd : dist (vertex .left w : HardTree m k) (vertex .left v) =
          ‖vpos .left (w.take k) - vpos .left (v.take k)‖ := by
        rw [← dist_eq_norm]; rfl
      rw [hd, hwt, hvt, distL w v c (by omega) hc h2.symm]
      · rw [h1, geom_sum_Ico (by norm_num) (by omega), geom_sum_Ico (by norm_num) hc, hv]
        have : k - 1 = c + (k - 1 - c) := by omega
        rw [pow_succ]
        ring
      · intro j hj1 hj2 hj3
        have hjc : j = c := by omega
        subst hjc
        rw [List.take_of_length_le (by omega : (w).length ≤ j + 1)]
        exact fun h => h3 (by omega) h.symm
    · have hd : dist (vertex .right [] : HardTree m k) (vertex .left v) =
          ‖vpos .right ([].take k) - vpos .left (v.take k)‖ := by
        rw [← dist_eq_norm]; rfl
      rw [hd, hvt]
      have hrw : vpos .right ([] : List (Fin m)) - vpos .left v =
          ∑ i ∈ ({0} : Finset ℕ).disjSum (Finset.range v.length),
            lp.single 1 (Sum.elim (fun _ => (none : Edge m))
              (fun j => some (Side.left, v.take (j + 1))) i)
              (Sum.elim (fun _ => (1 : ℝ)) (fun j => -(2 : ℝ) ^ j) i) := by
        rw [Finset.sum_disjSum]
        simp only [vpos, List.length_nil, Finset.range_zero, Finset.sum_empty, add_zero, zero_add,
          Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr, lp.single_neg,
          Finset.sum_neg_distrib, sub_eq_add_neg]
      simp only [List.take_nil]
      rw [hrw, normC]
      · rw [Finset.sum_disjSum]
        simp only [Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr, abs_one, abs_neg, abs_pow,
          abs_two]
        rw [geom_sum_eq (by norm_num), hv]
        have : k - 1 + 1 = k := by omega
        ring
      · rintro (i | i) hi (j | j) hj h <;>
          simp only [Finset.mem_coe, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum,
            Finset.mem_singleton, Finset.mem_range, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
            false_and, exists_false, or_false, false_or, exists_eq_right, Sum.elim_inl,
            Sum.elim_inr, Option.some.injEq, Prod.mk.injEq, true_and] at hi hj h ⊢
        · omega
        · have := congrArg List.length h
          rw [hlen _ _ hi, hlen _ _ hj] at this; omega
  unfold mc diracPM
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  show ∫ y, (⨆ i, dist (profileAlong m k n v i) y) ∂(MeasureTheory.Measure.dirac (vertex .left v : HardTree m k))
    = _
  rw [MeasureTheory.integral_dirac]
  simp_rw [hall]
  exact ciSup_const
