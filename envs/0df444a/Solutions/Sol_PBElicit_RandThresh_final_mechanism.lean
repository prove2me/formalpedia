-- Prove2me | solution 1 for PBElicit.RandThresh.final_mechanism
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:44:20.392871+00:00
-- url     : https://prove2.me/submissions/1bf3e687-c438-4a6b-8b59-68a553baa357

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

open Classical PBElicit.RandThresh

/-! Helpers for Theorem 3.5. -/

noncomputable def pbMkRule {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] {c : A → ℝ}
    {ι : Type*} [Fintype ι] (w t : ι → ℝ) (g : ι → (Fin n → Finset A) → Finset A)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (hg : ∀ i ρ, IsMaxFeasible c (g i ρ)) :
    ThresholdRule n A c where
  size := Fintype.card ι
  weight r := w ((Fintype.equivFin ι).symm r)
  thr r := t ((Fintype.equivFin ι).symm r)
  agg r := g ((Fintype.equivFin ι).symm r)
  weight_nonneg r := hw _
  weight_sum := by rw [← hs]; exact Equiv.sum_comp (Fintype.equivFin ι).symm w
  agg_mem r ρ := hg _ ρ

lemma pbMkRule_exp {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] {c : A → ℝ}
    {ι : Type*} [Fintype ι] (w t : ι → ℝ) (g : ι → (Fin n → Finset A) → Finset A)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (hg : ∀ i ρ, IsMaxFeasible c (g i ρ))
    (v : Fin n → A → ℝ) :
    (pbMkRule w t g hw hs hg).expWelfare v = ∑ i, w i * sw v (g i (approvals v (t i))) := by
  unfold ThresholdRule.expWelfare pbMkRule
  exact Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => w i * sw v (g i (approvals v (t i))))

lemma pb_exists_ext {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ) (S : Finset A) :
    ∃ T : Finset A, (cost c S ≤ 1 → S ⊆ T) ∧ IsMaxFeasible c T := by
  have key : ∀ S : Finset A, cost c S ≤ 1 → ∃ T, S ⊆ T ∧ IsMaxFeasible c T := by
    intro S hS
    obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image
      ((Finset.univ : Finset (Finset A)).filter (fun T => S ⊆ T ∧ cost c T ≤ 1)) Finset.card
      ⟨S, by simp [hS]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT hmax
    refine ⟨T, hT.1, hT.2, fun T' hT' => ?_⟩
    by_contra h
    push_neg at h
    have := hmax T' ⟨hT.1.trans hT'.le, h⟩
    exact absurd (Finset.card_lt_card hT') (not_lt.mpr this)
  by_cases h : cost c S ≤ 1
  · obtain ⟨T, h1, h2⟩ := key S h; exact ⟨T, fun _ => h1, h2⟩
  · obtain ⟨T, -, h2⟩ := key ∅ (by simp [cost]); exact ⟨T, fun h' => absurd h' h, h2⟩

noncomputable def pbExt {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ) (S : Finset A) :
    Finset A :=
  Classical.choose (pb_exists_ext c S)

lemma pbExt_max {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ) (S : Finset A) :
    IsMaxFeasible c (pbExt c S) := (Classical.choose_spec (pb_exists_ext c S)).2

lemma pbExt_sup {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ) (S : Finset A)
    (h : cost c S ≤ 1) : S ⊆ pbExt c S := (Classical.choose_spec (pb_exists_ext c S)).1 h

lemma pb_sw_mono {n : ℕ} {A : Type*} (v : Fin n → A → ℝ) (hv : ∀ i a, 0 ≤ v i a)
    {S T : Finset A} (h : S ⊆ T) : sw v S ≤ sw v T :=
  Finset.sum_le_sum_of_subset_of_nonneg h
    (fun a _ _ => Finset.sum_nonneg (fun i _ => hv i a))

lemma pb_sw_nonneg {n : ℕ} {A : Type*} (v : Fin n → A → ℝ) (hv : ∀ i a, 0 ≤ v i a)
    (S : Finset A) : 0 ≤ sw v S :=
  Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun i _ => hv i a))

lemma pb_sw_ext {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (v : Fin n → A → ℝ) (hv : ∀ i a, 0 ≤ v i a) (S : Finset A) (h : cost c S ≤ 1) :
    sw v S ≤ sw v (pbExt c S) := pb_sw_mono v hv (pbExt_sup c S h)

lemma pb_cost_mono {A : Type*} (c : A → ℝ) (hc : ∀ a, 0 ≤ c a) {S T : Finset A}
    (h : S ⊆ T) : cost c S ≤ cost c T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun a _ _ => hc a)

lemma pb_dyadic (L : ℕ) (x : ℝ) (h1 : (1/2:ℝ)^L < x) (h2 : x ≤ 1) :
    ∃ k < L, (1/2:ℝ)^(k+1) < x ∧ x ≤ (1/2:ℝ)^k := by
  induction L with
  | zero => simp at h1; linarith
  | succ L ih =>
    by_cases h : (1/2:ℝ)^L < x
    · obtain ⟨k, hk, hk'⟩ := ih h; exact ⟨k, by omega, hk'⟩
    · exact ⟨L, by omega, h1, not_lt.mp h⟩

lemma pb_val (L : ℕ) (x : ℝ) (_h0 : 0 ≤ x) (h2 : x ≤ 1) :
    x ≤ (1/2:ℝ)^L + ∑ j ∈ Finset.range L,
      (1/2:ℝ)^j * (if (1/2:ℝ)^(j+1) ≤ x then 1 else 0) := by
  have hs : 0 ≤ ∑ j ∈ Finset.range L,
      (1/2:ℝ)^j * (if (1/2:ℝ)^(j+1) ≤ x then 1 else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  by_cases h : (1/2:ℝ)^L < x
  · obtain ⟨k, hk, hk1, hk2⟩ := pb_dyadic L x h h2
    have := Finset.single_le_sum
      (f := fun j => (1/2:ℝ)^j * (if (1/2:ℝ)^(j+1) ≤ x then 1 else 0))
      (fun j _ => by split_ifs <;> positivity) (Finset.mem_range.mpr hk)
    simp only [if_pos hk1.le, mul_one] at this
    have : (0:ℝ) ≤ (1/2)^L := by positivity
    linarith
  · linarith

/-- welfare of a single alternative bounded via approval counts at dyadic thresholds -/
lemma pb_sw_a {n : ℕ} {A : Type*} [Fintype A] (v : Fin n → A → ℝ) (hv : IsUtilityProfile v)
    (L : ℕ) (a : A) :
    ∑ i, v i a ≤ (n : ℝ) * (1/2:ℝ)^L + ∑ j ∈ Finset.range L,
      (1/2:ℝ)^j * (approvalCount v ((1/2:ℝ)^(j+1)) a : ℝ) := by
  have hle1 : ∀ i, v i a ≤ 1 := by
    intro i
    rw [← hv.2 i]
    exact Finset.single_le_sum (f := fun b => v i b) (fun b _ => hv.1 i b) (Finset.mem_univ a)
  calc ∑ i, v i a ≤ ∑ i : Fin n, ((1/2:ℝ)^L + ∑ j ∈ Finset.range L,
        (1/2:ℝ)^j * (if (1/2:ℝ)^(j+1) ≤ v i a then 1 else 0)) :=
        Finset.sum_le_sum (fun i _ => pb_val L _ (hv.1 i a) (hle1 i))
    _ = (n : ℝ) * (1/2:ℝ)^L + ∑ j ∈ Finset.range L,
        (1/2:ℝ)^j * (approvalCount v ((1/2:ℝ)^(j+1)) a : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        congr 1
        unfold approvalCount
        rw [Finset.natCast_card_filter]

/-- number of approvals of `a` in profile `ρ`, summed over `Y` -/
noncomputable def pbScore {n : ℕ} {A : Type*} (ρ : Fin n → Finset A) (Y : Finset A) : ℕ :=
  ∑ a ∈ Y, (Finset.univ.filter (fun i => a ∈ ρ i)).card

lemma pbScore_approvals {n : ℕ} {A : Type*} [Fintype A] (v : Fin n → A → ℝ) (t : ℝ)
    (Y : Finset A) : pbScore (approvals v t) Y = ∑ a ∈ Y, approvalCount v t a := by
  unfold pbScore approvals approvalCount
  simp

lemma pb_exists_best {n : ℕ} {A : Type*} [DecidableEq A] (Sk : Finset A) (N : ℕ)
    (ρ : Fin n → Finset A) :
    ∃ B, B ⊆ Sk ∧ B.card ≤ N ∧ ∀ Y, Y ⊆ Sk → Y.card ≤ N → pbScore ρ Y ≤ pbScore ρ B := by
  obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image
    (Sk.powerset.filter (fun B => B.card ≤ N)) (pbScore ρ) ⟨∅, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hB hmax
  exact ⟨B, hB.1, hB.2, fun Y h1 h2 => hmax Y ⟨h1, h2⟩⟩

noncomputable def pbBest {n : ℕ} {A : Type*} [DecidableEq A] (Sk : Finset A) (N : ℕ)
    (ρ : Fin n → Finset A) : Finset A :=
  Classical.choose (pb_exists_best Sk N ρ)

lemma pbBest_spec {n : ℕ} {A : Type*} [DecidableEq A] (Sk : Finset A) (N : ℕ)
    (ρ : Fin n → Finset A) :
    pbBest Sk N ρ ⊆ Sk ∧ (pbBest Sk N ρ).card ≤ N ∧
      ∀ Y, Y ⊆ Sk → Y.card ≤ N → pbScore ρ Y ≤ pbScore ρ (pbBest Sk N ρ) :=
  Classical.choose_spec (pb_exists_best Sk N ρ)

lemma pbBest_double {n : ℕ} {A : Type*} [DecidableEq A] (Sk : Finset A) (N : ℕ)
    (ρ : Fin n → Finset A) (Y : Finset A) (hY : Y ⊆ Sk) (hc : Y.card ≤ 2 * N) :
    pbScore ρ Y ≤ 2 * pbScore ρ (pbBest Sk N ρ) := by
  obtain ⟨X, hXY, hXc⟩ := Finset.exists_subset_card_eq (min_le_right N Y.card)
  have h1 := (pbBest_spec Sk N ρ).2.2 X (hXY.trans hY) (by rw [hXc]; exact min_le_left _ _)
  have hcd : (Y \ X).card ≤ N := by
    rw [Finset.card_sdiff_of_subset hXY, hXc]; omega
  have h2 := (pbBest_spec Sk N ρ).2.2 (Y \ X) (Finset.sdiff_subset.trans hY) hcd
  have : pbScore ρ Y = pbScore ρ (Y \ X) + pbScore ρ X := by
    unfold pbScore; rw [Finset.sum_sdiff hXY]
  omega

/-- cost bucket `k`: `c_a ∈ (2^{-(k+1)}, 2^{-k}]` -/
noncomputable def pbBk {A : Type*} [Fintype A] (c : A → ℝ) (k : ℕ) : Finset A :=
  Finset.univ.filter (fun a => (1/2:ℝ)^(k+1) < c a ∧ c a ≤ (1/2:ℝ)^k)

lemma pb_cost_bucket {A : Type*} [Fintype A] (c : A → ℝ) (k : ℕ) (B : Finset A)
    (hB : B ⊆ pbBk c k) (hc : B.card ≤ 2 ^ k) : cost c B ≤ 1 := by
  unfold cost
  have h := Finset.sum_le_card_nsmul B c ((1/2:ℝ)^k) (fun a ha => by
    have := hB ha; simp only [pbBk, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this.2)
  rw [nsmul_eq_mul] at h
  have hc' : (B.card : ℝ) ≤ 2 ^ k := by exact_mod_cast hc
  have : (B.card : ℝ) * (1/2:ℝ)^k ≤ 2^k * (1/2:ℝ)^k :=
    mul_le_mul_of_nonneg_right hc' (by positivity)
  rw [← mul_pow] at this; norm_num at this
  linarith

lemma pb_card_bucket {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ) (hc : ∀ a, 0 ≤ c a)
    (k : ℕ) (T : Finset A) (hT : cost c T ≤ 1) : (T ∩ pbBk c k).card ≤ 2 * 2 ^ k := by
  have h := Finset.card_nsmul_le_sum (T ∩ pbBk c k) c ((1/2:ℝ)^(k+1)) (fun a ha => by
    have := (Finset.mem_inter.mp ha).2
    simp only [pbBk, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this.1.le)
  rw [nsmul_eq_mul] at h
  have h2 : ∑ a ∈ T ∩ pbBk c k, c a ≤ 1 :=
    (pb_cost_mono c hc Finset.inter_subset_left).trans hT
  have h3 : ((T ∩ pbBk c k).card : ℝ) * ((1/2:ℝ)^(k+1) * 2^(k+1)) ≤ 1 * 2^(k+1) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rw [← mul_pow] at h3; norm_num at h3
  have : ((T ∩ pbBk c k).card : ℝ) ≤ ((2 * 2 ^ k : ℕ) : ℝ) := by push_cast; rw [pow_succ] at h3; linarith
  exact_mod_cast this

lemma pb_cover {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ) (hc1 : ∀ a, c a ≤ 1)
    (L : ℕ) (T : Finset A) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ T.filter (fun a => ¬ c a ≤ (1/2:ℝ)^L), f a ≤
      ∑ k ∈ Finset.range L, ∑ a ∈ T ∩ pbBk c k, f a := by
  set T' := T.filter (fun a => ¬ c a ≤ (1/2:ℝ)^L)
  calc ∑ a ∈ T', f a ≤ ∑ a ∈ T', ∑ k ∈ Finset.range L, (if a ∈ pbBk c k then f a else 0) := by
        refine Finset.sum_le_sum (fun a ha => ?_)
        have ha' := (Finset.mem_filter.mp ha).2
        obtain ⟨k, hk, hk1, hk2⟩ := pb_dyadic L (c a) (not_le.mp ha') (hc1 a)
        have := Finset.single_le_sum (f := fun k => if a ∈ pbBk c k then f a else 0)
          (fun j _ => by split_ifs <;> simp [hf]) (Finset.mem_range.mpr hk)
        have hmem : a ∈ pbBk c k := by
          simp only [pbBk, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hk1, hk2⟩
        simp only [if_pos hmem] at this
        exact this
    _ = ∑ k ∈ Finset.range L, ∑ a ∈ T'.filter (fun a => a ∈ pbBk c k), f a := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact (Finset.sum_filter _ _).symm
    _ ≤ ∑ k ∈ Finset.range L, ∑ a ∈ T ∩ pbBk c k, f a := by
        refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun a _ _ => hf a))
        intro a ha
        simp only [T', Finset.mem_filter] at ha
        exact Finset.mem_inter.mpr ⟨ha.1.1, ha.2⟩

lemma pb_sw_ge_score {n : ℕ} {A : Type*} [Fintype A] (v : Fin n → A → ℝ)
    (hv : ∀ i a, 0 ≤ v i a) (t : ℝ) (ht : 0 ≤ t) (B : Finset A) :
    t * (pbScore (approvals v t) B : ℝ) ≤ sw v B := by
  rw [pbScore_approvals]
  unfold sw approvalCount
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun a _ => ?_)
  rw [Finset.natCast_card_filter, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  split_ifs with h
  · simpa using h
  · simpa using hv i a

/-- cheap alternatives: `c_a ≤ 2^{-L}` -/
noncomputable def pbS0 {A : Type*} [Fintype A] (c : A → ℝ) (L : ℕ) : Finset A :=
  Finset.univ.filter (fun a => c a ≤ (1/2:ℝ)^L)

noncomputable def pbArmA {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (j k : ℕ) (ρ : Fin n → Finset A) : Finset A :=
  pbExt c (pbBest (pbBk c k) (2 ^ k) ρ)

lemma pb_main {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (hc : ∀ a, 0 ≤ c a ∧ c a ≤ 1) (v : Fin n → A → ℝ) (hv : IsUtilityProfile v)
    (L : ℕ) (hm : 1 ≤ Fintype.card A)
    (hL : ((Fintype.card A : ℝ))^2 * (1/2:ℝ)^L ≤ 1) (T : Finset A) (hT : IsMaxFeasible c T) :
    sw v T ≤ sw v (pbExt c (pbS0 c L)) + (n : ℝ) / (Fintype.card A : ℝ)
      + 4 * ∑ j ∈ Finset.range L, ∑ k ∈ Finset.range L,
          sw v (pbArmA c j k (approvals v ((1/2:ℝ)^(j+1)))) := by
  set m : ℕ := Fintype.card A with hmdef
  have hv0 := hv.1
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0:ℝ) < (1/2:ℝ)^L := by positivity
  have hmL : (m:ℝ) * (1/2:ℝ)^L ≤ 1 := by
    have : (m:ℝ) * (1/2:ℝ)^L ≤ (m:ℝ)^2 * (1/2:ℝ)^L :=
      mul_le_mul_of_nonneg_right (by nlinarith) hpos.le
    linarith
  -- split T
  have hsplit : sw v T = sw v (T.filter (fun a => c a ≤ (1/2:ℝ)^L))
      + sw v (T.filter (fun a => ¬ c a ≤ (1/2:ℝ)^L)) := by
    unfold sw; exact (Finset.sum_filter_add_sum_filter_not T _ _).symm
  -- part 1 : mechanism B
  have hS0cost : cost c (pbS0 c L) ≤ 1 := by
    unfold cost
    have h := Finset.sum_le_card_nsmul (pbS0 c L) c ((1/2:ℝ)^L) (fun a ha => by
      simp only [pbS0, Finset.mem_filter, Finset.mem_univ, true_and] at ha; exact ha)
    rw [nsmul_eq_mul] at h
    have hcard : ((pbS0 c L).card : ℝ) ≤ m := by exact_mod_cast Finset.card_le_univ _
    have : ((pbS0 c L).card : ℝ) * (1/2:ℝ)^L ≤ m * (1/2:ℝ)^L :=
      mul_le_mul_of_nonneg_right hcard hpos.le
    linarith
  have hpart1 : sw v (T.filter (fun a => c a ≤ (1/2:ℝ)^L)) ≤ sw v (pbExt c (pbS0 c L)) := by
    refine le_trans (pb_sw_mono v hv0 ?_) (pb_sw_ext c v hv0 _ hS0cost)
    intro a ha
    simp only [Finset.mem_filter] at ha
    simp only [pbS0, Finset.mem_filter, Finset.mem_univ, true_and]; exact ha.2
  -- part 2 : mechanism A
  set T' := T.filter (fun a => ¬ c a ≤ (1/2:ℝ)^L) with hT'
  have hstep1 : sw v T' ≤ ∑ a ∈ T', ((n : ℝ) * (1/2:ℝ)^L + ∑ j ∈ Finset.range L,
      (1/2:ℝ)^j * (approvalCount v ((1/2:ℝ)^(j+1)) a : ℝ)) :=
    Finset.sum_le_sum (fun a _ => pb_sw_a v hv L a)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_comm] at hstep1
  have hlow : (T'.card : ℝ) * ((n : ℝ) * (1/2:ℝ)^L) ≤ (n:ℝ) / m := by
    have hcard : (T'.card : ℝ) ≤ m := by exact_mod_cast Finset.card_le_univ _
    rw [le_div_iff₀ hmpos]
    have hn : (0:ℝ) ≤ n := by positivity
    calc (T'.card : ℝ) * ((n : ℝ) * (1/2:ℝ)^L) * m ≤ (m:ℝ) * ((n : ℝ) * (1/2:ℝ)^L) * m := by
          gcongr
      _ = (n:ℝ) * ((m:ℝ)^2 * (1/2:ℝ)^L) := by ring
      _ ≤ (n:ℝ) * 1 := by gcongr
      _ = n := by ring
  have hhigh : ∀ j ∈ Finset.range L,
      ∑ a ∈ T', (1/2:ℝ)^j * (approvalCount v ((1/2:ℝ)^(j+1)) a : ℝ) ≤
        4 * ∑ k ∈ Finset.range L, sw v (pbArmA c j k (approvals v ((1/2:ℝ)^(j+1)))) := by
    intro j _
    set ρ := approvals v ((1/2:ℝ)^(j+1))
    rw [← Finset.mul_sum]
    have hcov := pb_cover c (fun a => (hc a).2) L T
      (fun a => (approvalCount v ((1/2:ℝ)^(j+1)) a : ℝ)) (fun a => by positivity)
    have hk : ∀ k ∈ Finset.range L,
        (1/2:ℝ)^j * ∑ a ∈ T ∩ pbBk c k, (approvalCount v ((1/2:ℝ)^(j+1)) a : ℝ)
          ≤ 4 * sw v (pbArmA c j k ρ) := by
      intro k _
      have e1 : ∑ a ∈ T ∩ pbBk c k, (approvalCount v ((1/2:ℝ)^(j+1)) a : ℝ)
          = (pbScore ρ (T ∩ pbBk c k) : ℝ) := by
        rw [pbScore_approvals]; push_cast; rfl
      have hd := pbBest_double (pbBk c k) (2 ^ k) ρ (T ∩ pbBk c k) Finset.inter_subset_right
        (pb_card_bucket c (fun a => (hc a).1) k T hT.1)
      have hd' : (pbScore ρ (T ∩ pbBk c k) : ℝ) ≤ 2 * (pbScore ρ (pbBest (pbBk c k) (2^k) ρ) : ℝ) := by
        exact_mod_cast hd
      have hsw := pb_sw_ge_score v hv0 ((1/2:ℝ)^(j+1)) (by positivity) (pbBest (pbBk c k) (2^k) ρ)
      have hspec := pbBest_spec (pbBk c k) (2 ^ k) ρ
      have hext := pb_sw_ext c v hv0 (pbBest (pbBk c k) (2^k) ρ)
        (pb_cost_bucket c k _ hspec.1 hspec.2.1)
      unfold pbArmA
      rw [e1]
      have hj : (1/2:ℝ)^j = 2 * (1/2:ℝ)^(j+1) := by rw [pow_succ]; ring
      rw [hj]
      have h0 : (0:ℝ) ≤ (1/2:ℝ)^(j+1) := by positivity
      nlinarith
    calc (1/2:ℝ)^j * ∑ a ∈ T', (approvalCount v ((1/2:ℝ)^(j+1)) a : ℝ)
        ≤ (1/2:ℝ)^j * ∑ k ∈ Finset.range L, ∑ a ∈ T ∩ pbBk c k,
            (approvalCount v ((1/2:ℝ)^(j+1)) a : ℝ) :=
          mul_le_mul_of_nonneg_left hcov (by positivity)
      _ = ∑ k ∈ Finset.range L, (1/2:ℝ)^j * ∑ a ∈ T ∩ pbBk c k,
            (approvalCount v ((1/2:ℝ)^(j+1)) a : ℝ) := Finset.mul_sum _ _ _
      _ ≤ ∑ k ∈ Finset.range L, 4 * sw v (pbArmA c j k ρ) := Finset.sum_le_sum hk
      _ = 4 * ∑ k ∈ Finset.range L, sw v (pbArmA c j k ρ) := (Finset.mul_sum _ _ _).symm
  have hhigh' := Finset.sum_le_sum hhigh
  rw [← Finset.mul_sum] at hhigh'
  have : sw v T' ≤ (n:ℝ) / m + 4 * ∑ j ∈ Finset.range L, ∑ k ∈ Finset.range L,
      sw v (pbArmA c j k (approvals v ((1/2:ℝ)^(j+1)))) := by linarith
  linarith

lemma pb_sum_fin (L : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ p : Fin L × Fin L, F p.1 p.2 = ∑ j ∈ Finset.range L, ∑ k ∈ Finset.range L, F j k := by
  rw [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ k ∈ Finset.range L, F j k)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact Fin.sum_univ_eq_sum_range (fun k => F j k) L

noncomputable def pbW {A : Type*} (L : ℕ) (D m : ℝ) : (Fin L × Fin L) ⊕ Option A → ℝ
  | Sum.inl _ => 4 / D
  | Sum.inr none => 1 / D
  | Sum.inr (some _) => 1 / (D * m)

noncomputable def pbT {A : Type*} (L : ℕ) : (Fin L × Fin L) ⊕ Option A → ℝ
  | Sum.inl p => (1/2:ℝ)^(p.1.val + 1)
  | Sum.inr _ => 0

noncomputable def pbG {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ) (L : ℕ) :
    (Fin L × Fin L) ⊕ Option A → (Fin n → Finset A) → Finset A
  | Sum.inl p => fun ρ => pbArmA c p.1.val p.2.val ρ
  | Sum.inr none => fun _ => pbExt c (pbS0 c L)
  | Sum.inr (some a) => fun _ => pbExt c {a}

theorem solution {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (hc : ∀ a, 0 ≤ c a ∧ c a ≤ 1) (m K : ℕ) (hA : Fintype.card A = m) (hmK : m = 2 ^ K) :
    ∃ R : ThresholdRule n A c, ∀ v : Fin n → A → ℝ, IsUtilityProfile v →
      ∀ T : Finset A, IsMaxFeasible c T →
        sw v T ≤ (2 + 16 * Real.logb 2 m ^ 2) * R.expWelfare v := by
  subst hA
  set m : ℕ := Fintype.card A with hmdef
  set L : ℕ := 2 * K with hLdef
  have hmpos : (0:ℝ) < m := by rw [hmK]; positivity
  have hm1 : 1 ≤ m := by rw [hmK]; exact Nat.one_le_two_pow
  have hL : (m:ℝ)^2 * (1/2:ℝ)^L ≤ 1 := by
    rw [hmK, hLdef]; push_cast
    rw [← pow_mul, mul_comm K 2, ← mul_pow]; norm_num
  have hlog : Real.logb 2 (m:ℝ) = K := by
    rw [hmK]; push_cast; rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  rw [hlog]
  set D : ℝ := 2 + 16 * (K:ℝ) ^ 2 with hD
  have hDpos : 0 < D := by positivity
  have hw : ∀ i, 0 ≤ pbW (A := A) L D m i := by
    intro i; rcases i with p | _ | a <;> simp only [pbW] <;> positivity
  have hs : ∑ i, pbW (A := A) L D m i = 1 := by
    rw [Fintype.sum_sum_type, Fintype.sum_option]
    simp only [pbW, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← hmdef]
    field_simp
    rw [hD, hLdef]
    push_cast
    ring
  have hg : ∀ i ρ, IsMaxFeasible c (pbG (n := n) c L i ρ) := by
    intro i ρ; rcases i with p | _ | a <;> simp only [pbG] <;> exact pbExt_max _ _
  refine ⟨pbMkRule (pbW L D m) (pbT L) (pbG c L) hw hs hg, fun v hv T hT => ?_⟩
  have hv0 := hv.1
  rw [pbMkRule_exp]
  rw [Fintype.sum_sum_type, Fintype.sum_option]
  simp only [pbW, pbT, pbG]
  rw [pb_sum_fin L (fun j k => 4 / D * sw v (pbArmA c j k (approvals v ((1/2:ℝ)^(j+1)))))]
  simp only [← Finset.mul_sum]
  set EA := ∑ j ∈ Finset.range L, ∑ k ∈ Finset.range L,
    sw v (pbArmA c j k (approvals v ((1/2:ℝ)^(j+1)))) with hEA
  set EB := sw v (pbExt c (pbS0 c L)) with hEB
  set EC := ∑ a : A, sw v (pbExt c {a}) with hEC
  have hmain := pb_main c hc v hv L hm1 hL T hT
  rw [← hmdef, ← hEA, ← hEB] at hmain
  have hnEC : (n:ℝ) ≤ EC := by
    have : (n:ℝ) = ∑ a : A, sw v {a} := by
      simp only [sw, Finset.sum_singleton]
      rw [Finset.sum_comm]
      simp [hv.2]
    rw [this]
    refine Finset.sum_le_sum (fun a _ => pb_sw_ext c v hv0 _ ?_)
    simp [cost, (hc a).2]
  have hexp : D * (4 / D * EA + (1 / D * EB + 1 / (D * m) * EC)) = 4 * EA + EB + EC / m := by
    field_simp; ring
  rw [hexp]
  have hnm : (n:ℝ) / m ≤ EC / m := div_le_div_of_nonneg_right hnEC hmpos.le
  linarith
