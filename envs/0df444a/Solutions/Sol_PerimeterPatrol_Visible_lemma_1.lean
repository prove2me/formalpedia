-- Prove2me | solution 1 for PerimeterPatrol.Visible.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T23:17:18.770871+00:00
-- url     : https://prove2.me/submissions/886f4a33-4eb0-4859-84ad-72bb9d185e6a

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model

open MeasureTheory Filter Topology

namespace PerimeterPatrol.Visible

lemma PP_card_eq_iff (S : Set ℕ) (k : ℕ) :
    Nat.card S = k ↔ (∃ F : {F : Finset ℕ // F.card = k}, S = ↑(F : Finset ℕ)) ∨ (k = 0 ∧ S.Infinite) := by
  constructor
  · intro h
    by_cases hS : S.Finite
    · left
      refine ⟨⟨hS.toFinset, ?_⟩, by simp⟩
      rw [← h, Nat.card_eq_card_finite_toFinset hS]
    · right
      refine ⟨?_, hS⟩
      rw [← h]
      have : Infinite S := Set.infinite_coe_iff.mpr hS
      exact Nat.card_eq_zero_of_infinite
  · rintro (⟨⟨F, hF⟩, rfl⟩ | ⟨rfl, hS⟩)
    · simp [hF]
    · have : Infinite S := hS.to_subtype
      exact Nat.card_eq_zero_of_infinite

lemma PP_measurable_card {X : Type*} [MeasurableSpace X] (P : X → ℕ → Prop)
    (hP : ∀ n, MeasurableSet {x | P x n}) : Measurable (fun x => Nat.card {n | P x n}) := by
  apply measurable_to_countable'
  intro k
  have hset : (fun x => Nat.card {n | P x n}) ⁻¹' {k} =
      (⋃ F : {F : Finset ℕ // F.card = k}, ⋂ n : ℕ, {x | P x n ↔ n ∈ (F : Finset ℕ)}) ∪
        {x | k = 0 ∧ ∀ N : ℕ, ∃ n, N ≤ n ∧ P x n} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_iUnion,
      Set.mem_iInter, Set.mem_setOf_eq]
    rw [PP_card_eq_iff]
    apply or_congr
    · apply exists_congr; intro F
      rw [Set.ext_iff]; simp
    · apply and_congr Iff.rfl
      rw [← Nat.frequently_atTop_iff_infinite, Filter.frequently_atTop]
  rw [hset]
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion; intro F
    apply MeasurableSet.iInter; intro n
    by_cases hn : n ∈ (F : Finset ℕ)
    · simpa [hn] using hP n
    · have : {x | P x n ↔ n ∈ (F : Finset ℕ)} = {x | P x n}ᶜ := by ext x; simp [hn]
      rw [this]; exact (hP n).compl
  · by_cases hk : k = 0
    · simp only [hk, true_and]
      have : {x | ∀ N : ℕ, ∃ n, N ≤ n ∧ P x n} = ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), {x | P x n} := by
        ext x; simp
      rw [this]
      exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
        MeasurableSet.iUnion fun _ => hP n
    · simp [hk]


/-- tangent line of `n ↦ 1 - q^n` on `[n, n+1]` -/
noncomputable def PPL (q : ℝ) (n : ℕ) (c : ℝ) : ℝ := 1 - q ^ n + (c - n) * (q ^ n - q ^ (n + 1))

lemma PP_valueC_eq (p c : ℝ) (hc : 0 ≤ c) : valueC c p = PPL (1 - p) ⌊c⌋₊ c := by
  unfold valueC PPL
  have h1 := Nat.floor_le hc
  have h2 := Nat.le_ceil c
  rcases Nat.eq_or_lt_of_le (Nat.ceil_le_floor_add_one c) with h | h
  · rw [h]; ring
  · have hle : ⌈c⌉₊ ≤ ⌊c⌋₊ := Nat.lt_add_one_iff.mp h
    have hge : ⌊c⌋₊ ≤ ⌈c⌉₊ := Nat.floor_le_ceil c
    have he : ⌈c⌉₊ = ⌊c⌋₊ := le_antisymm hle hge
    have : (⌊c⌋₊ : ℝ) = c := by
      apply le_antisymm h1; rw [← he]; exact h2
    rw [he, this]; ring

lemma PP_valueC_le_one (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc : 0 ≤ c) : valueC c p ≤ 1 := by
  unfold valueC
  have ha : 0 ≤ c - ⌊c⌋₊ := by linarith [Nat.floor_le hc]
  have hb : 0 ≤ 1 - c + ⌊c⌋₊ := by linarith [Nat.lt_floor_add_one c]
  have e1 : 0 ≤ (1 - p) ^ ⌈c⌉₊ := pow_nonneg (by linarith) _
  have e2 : 0 ≤ (1 - p) ^ ⌊c⌋₊ := pow_nonneg (by linarith) _
  nlinarith [mul_nonneg ha e1, mul_nonneg hb e2]

lemma PP_valueC_nonneg (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc : 0 ≤ c) : 0 ≤ valueC c p := by
  unfold valueC
  have ha : 0 ≤ c - ⌊c⌋₊ := by linarith [Nat.floor_le hc]
  have hb : 0 ≤ 1 - c + ⌊c⌋₊ := by linarith [Nat.lt_floor_add_one c]
  have e1 : (1 - p) ^ ⌈c⌉₊ ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have e2 : (1 - p) ^ ⌊c⌋₊ ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]

lemma PP_conc (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m n : ℕ) : 1 - q ^ m ≤ PPL q n m := by
  unfold PPL
  rcases le_or_gt n m with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hb : 1 + (d : ℝ) * (q - 1) ≤ (1 + (q - 1)) ^ d := one_add_mul_le_pow (by linarith) d
    simp only [add_sub_cancel] at hb
    have hqn : 0 ≤ q ^ n := pow_nonneg hq0 n
    have key : q ^ n * (1 + (d : ℝ) * (q - 1)) ≤ q ^ n * q ^ d := mul_le_mul_of_nonneg_left hb hqn
    push_cast
    rw [pow_add, pow_succ]
    nlinarith
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
    have hb : 1 + ((d + 1 : ℕ) : ℝ) * (1 - q) ≤ (1 + (1 - q)) ^ (d + 1) :=
      one_add_mul_le_pow (by linarith) (d + 1)
    have hqq : (q * (1 + (1 - q))) ^ (d + 1) ≤ 1 :=
      pow_le_one₀ (by nlinarith) (by nlinarith)
    have hqd : 0 ≤ q ^ (d + 1) := pow_nonneg hq0 _
    have k1 : q ^ (d + 1) * (1 + ((d + 1 : ℕ) : ℝ) * (1 - q)) ≤ 1 := by
      calc _ ≤ q ^ (d + 1) * (1 + (1 - q)) ^ (d + 1) := mul_le_mul_of_nonneg_left hb hqd
        _ = (q * (1 + (1 - q))) ^ (d + 1) := by rw [mul_pow]
        _ ≤ 1 := hqq
    have hqm : 0 ≤ q ^ m := pow_nonneg hq0 m
    have k2 := mul_le_mul_of_nonneg_left k1 hqm
    have e : m + d + 1 = m + (d + 1) := by ring
    have e2 : q ^ (m + (d + 1) + 1) = q ^ m * q ^ (d + 1) * q := by rw [pow_succ, pow_add]
    rw [e, e2, pow_add]
    push_cast at k2 ⊢
    nlinarith

lemma PP_PPL_nonneg (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ PPL q n c := by
  have h0 := PP_conc q hq0 hq1 0 n
  have hs : 0 ≤ q ^ n - q ^ (n + 1) := by
    have : q ^ (n + 1) ≤ q ^ n := pow_le_pow_of_le_one hq0 hq1 (Nat.le_succ n)
    linarith
  unfold PPL at h0 ⊢
  simp at h0
  nlinarith

/-- number of patrollers by time `v` -/
noncomputable def cnt (s : ℕ → ℝ) (v : ℝ) : ℕ := Nat.card {n : ℕ | s n ≤ v}

lemma PP_feasible_finite (lam : ℝ) (hlam : 0 < lam) (s : ℕ → ℝ) (hs : IsFeasible lam s) (v : ℝ) :
    {n : ℕ | s n ≤ v}.Finite := by
  by_contra hinf
  have hall : ∀ n, s n ≤ v := by
    intro n
    obtain ⟨m, hm, hmn⟩ := Set.Infinite.exists_gt hinf n
    exact le_trans (hs.1 hmn.le) hm
  have hev : (fun T : ℝ => (Nat.card {n : ℕ | s n ≤ T} : ℝ) / T) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_ge_atTop v] with T hT
    have : {n : ℕ | s n ≤ T} = Set.univ := by
      ext n; simp [le_trans (hall n) hT]
    rw [this]; simp
  have h2 := hs.2.2
  have h3 : Tendsto (fun T : ℝ => (Nat.card {n : ℕ | s n ≤ T} : ℝ) / T) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' hev.symm
  have := tendsto_nhds_unique h2 h3
  linarith

lemma PP_arrivals_eq (lam : ℝ) (hlam : 0 < lam) (s : ℕ → ℝ) (hs : IsFeasible lam s) (a b : ℝ)
    (hab : a ≤ b) : (arrivals s a b : ℝ) = (cnt s b : ℝ) - (cnt s a : ℝ) := by
  unfold arrivals cnt
  have hsub : {n : ℕ | s n ≤ a} ⊆ {n : ℕ | s n ≤ b} := fun n hn => le_trans hn hab
  have hset : {n : ℕ | a < s n ∧ s n ≤ b} = {n : ℕ | s n ≤ b} \ {n : ℕ | s n ≤ a} := by
    ext n; simp only [Set.mem_setOf_eq, Set.mem_diff, not_le]; tauto
  rw [hset, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_diff hsub (PP_feasible_finite lam hlam s hs a)]
  rw [Nat.cast_sub (Set.ncard_le_ncard hsub (PP_feasible_finite lam hlam s hs b))]

end PerimeterPatrol.Visible


open PerimeterPatrol.Visible in
theorem solution (p c : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hc : 0 < c) : (∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → HasSum w 1 → HasSum (fun n : ℕ => (n : ℝ) * w n) c → ∑' n : ℕ, (1 - (1 - p) ^ n) * w n ≤ valueC c p) ∧ ((∀ n, 0 ≤ twoPoint c n) ∧ HasSum (twoPoint c) 1 ∧ HasSum (fun n : ℕ => (n : ℝ) * twoPoint c n) c ∧ ∑' n : ℕ, (1 - (1 - p) ^ n) * twoPoint c n = valueC c p) := by
  set q := 1 - p with hq
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  have hq1 : q ≤ 1 := by rw [hq]; linarith
  set k := ⌊c⌋₊ with hk
  have hV : valueC c p = PPL q k c := PP_valueC_eq p c hc.le
  have hkc : (k : ℝ) ≤ c := Nat.floor_le hc.le
  have hck : c < k + 1 := Nat.lt_floor_add_one c
  constructor
  · intro w hw h1 hm
    set B := q ^ k - q ^ (k + 1)
    have hlin : ∀ x, PPL q k x = (1 - q ^ k - k * B) + x * B := by intro x; unfold PPL; ring
    have hL : HasSum (fun n : ℕ => PPL q k n * w n) (PPL q k c) := by
      have a := h1.mul_left (1 - q ^ k - k * B)
      have b := hm.mul_left B
      simp only [mul_one] at a
      have e1 : (fun n : ℕ => PPL q k n * w n) =
          fun n => (1 - q ^ k - k * B) * w n + B * (n * w n) := by
        funext n; rw [hlin]; ring
      rw [e1, show PPL q k c = (1 - q ^ k - k * B) + B * c by rw [hlin]; ring]
      exact a.add b
    have hs : Summable (fun n : ℕ => (1 - q ^ n) * w n) := by
      refine Summable.of_nonneg_of_le (fun n => mul_nonneg ?_ (hw n)) (fun n => ?_) h1.summable
      · linarith [pow_le_one₀ (n := n) hq0 hq1]
      · have := pow_nonneg hq0 n
        nlinarith [hw n]
    rw [hV, ← hL.tsum_eq]
    exact hs.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (PP_conc q hq0 hq1 n k) (hw n))
      hL.summable
  · by_cases he : ⌊c⌋₊ = ⌈c⌉₊
    · have hck' : (k : ℝ) = c := by
        apply le_antisymm hkc; rw [hk, he]; exact Nat.le_ceil c
      have htp : twoPoint c = fun n => if n = k then 1 else 0 := by
        funext n; unfold twoPoint; rw [if_pos he]
      rw [htp]
      refine ⟨fun n => by dsimp only; split_ifs <;> norm_num, hasSum_ite_eq k 1, ?_, ?_⟩
      · have : (fun n : ℕ => (n : ℝ) * if n = k then 1 else 0) = fun n => if n = k then (k : ℝ) else 0 := by
          funext n; split_ifs with h <;> simp [h]
        rw [this, ← hck']; exact hasSum_ite_eq k _
      · have : (fun n : ℕ => (1 - q ^ n) * if n = k then (1 : ℝ) else 0) = fun n => if n = k then (1 - q ^ k) else 0 := by
          funext n; split_ifs with h <;> simp [h]
        rw [this, tsum_ite_eq, hV]; unfold PPL; rw [hck']; ring
    · have hce : ⌈c⌉₊ = k + 1 := by
        rcases Nat.eq_or_lt_of_le (Nat.ceil_le_floor_add_one c) with h | h
        · exact h
        · exfalso; exact he (le_antisymm (Nat.floor_le_ceil c) (Nat.lt_add_one_iff.mp h))
      have hkc2 : (k : ℝ) < c := by
        rcases lt_or_eq_of_le hkc with h | h
        · exact h
        · exfalso; apply he; rw [← hk, hce]
          have : ⌈c⌉₊ = k := by rw [← h]; simp
          omega
      have htp : twoPoint c = fun n => if n = k then (k + 1 : ℝ) - c else if n = k + 1 then c - k else 0 := by
        funext n; unfold twoPoint; rw [if_neg he, hce]; push_cast; rfl
      rw [htp]
      have hne : k ≠ k + 1 := by omega
      have hsupp : ∀ (g : ℕ → ℝ), (∀ n, n ∉ ({k, k + 1} : Finset ℕ) →
          g n * (if n = k then (k + 1 : ℝ) - c else if n = k + 1 then c - k else 0) = 0) := by
        intro g n hn
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        rw [if_neg hn.1, if_neg hn.2, mul_zero]
      have key : ∀ g : ℕ → ℝ, HasSum (fun n => g n * (if n = k then (k + 1 : ℝ) - c else if n = k + 1 then c - k else 0))
          (g k * ((k + 1 : ℝ) - c) + g (k + 1) * (c - k)) := by
        intro g
        have : HasSum (fun n => g n * (if n = k then (k + 1 : ℝ) - c else if n = k + 1 then c - k else 0))
            (∑ n ∈ ({k, k + 1} : Finset ℕ),
              g n * (if n = k then (k + 1 : ℝ) - c else if n = k + 1 then c - k else 0)) :=
          hasSum_sum_of_ne_finset_zero (hsupp g)
        rw [Finset.sum_pair hne] at this
        simpa [hne, hne.symm] using this
      refine ⟨fun n => by dsimp only; split_ifs <;> linarith, ?_, ?_, ?_⟩
      · have := key (fun _ => 1)
        simp only [one_mul] at this
        convert this using 1; ring
      · have := key (fun n => (n : ℝ))
        convert this using 1; push_cast; ring
      · rw [(key (fun n => 1 - q ^ n)).tsum_eq, hV]
        unfold PPL; ring
