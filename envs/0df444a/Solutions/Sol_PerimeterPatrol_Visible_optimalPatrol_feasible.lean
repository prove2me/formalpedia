-- Prove2me | solution 1 for PerimeterPatrol.Visible.optimalPatrol_feasible
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T23:09:13.865792+00:00
-- url     : https://prove2.me/submissions/5eea4a12-d912-484a-857d-0e05aa2b7a35

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model
import Definitions.Def_PerimeterPatrol_Visible_OptimalPatrol

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


open MeasureTheory Filter Topology

namespace PerimeterPatrol.Visible

lemma PP_card_window {α : Type*} (P : α → Prop) (g : α → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hfin : {x | P x ∧ g x ≤ b}.Finite) :
    Nat.card {x | P x ∧ g x ≤ b} = Nat.card {x | P x ∧ g x ≤ a} + Nat.card {x | P x ∧ a < g x ∧ g x ≤ b} := by
  have hu : {x | P x ∧ g x ≤ b} = {x | P x ∧ g x ≤ a} ∪ {x | P x ∧ a < g x ∧ g x ≤ b} := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_or_gt (g x) a with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, _, h3⟩)
      · exact ⟨h1, le_trans h2 hab⟩
      · exact ⟨h1, h3⟩
  have hd : Disjoint {x | P x ∧ g x ≤ a} {x | P x ∧ a < g x ∧ g x ≤ b} := by
    rw [Set.disjoint_left]; rintro x ⟨_, h1⟩ ⟨_, h2, _⟩; linarith
  rw [hu] at hfin ⊢
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_union_eq hd (hfin.subset Set.subset_union_left) (hfin.subset Set.subset_union_right)]

section
variable (lam t : ℝ)

lemma PP_blue_finite (ht : 0 < t) (u : ℝ) :
    {jk : ℕ × ℕ | IsBlue lam t jk ∧ bluePoint lam t jk ≤ u}.Finite := by
  apply (Set.finite_Iic (⌊u / t⌋₊, ⌊lam * t⌋₊)).subset
  rintro ⟨j, k⟩ ⟨⟨hk1, hk2⟩, hb⟩
  simp only [Set.mem_Iic, Prod.mk_le_mk]
  refine ⟨Nat.le_floor ?_, hk2⟩
  unfold bluePoint at hb
  have : 0 ≤ (k : ℝ) * (t / (⌈lam * t⌉₊ : ℝ)) := by positivity
  rw [le_div_iff₀ ht]; simp only at hb; linarith

lemma PP_red_finite (ht : 0 < t) (u : ℝ) (Q : ℕ → Prop) :
    {j : ℕ | (j : ℝ) * t ≤ u ∧ Q j}.Finite := by
  apply (Set.finite_Iic ⌊u / t⌋₊).subset
  rintro j ⟨hj, _⟩
  simp only [Set.mem_Iic]
  exact Nat.le_floor (by rw [le_div_iff₀ ht]; exact hj)

lemma PP_count_mono (ht : 0 < t) (ω : ℕ → unitInterval) {u u' : ℝ} (h : u ≤ u') :
    count lam t ω u ≤ count lam t ω u' := by
  unfold count blueCount
  apply add_le_add
  · rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (fun jk hjk => ⟨hjk.1, le_trans hjk.2 h⟩) (PP_blue_finite lam t ht u')
  · rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (fun j hj => ⟨le_trans hj.1 h, hj.2⟩) (PP_red_finite t ht u' _)

lemma PP_count_neg (ht : 0 < t) (ω : ℕ → unitInterval) {u : ℝ} (h : u < 0) :
    count lam t ω u = 0 := by
  unfold count blueCount
  have e1 : {jk : ℕ × ℕ | IsBlue lam t jk ∧ bluePoint lam t jk ≤ u} = ∅ := by
    ext ⟨j, k⟩; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro _; unfold bluePoint
    have : 0 ≤ (k : ℝ) * (t / (⌈lam * t⌉₊ : ℝ)) := by positivity
    have : 0 ≤ (j : ℝ) * t := by positivity
    simp only; linarith
  have e2 : {j : ℕ | (j : ℝ) * t ≤ u ∧ redPresent lam t ω j} = ∅ := by
    ext j; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro h'; have : 0 ≤ (j : ℝ) * t := by positivity
    linarith
  rw [e1, e2]; simp

lemma PP_grid (D v u x : ℝ) (hD : 0 < D) (hv : 0 ≤ v) (m : ℕ) (hx : x = m * D) (hxu : x ≤ u)
    (hu : u < (⌊v / D⌋₊ + 1) * D) : x ≤ v := by
  subst hx
  have h1 : (m : ℝ) < ⌊v / D⌋₊ + 1 := by
    by_contra h; push_neg at h; nlinarith
  have h2 : m ≤ ⌊v / D⌋₊ := by
    have : m < ⌊v / D⌋₊ + 1 := by exact_mod_cast h1
    omega
  have h3 : (m : ℝ) ≤ v / D := le_trans (by exact_mod_cast h2) (Nat.floor_le (by positivity))
  rwa [le_div_iff₀ hD] at h3

lemma PP_count_grid (hlam : 0 < lam) (ht : 0 < t) (ω : ℕ → unitInterval) {u v : ℝ} (hv : 0 ≤ v)
    (hu : u < (⌊v / (t / (⌈lam * t⌉₊ : ℝ))⌋₊ + 1) * (t / (⌈lam * t⌉₊ : ℝ))) :
    count lam t ω u ≤ count lam t ω v := by
  have hK : (0 : ℝ) < ⌈lam * t⌉₊ := by
    have : 0 < ⌈lam * t⌉₊ := Nat.ceil_pos.mpr (by positivity)
    exact_mod_cast this
  have hD : 0 < t / (⌈lam * t⌉₊ : ℝ) := by positivity
  have htD : t = (⌈lam * t⌉₊ : ℝ) * (t / (⌈lam * t⌉₊ : ℝ)) := by field_simp
  unfold count blueCount
  apply add_le_add
  · rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    refine Set.ncard_le_ncard (fun jk hjk => ⟨hjk.1, ?_⟩) (PP_blue_finite lam t ht v)
    refine PP_grid _ v u _ hD hv (jk.1 * ⌈lam * t⌉₊ + jk.2) ?_ hjk.2 hu
    unfold bluePoint; push_cast
    field_simp
  · rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    refine Set.ncard_le_ncard (fun j hj => ⟨?_, hj.2⟩) (PP_red_finite t ht v _)
    refine PP_grid _ v u _ hD hv (j * ⌈lam * t⌉₊) ?_ hj.1 hu
    push_cast
    field_simp

lemma PP_sched_le_iff (hlam : 0 < lam) (ht : 0 < t) (ω : ℕ → unitInterval) (m : ℕ)
    (hne : ∃ u, m < count lam t ω u) (v : ℝ) :
    sched lam t ω m ≤ v ↔ m < count lam t ω v := by
  have hbdd : BddBelow {u : ℝ | m < count lam t ω u} := by
    refine ⟨0, fun u hu => ?_⟩
    by_contra h; push_neg at h
    change m < count lam t ω u at hu
    rw [PP_count_neg lam t ht ω h] at hu; omega
  unfold sched
  constructor
  · intro h
    by_contra hc; push_neg at hc
    rcases lt_or_ge v 0 with hv | hv
    · have : 0 ≤ sInf {u : ℝ | m < count lam t ω u} := by
        apply le_csInf hne
        intro u hu
        by_contra h'; push_neg at h'
        change m < count lam t ω u at hu
        rw [PP_count_neg lam t ht ω h'] at hu; omega
      linarith
    · set D := t / (⌈lam * t⌉₊ : ℝ)
      have hK : (0 : ℝ) < ⌈lam * t⌉₊ := by
        have : 0 < ⌈lam * t⌉₊ := Nat.ceil_pos.mpr (by positivity)
        exact_mod_cast this
      have hD : 0 < D := by positivity
      have hw : (⌊v / D⌋₊ + 1) * D ≤ sInf {u : ℝ | m < count lam t ω u} := by
        apply le_csInf hne
        intro u hu
        by_contra h'; push_neg at h'
        change m < count lam t ω u at hu
        have := PP_count_grid lam t hlam ht ω hv h'
        omega
      have : v < (⌊v / D⌋₊ + 1) * D := by
        have := Nat.lt_floor_add_one (v / D)
        rwa [div_lt_iff₀ hD] at this
      linarith
  · intro h
    exact csInf_le hbdd h

/-- the good event: the count is unbounded -/
def PPGood (ω : ℕ → unitInterval) : Prop := ∀ m : ℕ, ∃ u, m < count lam t ω u

lemma PP_sched_set (hlam : 0 < lam) (ht : 0 < t) (ω : ℕ → unitInterval) (hG : PPGood lam t ω)
    (v : ℝ) : {m : ℕ | sched lam t ω m ≤ v} = Set.Iio (count lam t ω v) := by
  ext m; simp only [Set.mem_setOf_eq, Set.mem_Iio]
  exact PP_sched_le_iff lam t hlam ht ω m (hG m) v

lemma PP_card_sched (hlam : 0 < lam) (ht : 0 < t) (ω : ℕ → unitInterval) (hG : PPGood lam t ω)
    (v : ℝ) : Nat.card {m : ℕ | sched lam t ω m ≤ v} = count lam t ω v := by
  have : {m : ℕ | sched lam t ω m ≤ v} = Set.Iio (count lam t ω v) := by
    ext m; simp only [Set.mem_setOf_eq, Set.mem_Iio]
    exact PP_sched_le_iff lam t hlam ht ω m (hG m) v
  rw [this, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
  simp

lemma PP_sched_mono (hlam : 0 < lam) (ht : 0 < t) (ω : ℕ → unitInterval) (hG : PPGood lam t ω) :
    Monotone (sched lam t ω) := by
  intro a b hab
  rw [PP_sched_le_iff lam t hlam ht ω a (hG a)]
  have := (PP_sched_le_iff lam t hlam ht ω b (hG b) (sched lam t ω b)).mp le_rfl
  omega

lemma PP_sched_nonneg (hlam : 0 < lam) (ht : 0 < t) (ω : ℕ → unitInterval) (hG : PPGood lam t ω) :
    0 ≤ sched lam t ω 0 := by
  by_contra h; push_neg at h
  have := (PP_sched_le_iff lam t hlam ht ω 0 (hG 0) (sched lam t ω 0)).mp le_rfl
  rw [PP_count_neg lam t ht ω h] at this; omega

lemma PP_slot_iff (b : ℝ) (ht : 0 < t) (hb : -t ≤ b) (j : ℕ) :
    (b < (j : ℝ) * t ∧ (j : ℝ) * t ≤ b + t) ↔ j = ⌊b / t + 1⌋₊ := by
  have hx : 0 ≤ b / t + 1 := by
    have : -1 ≤ b / t := by rw [le_div_iff₀ ht]; linarith
    linarith
  have e1 : b < (j : ℝ) * t ↔ b / t + 1 < (j : ℝ) + 1 := by
    rw [add_lt_add_iff_right, div_lt_iff₀ ht]
  have e2 : (j : ℝ) * t ≤ b + t ↔ (j : ℝ) ≤ b / t + 1 := by
    rw [show b / t + 1 = (b + t) / t by field_simp]; rw [le_div_iff₀ ht]
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    apply le_antisymm (Nat.le_floor h2)
    have := Nat.floor_le hx
    have : (⌊b / t + 1⌋₊ : ℝ) < (j : ℝ) + 1 := by linarith
    exact_mod_cast Nat.lt_add_one_iff.mp (by exact_mod_cast this)
  · rintro rfl
    exact ⟨Nat.lt_floor_add_one _, Nat.floor_le hx⟩

lemma PP_blue_window (a : ℝ) (hlam : 0 < lam) (ht : 0 < t) (ha : 0 ≤ a) :
    Nat.card {jk : ℕ × ℕ | IsBlue lam t jk ∧ a < bluePoint lam t jk ∧ bluePoint lam t jk ≤ a + t} = ⌊lam * t⌋₊ := by
  set n := ⌊lam * t⌋₊ with hn
  set D := t / (⌈lam * t⌉₊ : ℝ) with hD
  have hc : (0 : ℝ) < ⌈lam * t⌉₊ := by
    have : 0 < ⌈lam * t⌉₊ := Nat.ceil_pos.mpr (by positivity)
    exact_mod_cast this
  have hkD : ∀ k : ℕ, k ≤ n → (k : ℝ) * D ≤ t := by
    intro k hk
    have : (k : ℝ) ≤ ⌈lam * t⌉₊ := by
      exact_mod_cast le_trans hk (Nat.floor_le_ceil _)
    rw [hD, mul_div_assoc', div_le_iff₀ hc]; nlinarith
  let g : ℕ → ℕ × ℕ := fun k => (⌊(a - (k : ℝ) * D) / t + 1⌋₊, k)
  have hg : Function.Injective g := by
    intro x y h; simpa [g] using congrArg Prod.snd h
  have hset : {jk : ℕ × ℕ | IsBlue lam t jk ∧ a < bluePoint lam t jk ∧ bluePoint lam t jk ≤ a + t}
      = ↑((Finset.Icc 1 n).image g) := by
    ext ⟨j, k⟩
    simp only [Set.mem_setOf_eq, IsBlue, bluePoint, Finset.coe_image, Finset.coe_Icc,
      Set.mem_image, Set.mem_Icc, g, Prod.mk.injEq]
    rw [← hD, ← hn]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, h1, h2⟩
      refine ⟨k, ⟨hk1, hk2⟩, ?_, rfl⟩
      have hb : -t ≤ a - (k : ℝ) * D := by linarith [hkD k hk2]
      exact ((PP_slot_iff t (a - (k : ℝ) * D) ht hb j).mp ⟨by linarith, by linarith⟩).symm
    · rintro ⟨k', ⟨hk1, hk2⟩, hj, rfl⟩
      have hb : -t ≤ a - (k' : ℝ) * D := by linarith [hkD k' hk2]
      have := (PP_slot_iff t (a - (k' : ℝ) * D) ht hb j).mpr hj.symm
      exact ⟨⟨hk1, hk2⟩, by linarith [this.1], by linarith [this.2]⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hg]
  simp

lemma PP_measurable_count (u : ℝ) :
    Measurable (fun ω : ℕ → unitInterval => count lam t ω u) := by
  unfold count
  apply Measurable.add measurable_const
  apply PP_measurable_card (fun (ω : ℕ → unitInterval) j => (j : ℝ) * t ≤ u ∧ redPresent lam t ω j)
  intro j
  by_cases h : (j : ℝ) * t ≤ u
  · simp only [h, true_and, redPresent]
    exact measurableSet_lt ((measurable_subtype_coe).comp (measurable_pi_apply j)) measurable_const
  · simp [h]

lemma PP_measurable_sched (hlam : 0 < lam) (ht : 0 < t) (m : ℕ) :
    Measurable (fun ω : ℕ → unitInterval => sched lam t ω m) := by
  apply measurable_of_Iic
  intro v
  have hex : ∀ ω, (∃ u : ℝ, m < count lam t ω u) ↔ ∃ u : ℕ, m < count lam t ω u := by
    intro ω
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨⌈u⌉₊, lt_of_lt_of_le hu (PP_count_mono lam t ht ω (Nat.le_ceil u))⟩
    · rintro ⟨u, hu⟩; exact ⟨u, hu⟩
  have hset : (fun ω : ℕ → unitInterval => sched lam t ω m) ⁻¹' Set.Iic v =
      ((⋃ u : ℕ, {ω | m < count lam t ω u}) ∩ {ω | m < count lam t ω v}) ∪
        ((⋃ u : ℕ, {ω | m < count lam t ω u})ᶜ ∩ {_ω | 0 ≤ v}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion,
      Set.mem_compl_iff, Set.mem_setOf_eq]
    by_cases h : ∃ u : ℕ, m < count lam t ω u
    · simp only [h, true_and, not_true_eq_false, false_and, or_false]
      exact PP_sched_le_iff lam t hlam ht ω m ((hex ω).mpr h) v
    · simp only [h, false_and, not_false_eq_true, true_and, false_or]
      have : {u : ℝ | m < count lam t ω u} = ∅ := by
        ext u; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hu; exact h ((hex ω).mp ⟨u, hu⟩)
      unfold sched; rw [this, Real.sInf_empty]
  rw [hset]
  have hc : ∀ u, MeasurableSet {ω : ℕ → unitInterval | m < count lam t ω u} := fun u =>
    measurableSet_lt measurable_const (PP_measurable_count lam t u)
  exact (( MeasurableSet.iUnion fun u : ℕ => hc (u : ℝ)).inter (hc v)).union
    ((MeasurableSet.iUnion fun u : ℕ => hc (u : ℝ)).compl.inter (MeasurableSet.const _))

lemma PP_measurable_schedMap (hlam : 0 < lam) (ht : 0 < t) :
    Measurable (fun ω : ℕ → unitInterval => fun m => sched lam t ω m) :=
  measurable_pi_lambda _ fun m => PP_measurable_sched lam t hlam ht m

open Classical in
lemma PP_window (hlam : 0 < lam) (ht : 0 < t) (ω : ℕ → unitInterval) (hG : PPGood lam t ω)
    (a : ℝ) (ha : 0 ≤ a) :
    arrivals (sched lam t ω) a (a + t) =
      ⌊lam * t⌋₊ + (if redPresent lam t ω ⌊a / t + 1⌋₊ then 1 else 0) := by
  have hab : a ≤ a + t := by linarith
  -- schedule counts
  have e1 := PP_card_window (fun _ : ℕ => True) (sched lam t ω) a (a + t) hab (by
    have : {x : ℕ | True ∧ sched lam t ω x ≤ a + t} = {x | sched lam t ω x ≤ a + t} := by ext; simp
    rw [this, PP_sched_set lam t hlam ht ω hG]; exact Set.finite_Iio _)
  simp only [true_and] at e1
  rw [PP_card_sched lam t hlam ht ω hG, PP_card_sched lam t hlam ht ω hG] at e1
  have hred : ∀ v, Nat.card {j : ℕ | (j : ℝ) * t ≤ v ∧ redPresent lam t ω j} =
      Nat.card {j : ℕ | redPresent lam t ω j ∧ (j : ℝ) * t ≤ v} := by
    intro v; rw [show {j : ℕ | (j : ℝ) * t ≤ v ∧ redPresent lam t ω j} =
      {j : ℕ | redPresent lam t ω j ∧ (j : ℝ) * t ≤ v} from Set.ext fun j => and_comm]
  have e2 := PP_card_window (IsBlue lam t) (bluePoint lam t) a (a + t) hab (PP_blue_finite lam t ht _)
  rw [PP_blue_window lam t a hlam ht ha] at e2
  have e3 := PP_card_window (redPresent lam t ω) (fun j : ℕ => (j : ℝ) * t) a (a + t) hab (by
    have := PP_red_finite t ht (a + t) (redPresent lam t ω)
    refine this.subset ?_
    intro j hj; exact ⟨hj.2, hj.1⟩)
  beta_reduce at e3
  have e4 : Nat.card {j : ℕ | redPresent lam t ω j ∧ a < (j : ℝ) * t ∧
      (j : ℝ) * t ≤ a + t} =
      (if redPresent lam t ω ⌊a / t + 1⌋₊ then 1 else 0) := by
    have hs : {j : ℕ | redPresent lam t ω j ∧ a < (j : ℝ) * t ∧
        (j : ℝ) * t ≤ a + t} =
        {j : ℕ | redPresent lam t ω j ∧ j = ⌊a / t + 1⌋₊} := by
      ext j
      simp only [Set.mem_setOf_eq]
      rw [← PP_slot_iff t a ht (by linarith) j]
    rw [hs]
    split_ifs with h
    · have : {j : ℕ | redPresent lam t ω j ∧ j = ⌊a / t + 1⌋₊} = {⌊a / t + 1⌋₊} := by
        ext j; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · exact fun h' => h'.2
        · rintro rfl; exact ⟨h, rfl⟩
      rw [this]; simp
    · have : {j : ℕ | redPresent lam t ω j ∧ j = ⌊a / t + 1⌋₊} = ∅ := by
        ext j; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        rintro h' rfl; exact h h'
      rw [this]; simp
  rw [e4] at e3
  unfold count blueCount at e1
  rw [hred, hred] at e1
  unfold arrivals
  split_ifs at e3 ⊢ <;> omega

lemma PP_good_blue (hlam : 0 < lam) (ht : 0 < t) (hn : 1 ≤ ⌊lam * t⌋₊) (ω : ℕ → unitInterval) :
    PPGood lam t ω := by
  intro m
  refine ⟨((m : ℝ) + 1) * t, ?_⟩
  have hK : (1 : ℝ) ≤ ⌈lam * t⌉₊ := by
    have : 1 ≤ ⌈lam * t⌉₊ := le_trans hn (Nat.floor_le_ceil _)
    exact_mod_cast this
  have hD : t / (⌈lam * t⌉₊ : ℝ) ≤ t := div_le_self ht.le hK
  have hsub : ↑((Finset.range (m + 1)).image (fun j => (j, 1))) ⊆
      {jk : ℕ × ℕ | IsBlue lam t jk ∧ bluePoint lam t jk ≤ ((m : ℝ) + 1) * t} := by
    intro jk hjk
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hjk
    obtain ⟨j, hj, rfl⟩ := hjk
    refine ⟨⟨le_rfl, hn⟩, ?_⟩
    unfold bluePoint
    have : (j : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp hj
    simp only [Nat.cast_one, one_mul]
    nlinarith
  have h1 := Set.ncard_le_ncard hsub (PP_blue_finite lam t ht _)
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ (fun a b h => by simpa using h)] at h1
  simp only [Finset.card_range] at h1
  unfold count blueCount
  rw [Nat.card_coe_set_eq]
  omega

lemma PP_good_red (ht : 0 < t) (ω : ℕ → unitInterval) (hinf : {j : ℕ | redPresent lam t ω j}.Infinite) :
    PPGood lam t ω := by
  intro m
  obtain ⟨F, hF, hcard⟩ := hinf.exists_subset_card_eq (m + 1)
  refine ⟨((F.sup id : ℕ) : ℝ) * t, ?_⟩
  have hsub : (↑F : Set ℕ) ⊆ {j : ℕ | (j : ℝ) * t ≤ ((F.sup id : ℕ) : ℝ) * t ∧ redPresent lam t ω j} := by
    intro j hj
    refine ⟨?_, hF hj⟩
    have : j ≤ F.sup id := Finset.le_sup (f := id) hj
    have : (j : ℝ) ≤ (F.sup id : ℕ) := by exact_mod_cast this
    nlinarith
  have h1 := Set.ncard_le_ncard hsub (PP_red_finite t ht _ _)
  rw [Set.ncard_coe_finset, hcard] at h1
  unfold count
  rw [Nat.card_coe_set_eq (s := {j : ℕ | (j : ℝ) * t ≤ _ ∧ redPresent lam t ω j})]
  omega

lemma PP_blue_zero (ht : 0 < t) : blueCount lam t 0 = 0 := by
  unfold blueCount
  have : {jk : ℕ × ℕ | IsBlue lam t jk ∧ bluePoint lam t jk ≤ 0} = ∅ := by
    ext ⟨j, k⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    rintro ⟨hk, hk2⟩
    have hK : (0 : ℝ) < ⌈lam * t⌉₊ := by
      have : 0 < ⌈lam * t⌉₊ := lt_of_lt_of_le hk (le_trans hk2 (Nat.floor_le_ceil _))
      exact_mod_cast this
    unfold bluePoint
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : 0 < (k : ℝ) * (t / (⌈lam * t⌉₊ : ℝ)) := by positivity
    have : 0 ≤ (j : ℝ) * t := by positivity
    simp only; linarith
  rw [this]; simp

lemma PP_blue_mono (ht : 0 < t) {u u' : ℝ} (h : u ≤ u') : blueCount lam t u ≤ blueCount lam t u' := by
  unfold blueCount
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard (fun jk hjk => ⟨hjk.1, le_trans hjk.2 h⟩) (PP_blue_finite lam t ht u')

lemma PP_blue_mult (hlam : 0 < lam) (ht : 0 < t) (m : ℕ) :
    blueCount lam t ((m : ℝ) * t) = m * ⌊lam * t⌋₊ := by
  induction m with
  | zero => simp [PP_blue_zero lam t ht]
  | succ m ih =>
    have e2 := PP_card_window (IsBlue lam t) (bluePoint lam t) ((m : ℝ) * t) ((m : ℝ) * t + t)
      (by linarith) (PP_blue_finite lam t ht _)
    rw [PP_blue_window lam t _ hlam ht (by positivity)] at e2
    unfold blueCount at ih ⊢
    push_cast
    rw [show ((m : ℝ) + 1) * t = (m : ℝ) * t + t by ring, e2, ih]
    ring

lemma PP_blue_bounds (hlam : 0 < lam) (ht : 0 < t) (T : ℝ) (hT : 0 ≤ T) :
    (⌊lam * t⌋₊ : ℝ) * (T / t - 1) ≤ blueCount lam t T ∧
      (blueCount lam t T : ℝ) ≤ (⌊lam * t⌋₊ : ℝ) * (T / t + 1) := by
  set m := ⌊T / t⌋₊
  have h1 : (m : ℝ) ≤ T / t := Nat.floor_le (by positivity)
  have h2 : T / t < m + 1 := Nat.lt_floor_add_one _
  have l1 : (m : ℝ) * t ≤ T := by rwa [le_div_iff₀ ht] at h1
  have l2 : T ≤ ((m + 1 : ℕ) : ℝ) * t := by push_cast; rw [div_lt_iff₀ ht] at h2; linarith
  have b1 := PP_blue_mono lam t ht l1
  have b2 := PP_blue_mono lam t ht l2
  rw [PP_blue_mult lam t hlam ht] at b1 b2
  have hn : (0 : ℝ) ≤ ⌊lam * t⌋₊ := by positivity
  constructor
  · have : ((m * ⌊lam * t⌋₊ : ℕ) : ℝ) ≤ blueCount lam t T := by exact_mod_cast b1
    push_cast at this
    nlinarith
  · have : (blueCount lam t T : ℝ) ≤ (((m + 1) * ⌊lam * t⌋₊ : ℕ) : ℝ) := by exact_mod_cast b2
    push_cast at this
    nlinarith

lemma PP_blue_rate (hlam : 0 < lam) (ht : 0 < t) :
    Tendsto (fun T : ℝ => (blueCount lam t T : ℝ) / T) atTop (𝓝 ((⌊lam * t⌋₊ : ℝ) / t)) := by
  set n : ℝ := (⌊lam * t⌋₊ : ℝ)
  have hlo : Tendsto (fun T : ℝ => n / t - n / T) atTop (𝓝 (n / t - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
  have hhi : Tendsto (fun T : ℝ => n / t + n / T) atTop (𝓝 (n / t + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [sub_zero] at hlo; rw [add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_gt_atTop 0] with T hT
    have := (PP_blue_bounds lam t hlam ht T hT.le).1
    rw [le_div_iff₀ hT]
    have e : (n / t - n / T) * T = n * (T / t - 1) := by field_simp
    rw [e]; exact this
  · filter_upwards [eventually_gt_atTop 0] with T hT
    have := (PP_blue_bounds lam t hlam ht T hT.le).2
    rw [div_le_iff₀ hT]
    have e : (n / t + n / T) * T = n * (T / t + 1) := by field_simp
    rw [e]; exact this

/-- the red indicator -/
noncomputable def PPX (ω : ℕ → unitInterval) (j : ℕ) : ℝ := by
  classical exact if redPresent lam t ω j then 1 else 0

lemma PP_red_sum (ht : 0 < t) (ω : ℕ → unitInterval) (T : ℝ) (hT : 0 ≤ T) :
    (Nat.card {j : ℕ | (j : ℝ) * t ≤ T ∧ redPresent lam t ω j} : ℝ) =
      ∑ j ∈ Finset.range (⌊T / t⌋₊ + 1), PPX lam t ω j := by
  classical
  have hs : {j : ℕ | (j : ℝ) * t ≤ T ∧ redPresent lam t ω j} =
      ↑((Finset.range (⌊T / t⌋₊ + 1)).filter (fun j => redPresent lam t ω j)) := by
    ext j
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Nat.lt_succ_of_le (Nat.le_floor ?_), h2⟩
      rw [le_div_iff₀ ht]; exact h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have : (j : ℝ) ≤ ⌊T / t⌋₊ := by exact_mod_cast Nat.lt_succ_iff.mp h1
      have h3 := Nat.floor_le (div_nonneg hT ht.le)
      have : (j : ℝ) ≤ T / t := le_trans this h3
      rwa [le_div_iff₀ ht] at this
  rw [hs, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  unfold PPX
  split_ifs <;> simp

lemma PP_frac_bounds (h : 0 ≤ lam * t) : 0 ≤ lam * t - ⌊lam * t⌋₊ ∧ lam * t - ⌊lam * t⌋₊ < 1 :=
  ⟨by linarith [Nat.floor_le h], by linarith [Nat.lt_floor_add_one (lam * t)]⟩

lemma PP_slln (hlam : 0 < lam) (ht : 0 < t) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)),
      Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, PPX lam t ω j) / N) atTop
        (𝓝 (lam * t - ⌊lam * t⌋₊)) := by
  classical
  set P := Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)
  set fr := lam * t - ⌊lam * t⌋₊ with hfr
  obtain ⟨hf0, hf1⟩ := PP_frac_bounds lam t (by positivity)
  let frI : unitInterval := ⟨fr, hf0, hf1.le⟩
  let Xf : unitInterval → ℝ := Set.indicator (Set.Iio frI) 1
  have hXf : Measurable Xf := measurable_one.indicator measurableSet_Iio
  have hX : ∀ ω j, PPX lam t ω j = Xf (ω j) := by
    intro ω j
    unfold PPX redPresent
    simp only [Xf, Set.indicator, Set.mem_Iio, Pi.one_apply]
    have : ((ω j : ℝ) < fr) ↔ ω j < frI := by
      rw [← Subtype.coe_lt_coe]
    by_cases h : ω j < frI
    · rw [if_pos (this.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (this.mp h')), if_neg h]
  have hind := ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => (volume : Measure unitInterval))
    (X := fun _ => Xf) (fun _ => hXf)
  have hint : Integrable (fun ω : ℕ → unitInterval => Xf (ω 0)) P :=
    Integrable.of_bound (hXf.comp (measurable_pi_apply 0)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        simp only [Xf, Set.indicator]; split_ifs <;> simp)
  have hmap : ∀ i, P.map (fun ω => Xf (ω i)) = (volume : Measure unitInterval).map Xf := by
    intro i
    rw [show (fun ω : ℕ → unitInterval => Xf (ω i)) = Xf ∘ (fun ω => ω i) from rfl,
      ← Measure.map_map hXf (measurable_pi_apply i)]
    rw [Measure.infinitePi_map_eval]
  have hlaw := ProbabilityTheory.strong_law_ae_real (μ := P) (fun j ω => Xf (ω j)) hint
    (fun i j hij => hind.indepFun hij)
    (fun i => ⟨(hXf.comp (measurable_pi_apply i)).aemeasurable,
      (hXf.comp (measurable_pi_apply 0)).aemeasurable, by rw [hmap, hmap]⟩)
  have hE : (∫ ω, Xf (ω 0) ∂P) = fr := by
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hXf.aestronglyMeasurable,
      Measure.infinitePi_map_eval]
    simp only [Xf]
    rw [integral_indicator_one measurableSet_Iio, Measure.real, unitInterval.volume_Iio]
    exact ENNReal.toReal_ofReal hf0
  filter_upwards [hlaw] with ω hω
  rw [hE] at hω
  simpa only [hX] using hω

open Classical in
lemma PP_sum_PPX (ω : ℕ → unitInterval) (N : ℕ) :
    ∑ j ∈ Finset.range N, PPX lam t ω j =
      (((Finset.range N).filter (fun j => redPresent lam t ω j)).card : ℝ) := by
  classical
  rw [Finset.card_filter]; push_cast
  apply Finset.sum_congr rfl; intro j _; unfold PPX; split_ifs <;> simp

lemma PP_red_rate (ht : 0 < t) (ω : ℕ → unitInterval)
    (hω : Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, PPX lam t ω j) / N) atTop
      (𝓝 (lam * t - ⌊lam * t⌋₊))) :
    Tendsto (fun T : ℝ => (Nat.card {j : ℕ | (j : ℝ) * t ≤ T ∧ redPresent lam t ω j} : ℝ) / T)
      atTop (𝓝 ((lam * t - ⌊lam * t⌋₊) / t)) := by
  set fr := lam * t - ⌊lam * t⌋₊
  let M : ℝ → ℕ := fun T => ⌊T / t⌋₊ + 1
  have hM : Tendsto M atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const ht))
  have h1 := hω.comp hM
  have h2 : Tendsto (fun T : ℝ => (M T : ℝ) / T) atTop (𝓝 (1 / t)) := by
    have hlo : Tendsto (fun T : ℝ => 1 / t) atTop (𝓝 (1 / t)) := tendsto_const_nhds
    have hhi : Tendsto (fun T : ℝ => 1 / t + 1 / T) atTop (𝓝 (1 / t + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    rw [add_zero] at hhi
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · filter_upwards [eventually_gt_atTop 0] with T hT
      rw [le_div_iff₀ hT]
      have := Nat.lt_floor_add_one (T / t)
      have e : 1 / t * T = T / t := by ring
      rw [e]; simp only [M]; push_cast; linarith
    · filter_upwards [eventually_gt_atTop 0] with T hT
      rw [div_le_iff₀ hT]
      have := Nat.floor_le (div_nonneg hT.le ht.le)
      have e : (1 / t + 1 / T) * T = T / t + 1 := by field_simp
      rw [e]; simp only [M]; push_cast; linarith
  have h3 := h1.mul h2
  rw [show fr * (1 / t) = fr / t by ring] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  simp only [Function.comp]
  rw [PP_red_sum lam t ht ω T hT.le]
  have : (0 : ℝ) < M T := by positivity
  field_simp
  rfl

lemma PP_count_rate (hlam : 0 < lam) (ht : 0 < t) (ω : ℕ → unitInterval)
    (hω : Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, PPX lam t ω j) / N) atTop
      (𝓝 (lam * t - ⌊lam * t⌋₊))) :
    Tendsto (fun T : ℝ => (count lam t ω T : ℝ) / T) atTop (𝓝 lam) := by
  have h := (PP_blue_rate lam t hlam ht).add (PP_red_rate lam t ht ω hω)
  have e : (⌊lam * t⌋₊ : ℝ) / t + (lam * t - ⌊lam * t⌋₊) / t = lam := by field_simp; ring
  rw [e] at h
  refine h.congr' (Eventually.of_forall fun T => ?_)
  simp only [count]; push_cast; ring

lemma PP_good_ae (hlam : 0 < lam) (ht : 0 < t) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)),
      PPGood lam t ω ∧ Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, PPX lam t ω j) / N) atTop
        (𝓝 (lam * t - ⌊lam * t⌋₊)) := by
  classical
  filter_upwards [PP_slln lam t hlam ht] with ω hω
  refine ⟨?_, hω⟩
  by_cases hn : 1 ≤ ⌊lam * t⌋₊
  · exact PP_good_blue lam t hlam ht hn ω
  · have hn0 : ⌊lam * t⌋₊ = 0 := by omega
    have hfr : 0 < lam * t - ⌊lam * t⌋₊ := by rw [hn0]; simp; positivity
    apply PP_good_red lam t ht ω
    by_contra hfin
    rw [Set.not_infinite] at hfin
    set B := {j : ℕ | redPresent lam t ω j}.ncard
    have hb : ∀ N : ℕ, ∑ j ∈ Finset.range N, PPX lam t ω j ≤ B := by
      intro N
      rw [PP_sum_PPX]
      have : ((Finset.range N).filter (fun j => redPresent lam t ω j)).card ≤ B := by
        rw [← Set.ncard_coe_finset]
        apply Set.ncard_le_ncard _ hfin
        intro j hj; simp only [Finset.coe_filter, Set.mem_setOf_eq] at hj; exact hj.2
      exact_mod_cast this
    have hlim : Tendsto (fun N : ℕ => (B : ℝ) / N) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have : lam * t - ⌊lam * t⌋₊ ≤ 0 := by
      apply le_of_tendsto_of_tendsto' hω hlim
      intro N
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp
      · exact div_le_div_of_nonneg_right (hb N) (by positivity)
    linarith

end

end PerimeterPatrol.Visible


open MeasureTheory Filter Topology

namespace PerimeterPatrol.Visible

/-- a measurable set of feasible schedules -/
def PPE (lam : ℝ) : Set (ℕ → ℝ) :=
  (⋂ n : ℕ, {s | s n ≤ s (n + 1)}) ∩ {s | 0 ≤ s 0} ∩ (⋂ m : ℕ, ⋃ n : ℕ, {s | (m : ℝ) < s n}) ∩
    {s | Tendsto (fun m : ℕ => (cnt s m : ℝ) / m) atTop (𝓝 lam)}

lemma PP_measurable_cnt (v : ℝ) : Measurable (fun s : ℕ → ℝ => (cnt s v : ℝ)) :=
  measurable_from_nat.comp (PP_measurable_card (fun (s : ℕ → ℝ) k => s k ≤ v)
      (fun k => measurableSet_le (measurable_pi_apply k) measurable_const))

lemma PP_PPE_meas (lam : ℝ) : MeasurableSet (PPE lam) := by
  unfold PPE
  refine ((MeasurableSet.iInter fun n => measurableSet_le (measurable_pi_apply n)
    (measurable_pi_apply (n + 1))).inter (measurableSet_le measurable_const (measurable_pi_apply 0))
    |>.inter (MeasurableSet.iInter fun m => MeasurableSet.iUnion fun n =>
      measurableSet_lt measurable_const (measurable_pi_apply n))).inter ?_
  exact measurableSet_tendsto (𝓝 lam) fun m => (PP_measurable_cnt (m : ℝ)).div_const _

lemma PP_PPE_feasible (lam : ℝ) (s : ℕ → ℝ) (hs : s ∈ PPE lam) : IsFeasible lam s := by
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_iUnion] at h1 h2 h3 h4
  have hmono : Monotone s := monotone_nat_of_le_succ h1
  refine ⟨hmono, h2, ?_⟩
  have hfin : ∀ v : ℝ, {n : ℕ | s n ≤ v}.Finite := by
    intro v
    obtain ⟨n0, hn0⟩ := h3 ⌈v⌉₊
    apply (Set.finite_Iio n0).subset
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Set.mem_Iio]
    by_contra h; push_neg at h
    have := hmono h
    have := Nat.le_ceil v
    linarith
  have cmono : ∀ {u v : ℝ}, u ≤ v → cnt s u ≤ cnt s v := by
    intro u v huv
    unfold cnt; rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (fun n hn => le_trans hn huv) (hfin v)
  -- squeeze
  have hA : Tendsto (fun m : ℕ => (cnt s m : ℝ) / m * ((m : ℝ) / (m + 1))) atTop (𝓝 (lam * 1)) :=
    h4.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hB0 : Tendsto (fun m : ℕ => (cnt s ((m + 1 : ℕ) : ℝ) : ℝ) / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 lam) :=
    h4.comp (tendsto_add_atTop_nat 1)
  have hB1 : Tendsto (fun m : ℕ => ((m : ℝ) + 1) / m) atTop (𝓝 1) := by
    have : Tendsto (fun m : ℕ => 1 + 1 / (m : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have : (0 : ℝ) < m := by exact_mod_cast hm
    field_simp
  have hB := hB0.mul hB1
  rw [mul_one] at hA hB
  have hfl : Tendsto (fun T : ℝ => ⌊T⌋₊) atTop atTop := tendsto_nat_floor_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hA.comp hfl) (hB.comp hfl)
  · filter_upwards [eventually_ge_atTop 1] with T hT
    simp only [Function.comp]
    rw [show (Nat.card {n : ℕ | s n ≤ T} : ℝ) = cnt s T from rfl]
    have hm1 : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
    have hm : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast hm1
    have hfT : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
    have hTf : T < ⌊T⌋₊ + 1 := Nat.lt_floor_add_one T
    have hc := cmono hfT
    have hc' : (cnt s ⌊T⌋₊ : ℝ) ≤ cnt s T := by exact_mod_cast hc
    have e : (cnt s ⌊T⌋₊ : ℝ) / ⌊T⌋₊ * ((⌊T⌋₊ : ℝ) / (⌊T⌋₊ + 1)) = (cnt s ⌊T⌋₊ : ℝ) / (⌊T⌋₊ + 1) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by linarith)]
    have : (0 : ℝ) ≤ cnt s ⌊T⌋₊ := by positivity
    have : (0 : ℝ) ≤ cnt s T := by positivity
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with T hT
    simp only [Function.comp]
    rw [show (Nat.card {n : ℕ | s n ≤ T} : ℝ) = cnt s T from rfl]
    have hm1 : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
    have hm : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast hm1
    have hfT : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
    have hTf : T < ⌊T⌋₊ + 1 := Nat.lt_floor_add_one T
    have hc := cmono (show T ≤ ((⌊T⌋₊ + 1 : ℕ) : ℝ) by push_cast; linarith)
    have hc' : (cnt s T : ℝ) ≤ cnt s ((⌊T⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    have e : (cnt s ((⌊T⌋₊ + 1 : ℕ) : ℝ) : ℝ) / ((⌊T⌋₊ + 1 : ℕ) : ℝ) * (((⌊T⌋₊ : ℝ) + 1) / ⌊T⌋₊) =
        (cnt s ((⌊T⌋₊ + 1 : ℕ) : ℝ) : ℝ) / ⌊T⌋₊ := by
      push_cast; field_simp
    rw [e, div_le_div_iff₀ (by linarith) hm]
    have : (0 : ℝ) ≤ cnt s T := by positivity
    nlinarith

lemma PP_sched_mem_PPE (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (ω : ℕ → unitInterval)
    (hG : PPGood lam t ω)
    (hω : Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, PPX lam t ω j) / N) atTop
      (𝓝 (lam * t - ⌊lam * t⌋₊))) :
    (fun m => sched lam t ω m) ∈ PPE lam := by
  have hcnt : ∀ v, cnt (fun m => sched lam t ω m) v = count lam t ω v := fun v =>
    PP_card_sched lam t hlam ht ω hG v
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro n; exact PP_sched_mono lam t hlam ht ω hG (Nat.le_succ n)
  · exact PP_sched_nonneg lam t hlam ht ω hG
  · simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
    intro m
    refine ⟨count lam t ω m, ?_⟩
    by_contra h; push_neg at h
    have := (PP_sched_le_iff lam t hlam ht ω _ (hG _) m).mp h
    omega
  · simp only [Set.mem_setOf_eq, hcnt]
    exact (PP_count_rate lam t hlam ht ω hω).comp tendsto_natCast_atTop_atTop

end PerimeterPatrol.Visible

open PerimeterPatrol.Visible in
theorem solution (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) : IsMixedStrategy lam (optimalPatrol lam t) := by
  have hF := PP_measurable_schedMap lam t hlam ht
  refine ⟨Measure.isProbabilityMeasure_map hF.aemeasurable, ?_⟩
  unfold optimalPatrol
  have h : ∀ᵐ s ∂(Measure.map (fun ω : ℕ → unitInterval => fun n => sched lam t ω n)
      (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))), s ∈ PPE lam := by
    refine (ae_map_iff (p := fun s => s ∈ PPE lam) hF.aemeasurable (PP_PPE_meas lam)).mpr ?_
    filter_upwards [PP_good_ae lam t hlam ht] with ω hω
    exact PP_sched_mem_PPE lam t hlam ht ω hω.1 hω.2
  filter_upwards [h] with s hs using PP_PPE_feasible lam s hs
