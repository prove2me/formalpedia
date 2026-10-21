-- Prove2me | solution 1 for PerimeterPatrol.Visible.converse
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:54:47.068051+00:00
-- url     : https://prove2.me/submissions/199a8b3d-7f1a-40ac-9ab0-80e2a2f5b1e9

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


open MeasureTheory Filter Topology

open PerimeterPatrol.Visible in
theorem solution (lam t p : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hp0 : 0 < p) (hp1 : p ≤ 1) (μ : Measure (ℕ → ℝ)) (hμ : IsMixedStrategy lam μ) (ε : ℝ) (hε : 0 < ε) : ∃ y : ℝ, 0 < y ∧ detectionProb p t μ (fun _ => y) < patrolValue lam t p + ε := by
  obtain ⟨hprob, hfeas⟩ := hμ
  set q := 1 - p with hq
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  have hq1 : q ≤ 1 := by rw [hq]; linarith
  set n := ⌊lam * t⌋₊ with hn
  set V := patrolValue lam t p with hVdef
  have hV : V = PPL q n (lam * t) := PP_valueC_eq p _ (by positivity)
  have hV0 : 0 ≤ V := PP_valueC_nonneg p _ hp0.le hp1 (by positivity)
  have hV1 : V ≤ 1 := PP_valueC_le_one p _ hp0.le hp1 (by positivity)
  let N : ℕ → (ℕ → ℝ) → ℕ := fun i s => arrivals s (1 + i * t) (1 + i * t + t)
  let g : ℕ → (ℕ → ℝ) → ℝ := fun i s => 1 - q ^ N i s
  let c : ℕ → (ℕ → ℝ) → ℝ := fun M s => ((cnt s (1 + M * t) : ℝ) - cnt s 1) / M
  let h : ℕ → (ℕ → ℝ) → ℝ := fun M s => max 0 (min 1 (PPL q n (c M s)))
  -- measurability
  have mcnt : ∀ v, Measurable (fun s : ℕ → ℝ => (cnt s v : ℝ)) := fun v =>
    measurable_from_nat.comp (PP_measurable_card (fun (s : ℕ → ℝ) k => s k ≤ v)
      (fun k => measurableSet_le (measurable_pi_apply k) measurable_const))
  have mN : ∀ i, Measurable (N i) := fun i =>
    PP_measurable_card (fun (s : ℕ → ℝ) k => 1 + i * t < s k ∧ s k ≤ 1 + i * t + t)
      (fun k => (measurableSet_lt measurable_const (measurable_pi_apply k)).inter
        (measurableSet_le (measurable_pi_apply k) measurable_const))
  have mg : ∀ i, Measurable (g i) := fun i =>
    (measurable_from_nat (f := fun k : ℕ => 1 - q ^ k)).comp (mN i)
  have mc : ∀ M, Measurable (c M) := fun M => ((mcnt _).sub (mcnt _)).div_const _
  have mPPL : Continuous (fun x => max 0 (min 1 (PPL q n x))) := by
    unfold PPL; fun_prop
  have mh : ∀ M, Measurable (h M) := fun M => mPPL.measurable.comp (mc M)
  have gb : ∀ i s, 0 ≤ g i s ∧ g i s ≤ 1 := by
    intro i s
    have a1 : q ^ N i s ≤ 1 := pow_le_one₀ hq0 hq1
    have a2 : 0 ≤ q ^ N i s := pow_nonneg hq0 _
    exact ⟨by simp only [g]; linarith, by simp only [g]; linarith⟩
  have gint : ∀ i, Integrable (g i) μ := fun i =>
    Integrable.of_bound (mg i).aestronglyMeasurable 1
      (Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [gb i s])
  have hint : ∀ M, Integrable (h M) μ := fun M =>
    Integrable.of_bound (mh M).aestronglyMeasurable 1
      (Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_le]; simp only [h]
        constructor
        · linarith [le_max_left 0 (min 1 (PPL q n (c M s)))]
        · exact max_le (by norm_num) (min_le_left _ _))
  -- pathwise bound
  have path : ∀ s, IsFeasible lam s → ∀ M : ℕ, 1 ≤ M →
      (∑ i ∈ Finset.range M, g i s) / M ≤ h M s := by
    intro s hs M hM
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hsumN : ∑ i ∈ Finset.range M, (N i s : ℝ) = (cnt s (1 + M * t) : ℝ) - cnt s 1 := by
      have : ∀ i ∈ Finset.range M, (N i s : ℝ) =
          (cnt s (1 + ((i + 1 : ℕ) : ℝ) * t) : ℝ) - cnt s (1 + (i : ℝ) * t) := by
        intro i _
        simp only [N]
        rw [PP_arrivals_eq lam hlam s hs _ _ (by linarith)]
        push_cast; ring_nf
      rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun i => (cnt s (1 + (i : ℝ) * t) : ℝ))]
      simp
    set B := q ^ n - q ^ (n + 1)
    have hlin : ∀ x, PPL q n x = (1 - q ^ n - n * B) + x * B := by
      intro x; unfold PPL; ring
    have h1 : ∑ i ∈ Finset.range M, g i s ≤ M * PPL q n (c M s) := by
      calc ∑ i ∈ Finset.range M, g i s ≤ ∑ i ∈ Finset.range M, PPL q n (N i s) :=
            Finset.sum_le_sum fun i _ => PP_conc q hq0 hq1 _ n
        _ = M * PPL q n (c M s) := by
            simp only [hlin, Finset.sum_add_distrib, ← Finset.sum_mul, hsumN]
            simp only [c, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            field_simp
    have h2 : ∑ i ∈ Finset.range M, g i s ≤ M := by
      calc ∑ i ∈ Finset.range M, g i s ≤ ∑ i ∈ Finset.range M, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => (gb i s).2
        _ = M := by simp
    have h3 : 0 ≤ ∑ i ∈ Finset.range M, g i s := Finset.sum_nonneg fun i _ => (gb i s).1
    simp only [h]
    apply le_max_of_le_right
    apply le_min
    · rw [div_le_one hMpos]; exact h2
    · rw [div_le_iff₀ hMpos]; linarith
  -- pathwise limit
  have lim : ∀ s, IsFeasible lam s → Tendsto (fun M : ℕ => h M s) atTop (𝓝 V) := by
    intro s hs
    have hT : Tendsto (fun T : ℝ => (cnt s T : ℝ) / T) atTop (𝓝 lam) := hs.2.2
    have hu : Tendsto (fun M : ℕ => 1 + (M : ℝ) * t) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const ht)
    have h1 := hT.comp hu
    have h2 : Tendsto (fun M : ℕ => (1 : ℝ) / M + t) atTop (𝓝 (0 + t)) :=
      tendsto_one_div_atTop_nhds_zero_nat.add tendsto_const_nhds
    have h3 : Tendsto (fun M : ℕ => (cnt s 1 : ℝ) / M) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h4 := (h1.mul h2).sub h3
    simp only [zero_add, sub_zero] at h4
    have hc : Tendsto (fun M => c M s) atTop (𝓝 (lam * t)) := by
      refine h4.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with M hM
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
      have hu : (0 : ℝ) < 1 + M * t := by positivity
      simp only [Function.comp, c]
      field_simp
    have := (mPPL.tendsto (lam * t)).comp hc
    simp only [← hV] at this
    rw [show max 0 (min 1 V) = V by rw [min_eq_right hV1, max_eq_right hV0]] at this
    exact this
  -- dominated convergence
  have dct : Tendsto (fun M => ∫ s, h M s ∂μ) atTop (𝓝 (∫ _ : ℕ → ℝ, V ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun M => (mh M).aestronglyMeasurable) (integrable_const 1)
      (fun M => Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_le]; simp only [h]
        constructor
        · linarith [le_max_left 0 (min 1 (PPL q n (c M s)))]
        · exact max_le (by norm_num) (min_le_left _ _))
      (by filter_upwards [hfeas] with s hs using lim s hs)
  simp only [integral_const, probReal_univ, one_smul] at dct
  obtain ⟨M, hM, hM1⟩ := ((dct.eventually (gt_mem_nhds (by linarith : V < V + ε))).and
    (eventually_ge_atTop 1)).exists
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have havg : (∑ i ∈ Finset.range M, ∫ s, g i s ∂μ) / M < V + ε := by
    have e : (∑ i ∈ Finset.range M, ∫ s, g i s ∂μ) / M =
        ∫ s, (∑ i ∈ Finset.range M, g i s) / M ∂μ := by
      rw [integral_div, integral_finset_sum _ fun i _ => gint i]
    rw [e]
    refine lt_of_le_of_lt (integral_mono_ae ?_ (hint M) ?_) hM
    · exact (integrable_finset_sum _ fun i _ => gint i).div_const _
    · filter_upwards [hfeas] with s hs using path s hs M hM1
  by_contra hcon
  push_neg at hcon
  have : ∀ i ∈ Finset.range M, V + ε ≤ ∫ s, g i s ∂μ := by
    intro i _
    have := hcon (1 + i * t) (by positivity)
    exact this
  have hs := Finset.card_nsmul_le_sum (Finset.range M) (fun i => ∫ s, g i s ∂μ) (V + ε) this
  simp only [Finset.card_range, nsmul_eq_mul] at hs
  rw [div_lt_iff₀ hMpos] at havg
  linarith
