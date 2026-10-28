-- Prove2me | solution 1 for ScheduledQueue.Diffusion.op_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T18:21:49.96399+00:00
-- url     : https://prove2.me/submissions/3d21b0f2-9d46-4aeb-bc1a-97c5ba50b0c1

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting
import Theorems.Thm_ScheduledQueue_Diffusion_count_decomposition
import Theorems.Thm_ScheduledQueue_Diffusion_proposition_1

open Set Filter Topology MeasureTheory ProbabilityTheory

lemma SQO_sum_le (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ i ∈ Finset.Icc 1 a, f i ≤ ∑ i ∈ Finset.Icc 1 b, |f i| :=
  calc ∑ i ∈ Finset.Icc 1 a, f i ≤ ∑ i ∈ Finset.Icc 1 a, |f i| :=
        Finset.sum_le_sum (fun i _ => le_abs_self _)
    _ ≤ ∑ i ∈ Finset.Icc 1 b, |f i| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hab)
          (fun i _ _ => abs_nonneg _)

/-- pathwise comparison of the two suprema -/
lemma SQO_path (h : ℝ) (hh : 0 < h) (N : ℝ → ℕ) (V : ℕ → ℝ)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → N a ≤ N b) (t : ℝ) (ht : 1 ≤ t) (n : ℕ)
    (hn : t ≤ n) :
    |(⨆ s : Icc 0 t, ((∑ i ∈ Finset.Icc 1 (N s), V i) - s)) -
        ⨆ s : Icc (0 : ℝ) 1, ∑ i ∈ Finset.Icc 1 (N (s * t)), (V i - h)| ≤
      ⨆ v : Icc (0 : ℝ) 1, |h * (N ((n : ℝ) * v) : ℝ) - (n : ℝ) * v| := by
  have hnpos : (0 : ℝ) < n := by linarith
  set F : ℝ → ℝ := fun s => (∑ i ∈ Finset.Icc 1 (N s), V i) - s with hF
  set A : ℝ → ℝ := fun u => ∑ i ∈ Finset.Icc 1 (N (u * t)), (V i - h) with hA
  set R := ⨆ v : Icc (0 : ℝ) 1, |h * (N ((n : ℝ) * v) : ℝ) - (n : ℝ) * v| with hR
  have hRbdd : BddAbove (Set.range fun v : Icc (0 : ℝ) 1 =>
      |h * (N ((n : ℝ) * v) : ℝ) - (n : ℝ) * v|) := by
    refine ⟨h * N n + n, ?_⟩
    rintro _ ⟨⟨v, hv0, hv1⟩, rfl⟩
    have hnv : (n : ℝ) * v ≤ n := by nlinarith
    have hNv : N ((n : ℝ) * v) ≤ N n := hmono _ _ (by positivity) hnv
    have hNvR : (N ((n : ℝ) * v) : ℝ) ≤ N n := by exact_mod_cast hNv
    have h0 : (0 : ℝ) ≤ (N ((n : ℝ) * v) : ℝ) := Nat.cast_nonneg _
    rw [abs_le]; constructor <;> nlinarith
  have hkey : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |F (u * t) - A u| ≤ R := by
    intro u hu0 hu1
    have e : F (u * t) - A u = h * (N (u * t) : ℝ) - u * t := by
      simp only [hF, hA, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      push_cast; ring
    rw [e]
    have hv0 : 0 ≤ u * t / n := by positivity
    have hv1 : u * t / n ≤ 1 := by
      rw [div_le_one hnpos]; nlinarith
    have e2 : (n : ℝ) * (u * t / n) = u * t := by field_simp
    have := le_ciSup hRbdd ⟨u * t / n, hv0, hv1⟩
    simp only [e2] at this
    exact this
  have hFbdd : BddAbove (Set.range fun s : Icc 0 t => F s) := by
    refine ⟨∑ i ∈ Finset.Icc 1 (N t), |V i|, ?_⟩
    rintro _ ⟨⟨s, hs0, hs1⟩, rfl⟩
    simp only [hF]
    have := SQO_sum_le V (N s) (N t) (hmono s t hs0 hs1)
    linarith
  have hAbdd : BddAbove (Set.range fun u : Icc (0 : ℝ) 1 => A u) := by
    refine ⟨∑ i ∈ Finset.Icc 1 (N t), |V i - h|, ?_⟩
    rintro _ ⟨⟨u, hu0, hu1⟩, rfl⟩
    simp only [hA]
    exact SQO_sum_le (fun i => V i - h) _ _ (hmono _ _ (by positivity) (by nlinarith))
  have hne1 : Nonempty (Icc (0 : ℝ) t) := ⟨⟨0, by simp; linarith⟩⟩
  have hne2 : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, by simp⟩⟩
  have i1 : (⨆ s : Icc 0 t, F s) ≤ (⨆ u : Icc (0 : ℝ) 1, A u) + R := by
    refine ciSup_le (fun ⟨s, hs0, hs1⟩ => ?_)
    have hu0 : 0 ≤ s / t := by positivity
    have hu1 : s / t ≤ 1 := by rw [div_le_one (by linarith)]; exact hs1
    have e : s / t * t = s := by field_simp
    have h1 := hkey (s / t) hu0 hu1
    rw [e] at h1
    have h2 : A (s / t) ≤ ⨆ u : Icc (0 : ℝ) 1, A u := le_ciSup hAbdd ⟨s / t, hu0, hu1⟩
    have := (abs_le.mp h1).2
    show F s ≤ _
    linarith
  have i2 : (⨆ u : Icc (0 : ℝ) 1, A u) ≤ (⨆ s : Icc 0 t, F s) + R := by
    refine ciSup_le (fun ⟨u, hu0, hu1⟩ => ?_)
    have h1 := hkey u hu0 hu1
    have h2 : F (u * t) ≤ ⨆ s : Icc 0 t, F s :=
      le_ciSup hFbdd ⟨u * t, by positivity, by nlinarith⟩
    have := (abs_le.mp h1).1
    show A u ≤ _
    linarith
  show |(⨆ s : Icc 0 t, F s) - ⨆ u : Icc (0 : ℝ) 1, A u| ≤ R
  rw [abs_le]; constructor <;> linarith

open ScheduledQueue.Diffusion in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U)
    (V : ℕ → Ω → ℝ) (hV : ServiceInput P ξ U V) (hmean : ∫ ω, V 1 ω ∂P = h) :
    TendstoInMeasure P
      (fun (t : ℝ) ω =>
        (Real.sqrt t)⁻¹ * (⨆ s : Icc 0 t, ((∑ i ∈ Finset.Icc 1 (ScheduledQueue.Stability.count h ξ U s ω), V i ω) - s))
          - (Real.sqrt t)⁻¹ *
            ⨆ s : Icc (0 : ℝ) 1, ∑ i ∈ Finset.Icc 1 (ScheduledQueue.Stability.count h ξ U (s * t) ω), (V i ω - h))
      atTop (fun _ => 0) := by
  have hP1 := proposition_1 P h hh ξ U hin
  have hX := hP1.comp (tendsto_nat_ceil_atTop (α := ℝ))
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  -- the good event: all counts finite
  have hfin : ∀ᵐ ω ∂P, ∀ k : ℕ,
      {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc 0 ((k : ℝ) * h)}.Finite :=
    ae_all_iff.2 (fun k => (count_decomposition P h hh ξ U hin ((k : ℝ) * h) (by positivity)).mono
      (fun ω hω => hω.2.2.2.2.1))
  obtain ⟨G, hG, hGm⟩ : ∃ G : Set Ω, P Gᶜ = 0 ∧ ∀ ω ∈ G, ∀ k : ℕ,
      {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc 0 ((k : ℝ) * h)}.Finite := by
    refine ⟨_, ?_, fun ω hω => hω⟩
    rw [ae_iff] at hfin
    exact hfin
  have hmono : ∀ ω ∈ G, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ScheduledQueue.Stability.count h ξ U a ω ≤ ScheduledQueue.Stability.count h ξ U b ω := by
    intro ω hω a b ha hab
    set k := ⌈b / h⌉₊
    have hbk : b ≤ (k : ℝ) * h := by
      have := Nat.le_ceil (b / h)
      rwa [div_le_iff₀ hh] at this
    have hfb : {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc 0 b}.Finite := by
      refine (hGm ω hω k).subset (fun j hj => ?_)
      simp only [mem_setOf_eq, mem_Ioc] at hj ⊢
      exact ⟨hj.1, by linarith [hj.2]⟩
    refine Set.ncard_le_ncard (fun j hj => ?_) hfb
    simp only [mem_setOf_eq, mem_Ioc] at hj ⊢
    exact ⟨hj.1, by linarith [hj.2]⟩
  intro ε hε
  have hlim := hX (ε / 3) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun t => bot_le)) ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
  set n : ℕ := ⌈t⌉₊ with hn
  have htn : t ≤ n := Nat.le_ceil t
  have hnt : (n : ℝ) < t + 1 := Nat.ceil_lt_add_one (by linarith)
  have hn2 : (2 : ℝ) ≤ n := le_trans ht htn
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
  -- `log n ≤ 3 √t`
  have hlogle : Real.log n ≤ 3 * Real.sqrt t := by
    have h1 : Real.log n = 2 * Real.log (Real.sqrt n) := by
      rw [Real.log_sqrt (by linarith)]; ring
    have h2 : Real.log (Real.sqrt n) ≤ Real.sqrt n - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
    have h3 : Real.sqrt n ≤ Real.sqrt (2 * t) := Real.sqrt_le_sqrt (by linarith)
    have h4 : Real.sqrt (2 * t) = Real.sqrt 2 * Real.sqrt t := Real.sqrt_mul (by norm_num) t
    have h5 : Real.sqrt 2 < 1.5 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg n]
  have hsub : {ω | ε ≤ dist ((Real.sqrt t)⁻¹ *
        (⨆ s : Icc 0 t, ((∑ i ∈ Finset.Icc 1 (ScheduledQueue.Stability.count h ξ U s ω), V i ω) - s))
          - (Real.sqrt t)⁻¹ * ⨆ s : Icc (0 : ℝ) 1,
            ∑ i ∈ Finset.Icc 1 (ScheduledQueue.Stability.count h ξ U (s * t) ω), (V i ω - h)) 0} ⊆
      Gᶜ ∪ {ω | ε / 3 ≤ dist (((fun (n : ℕ) ω => (Real.log n)⁻¹ *
        ⨆ s : Icc (0 : ℝ) 1, |h * (ScheduledQueue.Stability.count h ξ U ((n : ℝ) * s) ω : ℝ) -
          (n : ℝ) * s|) ∘ fun t : ℝ => ⌈t⌉₊) t ω) 0} := by
    intro ω hω
    by_cases hωG : ω ∈ G
    · right
      simp only [mem_setOf_eq, Real.dist_eq, sub_zero, Function.comp_apply] at hω ⊢
      have hpath := SQO_path h hh (fun s => ScheduledQueue.Stability.count h ξ U s ω)
        (fun i => V i ω) (hmono ω hωG) t (by linarith) n htn
      set R := ⨆ v : Icc (0 : ℝ) 1,
        |h * (ScheduledQueue.Stability.count h ξ U ((n : ℝ) * v) ω : ℝ) - (n : ℝ) * v| with hR
      have hR0 : 0 ≤ R := Real.iSup_nonneg (fun v => abs_nonneg _)
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hsqrt)] at hω
      have hX0 : (Real.log n)⁻¹ * R = |(Real.log n)⁻¹ * R| := by
        rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hlogn.le) hR0)]
      rw [← hX0]
      have hb : (Real.sqrt t)⁻¹ * R ≤ 3 * ((Real.log n)⁻¹ * R) := by
        have hY := mul_nonneg (inv_nonneg.mpr hlogn.le) hR0
        calc (Real.sqrt t)⁻¹ * R = ((Real.sqrt t)⁻¹ * Real.log n) * ((Real.log n)⁻¹ * R) := by
              field_simp
          _ ≤ 3 * ((Real.log n)⁻¹ * R) :=
              mul_le_mul_of_nonneg_right (by rw [inv_mul_le_iff₀ hsqrt]; linarith) hY
      have hc : (Real.sqrt t)⁻¹ * |(⨆ s : Icc 0 t, ((∑ i ∈ Finset.Icc 1
          (ScheduledQueue.Stability.count h ξ U s ω), V i ω) - s)) - ⨆ s : Icc (0 : ℝ) 1,
            ∑ i ∈ Finset.Icc 1 (ScheduledQueue.Stability.count h ξ U (s * t) ω), (V i ω - h)| ≤
          (Real.sqrt t)⁻¹ * R := mul_le_mul_of_nonneg_left hpath (inv_nonneg.mpr hsqrt.le)
      linarith
    · left; exact hωG
  calc _ ≤ P (Gᶜ ∪ _) := measure_mono hsub
    _ ≤ P Gᶜ + _ := measure_union_le _ _
    _ = _ := by rw [hG, zero_add]
