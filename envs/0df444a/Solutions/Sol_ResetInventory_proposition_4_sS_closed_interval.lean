-- Prove2me | solution 1 for ResetInventory.proposition_4_sS_closed_interval
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T09:27:18.772971+00:00
-- url     : https://prove2.me/submissions/b59bec9f-0374-45ad-af9a-99a18aa8a425

import Mathlib

open Set Filter
open scoped Topology

theorem solution (cmax K : ℝ) (G : ℝ → ℝ)
    (hcmax : 0 ≤ cmax) (hK : 0 ≤ K)
    (hcont : ContinuousOn G (Set.Icc 0 cmax)) (hconv : ConvexOn ℝ (Set.Icc 0 cmax) G) :
    ∃ S ∈ Set.Icc 0 cmax, (∀ z ∈ Set.Icc 0 cmax, G S ≤ G z) ∧
      ({z : ℝ | z ∈ Set.Icc 0 S ∧ G S + K = G z}.Nonempty →
        ∀ s : ℝ, s = sInf {z : ℝ | z ∈ Set.Icc 0 S ∧ G S + K = G z} →
          G S + K = G s ∧
          AntitoneOn G (Set.Icc 0 s) ∧
          (∀ z ∈ Set.Icc 0 s, G S + K ≤ G z) ∧
          (∀ y z : ℝ, s ≤ y → y ≤ z → z ≤ cmax → G y ≤ G z + K)) := by
  classical
  obtain ⟨S, hS_mem, hS_min⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hcmax) hcont
  have hSle : ∀ z ∈ Set.Icc 0 cmax, G S ≤ G z := fun z hz => hS_min hz
  refine ⟨S, hS_mem, hSle, ?_⟩
  intro hLne s hs
  set Lset : Set ℝ := {z : ℝ | z ∈ Set.Icc 0 S ∧ G S + K = G z} with hLdef
  have hLsub : Lset ⊆ Set.Icc 0 cmax := by
    intro z hz
    exact ⟨hz.1.1, le_trans hz.1.2 hS_mem.2⟩
  have hbdd : BddBelow Lset := ⟨0, fun z hz => hz.1.1⟩
  have hsdef : s = sInf Lset := hs
  have hs0 : 0 ≤ s := by
    rw [hsdef]
    exact le_csInf hLne (fun z hz => hz.1.1)
  have hsS : s ≤ S := by
    rw [hsdef]
    obtain ⟨z, hz⟩ := hLne
    exact le_trans (csInf_le hbdd hz) hz.1.2
  have hnb : (𝓝[Lset] s).NeBot := by
    rw [nhdsWithin_neBot]
    intro t ht
    rw [Metric.mem_nhds_iff] at ht
    obtain ⟨ε, hε, hball⟩ := ht
    have h1 : sInf Lset < s + ε := by rw [← hsdef]; linarith
    obtain ⟨z, hzL, hzlt⟩ := exists_lt_of_csInf_lt hLne h1
    refine ⟨z, hball ?_, hzL⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · have h2 := csInf_le hbdd hzL
      rw [← hsdef] at h2
      linarith
    · linarith
  have hs_cl : s ∈ closure Lset := by
    rw [mem_closure_iff]
    intro o ho hso
    exact nhdsWithin_neBot.mp hnb (ho.mem_nhds hso)
  have hsI : s ∈ Set.Icc 0 cmax := by
    have h1 : closure Lset ⊆ closure (Set.Icc 0 cmax) := closure_mono hLsub
    have h2 : closure (Set.Icc 0 cmax) = Set.Icc 0 cmax := isClosed_Icc.closure_eq
    exact h2 ▸ h1 hs_cl
  have hval : G s = G S + K := by
    haveI : (𝓝[Lset] s).NeBot := hnb
    have hcwa : ContinuousWithinAt G Lset s :=
      (hcont.continuousWithinAt hsI).mono hLsub
    have heq : G =ᶠ[𝓝[Lset] s] (fun _ => G S + K) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hz.2.symm
    have h1 : Tendsto G (𝓝[Lset] s) (𝓝 (G S + K)) :=
      Filter.Tendsto.congr' heq.symm tendsto_const_nhds
    have h2 : Tendsto G (𝓝[Lset] s) (𝓝 (G s)) := hcwa
    exact tendsto_nhds_unique h2 h1
  have hanti : AntitoneOn G (Set.Icc 0 s) := by
    intro y hy z hz hyz
    have hyI : y ∈ Set.Icc 0 cmax := ⟨hy.1, le_trans hy.2 (le_trans hsS hS_mem.2)⟩
    have hzS : z ∈ Set.Icc y S := ⟨hyz, le_trans hz.2 hsS⟩
    have hmax := hconv.le_max_of_mem_Icc hyI hS_mem hzS
    have h1 : G S ≤ G y := hSle y hyI
    have h2 : max (G y) (G S) = G y := max_eq_left h1
    rwa [h2] at hmax
  have hprop3 : ∀ z ∈ Set.Icc 0 s, G S + K ≤ G z := by
    intro z hz
    rcases eq_or_lt_of_le hz.2 with hzs | hzs
    · rw [hzs]
      exact hval.ge
    · have hzS : z ∈ Set.Icc 0 S := ⟨hz.1, le_trans hz.2 hsS⟩
      have hzI : z ∈ Set.Icc 0 cmax := ⟨hz.1, le_trans hz.2 (le_trans hsS hS_mem.2)⟩
      have hGSz : G S ≤ G z := hSle z hzI
      have hden : 0 < S - z := by linarith
      set a : ℝ := (S - s) / (S - z) with ha
      set b : ℝ := (s - z) / (S - z) with hb
      have ha0 : 0 ≤ a := by
        rw [ha]
        positivity
      have hb0 : 0 ≤ b := by
        rw [hb]
        positivity
      have hab : a + b = 1 := by
        rw [ha, hb]
        field_simp
        ring
      have hpt : a • z + b • S = s := by
        rw [ha, hb]
        simp only [smul_eq_mul]
        field_simp
        ring
      have hkey := hconv.2 hzI hS_mem ha0 hb0 hab
      rw [hpt] at hkey
      rw [hval] at hkey
      simp only [smul_eq_mul] at hkey
      have ha1 : a ≤ 1 := by
        rw [ha, div_le_one hden]
        linarith
      have hb' : b = 1 - a := by linarith
      have hKle : K ≤ a * (G z - G S) := by
        rw [hb'] at hkey
        nlinarith [hkey]
      have hnn : 0 ≤ G z - G S := by linarith
      have hstep : a * (G z - G S) ≤ 1 * (G z - G S) :=
        mul_le_mul_of_nonneg_right ha1 hnn
      linarith
  have hprop4 : ∀ y z : ℝ, s ≤ y → y ≤ z → z ≤ cmax → G y ≤ G z + K := by
    intro y z hsy hyz hzcmax
    have hz0 : 0 ≤ z := le_trans hs0 (le_trans hsy hyz)
    have hzI : z ∈ Set.Icc 0 cmax := ⟨hz0, hzcmax⟩
    have hyI : y ∈ Set.Icc 0 cmax := ⟨le_trans hs0 hsy, le_trans hyz hzcmax⟩
    have hmax := hconv.le_max_of_mem_Icc hsI hzI (show y ∈ Set.Icc s z from ⟨hsy, hyz⟩)
    have h1 : G s ≤ G z + K := by
      rw [hval]
      linarith [hSle z hzI]
    have h2 : G z ≤ G z + K := by linarith
    exact le_trans hmax (max_le h1 h2)
  exact ⟨hval.symm, hanti, hprop3, hprop4⟩
