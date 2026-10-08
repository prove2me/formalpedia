-- Prove2me | solution 1 for SionMinimax.KKM.remark_3_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:58:42.973086+00:00
-- url     : https://prove2.me/submissions/9c24fd6e-2101-42f7-bbb7-8f5e35f5d37c

import Mathlib



namespace SionMinimax.KKM

theorem r36_lsc_pt (p : ℝ) : LowerSemicontinuous (fun ν : ℝ => if ν = p then (0:ℝ) else 1) := by
  intro x y hy
  by_cases hx : x = p
  · subst hx
    simp only [if_true] at hy
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z = x <;> simp [hz] <;> linarith
  · simp only [hx, if_false] at hy
    filter_upwards [eventually_ne_nhds hx] with z hz
    simp [hz]; exact hy

theorem r36_core :
    let f : ℝ → ℝ → ℝ := fun μ ν =>
      if (0 ≤ μ ∧ μ < 1 / 2 ∧ ν = 0) ∨ (1 / 2 ≤ μ ∧ μ ≤ 1 ∧ ν = 1) then 0 else 1
    (∀ ν ∈ Set.Icc (0 : ℝ) 1, QuasiconcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun μ => f μ ν)) ∧
    (∀ μ ∈ Set.Icc (0 : ℝ) 1, QuasiconvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun ν => f μ ν)) ∧
    (∀ μ ∈ Set.Icc (0 : ℝ) 1, LowerSemicontinuousOn (fun ν => f μ ν) (Set.Icc (0 : ℝ) 1)) ∧
    ¬ UpperSemicontinuousOn (fun μ => f μ 1) (Set.Icc (0 : ℝ) 1) ∧
    (⨆ μ : Set.Icc (0 : ℝ) 1, ⨅ ν : Set.Icc (0 : ℝ) 1, ((f μ ν : ℝ) : EReal)) = 0 ∧
    (⨅ ν : Set.Icc (0 : ℝ) 1, ⨆ μ : Set.Icc (0 : ℝ) 1, ((f μ ν : ℝ) : EReal)) = 1 := by
  intro f
  have hf0 : ∀ μ ν, f μ ν = 0 ∨ f μ ν = 1 := by
    intro μ ν; simp only [f]; split_ifs <;> simp
  have hfle : ∀ μ ν, f μ ν ≤ 1 := fun μ ν => by rcases hf0 μ ν with h | h <;> rw [h] <;> norm_num
  have hfge : ∀ μ ν, 0 ≤ f μ ν := fun μ ν => by rcases hf0 μ ν with h | h <;> rw [h] <;> norm_num
  have hA : ∀ μ, 0 ≤ μ → μ ≤ 1 → f μ 0 = if μ < 1/2 then 0 else 1 := by
    intro μ h0 h1
    show (if _ then (0:ℝ) else 1) = _
    by_cases h : μ < 1/2
    · rw [if_pos (Or.inl ⟨h0, h, rfl⟩), if_pos h]
    · have : ¬ (0 ≤ μ ∧ μ < 1 / 2 ∧ (0:ℝ) = 0 ∨ 1 / 2 ≤ μ ∧ μ ≤ 1 ∧ (0:ℝ) = 1) := by
        rintro (⟨_, h', _⟩ | ⟨_, _, h'⟩)
        · exact h h'
        · norm_num at h'
      rw [if_neg this, if_neg h]
  have hB : ∀ μ, 0 ≤ μ → μ ≤ 1 → f μ 1 = if 1/2 ≤ μ then 0 else 1 := by
    intro μ h0 h1
    show (if _ then (0:ℝ) else 1) = _
    by_cases h : 1/2 ≤ μ
    · rw [if_pos (Or.inr ⟨h, h1, rfl⟩), if_pos h]
    · have : ¬ (0 ≤ μ ∧ μ < 1 / 2 ∧ (1:ℝ) = 0 ∨ 1 / 2 ≤ μ ∧ μ ≤ 1 ∧ (1:ℝ) = 1) := by
        rintro (⟨_, _, h'⟩ | ⟨h', _, _⟩)
        · norm_num at h'
        · exact h h'
      rw [if_neg this, if_neg h]
  have hC : ∀ μ ν, ν ≠ 0 → ν ≠ 1 → f μ ν = 1 := by
    intro μ ν h0 h1
    simp [f, h0, h1]
  have hD : ∀ μ, 0 ≤ μ → μ < 1/2 → ∀ ν, f μ ν = if ν = 0 then 0 else 1 := by
    intro μ h0 h1 ν
    show (if _ then (0:ℝ) else 1) = _
    by_cases h : ν = 0
    · rw [if_pos (Or.inl ⟨h0, h1, h⟩), if_pos h]
    · have : ¬ (0 ≤ μ ∧ μ < 1 / 2 ∧ ν = 0 ∨ 1 / 2 ≤ μ ∧ μ ≤ 1 ∧ ν = 1) := by
        rintro (⟨_, _, h'⟩ | ⟨h', _, _⟩)
        · exact h h'
        · linarith
      rw [if_neg this, if_neg h]
  have hE : ∀ μ, 1/2 ≤ μ → μ ≤ 1 → ∀ ν, f μ ν = if ν = 1 then 0 else 1 := by
    intro μ h0 h1 ν
    show (if _ then (0:ℝ) else 1) = _
    by_cases h : ν = 1
    · rw [if_pos (Or.inr ⟨h0, h1, h⟩), if_pos h]
    · have : ¬ (0 ≤ μ ∧ μ < 1 / 2 ∧ ν = 0 ∨ 1 / 2 ≤ μ ∧ μ ≤ 1 ∧ ν = 1) := by
        rintro (⟨_, h', _⟩ | ⟨_, _, h'⟩)
        · linarith
        · exact h h'
      rw [if_neg this, if_neg h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ν hν
    rw [quasiconcaveOn_iff_min_le]
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    simp only [smul_eq_mul]
    rcases hx with ⟨hx0, hx1⟩
    rcases hy with ⟨hy0, hy1⟩
    have hz0 : 0 ≤ a * x + (1 - a) * y := by nlinarith
    have hz1 : a * x + (1 - a) * y ≤ 1 := by nlinarith
    by_cases h0 : ν = 0
    · subst h0
      rw [hA x hx0 hx1, hA y hy0 hy1, hA _ hz0 hz1]
      split_ifs <;> first | (simp; done) | (exfalso; nlinarith)
    · by_cases h1 : ν = 1
      · subst h1
        rw [hB x hx0 hx1, hB y hy0 hy1, hB _ hz0 hz1]
        split_ifs <;> first | (simp; done) | (exfalso; rcases ha.eq_or_lt with h | h <;> nlinarith [mul_nonneg ha hb])
      · rw [hC _ _ h0 h1, hC _ _ h0 h1, hC _ _ h0 h1]; simp
  · intro μ hμ
    rw [quasiconvexOn_iff_le_max]
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    simp only [smul_eq_mul]
    rcases hμ with ⟨hm0, hm1⟩
    rcases lt_or_ge μ (1/2) with h | h
    · rw [hD μ hm0 h, hD μ hm0 h, hD μ hm0 h]
      by_cases hx0 : x = 0
      · by_cases hy0 : y = 0
        · subst hx0; subst hy0; simp
        · simp [hy0]; split_ifs <;> simp
      · simp [hx0]; split_ifs <;> simp
    · rw [hE μ h hm1, hE μ h hm1, hE μ h hm1]
      by_cases hx0 : x = 1
      · by_cases hy0 : y = 1
        · subst hx0; subst hy0; simp
        · simp [hy0]; split_ifs <;> simp
      · simp [hx0]; split_ifs <;> simp
  · intro μ hμ
    rcases hμ with ⟨hm0, hm1⟩
    rcases lt_or_ge μ (1/2) with h | h
    · have : (fun ν => f μ ν) = fun ν : ℝ => if ν = 0 then (0:ℝ) else 1 := funext (hD μ hm0 h)
      rw [this]; exact (r36_lsc_pt 0).lowerSemicontinuousOn _
    · have : (fun ν => f μ ν) = fun ν : ℝ => if ν = 1 then (0:ℝ) else 1 := funext (hE μ h hm1)
      rw [this]; exact (r36_lsc_pt 1).lowerSemicontinuousOn _
  · intro hu
    have h1 := hu (1/2) ⟨by norm_num, by norm_num⟩ (1/2) (by show f (1/2) 1 < 1/2; rw [hB _ (by norm_num) (by norm_num)]; norm_num)
    have h2 := h1.filter_mono (nhdsWithin_mono (1/2 : ℝ) (Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl (by norm_num : (1/2:ℝ) ≤ 1)) |>.trans (Set.Icc_subset_Icc le_rfl (by norm_num)) : Set.Ico (0:ℝ) (1/2) ⊆ Set.Icc 0 1))
    rw [nhdsWithin_Ico_eq_nhdsLT (by norm_num)] at h2
    obtain ⟨x', hx', hx''⟩ := (h2.and (Ioo_mem_nhdsLT (show (0:ℝ) < 1/2 by norm_num))).exists
    have hx' : f x' 1 < 1/2 := hx'
    rw [hB x' hx''.1.le (by linarith [hx''.2])] at hx'
    have : ¬ (1/2 ≤ x') := by linarith [hx''.2]
    rw [if_neg this] at hx'
    norm_num at hx'
  · have hinner : ∀ μ : Set.Icc (0:ℝ) 1, (⨅ ν : Set.Icc (0 : ℝ) 1, ((f μ ν : ℝ) : EReal)) = 0 := by
      intro μ
      apply le_antisymm
      · rcases lt_or_ge (μ:ℝ) (1/2) with h | h
        · refine (iInf_le _ ⟨0, by norm_num, by norm_num⟩).trans ?_
          rw [hD μ μ.2.1 h]; simp
        · refine (iInf_le _ ⟨1, by norm_num, by norm_num⟩).trans ?_
          rw [hE μ h μ.2.2]; simp
      · refine le_iInf fun ν => ?_
        exact_mod_cast hfge _ _
    simp only [hinner]
    simp
  · have hinner : ∀ ν : Set.Icc (0:ℝ) 1, (⨆ μ : Set.Icc (0 : ℝ) 1, ((f μ ν : ℝ) : EReal)) = 1 := by
      intro ν
      apply le_antisymm
      · refine iSup_le fun μ => ?_
        exact_mod_cast hfle _ _
      · by_cases h0 : (ν:ℝ) = 0
        · refine le_iSup_of_le ⟨1, by norm_num, by norm_num⟩ ?_
          have : f 1 ν = 1 := by
            rw [hE 1 (by norm_num) le_rfl]; simp [h0]
          rw [this]; simp
        · refine le_iSup_of_le ⟨0, by norm_num, by norm_num⟩ ?_
          have : f 0 ν = 1 := by
            rw [hD 0 le_rfl (by norm_num)]; simp [h0]
          rw [this]; simp
    simp only [hinner]
    simp

end SionMinimax.KKM

open SionMinimax.KKM


theorem solution :
    let f : ℝ → ℝ → ℝ := fun μ ν =>
      if (0 ≤ μ ∧ μ < 1 / 2 ∧ ν = 0) ∨ (1 / 2 ≤ μ ∧ μ ≤ 1 ∧ ν = 1) then 0 else 1
    (∀ ν ∈ Set.Icc (0 : ℝ) 1, QuasiconcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun μ => f μ ν)) ∧
    (∀ μ ∈ Set.Icc (0 : ℝ) 1, QuasiconvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun ν => f μ ν)) ∧
    (∀ μ ∈ Set.Icc (0 : ℝ) 1, LowerSemicontinuousOn (fun ν => f μ ν) (Set.Icc (0 : ℝ) 1)) ∧
    ¬ UpperSemicontinuousOn (fun μ => f μ 1) (Set.Icc (0 : ℝ) 1) ∧
    (⨆ μ : Set.Icc (0 : ℝ) 1, ⨅ ν : Set.Icc (0 : ℝ) 1, ((f μ ν : ℝ) : EReal)) = 0 ∧
    (⨅ ν : Set.Icc (0 : ℝ) 1, ⨆ μ : Set.Icc (0 : ℝ) 1, ((f μ ν : ℝ) : EReal)) = 1 := by
  exact r36_core
