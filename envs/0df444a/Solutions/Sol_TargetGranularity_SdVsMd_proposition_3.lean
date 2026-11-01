-- Prove2me | solution 1 for TargetGranularity.SdVsMd.proposition_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:56:08.866455+00:00
-- url     : https://prove2.me/submissions/40a9e523-43ab-46fd-853b-d16acca12ed1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model
import Theorems.Thm_TargetGranularity_SdVsMd_proposition_1
import Theorems.Thm_TargetGranularity_SdVsMd_proposition_2
import Theorems.Thm_TargetGranularity_SdVsMd_lemma_4
import Theorems.Thm_TargetGranularity_SdVsMd_lemma_5
import Theorems.Thm_TargetGranularity_SdVsMd_lemma_6
import Theorems.Thm_TargetGranularity_SdVsMd_sd_profit_bounded_below_small_cad

open TargetGranularity.SdVsMd

theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ cad : ℝ, 0 < cad → cad < δ →
      ∃ c₁ : ℝ, c₁ < cmaxClick cad p ∧
        ∀ cclick : ℝ, 0 < cclick → c₁ < cclick → cclick ≤ cmaxClick cad p →
          (∃ S : Set ℝ, IsSdEq p cad cclick S) ∧
          (∃ S : Set (ℝ × ℝ), IsSymMdEq p cad cclick S) ∧
          ∀ (Ssd : Set ℝ) (Smd : Set (ℝ × ℝ)), IsSdEq p cad cclick Ssd →
            IsSymMdEq p cad cclick Smd →
              mdProfit p cad cclick Smd < sdProfit p cad cclick Ssd := by
  have h1p : 0 < 1 - p := by linarith
  have hpp : 0 < p * (1 - p) := mul_pos hp0 h1p
  have hp2 : 0 < p ^ 2 := by positivity
  set c0 : ℝ := (1 - p) / (2 * (1 + p)) with hc0
  set cs : ℝ := (c0 + (1 - p) / 2) / 2 with hcs
  have hc0lo : (1 - p) ^ 2 / 2 < c0 := by
    rw [hc0, lt_div_iff₀ (by positivity)]; nlinarith [mul_pos hpp hp0]
  have hc0hi : c0 < (1 - p) / 2 := by
    rw [hc0, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hcslo : (1 - p) ^ 2 / 2 < cs := by rw [hcs]; linarith
  have hcshi : cs < (1 - p) / 2 := by rw [hcs]; linarith
  have hc0cs : c0 < cs := by rw [hcs]; linarith
  -- uniform lower bound on the sd profit at c* = cs
  obtain ⟨ε, δ₁, hε, hδ₁, hsd⟩ := sd_profit_bounded_below_small_cad p cs hp0 hp1 hcslo hcshi
  -- Lemma 5
  obtain ⟨δ₂, hδ₂, hmd⟩ := lemma_5 p hp0 hp1 ε hε
  -- continuity of the closed form of c^max_click at c_ad = 0
  set D0 : ℝ := p * (1 - p) * (1 + p) with hD0
  have hD0pos : 0 < D0 := by rw [hD0]; positivity
  let f : ℝ → ℝ := fun c => (c ^ 2 - 3 * c * (1 - p) * p + 3 * (1 - p) ^ 2 * p ^ 2) /
      (6 * p * (p * (1 - p) * (1 + p) - c))
  have hf0 : f 0 = c0 := by
    simp only [f, hc0]
    field_simp
    ring
  have hfc : ContinuousAt f 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · have : (6 * p * (p * (1 - p) * (1 + p) - 0)) = 6 * p * D0 := by rw [hD0]; ring
      rw [this]; positivity
  have hev : ∀ᶠ c in nhds (0 : ℝ), f c < cs := by
    apply hfc.eventually (gt_mem_nhds _)
    rw [hf0]; exact hc0cs
  obtain ⟨δ₃, hδ₃, hf⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (min δ₁ δ₂) (min δ₃ (min (p ^ 2) (p * (1 - p)))), ?_, ?_⟩
  · exact lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ (lt_min hp2 hpp))
  intro cad hcad hcadδ
  have hcδ₁ : cad < δ₁ := lt_of_lt_of_le hcadδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcδ₂ : cad < δ₂ := lt_of_lt_of_le hcadδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδ₃ : cad < δ₃ := lt_of_lt_of_le hcadδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcp2 : cad < p ^ 2 := lt_of_lt_of_le hcadδ
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hcp1 : cad < p * (1 - p) := lt_of_lt_of_le hcadδ
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  obtain ⟨h6lo, h6hi⟩ := lemma_6 p cad hp0 hp1 hcad hcp2 hcp1
  have hcmax : cmaxClick cad p = f cad := by
    simp only [cmaxClick, f]
    rw [if_neg (not_lt.mpr hcp1.le), if_pos hcp2.le]
  have hcmaxcs : cmaxClick cad p < cs := by
    rw [hcmax]; apply hf
    rw [Real.dist_eq, sub_zero, abs_of_pos hcad]; exact hcδ₃
  obtain ⟨η, hη, hmdη⟩ := hmd cad hcad hcδ₂
  -- c̄_ad bound: for (1-p)²/2 < c ≤ (1-p)/2, p(1-p) ≤ c̄_ad(c, p)
  have hbar : ∀ c : ℝ, (1 - p) ^ 2 / 2 < c → c ≤ (1 - p) / 2 → cad < cadBar c p := by
    intro c hc1 hc2
    have hcpos : 0 < c := lt_of_le_of_lt (by positivity) hc1
    simp only [cadBar]
    rw [if_neg (not_le.mpr hc1), if_pos hc2]
    have hlog : 0 ≤ Real.log ((1 - p) / (2 * c)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith
  refine ⟨max ((1 - p) ^ 2 / 2) (cmaxClick cad p - η), ?_, ?_⟩
  · exact max_lt h6lo (by linarith)
  intro cclick hcpos hc1 hc2
  have hclo : (1 - p) ^ 2 / 2 < cclick := lt_of_le_of_lt (le_max_left _ _) hc1
  have hceta : cmaxClick cad p - η < cclick := lt_of_le_of_lt (le_max_right _ _) hc1
  have hchi : cclick < (1 - p) / 2 := lt_of_le_of_lt hc2 h6hi
  have hccs : cclick < cs := lt_of_le_of_lt hc2 hcmaxcs
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨αbar, ωhi, -, -, -, -, hEq, -, -⟩ :=
      proposition_1 p cad cclick hp0 hp1 hcad (hbar cclick hclo hchi.le) hclo hchi
    exact ⟨_, hEq⟩
  · exact ⟨_, ((proposition_2 p cad cclick hp0 hp1 hcad hcp2 hcp1 hcpos).1 hc2).1⟩
  · intro Ssd Smd hSsd hSmd
    have hm := hmdη cclick hceta hc2 Smd hSmd
    obtain ⟨αbar, ωhi, -, -, -, -, hEq, -, -⟩ :=
      proposition_1 p cad cs hp0 hp1 hcad (hbar cs hcslo hcshi.le) hcslo hcshi
    have h4 := (lemma_4 p cad hp0 hp1 hcad hcp1).1 cclick cs hclo hccs hcshi _ _ hSsd hEq
    have hb := hsd cad hcad hcδ₁ _ hEq
    linarith
