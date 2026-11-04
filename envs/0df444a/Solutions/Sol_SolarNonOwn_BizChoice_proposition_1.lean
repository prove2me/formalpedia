-- Prove2me | solution 1 for SolarNonOwn.BizChoice.proposition_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T10:15:42.899544+00:00
-- url     : https://prove2.me/submissions/a0bdc952-847f-4649-874f-4afccba86fd2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms
import Theorems.Thm_SolarNonOwn_BizChoice_part_A
import Theorems.Thm_SolarNonOwn_BizChoice_part_B
import Theorems.Thm_SolarNonOwn_BizChoice_crossing_low_alpha
import Theorems.Thm_SolarNonOwn_BizChoice_crossing_high_alpha

noncomputable section
open MeasureTheory
open SolarNonOwn.BizChoice

/-- A strictly decreasing function on `[0, C]` that is positive at `0` changes sign at a
single point `cs`. -/
private lemma solar_crossing_point (D : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) C → b ∈ Set.Icc (0 : ℝ) C → a < b → D b < D a)
    (h0 : 0 < D 0) :
    ∃ cs : ℝ,
      (∀ c, c ∈ Set.Icc (0 : ℝ) C → c < cs → 0 < D c) ∧
      (∀ c, c ∈ Set.Icc (0 : ℝ) C → cs < c → D c < 0) ∧
      (∀ c, c ∈ Set.Icc (0 : ℝ) C → D c < 0 → cs ≤ c) := by
  set S : Set ℝ := {c | c ∈ Set.Icc (0 : ℝ) C ∧ 0 < D c} with hS
  have hne : S.Nonempty := ⟨0, ⟨le_refl _, hC⟩, h0⟩
  have hbdd : BddAbove S := ⟨C, fun c hc => hc.1.2⟩
  refine ⟨sSup S, ?_, ?_, ?_⟩
  · intro c hc hlt
    obtain ⟨c', hc'S, hcc'⟩ := exists_lt_of_lt_csSup hne hlt
    exact lt_trans hc'S.2 (hdec c c' hc hc'S.1 hcc')
  · intro c hc hlt
    by_contra hneg
    push Not at hneg
    have h0S : (0 : ℝ) ≤ sSup S := le_csSup hbdd ⟨⟨le_refl _, hC⟩, h0⟩
    set m := (sSup S + c) / 2 with hm
    have hmI : m ∈ Set.Icc (0 : ℝ) C := ⟨by linarith, by linarith [hc.2]⟩
    have hmc : m < c := by linarith
    have hDm : 0 < D m := lt_of_le_of_lt hneg (hdec m c hmI hc hmc)
    have : m ≤ sSup S := le_csSup hbdd ⟨hmI, hDm⟩
    linarith
  · intro c hc hD
    apply csSup_le hne
    intro c' hc'
    by_contra hlt
    push Not at hlt
    have := hdec c c' hc hc'.1 hlt
    linarith [hc'.2]

theorem solution (prm : Params) (hs : Standing prm) :
    (prm.alpha < A2 prm →
      ∃ C1 C2 : ℝ, C1 ≤ C2 ∧
        ∀ (h : Measure ℝ) [IsProbabilityMeasure h], h (Set.Iic 0) = 0 →
        ∀ c : ℝ, 0 < c → c < C0 prm →
        (∃ x : Prices, IsMaxOn (profit prm h c) Set.univ x) ∧
        ∀ x : Prices, IsMaxOn (profit prm h c) Set.univ x →
          (c < C1 → offers prm h x = ({BizOpt.P, BizOpt.S} : Finset BizOpt)) ∧
          (C1 < c → c < C2 → offers prm h x = ({BizOpt.P, BizOpt.L, BizOpt.S} : Finset BizOpt)) ∧
          (C2 < c → offers prm h x = ({BizOpt.L, BizOpt.S} : Finset BizOpt))) ∧
    (A2 prm ≤ prm.alpha →
      ∃ C3 : ℝ,
        ∀ (h : Measure ℝ) [IsProbabilityMeasure h], h (Set.Iic 0) = 0 →
        ∀ c : ℝ, 0 < c → c < C0 prm →
        (∃ x : Prices, IsMaxOn (profit prm h c) Set.univ x) ∧
        ∀ x : Prices, IsMaxOn (profit prm h c) Set.univ x →
          (c < C3 → offers prm h x = ({BizOpt.P, BizOpt.S} : Finset BizOpt)) ∧
          (C3 < c → offers prm h x = ({BizOpt.S} : Finset BizOpt))) := by
  obtain ⟨⟨hα, hβ, ht, htr, hg⟩, hβr, hαA⟩ := hs
  -- basic sign facts
  have hrpos : 0 < prm.r := lt_trans ht htr
  -- `C0 > 0` forces `α < 1`
  have hα1_of : ∀ c : ℝ, 0 < c → c < C0 prm → prm.alpha < 1 := by
    intro c hc hc0
    by_contra hcon
    push Not at hcon
    have : C0 prm ≤ 0 := by
      unfold C0
      apply div_nonpos_of_nonneg_of_nonpos
      · positivity
      · linarith
    linarith
  -- maximizer over the region `p ≤ r`
  have hA : ∀ (h : Measure ℝ) [IsProbabilityMeasure h], h (Set.Iic 0) = 0 →
      ∀ c : ℝ, 0 < c → c < C0 prm →
      ∃ x : Prices, x.p ≤ prm.r ∧ IsMaxOn (profit prm h c) {y | y.p ≤ prm.r} x ∧
        profit prm h c x = profAstar prm c := by
    intro h _ hh c hc hc0
    have hPA := part_A prm h hh ⟨⟨hα, hβ, ht, htr, hg⟩, hβr, hαA⟩ c hc hc0
    by_cases h1 : c ≤ CA1 prm
    · obtain ⟨a1, a2, a3, -⟩ := hPA.1 h1
      exact ⟨_, a1, a2, a3⟩
    · push Not at h1
      by_cases h2 : c < CA2 prm
      · obtain ⟨a1, a2, a3, -⟩ := hPA.2.1 h1 h2
        exact ⟨_, a1, a2, a3⟩
      · push Not at h2
        obtain ⟨a1, a2, a3, -⟩ := hPA.2.2 h2
        exact ⟨_, a1, a2, a3⟩
  -- maximizer over the region `p > r`
  have hB : ∀ (h : Measure ℝ) [IsProbabilityMeasure h], h (Set.Iic 0) = 0 →
      ∀ c : ℝ, 0 < c → c < C0 prm →
      ∃ x : Prices, prm.r < x.p ∧ IsMaxOn (profit prm h c) {y | prm.r < y.p} x ∧
        profit prm h c x = profBstar prm c := by
    intro h _ hh c hc hc0
    have hPB := part_B prm h hh ⟨⟨hα, hβ, ht, htr, hg⟩, hβr, hαA⟩ c hc hc0
    by_cases h1 : prm.alpha < A2 prm
    · obtain ⟨a1, a2, a3, -⟩ := hPB.1 h1
      exact ⟨_, a1, a2, a3⟩
    · push Not at h1
      obtain ⟨a1, a2, a3, -⟩ := hPB.2 h1
      exact ⟨_, a1, a2, a3⟩
  -- existence of a global maximizer
  have hEx : ∀ (h : Measure ℝ) [IsProbabilityMeasure h], h (Set.Iic 0) = 0 →
      ∀ c : ℝ, 0 < c → c < C0 prm → ∃ x : Prices, IsMaxOn (profit prm h c) Set.univ x := by
    intro h _ hh c hc hc0
    obtain ⟨xa, _, hxa, hva⟩ := hA h hh c hc hc0
    obtain ⟨xb, _, hxb, hvb⟩ := hB h hh c hc hc0
    rcases le_total (profBstar prm c) (profAstar prm c) with hle | hle
    · refine ⟨xa, fun y _ => ?_⟩
      by_cases hy : y.p ≤ prm.r
      · exact hxa hy
      · push Not at hy
        have := hxb hy
        simp only [Set.mem_ofPred_eq] at this ⊢
        linarith
    · refine ⟨xb, fun y _ => ?_⟩
      by_cases hy : y.p ≤ prm.r
      · have := hxa hy
        simp only [Set.mem_ofPred_eq] at this ⊢
        linarith
      · push Not at hy
        exact hxb hy
  -- when region A is strictly better, every global maximizer lies in region A
  have hInA : ∀ (h : Measure ℝ) [IsProbabilityMeasure h], h (Set.Iic 0) = 0 →
      ∀ c : ℝ, 0 < c → c < C0 prm → profBstar prm c < profAstar prm c →
      ∀ y : Prices, IsMaxOn (profit prm h c) Set.univ y →
        y.p ≤ prm.r ∧ IsMaxOn (profit prm h c) {z | z.p ≤ prm.r} y := by
    intro h _ hh c hc hc0 hlt y hy
    obtain ⟨xa, _, _, hva⟩ := hA h hh c hc hc0
    obtain ⟨xb, _, hxb, hvb⟩ := hB h hh c hc hc0
    refine ⟨?_, hy.on_subset (Set.subset_univ _)⟩
    by_contra hp
    push Not at hp
    have h1 : profit prm h c y ≤ profit prm h c xb := hxb hp
    have h2 : profit prm h c xa ≤ profit prm h c y := hy (Set.mem_univ xa)
    linarith
  have hInB : ∀ (h : Measure ℝ) [IsProbabilityMeasure h], h (Set.Iic 0) = 0 →
      ∀ c : ℝ, 0 < c → c < C0 prm → profAstar prm c < profBstar prm c →
      ∀ y : Prices, IsMaxOn (profit prm h c) Set.univ y →
        prm.r < y.p ∧ IsMaxOn (profit prm h c) {z | prm.r < z.p} y := by
    intro h _ hh c hc hc0 hlt y hy
    obtain ⟨xa, _, hxa, hva⟩ := hA h hh c hc hc0
    obtain ⟨xb, _, _, hvb⟩ := hB h hh c hc hc0
    refine ⟨?_, hy.on_subset (Set.subset_univ _)⟩
    by_contra hp
    push Not at hp
    have h1 : profit prm h c y ≤ profit prm h c xa := hxa hp
    have h2 : profit prm h c xb ≤ profit prm h c y := hy (Set.mem_univ xb)
    linarith
  have hC0nn : 0 ≤ C0 prm ∨ C0 prm < 0 := le_or_gt 0 (C0 prm)
  constructor
  · -- low investment subsidy
    intro hαl
    obtain ⟨hdec, hD0, hDCA2⟩ := crossing_low_alpha prm ⟨⟨hα, hβ, ht, htr, hg⟩, hβr, hαA⟩ hαl
    rcases hC0nn with hC0 | hC0
    swap
    · -- no admissible cost
      refine ⟨0, 0, le_refl _, fun h _ _ c hc hc0 => absurd (lt_trans hc hc0) (by linarith)⟩
    obtain ⟨cs, hcs1, hcs2, hcs3⟩ :=
      solar_crossing_point (fun c => profAstar prm c - profB2 prm c) (C0 prm) hC0 hdec hD0
    have hBs : profBstar prm = profB2 prm := by
      funext c; unfold profBstar; rw [if_pos hαl]
    refine ⟨min (CA1 prm) cs, cs, min_le_right _ _, ?_⟩
    intro h _ hh c hc hc0
    have hα1 := hα1_of c hc hc0
    have hcI : c ∈ Set.Icc (0 : ℝ) (C0 prm) := ⟨hc.le, hc0.le⟩
    refine ⟨hEx h hh c hc hc0, fun y hy => ⟨?_, ?_, ?_⟩⟩
    · intro hc1
      have hccs : c < cs := lt_of_lt_of_le hc1 (min_le_right _ _)
      have hpos := hcs1 c hcI hccs
      have hlt : profBstar prm c < profAstar prm c := by rw [hBs]; linarith
      obtain ⟨hyp, hymax⟩ := hInA h hh c hc hc0 hlt y hy
      have hPA := part_A prm h hh ⟨⟨hα, hβ, ht, htr, hg⟩, hβr, hαA⟩ c hc hc0
      have hcA1 : c ≤ CA1 prm := (lt_of_lt_of_le hc1 (min_le_left _ _)).le
      obtain ⟨-, -, -, a4⟩ := hPA.1 hcA1
      exact a4 y hyp hymax
    · intro hc1 hc2
      have hpos := hcs1 c hcI hc2
      have hlt : profBstar prm c < profAstar prm c := by rw [hBs]; linarith
      obtain ⟨hyp, hymax⟩ := hInA h hh c hc hc0 hlt y hy
      have hPA := part_A prm h hh ⟨⟨hα, hβ, ht, htr, hg⟩, hβr, hαA⟩ c hc hc0
      have hcA1 : CA1 prm < c := by
        rcases min_choice (CA1 prm) cs with hm | hm
        · rw [hm] at hc1; exact hc1
        · rw [hm] at hc1; linarith
      have hcA2 : c < CA2 prm := by
        by_contra hge
        push Not at hge
        have hCA2nn : 0 ≤ CA2 prm := by
          unfold CA2
          apply div_nonneg
          · have : 0 ≤ prm.r ^ 2 + prm.beta * (prm.r + prm.t) := by positivity
            positivity
          · apply mul_nonneg <;> linarith
        have hCA2I : CA2 prm ∈ Set.Icc (0 : ℝ) (C0 prm) := ⟨hCA2nn, by linarith⟩
        rcases eq_or_lt_of_le hge with heq | hlt2
        · rw [heq] at hDCA2; linarith
        · have := hdec (CA2 prm) c hCA2I hcI hlt2
          linarith
      obtain ⟨-, -, -, a4⟩ := hPA.2.1 hcA1 hcA2
      exact a4 y hyp hymax
    · intro hc2
      have hneg := hcs2 c hcI hc2
      have hlt : profAstar prm c < profBstar prm c := by rw [hBs]; linarith
      obtain ⟨hyp, hymax⟩ := hInB h hh c hc hc0 hlt y hy
      have hPB := part_B prm h hh ⟨⟨hα, hβ, ht, htr, hg⟩, hβr, hαA⟩ c hc hc0
      obtain ⟨-, -, -, a4⟩ := hPB.1 hαl
      exact a4 y hyp hymax
  · -- high investment subsidy
    intro hαh
    obtain ⟨hdec, hD0, hDCA1, hCA1C0⟩ :=
      crossing_high_alpha prm ⟨⟨hα, hβ, ht, htr, hg⟩, hβr, hαA⟩ hαh
    rcases hC0nn with hC0 | hC0
    swap
    · exact ⟨0, fun h _ _ c hc hc0 => absurd (lt_trans hc hc0) (by linarith)⟩
    obtain ⟨cs, hcs1, hcs2, hcs3⟩ :=
      solar_crossing_point (fun c => profAstar prm c - profB1 prm c) (C0 prm) hC0 hdec hD0
    have hBs : profBstar prm = profB1 prm := by
      funext c; unfold profBstar; rw [if_neg (not_lt.mpr hαh)]
    refine ⟨cs, ?_⟩
    intro h _ hh c hc hc0
    have hα1 := hα1_of c hc hc0
    have hcI : c ∈ Set.Icc (0 : ℝ) (C0 prm) := ⟨hc.le, hc0.le⟩
    refine ⟨hEx h hh c hc hc0, fun y hy => ⟨?_, ?_⟩⟩
    · intro hc3
      have hpos := hcs1 c hcI hc3
      have hlt : profBstar prm c < profAstar prm c := by rw [hBs]; linarith
      obtain ⟨hyp, hymax⟩ := hInA h hh c hc hc0 hlt y hy
      have hPA := part_A prm h hh ⟨⟨hα, hβ, ht, htr, hg⟩, hβr, hαA⟩ c hc hc0
      have hCA1pos : 0 < CA1 prm := by
        have hA2 : prm.beta ≤ prm.alpha * (prm.beta + prm.r) := by
          unfold A2 at hαh
          rwa [div_le_iff₀ (by linarith)] at hαh
        unfold CA1
        apply div_pos
        · apply mul_pos hg
          have h1a : 0 < 1 - prm.alpha := by linarith
          have : prm.t * prm.beta * (1 - prm.alpha) < prm.r * prm.beta := by
            have : prm.t * prm.beta * (1 - prm.alpha) ≤ prm.t * prm.beta := by
              have := mul_pos ht hβ
              nlinarith
            nlinarith
          nlinarith
        · have h1a : 0 < 1 - prm.alpha := by linarith
          have : 0 < prm.r + prm.t * (1 - prm.alpha) := by positivity
          positivity
      have hcs_le : cs ≤ CA1 prm := hcs3 (CA1 prm) ⟨hCA1pos.le, hCA1C0.le⟩ hDCA1
      have hcA1 : c ≤ CA1 prm := (lt_of_lt_of_le hc3 hcs_le).le
      obtain ⟨-, -, -, a4⟩ := hPA.1 hcA1
      exact a4 y hyp hymax
    · intro hc3
      have hneg := hcs2 c hcI hc3
      have hlt : profAstar prm c < profBstar prm c := by rw [hBs]; linarith
      obtain ⟨hyp, hymax⟩ := hInB h hh c hc hc0 hlt y hy
      have hPB := part_B prm h hh ⟨⟨hα, hβ, ht, htr, hg⟩, hβr, hαA⟩ c hc hc0
      obtain ⟨-, -, -, a4⟩ := hPB.2 hαh
      exact a4 y hyp hymax
