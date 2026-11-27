-- Prove2me | solution 1 for UnfairML.Coverage.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:21:37.164139+00:00
-- url     : https://prove2.me/submissions/920a1ae0-63da-45ba-add9-94326ef3b2f6

import Mathlib
import Definitions.Def_UnfairML_Coverage_Supplement_CostModel

open UnfairML
open UnfairML.Coverage
open UnfairML.Coverage.Supplement

/-- Theorem 1, p. 18, including the medium- and large-loss regimes of Appendix B. -/
theorem solution (P : Params) (hS : P.Standing) (τ : ℝ → ℝ)
    (hτ : IsLearningCost P τ)
    (cET sET : ℝ) (hET : IsOptETWithCost P τ cET sET)
    (cpEO crEO sEO : ℝ) (hEO : IsOptEOWithCost P τ cpEO crEO sEO) :
    sEO ≤ sET := by
      obtain ⟨hα, hβ, hdr, hdrp, hdp, hab, hγp, hγ⟩ := hS
      have hap : 0 < P.αp := by unfold Params.αp; exact mul_pos hα (by linarith)
      have hbp : 0 < P.βp := by unfold Params.βp; exact mul_pos hβ (by linarith)
      have har : 0 < P.αr := by unfold Params.αr; exact mul_pos hα (by linarith)
      have hbr : 0 < P.βr := by unfold Params.βr; exact mul_pos hβ hdr
      have hapbp : P.αp < P.βp := by
        have h1 := hab
        unfold Params.αr Params.βr at h1
        unfold Params.αp Params.βp
        linarith only [h1, mul_pos hβ (sub_pos.2 hdrp), mul_pos hα (sub_pos.2 hdrp)]
      have harbr : P.αr ≤ P.βr := hab
      -- generic one-group facts
      have L12 : ∀ a b g c : ℝ, 0 ≤ a → 0 ≤ b → g < 1 →
          (min ((1 - c) / (1 - g)) 1 * a - max ((1 - g - c) / (1 - g)) 0 * b
            ≤ a * ((1 - c) * (1 / (1 - g)))) ∧
          (min ((1 - c) / (1 - g)) 1 * a - max ((1 - g - c) / (1 - g)) 0 * b
            ≤ a * ((1 - c) * (1 / (1 - g))) - b * ((1 - c) * (1 / (1 - g)) - g * (1 / (1 - g)))) := by
        intro a b g c ha hb hg
        have e1 : (1 - c) / (1 - g) = (1 - c) * (1 / (1 - g)) := by rw [mul_one_div]
        have e2 : (1 - g - c) / (1 - g) = (1 - c) * (1 / (1 - g)) - g * (1 / (1 - g)) := by
          rw [mul_one_div, mul_one_div, div_sub_div_same]; ring_nf
        rw [e1, e2]
        have h1 := min_le_left ((1 - c) * (1 / (1 - g))) 1
        have h2 := le_max_left ((1 - c) * (1 / (1 - g)) - g * (1 / (1 - g))) 0
        have h3 := le_max_right ((1 - c) * (1 / (1 - g)) - g * (1 / (1 - g))) 0
        constructor
        · linarith only [mul_le_mul_of_nonneg_right h1 ha, mul_le_mul_of_nonneg_right h3 hb]
        · linarith only [mul_le_mul_of_nonneg_right h1 ha, mul_le_mul_of_nonneg_right h2 hb]
      have L3 : ∀ a b g c : ℝ, g < 1 → (1 - c) * (1 / (1 - g)) ≤ 1 → 1 - c ≤ g →
          min ((1 - c) / (1 - g)) 1 * a - max ((1 - g - c) / (1 - g)) 0 * b
            = a * ((1 - c) * (1 / (1 - g))) := by
        intro a b g c hg ht hc
        have e1 : (1 - c) / (1 - g) = (1 - c) * (1 / (1 - g)) := by rw [mul_one_div]
        have e2 : (1 - g - c) / (1 - g) = (1 - c - g) * (1 / (1 - g)) := by
          rw [mul_one_div]; ring_nf
        have hpos : 0 < 1 / (1 - g) := one_div_pos.2 (by linarith)
        rw [e1, e2, min_eq_left ht,
          max_eq_right (mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le)]
        ring
      have L4 : ∀ a b g c : ℝ, g < 1 → (1 - c) * (1 / (1 - g)) ≤ 1 → g ≤ 1 - c →
          min ((1 - c) / (1 - g)) 1 * a - max ((1 - g - c) / (1 - g)) 0 * b
            = a * ((1 - c) * (1 / (1 - g))) - b * ((1 - c) * (1 / (1 - g)) - g * (1 / (1 - g))) := by
        intro a b g c hg ht hc
        have e1 : (1 - c) / (1 - g) = (1 - c) * (1 / (1 - g)) := by rw [mul_one_div]
        have e2 : (1 - g - c) / (1 - g) = (1 - c - g) * (1 / (1 - g)) := by
          rw [mul_one_div]; ring_nf
        have hpos : 0 < 1 / (1 - g) := one_div_pos.2 (by linarith)
        rw [e1, e2, min_eq_left ht,
          max_eq_left (mul_nonneg (by linarith) hpos.le)]
        ring
      have hprof : ∀ cp cr s, profit P 0 cp cr s =
          (min ((1 - cr) / (1 - P.γr * s)) 1 * P.αr - max ((1 - P.γr * s - cr) / (1 - P.γr * s)) 0 * P.βr)
          + (min ((1 - cp) / (1 - P.γp * s)) 1 * P.αp
              - max ((1 - P.γp * s - cp) / (1 - P.γp * s)) 0 * P.βp) := by
        intro cp cr s; simp only [profit, tau]; ring
      obtain ⟨pf, hpf⟩ : ∃ f : ℝ → ℝ, ∀ s, f s = 1 / (1 - P.γp * s) :=
        ⟨fun s => 1 / (1 - P.γp * s), fun _ => rfl⟩
      obtain ⟨qf, hqf⟩ : ∃ f : ℝ → ℝ, ∀ s, f s = 1 / (1 - P.γr * s) :=
        ⟨fun s => 1 / (1 - P.γr * s), fun _ => rfl⟩
      obtain ⟨Vx, hVx⟩ : ∃ f : ℝ → ℝ, ∀ s,
          f s = P.αp * (P.γp * s * pf s) + P.αr * (P.γp * s * qf s) :=
        ⟨fun s => P.αp * (P.γp * s * pf s) + P.αr * (P.γp * s * qf s), fun _ => rfl⟩
      obtain ⟨Vy, hVy⟩ : ∃ f : ℝ → ℝ, ∀ s,
          f s = P.αp * (P.γr * s * pf s) - P.βp * (P.γr * s * pf s - P.γp * s * pf s)
            + P.αr * (P.γr * s * qf s) :=
        ⟨fun s => P.αp * (P.γr * s * pf s) - P.βp * (P.γr * s * pf s - P.γp * s * pf s)
            + P.αr * (P.γr * s * qf s), fun _ => rfl⟩
      obtain ⟨Wp, hWp⟩ : ∃ f : ℝ → ℝ, ∀ s, f s = (P.αp + P.αr) * (P.γp * s * pf s) :=
        ⟨fun s => (P.αp + P.αr) * (P.γp * s * pf s), fun _ => rfl⟩
      obtain ⟨Wr, hWr⟩ : ∃ f : ℝ → ℝ, ∀ s,
          f s = (P.αp + P.αr) * (P.γr * s * qf s) - P.βp * (P.γr * s * qf s - P.γp * s * pf s) :=
        ⟨fun s => (P.αp + P.αr) * (P.γr * s * qf s) - P.βp * (P.γr * s * qf s - P.γp * s * pf s),
          fun _ => rfl⟩
      have hbase : ∀ s, s ∈ Set.Icc (0:ℝ) P.sMax →
          0 ≤ P.γp * s ∧ P.γp * s ≤ P.γr * s ∧ P.γr * s ≤ 1/2 ∧ 0 < pf s ∧ 0 < qf s ∧
          pf s * (1 - P.γp * s) = 1 ∧ qf s * (1 - P.γr * s) = 1 ∧ pf s ≤ qf s := by
        intro s hs
        have hs2 : P.γr * s ≤ 1/2 := by
          have h := hs.2
          unfold Params.sMax at h
          rw [le_div_iff₀ (by linarith)] at h
          linarith
        have hx0 : 0 ≤ P.γp * s := mul_nonneg hγp.le hs.1
        have hxy : P.γp * s ≤ P.γr * s := mul_le_mul_of_nonneg_right hγ.le hs.1
        have hd1 : 0 < 1 - P.γp * s := by linarith
        have hd2 : 0 < 1 - P.γr * s := by linarith
        refine ⟨hx0, hxy, hs2, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hpf]; exact one_div_pos.2 hd1
        · rw [hqf]; exact one_div_pos.2 hd2
        · rw [hpf]; exact one_div_mul_cancel hd1.ne'
        · rw [hqf]; exact one_div_mul_cancel hd2.ne'
        · rw [hpf, hqf]; exact one_div_le_one_div_of_le hd2 (by linarith)
      have hmono : ∀ s1 s2, s1 ∈ Set.Icc (0:ℝ) P.sMax → s2 ∈ Set.Icc (0:ℝ) P.sMax → s1 ≤ s2 →
          pf s1 ≤ pf s2 ∧ qf s1 ≤ qf s2 := by
        intro s1 s2 h1 h2 h12
        obtain ⟨-, hxy2, hy2, -⟩ := hbase s2 h2
        have e1 : P.γp * s1 ≤ P.γp * s2 := mul_le_mul_of_nonneg_left h12 hγp.le
        have e2 : P.γr * s1 ≤ P.γr * s2 := mul_le_mul_of_nonneg_left h12 (by linarith)
        constructor
        · rw [hpf, hpf]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
        · rw [hqf, hqf]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
      have hD : ∀ s, s ∈ Set.Icc (0:ℝ) P.sMax →
          qf s - pf s = (P.γr - P.γp) * (s * pf s * qf s) := by
        intro s hs
        obtain ⟨-, -, -, -, -, hp1, hq1, -⟩ := hbase s hs
        linear_combination (-(qf s)) * hp1 + (pf s) * hq1
      have hstrict : ∀ a b, a ∈ Set.Icc (0:ℝ) P.sMax → b ∈ Set.Icc (0:ℝ) P.sMax → a < b →
          P.γr * a * (qf a - pf a) < P.γr * b * (qf b - pf b) ∧
          P.γp * a * (qf a - pf a) < P.γp * b * (qf b - pf b) := by
        intro a b ha hb hab'
        obtain ⟨-, -, -, hpa, hqa, -, -, -⟩ := hbase a ha
        obtain ⟨-, -, -, hpb, hqb, -, -, -⟩ := hbase b hb
        obtain ⟨hp12, hq12⟩ := hmono a b ha hb hab'.le
        rw [hD a ha, hD b hb]
        have hc0 : 0 < P.γr - P.γp := by linarith
        have hb0 : 0 < b := by linarith [ha.1]
        have e1 : a * pf a ≤ b * pf b := mul_le_mul hab'.le hp12 hpa.le hb0.le
        have e2 : a * pf a * qf a ≤ b * pf b * qf b :=
          mul_le_mul e1 hq12 hqa.le (mul_pos hb0 hpb).le
        have e3 : (P.γr - P.γp) * (a * pf a * qf a) ≤ (P.γr - P.γp) * (b * pf b * qf b) :=
          mul_le_mul_of_nonneg_left e2 hc0.le
        have e4 : 0 < (P.γr - P.γp) * (b * pf b * qf b) :=
          mul_pos hc0 (mul_pos (mul_pos hb0 hpb) hqb)
        constructor
        · have f1 := mul_le_mul_of_nonneg_left e3 (mul_nonneg (by linarith : (0:ℝ) ≤ P.γr) ha.1)
          have f2 := mul_lt_mul_of_pos_right
            (show P.γr * a < P.γr * b from mul_lt_mul_of_pos_left hab' (by linarith)) e4
          linarith
        · have f1 := mul_le_mul_of_nonneg_left e3 (mul_nonneg hγp.le ha.1)
          have f2 := mul_lt_mul_of_pos_right
            (show P.γp * a < P.γp * b from mul_lt_mul_of_pos_left hab' hγp) e4
          linarith
      -- upper bound for ET
      have ETup : ∀ c s, c ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) P.sMax →
          profit P 0 c c s ≤ max (Vx s) (Vy s) := by
        intro c s hc hs
        obtain ⟨hx0, hxy, hy, hp, hq, hp1, hq1, hpq⟩ := hbase s hs
        obtain ⟨Ap1, Ap2⟩ := L12 P.αp P.βp (P.γp * s) c hap.le hbp.le (by linarith)
        obtain ⟨Ar1, Ar2⟩ := L12 P.αr P.βr (P.γr * s) c har.le hbr.le (by linarith)
        rw [← hpf s] at Ap1 Ap2
        rw [← hqf s] at Ar1 Ar2
        rw [hprof, hVx, hVy]
        by_cases hA : 0 ≤ (P.αp - P.βp) * pf s + P.αr * qf s
        · apply le_max_of_le_right
          by_cases hu : 1 - c ≤ P.γr * s
          · linarith only [Ap2, Ar1, mul_nonneg (sub_nonneg.2 hu) hA]
          · push_neg at hu
            have hB : 0 ≤ P.βr * qf s - ((P.αp - P.βp) * pf s + P.αr * qf s) := by
              linarith only [mul_nonneg (sub_nonneg.2 harbr) hq.le,
                mul_nonneg (sub_nonneg.2 hapbp.le) hp.le]
            linarith only [Ap2, Ar2, mul_nonneg (sub_nonneg.2 hu.le) hB]
        · push_neg at hA
          apply le_max_of_le_left
          by_cases hu : 1 - c ≤ P.γp * s
          · linarith only [Ap1, Ar1, mul_nonneg (sub_nonneg.2 hu)
              (add_nonneg (mul_nonneg hap.le hp.le) (mul_nonneg har.le hq.le))]
          · push_neg at hu
            linarith only [Ap2, Ar1, mul_nonneg (sub_nonneg.2 hu.le) (show 0 ≤ -((P.αp - P.βp) * pf s + P.αr * qf s) by linarith)]
      -- upper bound for EO
      have EOup : ∀ cp cr s, cp ∈ Set.Icc (0:ℝ) 1 → cr ∈ Set.Icc (0:ℝ) 1 →
          s ∈ Set.Icc (0:ℝ) P.sMax → EOConstraint P cp cr s →
          (0 ≤ P.αr + P.αp - P.βp → profit P 0 cp cr s ≤ Wr s) ∧
          (P.αr + P.αp - P.βp < 0 → profit P 0 cp cr s ≤ Wp s) := by
        intro cp cr s hcp hcr hs hc
        obtain ⟨hx0, hxy, hy, hp, hq, hp1, hq1, hpq⟩ := hbase s hs
        obtain ⟨Ap1, Ap2⟩ := L12 P.αp P.βp (P.γp * s) cp hap.le hbp.le (by linarith)
        obtain ⟨Ar1, Ar2⟩ := L12 P.αr P.βr (P.γr * s) cr har.le hbr.le (by linarith)
        rw [← hpf s] at Ap1 Ap2
        rw [← hqf s] at Ar1 Ar2
        have ht : (1 - cr) * qf s = (1 - cp) * pf s := by
          unfold EOConstraint at hc
          rw [hpf, hqf, mul_one_div, mul_one_div]; exact hc
        obtain ⟨t, htp⟩ : ∃ t, (1 - cp) * pf s = t := ⟨_, rfl⟩
        rw [ht, htp] at Ar1 Ar2
        rw [htp] at Ap1 Ap2
        rw [hprof, hWr, hWp]
        constructor
        · intro hE
          by_cases h : t ≤ P.γr * s * qf s
          · linarith only [Ap2, Ar1, mul_nonneg (sub_nonneg.2 h) hE]
          · push_neg at h
            linarith only [Ap2, Ar2, mul_nonneg (sub_nonneg.2 h.le)
              (show 0 ≤ P.βr - (P.αr + P.αp - P.βp) by linarith)]
        · intro hE
          by_cases h : t ≤ P.γp * s * pf s
          · linarith only [Ap1, Ar1, mul_nonneg (sub_nonneg.2 h) (show 0 ≤ P.αp + P.αr by linarith)]
          · push_neg at h
            linarith only [Ap2, Ar1, mul_nonneg (sub_nonneg.2 h.le) (show 0 ≤ -(P.αr + P.αp - P.βp) by linarith)]
      -- witnesses
      have ETx : ∀ s, s ∈ Set.Icc (0:ℝ) P.sMax →
          (1 - P.γp * s) ∈ Set.Icc (0:ℝ) 1 ∧
          profit P 0 (1 - P.γp * s) (1 - P.γp * s) s = Vx s := by
        intro s hs
        obtain ⟨hx0, hxy, hy, hp, hq, hp1, hq1, hpq⟩ := hbase s hs
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        have Ap := L3 P.αp P.βp (P.γp * s) (1 - P.γp * s) (by linarith)
          (by rw [← hpf s]; linarith only [hp1, mul_nonneg hp.le (show 0 ≤ 1 - 2 * (P.γp * s) by linarith)])
          (by linarith)
        have Ar := L3 P.αr P.βr (P.γr * s) (1 - P.γp * s) (by linarith)
          (by rw [← hqf s]; linarith only [hq1, mul_nonneg hq.le (show 0 ≤ 1 - P.γr * s - P.γp * s by linarith)])
          (by linarith)
        rw [hprof, Ap, Ar, hVx, ← hpf s, ← hqf s]; ring
      have ETy : ∀ s, s ∈ Set.Icc (0:ℝ) P.sMax →
          (1 - P.γr * s) ∈ Set.Icc (0:ℝ) 1 ∧
          profit P 0 (1 - P.γr * s) (1 - P.γr * s) s = Vy s := by
        intro s hs
        obtain ⟨hx0, hxy, hy, hp, hq, hp1, hq1, hpq⟩ := hbase s hs
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        have Ap := L4 P.αp P.βp (P.γp * s) (1 - P.γr * s) (by linarith)
          (by rw [← hpf s]; linarith only [hp1, mul_nonneg hp.le (show 0 ≤ 1 - P.γr * s - P.γp * s by linarith)])
          (by linarith)
        have Ar := L3 P.αr P.βr (P.γr * s) (1 - P.γr * s) (by linarith)
          (by rw [← hqf s]; linarith only [hq1, mul_nonneg hq.le (show 0 ≤ 1 - 2 * (P.γr * s) by linarith)])
          (by linarith)
        rw [hprof, Ap, Ar, hVy, ← hpf s, ← hqf s]; ring
      have EOp : ∀ s, s ∈ Set.Icc (0:ℝ) P.sMax →
          (1 - P.γp * s) ∈ Set.Icc (0:ℝ) 1 ∧
          (1 - P.γp * s * pf s * (1 - P.γr * s)) ∈ Set.Icc (0:ℝ) 1 ∧
          EOConstraint P (1 - P.γp * s) (1 - P.γp * s * pf s * (1 - P.γr * s)) s ∧
          profit P 0 (1 - P.γp * s) (1 - P.γp * s * pf s * (1 - P.γr * s)) s = Wp s := by
        intro s hs
        obtain ⟨hx0, hxy, hy, hp, hq, hp1, hq1, hpq⟩ := hbase s hs
        have hd2 : 0 < 1 - P.γr * s := by linarith
        have hxp : P.γp * s * pf s ≤ 1 := by
          linarith only [hp1, mul_nonneg hp.le (show 0 ≤ 1 - 2 * (P.γp * s) by linarith)]
        have hxp0 : 0 ≤ P.γp * s * pf s := mul_nonneg hx0 hp.le
        have hpy : pf s * (1 - P.γr * s) ≤ 1 := by
          linarith only [hp1, mul_le_mul_of_nonneg_left (show 1 - P.γr * s ≤ 1 - P.γp * s by linarith) hp.le]
        refine ⟨⟨by linarith, by linarith⟩,
          ⟨by linarith only [hxp, mul_nonneg hxp0 (show 0 ≤ P.γr * s by linarith)],
           by linarith only [mul_nonneg hxp0 hd2.le]⟩, ?_, ?_⟩
        · unfold EOConstraint
          rw [show (1:ℝ) - (1 - P.γp * s * pf s * (1 - P.γr * s)) = P.γp * s * pf s * (1 - P.γr * s) by ring,
            mul_div_assoc, div_self hd2.ne', mul_one, hpf]
          ring
        · have Ap := L3 P.αp P.βp (P.γp * s) (1 - P.γp * s) (by linarith)
            (by rw [← hpf s]; linarith only [hp1, mul_nonneg hp.le (show 0 ≤ 1 - 2 * (P.γp * s) by linarith)])
            (by linarith)
          have Ar := L3 P.αr P.βr (P.γr * s) (1 - P.γp * s * pf s * (1 - P.γr * s)) (by linarith)
            (by
              rw [← hqf s]
              have : (1 - (1 - P.γp * s * pf s * (1 - P.γr * s))) * qf s = P.γp * s * pf s := by
                linear_combination (P.γp * s * pf s) * hq1
              rw [this]; exact hxp)
            (by linarith only [hxy, mul_le_mul_of_nonneg_left hpy hx0])
          rw [hprof, Ap, Ar, hWp, ← hpf s, ← hqf s]
          linear_combination (P.αr * (P.γp * s * pf s)) * hq1
      have EOr : ∀ s, s ∈ Set.Icc (0:ℝ) P.sMax →
          (1 - P.γr * s * qf s * (1 - P.γp * s)) ∈ Set.Icc (0:ℝ) 1 ∧
          (1 - P.γr * s) ∈ Set.Icc (0:ℝ) 1 ∧
          EOConstraint P (1 - P.γr * s * qf s * (1 - P.γp * s)) (1 - P.γr * s) s ∧
          profit P 0 (1 - P.γr * s * qf s * (1 - P.γp * s)) (1 - P.γr * s) s = Wr s := by
        intro s hs
        obtain ⟨hx0, hxy, hy, hp, hq, hp1, hq1, hpq⟩ := hbase s hs
        have hd1 : 0 < 1 - P.γp * s := by linarith
        have hyq : P.γr * s * qf s ≤ 1 := by
          linarith only [hq1, mul_nonneg hq.le (show 0 ≤ 1 - 2 * (P.γr * s) by linarith)]
        have hyq0 : 0 ≤ P.γr * s * qf s := mul_nonneg (by linarith) hq.le
        have hqx : 1 ≤ qf s * (1 - P.γp * s) := by
          linarith only [hq1, mul_le_mul_of_nonneg_left (show 1 - P.γr * s ≤ 1 - P.γp * s by linarith) hq.le]
        refine ⟨⟨by linarith only [hyq, mul_nonneg hyq0 hx0], by linarith only [mul_nonneg hyq0 hd1.le]⟩,
          ⟨by linarith, by linarith⟩, ?_, ?_⟩
        · unfold EOConstraint
          rw [show (1:ℝ) - (1 - P.γr * s * qf s * (1 - P.γp * s)) = P.γr * s * qf s * (1 - P.γp * s) by ring,
            mul_div_assoc, div_self hd1.ne', mul_one, hqf]
          ring
        · have Ar := L3 P.αr P.βr (P.γr * s) (1 - P.γr * s) (by linarith)
            (by rw [← hqf s]; linarith only [hq1, mul_nonneg hq.le (show 0 ≤ 1 - 2 * (P.γr * s) by linarith)])
            (by linarith)
          have Ap := L4 P.αp P.βp (P.γp * s) (1 - P.γr * s * qf s * (1 - P.γp * s)) (by linarith)
            (by
              rw [← hpf s]
              have : (1 - (1 - P.γr * s * qf s * (1 - P.γp * s))) * pf s = P.γr * s * qf s := by
                linear_combination (P.γr * s * qf s) * hp1
              rw [this]; exact hyq)
            (by linarith only [hxy, mul_le_mul_of_nonneg_left hqx (show 0 ≤ P.γr * s by linarith)])
          rw [hprof, Ap, Ar, hWr, ← hpf s, ← hqf s]
          linear_combination ((P.αp - P.βp) * (P.γr * s * qf s)) * hp1
      -- main argument
      by_contra hcon
      push_neg at hcon
      obtain ⟨hcET, hsET, hETopt⟩ := hET
      obtain ⟨hcp, hcr, hsEO, hEOc, hEOopt⟩ := hEO
      have kET : ∀ c', c' ∈ Set.Icc (0:ℝ) 1 →
          profit P 0 c' c' sEO - τ sEO ≤ profit P 0 cET cET sET - τ sET :=
        fun c' hc' => hETopt c' sEO hc' hsEO
      have kEO : ∀ cp' cr', cp' ∈ Set.Icc (0:ℝ) 1 → cr' ∈ Set.Icc (0:ℝ) 1 →
          EOConstraint P cp' cr' sET →
          profit P 0 cp' cr' sET - τ sET ≤ profit P 0 cpEO crEO sEO - τ sEO :=
        fun cp' cr' h1 h2 h3 => hEOopt cp' cr' sET h1 h2 hsET h3
      have u1 := ETup cET sET hcET hsET
      obtain ⟨hx1, hxy1, hy1, hp1p, hq1p, hp11, hq11, hpq1⟩ := hbase sET hsET
      obtain ⟨hx2, hxy2, hy2, hp2p, hq2p, hp21, hq21, hpq2⟩ := hbase sEO hsEO
      by_cases hE : 0 ≤ P.αr + P.αp - P.βp
      · have u2 := (EOup cpEO crEO sEO hcp hcr hsEO hEOc).1 hE
        obtain ⟨m1, w1⟩ := ETy sEO hsEO
        have w1' := kET _ m1
        rw [w1] at w1'
        obtain ⟨m2, m3, m4, w2⟩ := EOr sET hsET
        have w2' := kEO _ _ m2 m3 m4
        rw [w2] at w2'
        have hxy1' : Vx sET ≤ Vy sET := by
          have hA : 0 ≤ (P.αp - P.βp) * pf sET + P.αr * qf sET := by
            linarith only [mul_le_mul_of_nonneg_right (show P.βp - P.αp ≤ P.αr by linarith) hq1p.le,
              mul_le_mul_of_nonneg_left hpq1 (show 0 ≤ P.βp - P.αp by linarith)]
          have e : Vy sET - Vx sET = (P.γr * sET - P.γp * sET) *
              ((P.αp - P.βp) * pf sET + P.αr * qf sET) := by rw [hVy, hVx]; ring
          linarith only [e, mul_nonneg (sub_nonneg.2 hxy1) hA]
        have hgap : Vy sET - Wr sET < Vy sEO - Wr sEO := by
          have e : ∀ s, Vy s - Wr s = (P.βp - P.αp) * (P.γr * s * (qf s - pf s)) := by
            intro s; rw [hVy, hWr]; ring
          rw [e, e]
          exact mul_lt_mul_of_pos_left (hstrict sET sEO hsET hsEO hcon).1 (by linarith)
        have hm : max (Vx sET) (Vy sET) = Vy sET := max_eq_right hxy1'
        linarith
      · push_neg at hE
        have u2 := (EOup cpEO crEO sEO hcp hcr hsEO hEOc).2 hE
        obtain ⟨m1, w1⟩ := ETy sEO hsEO
        have w1' := kET _ m1
        rw [w1] at w1'
        obtain ⟨m1x, w1x⟩ := ETx sEO hsEO
        have w1x' := kET _ m1x
        rw [w1x] at w1x'
        obtain ⟨m2, m3, m4, w2⟩ := EOp sET hsET
        have w2' := kEO _ _ m2 m3 m4
        rw [w2] at w2'
        have hh : Vx sET - Wp sET < Vx sEO - Wp sEO := by
          have e : ∀ s, Vx s - Wp s = P.αr * (P.γp * s * (qf s - pf s)) := by
            intro s; rw [hVx, hWp]; ring
          rw [e, e]
          exact mul_lt_mul_of_pos_left (hstrict sET sEO hsET hsEO hcon).2 har
        rcases le_or_gt (Vy sET) (Vx sET) with hc | hc
        · have hm : max (Vx sET) (Vy sET) = Vx sET := max_eq_left hc
          linarith
        · have hm : max (Vx sET) (Vy sET) = Vy sET := max_eq_right hc.le
          have eK : ∀ s, s ∈ Set.Icc (0:ℝ) P.sMax → Vy s - Vx s = (P.γr - P.γp) *
              (s * (P.αr + P.αp - P.βp + s * ((P.βp - P.αp) * P.γr - P.αr * P.γp)) * pf s * qf s) := by
            intro s hs
            obtain ⟨-, -, -, -, -, hp1, hq1, -⟩ := hbase s hs
            rw [hVy, hVx]
            linear_combination (-(P.γr - P.γp) * s * (P.αp - P.βp) * pf s) * hq1
              + (-(P.γr - P.γp) * s * P.αr * qf s) * hp1
          have hc0 : 0 < P.γr - P.γp := by linarith
          have hL1 : 0 < P.αr + P.αp - P.βp + sET * ((P.βp - P.αp) * P.γr - P.αr * P.γp) := by
            by_contra hL
            push_neg at hL
            have h1 := mul_nonpos_of_nonneg_of_nonpos hsET.1 hL
            have h2 := mul_nonpos_of_nonpos_of_nonneg h1 hp1p.le
            have h3 := mul_nonpos_of_nonpos_of_nonneg h2 hq1p.le
            have h4 := mul_nonpos_of_nonneg_of_nonpos hc0.le h3
            linarith [eK sET hsET]
          have hκ : 0 < (P.βp - P.αp) * P.γr - P.αr * P.γp := by
            by_contra hk
            push_neg at hk
            have := mul_nonpos_of_nonneg_of_nonpos hsET.1 hk
            linarith
          have hL12 : P.αr + P.αp - P.βp + sET * ((P.βp - P.αp) * P.γr - P.αr * P.γp)
              ≤ P.αr + P.αp - P.βp + sEO * ((P.βp - P.αp) * P.γr - P.αr * P.γp) := by
            linarith only [mul_le_mul_of_nonneg_right hcon.le hκ.le]
          obtain ⟨hp12, hq12⟩ := hmono sET sEO hsET hsEO hcon.le
          have hs2 : 0 ≤ sEO := hsEO.1
          have hL2 : 0 ≤ P.αr + P.αp - P.βp + sEO * ((P.βp - P.αp) * P.γr - P.αr * P.γp) := by
            linarith
          have g1 := mul_le_mul hcon.le hL12 hL1.le hs2
          have g2 := mul_le_mul g1 hp12 hp1p.le (mul_nonneg hs2 hL2)
          have g3 := mul_le_mul g2 hq12 hq1p.le (mul_nonneg (mul_nonneg hs2 hL2) hp2p.le)
          have g4 := mul_le_mul_of_nonneg_left g3 hc0.le
          have key : Vy sET - Vx sET ≤ Vy sEO - Vx sEO := by
            rw [eK sET hsET, eK sEO hsEO]; exact g4
          linarith
