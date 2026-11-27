-- Prove2me | solution 1 for TwoSidedMatching.Statics.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:13.493806+00:00
-- url     : https://prove2.me/submissions/0928714a-dbc9-44b3-8010-8f4aa0c130b3

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Supplement_Uniform

open TwoSidedMatching
open TwoSidedMatching.Statics
open TwoSidedMatching.Statics.Supplement

/-- All clauses of Theorem 4, with the quantile optimization and its representation bridge. -/
theorem solution (V C : ℝ) (hCV : C < V) :
    (∀ s : ℝ, 0 ≤ s →
      AntitoneOn (fun d => uniformP V C d s) (Set.Icc 0 (turn V C s)) ∧
      MonotoneOn (fun d => uniformP V C d s) (Set.Ici (turn V C s))) ∧
    (∀ d : ℝ, 0 ≤ d → MonotoneOn (fun s => uniformP V C d s) (Set.Ici 0)) ∧
    (∀ d : ℝ, 0 ≤ d →
      MonotoneOn (fun s => uniformW V C d s) (Set.Icc 0 (turn V C d)) ∧
      AntitoneOn (fun s => uniformW V C d s) (Set.Ici (turn V C d))) ∧
    (∀ s : ℝ, 0 ≤ s → AntitoneOn (fun d => uniformW V C d s) (Set.Ici 0)) ∧
    (∀ d₁ s₁ d₂ s₂ : ℝ, 0 ≤ d₁ → 0 ≤ s₁ → 0 ≤ d₂ → 0 ≤ s₂ →
      d₁ + s₁ ≤ d₂ + s₂ → uniformMu V C d₂ s₂ ≤ uniformMu V C d₁ s₁) ∧
    (∀ d₁ s₁ d₂ s₂ : ℝ, 0 ≤ d₁ → 0 ≤ s₁ → 0 ≤ d₂ → 0 ≤ s₂ →
      d₁ + s₁ ≤ d₂ + s₂ → d₂ + s₂ ≤ V - C →
      uniformValue V C d₂ s₂ ≤ uniformValue V C d₁ s₁) ∧
    (∀ d₁ s₁ d₂ s₂ : ℝ, 0 ≤ d₁ → 0 ≤ s₁ → 0 ≤ d₂ → 0 ≤ s₂ →
      V - C ≤ d₁ + s₁ → d₁ + s₁ ≤ d₂ + s₂ →
      uniformValue V C d₁ s₁ ≤ uniformValue V C d₂ s₂) ∧
    (∀ d s : ℝ, 0 ≤ d → 0 ≤ s →
      IsGreatest (uniformOptimizers V C d s) (uniformMu V C d s) ∧
      IsGreatest (uniformObjective V C d s '' Set.Icc 0 1) (uniformValue V C d s) ∧
      uniformMu V C d s =
        (if d + s = 0 then 1 else min ((1 + (V - C) / (d + s)) / 4) 1) ∧
      (d + s ≤ (V - C) / 3 →
        uniformMu V C d s = 1 ∧ uniformP V C d s = V - d ∧
        uniformW V C d s = C + s ∧ uniformValue V C d s = V - C - d - s)) ∧
    (∀ (E : TwoSidedMatching.Statics.Environment) (d s lamD lamS T : ℝ),
      0 < d → 0 < s → 0 ≤ C - s → IsUniformMarket E V C d s →
      0 < T → lamD * T = 1 → lamS * T = 1 →
      TwoSidedMatching.Statics.muStar E lamD lamS T = uniformMu V C d s ∧
      TwoSidedMatching.Statics.pStar E lamD lamS T = uniformP V C d s ∧
      TwoSidedMatching.Statics.wStar E lamD lamS T = uniformW V C d s ∧
      TwoSidedMatching.Statics.fluidValue E lamD lamS T = uniformValue V C d s) := by
        classical
        obtain ⟨a, ha⟩ : ∃ a : ℝ, a = V - C := ⟨_, rfl⟩
        have ha0 : 0 < a := by rw [ha]; linarith
        obtain ⟨m, hm⟩ : ∃ m : ℝ → ℝ, m = fun x => if x = 0 then 1 else min ((1 + a / x) / 4) 1 :=
          ⟨_, rfl⟩
        have hm1 : ∀ x, 0 ≤ x → x ≤ a / 3 → m x = 1 := by
          intro x hx hxa
          rw [hm]
          by_cases h : x = 0
          · simp [h]
          · have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
            simp only [h, if_false]
            apply min_eq_right
            have : 3 ≤ a / x := by rw [le_div_iff₀ hx']; linarith
            linarith
        have hm2 : ∀ x, a / 3 ≤ x → m x = (1 + a / x) / 4 := by
          intro x hxa
          have hx' : 0 < x := by linarith
          rw [hm]
          simp only [hx'.ne', if_false]
          apply min_eq_left
          have : a / x ≤ 3 := by rw [div_le_iff₀ hx']; linarith
          linarith
        have hm2' : ∀ x, a / 3 ≤ x → 4 * x * m x = a + x := by
          intro x hxa
          have hx' : 0 < x := by linarith
          rw [hm2 x hxa]
          field_simp
          ring
        have hmpos : ∀ x, 0 ≤ x → 0 < m x := by
          intro x hx
          rcases le_total x (a / 3) with h | h
          · rw [hm1 x hx h]; norm_num
          · rw [hm2 x h]
            have hx' : 0 < x := by linarith
            positivity
        have hmle : ∀ x, 0 ≤ x → m x ≤ 1 := by
          intro x hx
          rcases le_total x (a / 3) with h | h
          · rw [hm1 x hx h]
          · rw [hm2 x h]
            have hx' : 0 < x := by linarith
            have : a / x ≤ 3 := by rw [div_le_iff₀ hx']; linarith
            linarith
        have hmanti : ∀ x y, 0 ≤ x → x ≤ y → m y ≤ m x := by
          intro x y hx hxy
          rcases le_total x (a / 3) with h | h
          · rw [hm1 x hx h]; exact hmle y (by linarith)
          · rw [hm2 x h, hm2 y (by linarith)]
            have hx' : 0 < x := by linarith
            have : a / y ≤ a / x := div_le_div_of_nonneg_left ha0.le hx' hxy
            linarith
        have hid : ∀ x r, a / 3 ≤ x →
            m x * (a + x - 2 * x * m x) - r * (a + x - 2 * x * r) = 2 * x * (r - m x) ^ 2 := by
          intro x r h
          have := hm2' x h
          linear_combination (m x - r) * this * (-1)
        have hopt : ∀ x r, 0 ≤ x → 0 ≤ r → r ≤ 1 →
            r * (a + x - 2 * x * r) ≤ m x * (a + x - 2 * x * m x) := by
          intro x r hx hr0 hr1
          rcases le_total x (a / 3) with h | h
          · rw [hm1 x hx h]
            nlinarith [mul_nonneg (sub_nonneg.2 hr1)
              (by nlinarith : 0 ≤ a - x - 2 * x * r)]
          · have := hid x r h
            have h2 : 0 ≤ 2 * x * (r - m x) ^ 2 := by positivity
            linarith
        have hobj : ∀ d s q, uniformObjective V C d s q = q * (a + (d + s) - 2 * (d + s) * q) := by
          intro d s q
          simp only [uniformObjective, uniformB, uniformS, ha]
          ring
        have hG : ∀ d s, 0 ≤ d → 0 ≤ s → IsGreatest (uniformOptimizers V C d s) (m (d + s)) := by
          intro d s hd hs
          have hx : 0 ≤ d + s := by linarith
          refine ⟨⟨⟨(hmpos _ hx).le, hmle _ hx⟩, ?_⟩, ?_⟩
          · intro r hr
            rw [hobj, hobj]
            exact hopt _ r hx hr.1 hr.2
          · rintro q ⟨hq, hq2⟩
            rcases le_total (d + s) (a / 3) with h | h
            · rw [hm1 _ hx h]; exact hq.2
            · have h1 := hq2 (m (d + s)) ⟨(hmpos _ hx).le, hmle _ hx⟩
              rw [hobj, hobj] at h1
              have h2 := hid (d + s) q h
              have hx' : 0 < d + s := by linarith
              have h3 : 2 * (d + s) * (q - m (d + s)) ^ 2 ≤ 0 := by linarith
              have h4 : (q - m (d + s)) ^ 2 ≤ 0 := by
                by_contra hc
                push Not at hc
                have : 0 < 2 * (d + s) * (q - m (d + s)) ^ 2 := by positivity
                linarith
              have h5 : q - m (d + s) = 0 := by
                have : (q - m (d + s)) ^ 2 = 0 := le_antisymm h4 (sq_nonneg _)
                exact pow_eq_zero_iff (two_ne_zero) |>.1 this
              linarith
        have hMu : ∀ d s, 0 ≤ d → 0 ≤ s → uniformMu V C d s = m (d + s) := by
          intro d s hd hs
          exact (hG d s hd hs).csSup_eq
        have hGV : ∀ d s, 0 ≤ d → 0 ≤ s → IsGreatest (uniformObjective V C d s '' Set.Icc 0 1)
            (m (d + s) * (a + (d + s) - 2 * (d + s) * m (d + s))) := by
          intro d s hd hs
          have hx : 0 ≤ d + s := by linarith
          refine ⟨⟨m (d + s), ⟨(hmpos _ hx).le, hmle _ hx⟩, hobj _ _ _⟩, ?_⟩
          rintro _ ⟨r, hr, rfl⟩
          rw [hobj]
          exact hopt _ r hx hr.1 hr.2
        have hVal : ∀ d s, 0 ≤ d → 0 ≤ s → uniformValue V C d s =
            m (d + s) * (a + (d + s) - 2 * (d + s) * m (d + s)) := by
          intro d s hd hs
          exact (hGV d s hd hs).csSup_eq
        have hP : ∀ d s, 0 ≤ d → 0 ≤ s → uniformP V C d s = V + (d - 2 * d * m (d + s)) := by
          intro d s hd hs
          simp only [uniformP, uniformB, hMu d s hd hs]
          ring
        have hW : ∀ d s, 0 ≤ d → 0 ≤ s → uniformW V C d s = C - (s - 2 * s * m (s + d)) := by
          intro d s hd hs
          simp only [uniformW, uniformS, hMu d s hd hs, add_comm s d]
          ring
        have hf1 : ∀ d s, 0 ≤ d → 0 ≤ s → d + s ≤ a / 3 → d - 2 * d * m (d + s) = - d := by
          intro d s hd hs h
          rw [hm1 _ (by linarith) h]; ring
        have hf2 : ∀ d₁ d₂ s, a / 3 ≤ d₁ + s → a / 3 ≤ d₂ + s →
            (d₂ - 2 * d₂ * m (d₂ + s)) - (d₁ - 2 * d₁ * m (d₁ + s)) =
              (d₂ - d₁) / 2 * (1 - a * s / ((d₁ + s) * (d₂ + s))) := by
          intro d₁ d₂ s h1 h2
          have h1' : 0 < d₁ + s := by linarith
          have h2' : 0 < d₂ + s := by linarith
          rw [hm2 _ h1, hm2 _ h2]
          field_simp
          ring
        have hturn1 : ∀ s, a / 3 - s ≤ turn V C s := by
          intro s; unfold turn; rw [← ha]
          exact le_trans (le_max_left _ _) (le_max_left _ _)
        have hturn2 : ∀ s, Real.sqrt (a * s) - s ≤ turn V C s := by
          intro s; unfold turn; rw [← ha]
          exact le_trans (le_max_left _ _) (le_max_right _ _)
        have hturn0 : ∀ s, 0 ≤ turn V C s := by
          intro s; unfold turn
          exact le_trans (le_max_right _ _) (le_max_left _ _)
        have hturn3 : ∀ s d, d ≤ turn V C s → d ≤ a / 3 - s ∨ d ≤ 0 ∨ d ≤ Real.sqrt (a * s) - s := by
          intro s d h
          unfold turn at h
          rw [← ha] at h
          rcases le_max_iff.1 h with h | h <;> rcases le_max_iff.1 h with h | h <;> simp [h]
        have hganti : ∀ s, 0 ≤ s → ∀ d₁ d₂, 0 ≤ d₁ → d₁ ≤ d₂ → d₂ ≤ turn V C s →
            d₂ - 2 * d₂ * m (d₂ + s) ≤ d₁ - 2 * d₁ * m (d₁ + s) := by
          intro s hs d₁ d₂ h0 h12 ht
          rcases le_total (d₂ + s) (a / 3) with h | h
          · rw [hf1 d₁ s h0 hs (by linarith), hf1 d₂ s (by linarith) hs h]; linarith
          · have key : ∀ d, 0 ≤ d → a / 3 ≤ d + s → d ≤ d₂ →
                d₂ - 2 * d₂ * m (d₂ + s) ≤ d - 2 * d * m (d + s) := by
              intro d hd hda hd2
              rcases hturn3 s d₂ ht with h' | h' | h'
              · have : d = d₂ := by linarith
                rw [this]
              · have : d = d₂ := by linarith
                rw [this]
              · have := hf2 d d₂ s hda h
                have hxs : 0 < d + s := by linarith
                have hxs2 : 0 < d₂ + s := by linarith
                have hsq : Real.sqrt (a * s) ^ 2 = a * s := Real.sq_sqrt (by positivity)
                have hle : (d + s) * (d₂ + s) ≤ a * s := by
                  rw [← hsq]
                  nlinarith
                have h1 : 1 ≤ a * s / ((d + s) * (d₂ + s)) := by
                  rw [le_div_iff₀ (by positivity)]; linarith
                nlinarith [mul_nonneg (sub_nonneg.2 hd2) (sub_nonneg.2 h1)]
            rcases le_total (d₁ + s) (a / 3) with h' | h'
            · have h3 := key (a / 3 - s) (by linarith) (by linarith) (by linarith)
              rw [hf1 (a / 3 - s) s (by linarith) hs (by linarith)] at h3
              rw [hf1 d₁ s h0 hs h']
              linarith
            · exact key d₁ h0 h' h12
        have hgmono : ∀ s, 0 ≤ s → ∀ d₁ d₂, turn V C s ≤ d₁ → d₁ ≤ d₂ →
            d₁ - 2 * d₁ * m (d₁ + s) ≤ d₂ - 2 * d₂ * m (d₂ + s) := by
          intro s hs d₁ d₂ ht h12
          have h1 := hturn1 s
          have h2 := hturn2 s
          have := hf2 d₁ d₂ s (by linarith) (by linarith)
          have hxs : 0 < d₁ + s := by linarith
          have hxs2 : 0 < d₂ + s := by linarith
          have hsq : Real.sqrt (a * s) ^ 2 = a * s := Real.sq_sqrt (by positivity)
          have hsn : 0 ≤ Real.sqrt (a * s) := Real.sqrt_nonneg _
          have hle : a * s ≤ (d₁ + s) * (d₂ + s) := by
            rw [← hsq]
            nlinarith
          have h1 : a * s / ((d₁ + s) * (d₂ + s)) ≤ 1 := by
            rw [div_le_iff₀ (by positivity)]; linarith
          nlinarith [mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 h1)]
        have hhalf1 : ∀ x, 0 ≤ x → x ≤ a → 1 / 2 ≤ m x := by
          intro x hx hxa
          rcases le_total x (a / 3) with h | h
          · rw [hm1 x hx h]; norm_num
          · rw [hm2 x h]
            have hx' : 0 < x := by linarith
            have : 1 ≤ a / x := by rw [le_div_iff₀ hx']; linarith
            linarith
        have hhalf2 : ∀ x, a ≤ x → m x ≤ 1 / 2 := by
          intro x hxa
          rw [hm2 x (by linarith)]
          have hx' : 0 < x := by linarith
          have : a / x ≤ 1 := by rw [div_le_iff₀ hx']; linarith
          linarith
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro s hs
          constructor
          · intro d₁ h1 d₂ h2 h12
            have := hganti s hs d₁ d₂ h1.1 h12 h2.2
            simp only
            rw [hP d₁ s h1.1 hs, hP d₂ s h2.1 hs]
            linarith
          · intro d₁ h1 d₂ h2 h12
            have h0 := hturn0 s
            have h1' : turn V C s ≤ d₁ := h1
            have := hgmono s hs d₁ d₂ h1' h12
            simp only
            rw [hP d₁ s (by linarith) hs, hP d₂ s (by linarith) hs]
            linarith
        · intro d hd s₁ h1 s₂ h2 h12
          have h1' : 0 ≤ s₁ := h1
          have h2' : 0 ≤ s₂ := h2
          simp only
          rw [hP d s₁ hd h1', hP d s₂ hd h2']
          nlinarith [hmanti (d + s₁) (d + s₂) (by linarith) (by linarith)]
        · intro s hs
          constructor
          · intro d₁ h1 d₂ h2 h12
            have := hganti s hs d₁ d₂ h1.1 h12 h2.2
            simp only
            rw [hW s d₁ hs h1.1, hW s d₂ hs h2.1]
            linarith
          · intro d₁ h1 d₂ h2 h12
            have h0 := hturn0 s
            have h1' : turn V C s ≤ d₁ := h1
            have := hgmono s hs d₁ d₂ h1' h12
            simp only
            rw [hW s d₁ hs (by linarith), hW s d₂ hs (by linarith)]
            linarith
        · intro d hd s₁ h1 s₂ h2 h12
          have h1' : 0 ≤ s₁ := h1
          have h2' : 0 ≤ s₂ := h2
          simp only
          rw [hW s₁ d h1' hd, hW s₂ d h2' hd]
          nlinarith [hmanti (d + s₁) (d + s₂) (by linarith) (by linarith)]
        · intro d₁ s₁ d₂ s₂ h1 h2 h3 h4 h
          rw [hMu _ _ h1 h2, hMu _ _ h3 h4]
          exact hmanti _ _ (by linarith) h
        · intro d₁ s₁ d₂ s₂ h1 h2 h3 h4 h h'
          rw [hVal _ _ h1 h2, hVal _ _ h3 h4]
          rw [← ha] at h'
          have hp := hmpos (d₂ + s₂) (by linarith)
          have hq := hhalf1 (d₂ + s₂) (by linarith) h'
          have ho := hopt (d₁ + s₁) (m (d₂ + s₂)) (by linarith) hp.le (hmle _ (by linarith))
          have : 0 ≤ (m (d₂ + s₂) * (2 * m (d₂ + s₂) - 1)) * ((d₂ + s₂) - (d₁ + s₁)) :=
            mul_nonneg (mul_nonneg hp.le (by linarith)) (by linarith)
          nlinarith
        · intro d₁ s₁ d₂ s₂ h1 h2 h3 h4 h' h
          rw [hVal _ _ h1 h2, hVal _ _ h3 h4]
          rw [← ha] at h'
          have hp := hmpos (d₁ + s₁) (by linarith)
          have hq := hhalf2 (d₁ + s₁) h'
          have ho := hopt (d₂ + s₂) (m (d₁ + s₁)) (by linarith) hp.le (hmle _ (by linarith))
          have : 0 ≤ (m (d₁ + s₁) * (1 - 2 * m (d₁ + s₁))) * ((d₂ + s₂) - (d₁ + s₁)) :=
            mul_nonneg (mul_nonneg hp.le (by linarith)) (by linarith)
          nlinarith
        · intro d s hd hs
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hMu d s hd hs]; exact hG d s hd hs
          · rw [hVal d s hd hs]; exact hGV d s hd hs
          · rw [hMu d s hd hs, hm, ← ha]
          · intro h
            rw [← ha] at h
            have hx : 0 ≤ d + s := by linarith
            rw [hMu d s hd hs, hP d s hd hs, hW d s hd hs, hVal d s hd hs, add_comm s d, hm1 _ hx h, ha]
            refine ⟨rfl, ?_, ?_, ?_⟩ <;> ring
        · intro E d s lamD lamS T hd hs hCs hE hT hlD hlS
          obtain ⟨hloB, hhiB, hloS, hhiS, hfB, hfS⟩ := hE
          have hlam : lamS = lamD := by
            have : (lamS - lamD) * T = 0 := by linarith
            rcases mul_eq_zero.1 this with h | h
            · linarith
            · exact absurd h hT.ne'
          subst hlam
          have hx : 0 < d + s := by linarith
          have hlpos : 0 < lamS := by
            refine pos_of_mul_pos_left ?_ hT.le
            rw [hlS]; exact one_pos
          have hcdfB : ∀ y ∈ Set.Icc (V - d) (V + d), E.cdfB y = (y - (V - d)) / (2 * d) := by
            intro y hy
            unfold MechanismDesign.BilateralTrade.Environment.cdfB
            have : ∫ z in E.loB..y, E.fB z = ∫ z in E.loB..y, (1 / (2 * d)) := by
              apply intervalIntegral.integral_congr
              intro z hz
              rw [hloB, Set.uIcc_of_le hy.1] at hz
              exact hfB z ⟨by rw [hloB]; exact hz.1, by rw [hhiB]; exact hz.2.trans hy.2⟩
            rw [this, intervalIntegral.integral_const, hloB, smul_eq_mul]
            ring
          have hcdfS : ∀ y ∈ Set.Icc (C - s) (C + s), E.cdfS y = (y - (C - s)) / (2 * s) := by
            intro y hy
            unfold MechanismDesign.BilateralTrade.Environment.cdfS
            have : ∫ z in E.loS..y, E.fS z = ∫ z in E.loS..y, (1 / (2 * s)) := by
              apply intervalIntegral.integral_congr
              intro z hz
              rw [hloS, Set.uIcc_of_le hy.1] at hz
              exact hfS z ⟨by rw [hloS]; exact hz.1, by rw [hhiS]; exact hz.2.trans hy.2⟩
            rw [this, intervalIntegral.integral_const, hloS, smul_eq_mul]
            ring
          have hclB : ∀ p, max E.loB (min p E.hiB) ∈ Set.Icc (V - d) (V + d) := by
            intro p
            rw [hloB, hhiB]
            exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
          have hclS : ∀ p, max E.loS (min p E.hiS) ∈ Set.Icc (C - s) (C + s) := by
            intro p
            rw [hloS, hhiS]
            exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
          have hFB : ∀ p, FdBar E p = (V + d - max (V - d) (min p (V + d))) / (2 * d) := by
            intro p
            have := hcdfB _ (hclB p)
            unfold FdBar Fd
            rw [this, hloB, hhiB]
            field_simp
            ring
          have hFS : ∀ p, Fs E p = (max (C - s) (min p (C + s)) - (C - s)) / (2 * s) := by
            intro p
            have := hcdfS _ (hclS p)
            unfold Fs
            rw [this, hloS, hhiS]
          have hFBin : ∀ p ∈ Set.Icc (V - d) (V + d), FdBar E p = (V + d - p) / (2 * d) := by
            intro p hp
            rw [hFB, min_eq_left hp.2, max_eq_right hp.1]
          have hFSin : ∀ p ∈ Set.Icc (C - s) (C + s), Fs E p = (p - (C - s)) / (2 * s) := by
            intro p hp
            rw [hFS, min_eq_left hp.2, max_eq_right hp.1]
          have hBmem : ∀ q, 0 ≤ q → q ≤ 1 → V + d - 2 * d * q ∈ Set.Icc (V - d) (V + d) := by
            intro q h0 h1
            have e1 := mul_nonneg hd.le h0
            have e2 := mul_nonneg hd.le (sub_nonneg.2 h1)
            constructor <;> linarith only [e1, e2]
          have hSmem : ∀ q, 0 ≤ q → q ≤ 1 → C - s + 2 * s * q ∈ Set.Icc (C - s) (C + s) := by
            intro q h0 h1
            have e1 := mul_nonneg hs.le h0
            have e2 := mul_nonneg hs.le (sub_nonneg.2 h1)
            constructor <;> linarith only [e1, e2]
          have hBq : ∀ q, 0 ≤ q → q ≤ 1 → FdBar E (V + d - 2 * d * q) = q := by
            intro q h0 h1
            rw [hFBin _ (hBmem q h0 h1)]
            field_simp
            ring
          have hSq : ∀ q, 0 ≤ q → q ≤ 1 → Fs E (C - s + 2 * s * q) = q := by
            intro q h0 h1
            rw [hFSin _ (hSmem q h0 h1)]
            field_simp
            ring
          have hBinv : ∀ q, 0 ≤ q → q ≤ 1 → FdBarInv E q = V + d - 2 * d * q := by
            intro q h0 h1
            apply IsLeast.csInf_eq
            refine ⟨⟨by rw [hloB, hhiB]; exact hBmem q h0 h1, (hBq q h0 h1).le⟩, ?_⟩
            rintro p ⟨hp, hpq⟩
            rw [hloB, hhiB] at hp
            rw [hFBin p hp, div_le_iff₀ (by linarith)] at hpq
            linarith
          have hSinv : ∀ q, 0 ≤ q → q ≤ 1 → FsInv E q = C - s + 2 * s * q := by
            intro q h0 h1
            apply IsLeast.csInf_eq
            refine ⟨⟨by rw [hloS, hhiS]; exact hSmem q h0 h1, (hSq q h0 h1).ge⟩, ?_⟩
            rintro p ⟨hp, hpq⟩
            rw [hloS, hhiS] at hp
            rw [hFSin p hp, le_div_iff₀ (by linarith)] at hpq
            linarith
          have hVV : ∀ q, 0 ≤ q → q ≤ 1 →
              TwoSidedMatching.Statics.V E lamS lamS T q = a + (d + s) - 4 * (d + s) * q := by
            intro q h0 h1
            unfold TwoSidedMatching.Statics.V
            rw [hlS, div_one, hBinv q h0 h1, hSinv q h0 h1]
            unfold MechanismDesign.BilateralTrade.Environment.psiB
              MechanismDesign.BilateralTrade.Environment.psiS
            have e1 := hBmem q h0 h1
            have e2 := hSmem q h0 h1
            rw [hcdfB _ e1, hcdfS _ e2, hfB _ (by rw [hloB, hhiB]; exact e1),
              hfS _ (by rw [hloS, hhiS]; exact e2), ha]
            field_simp
            ring
          have hmu0 := hmpos (d + s) hx.le
          have hmu1 := hmle (d + s) hx.le
          have hmux : 4 * (d + s) * m (d + s) ≤ a + (d + s) := by
            rcases le_total (d + s) (a / 3) with h | h
            · rw [hm1 _ hx.le h]; linarith
            · exact (hm2' _ h).le
          have hmuS : TwoSidedMatching.Statics.muStar E lamS lamS T = m (d + s) := by
            apply IsGreatest.csSup_eq
            rw [hlS, min_self]
            refine ⟨⟨⟨hmu0.le, hmu1⟩, ?_⟩, ?_⟩
            · rw [hVV _ hmu0.le hmu1]; linarith
            · rintro q ⟨hq, hq2⟩
              rw [hVV _ hq.1 hq.2] at hq2
              rcases le_total (d + s) (a / 3) with h | h
              · rw [hm1 _ hx.le h]; exact hq.2
              · have := hm2' _ h
                refine le_of_mul_le_mul_left (a := 4 * (d + s)) ?_ (by linarith only [hx])
                linarith only [this, hq2]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hmuS, hMu d s hd.le hs.le]
          · unfold pStar
            rw [hmuS, hlS, div_one, hBinv _ hmu0.le hmu1, hP d s hd.le hs.le]; ring
          · unfold wStar
            rw [hmuS, hlS, div_one, hSinv _ hmu0.le hmu1, hW d s hd.le hs.le, add_comm s d]; ring
          · rw [hVal d s hd.le hs.le]
            apply IsGreatest.csSup_eq
            constructor
            · refine ⟨fun _ => (V + d - 2 * d * m (d + s), C - s + 2 * s * m (d + s)), ?_, ?_⟩
              · refine ⟨measurable_const, ?_, ?_, ?_⟩
                · intro t ht
                  simp only
                  refine ⟨?_, ?_, ?_⟩
                  · have := mul_nonneg hs.le hmu0.le
                    linarith only [this, hmux, ha, hCs, mul_pos hx hmu0, hd, hx, ha0]
                  · have := mul_nonneg hs.le hmu0.le
                    linarith only [this, hCs]
                  · rw [hBq _ hmu0.le hmu1, hSq _ hmu0.le hmu1]
                · exact intervalIntegrable_const
                · exact intervalIntegrable_const
              · unfold fluidObjective
                simp only
                rw [hBq _ hmu0.le hmu1, hSq _ hmu0.le hmu1, intervalIntegral.integral_const,
                  intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul, ha]
                linear_combination (-1 : ℝ) * (m (d + s) * (V - C + (d + s) - 2 * (d + s) * m (d + s))) * hlS
            · rintro v ⟨π, ⟨hπm, hπ, hi1, hi2⟩, rfl⟩
              unfold fluidObjective
              rw [← intervalIntegral.integral_sub hi1 hi2]
              have hpt : ∀ t ∈ Set.Icc 0 T,
                  lamS * (π t).1 * FdBar E (π t).1 - lamS * (π t).2 * Fs E (π t).2 ≤
                    lamS * (m (d + s) * (a + (d + s) - 2 * (d + s) * m (d + s))) := by
                intro t ht
                obtain ⟨-, -, hbal⟩ := hπ t ht
                have hq := mul_left_cancel₀ hlpos.ne' hbal
                obtain ⟨p, hp⟩ : ∃ p, p = (π t).1 := ⟨_, rfl⟩
                obtain ⟨w, hw⟩ : ∃ w, w = (π t).2 := ⟨_, rfl⟩
                obtain ⟨q, hqd⟩ : ∃ q, q = FdBar E (π t).1 := ⟨_, rfl⟩
                rw [← hq, ← hqd, ← hp, ← hw]
                have hqB : q * (2 * d) = V + d - max (V - d) (min p (V + d)) := by
                  rw [hqd, hFB, ← hp, div_mul_cancel₀ _ (by linarith only [hd])]
                have hqS : q * (2 * s) = max (C - s) (min w (C + s)) - (C - s) := by
                  rw [hqd, hq, hFS, ← hw, div_mul_cancel₀ _ (by linarith only [hs])]
                have hc1 := hclB p
                have hc2 := hclS w
                rw [hloB, hhiB] at hc1
                rw [hloS, hhiS] at hc2
                have h2d : 0 < 2 * d := by linarith only [hd]
                have h2s : 0 < 2 * s := by linarith only [hs]
                have hq0 : 0 ≤ q := by
                  rw [hqd, hFB, ← hp]
                  exact div_nonneg (by linarith only [hc1.2]) h2d.le
                have hq1 : q ≤ 1 := by
                  rw [hqd, hFB, ← hp]
                  exact (div_le_one h2d).2 (by linarith only [hc1.1])
                have hqp : q * p ≤ q * (V + d - 2 * d * q) := by
                  rcases hq0.eq_or_lt with h | h
                  · rw [← h]; simp
                  · apply mul_le_mul_of_nonneg_left _ hq0
                    have e : max (V - d) (min p (V + d)) < V + d := by
                      have := mul_pos h h2d
                      linarith only [this, hqB]
                    have e2 : p ≤ max (V - d) (min p (V + d)) := by
                      have e3 := lt_of_le_of_lt (le_max_right _ _) e
                      have e4 : p < V + d := by
                        rcases min_lt_iff.1 e3 with h | h
                        · exact h
                        · exact absurd h (lt_irrefl _)
                      rw [min_eq_left e4.le]
                      exact le_max_right _ _
                    linarith only [e2, hqB]
                have hqw : q * (C - s + 2 * s * q) ≤ q * w := by
                  rcases hq0.eq_or_lt with h | h
                  · rw [← h]; simp
                  · apply mul_le_mul_of_nonneg_left _ hq0
                    have e : C - s < max (C - s) (min w (C + s)) := by
                      have := mul_pos h h2s
                      linarith only [this, hqS]
                    have e2 : max (C - s) (min w (C + s)) ≤ w := by
                      rcases lt_max_iff.1 e with h | h
                      · exact absurd h (lt_irrefl _)
                      · rw [max_eq_right h.le]; exact min_le_left _ _
                    linarith only [e2, hqS]
                have ho := hopt (d + s) q hx.le hq0 hq1
                have : q * p - q * w ≤ m (d + s) * (a + (d + s) - 2 * (d + s) * m (d + s)) := by
                  rw [ha] at ho ⊢
                  linarith only [ho, hqp, hqw]
                calc lamS * p * q - lamS * w * q = lamS * (q * p - q * w) := by ring
                  _ ≤ _ := mul_le_mul_of_nonneg_left this hlpos.le
              have := intervalIntegral.integral_mono_on hT.le (hi1.sub hi2)
                (intervalIntegrable_const (μ := MeasureTheory.volume) (c := lamS * (m (d + s) * (a + (d + s) - 2 * (d + s) * m (d + s))))) hpt
              rw [intervalIntegral.integral_const, smul_eq_mul] at this
              refine this.trans (le_of_eq ?_)
              linear_combination (m (d + s) * (a + (d + s) - 2 * (d + s) * m (d + s))) * hlS
