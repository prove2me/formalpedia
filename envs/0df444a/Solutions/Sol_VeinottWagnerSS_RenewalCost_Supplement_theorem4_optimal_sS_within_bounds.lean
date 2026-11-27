-- Prove2me | solution 1 for VeinottWagnerSS.RenewalCost.Supplement.theorem4_optimal_sS_within_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:54.006827+00:00
-- url     : https://prove2.me/submissions/e330bb9c-536b-4381-ad40-1becef6284c0

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers
import Definitions.Def_VeinottWagnerSS_RenewalCost_Supplement_InfiniteHorizon

open scoped ENNReal

open VeinottWagnerSS
open VeinottWagnerSS.RenewalCost
open VeinottWagnerSS.RenewalCost.Supplement

open VeinottWagnerSS.Bounds

/-- Theorem 4, p. 549 (proof: Appendix §2, p. 550), both parts.
(a) For the `n`-period model (`n = 2, 3, ⋯`) there exists an optimal `(s, S)` policy whose
first-period rule `(s_n, S_n)` satisfies `s̲ ≤ s_n ≤ s̄ ≤ S̲ ≤ S_n ≤ S̄`.
(b) For the infinite period model (discounted for `0 ≤ α < 1`, average cost for `α = 1`) there
exists an optimal stationary policy `(s*, S*)` with `s̲ ≤ s* ≤ s̄ ≤ S̲ ≤ S* ≤ S̄`.
Optimality is against every admissible (history-dependent) policy and for every initial level.
`S̲ = SLow G`, `S̄ = SHigh G K α`, `s̲ = sLow G K`, `s̄ = sHigh G K α` (p. 537, (21)–(23)). -/
theorem solution (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (hφ0 : α * (φ 0).toReal < 1) :
    (∀ n : ℕ, 2 ≤ n →
      ∃ (Y : Policy) (sn Sn : ℤ), IsOptimal φ G K α n Y ∧ IsSSPolicy n Y ∧
        sn ≤ Sn ∧ UsesRule Y 0 sn Sn ∧
        sLow G K ≤ sn ∧ sn ≤ sHigh G K α ∧ sHigh G K α ≤ SLow G ∧
        SLow G ≤ Sn ∧ Sn ≤ SHigh G K α) ∧
    (∃ sStar SStar : ℤ, IsInfOptimal φ G K α (stationary sStar SStar) ∧
        sLow G K ≤ sStar ∧ sStar ≤ sHigh G K α ∧ sHigh G K α ≤ SLow G ∧
        SLow G ≤ SStar ∧ SStar ≤ SHigh G K α) := by
          set_option maxHeartbeats 1000000 in
            have hbdd : ∀ c : ℝ, BddBelow {y : ℤ | G y ≤ c} := by
              intro c
              obtain ⟨N, hN⟩ := Filter.eventually_atBot.1 (hG_bot.eventually (Filter.eventually_gt_atTop c))
              refine ⟨N, fun y hy => ?_⟩
              by_contra h
              push Not at h
              exact absurd (hN y h.le) (not_lt.2 hy)
            have hmin : ∃ m : ℤ, ∀ z, G m ≤ G z := by
              obtain ⟨N, hN⟩ := Filter.eventually_atBot.1 (hG_bot.eventually (Filter.eventually_gt_atTop (G 0)))
              obtain ⟨P, hP⟩ := Filter.eventually_atTop.1 (hG_top.eventually (Filter.eventually_gt_atTop (G 0)))
              have hfin : (Finset.Icc (min N 0) (max P 0)).Nonempty := ⟨0, by simp⟩
              obtain ⟨m, hm, hmm⟩ := Finset.exists_min_image _ G hfin
              refine ⟨m, fun z => ?_⟩
              by_cases hz : z ∈ Finset.Icc (min N 0) (max P 0)
              · exact hmm z hz
              · have h0 : G m ≤ G 0 := hmm 0 (by simp)
                simp only [Finset.mem_Icc, not_and_or, not_le] at hz
                rcases hz with hz | hz
                · exact h0.trans (hN z (le_of_lt (lt_of_lt_of_le hz (min_le_left _ _)))).le
                · exact h0.trans (hP z (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hz))).le
            have hMne : ({y : ℤ | ∀ z : ℤ, G y ≤ G z}).Nonempty := hmin
            have hMbdd : BddBelow {y : ℤ | ∀ z : ℤ, G y ≤ G z} := by
              obtain ⟨m, hm⟩ := hmin
              exact (hbdd (G m)).mono (fun y hy => hy m)
            have hSLmem : ∀ z, G (SLow G) ≤ G z := Int.csInf_mem hMne hMbdd
            have hsHmemset : ({y : ℤ | G y ≤ G (SLow G) + (1 - α) * K}).Nonempty :=
              ⟨SLow G, by simp only [Set.mem_ofPred_eq]; nlinarith⟩
            have hsH_le : sHigh G K α ≤ SLow G :=
              csInf_le (hbdd _) (by simp only [Set.mem_ofPred_eq]; nlinarith)
            have hsHmem : G (sHigh G K α) ≤ G (SLow G) + (1 - α) * K := Int.csInf_mem hsHmemset (hbdd _)
            have hsL_le : sLow G K ≤ sHigh G K α :=
              csInf_le (hbdd _) (by simp only [Set.mem_ofPred_eq]; nlinarith)
            have hSH_ne : ({y : ℤ | SLow G ≤ y ∧ G (SLow G) + α * K ≤ G (y + 1)}).Nonempty := by
              obtain ⟨P, hP⟩ := Filter.eventually_atTop.1
                (hG_top.eventually (Filter.eventually_ge_atTop (G (SLow G) + α * K)))
              exact ⟨max P (SLow G), le_max_right _ _, hP _ (by omega)⟩
            have hSL_le : SLow G ≤ SHigh G K α := le_csInf hSH_ne (fun y hy => hy.1)
            have hw_snoc : ∀ (t : ℕ) (h' : Fin t → ℕ) (k : ℕ),
                weight φ (Fin.snoc h' k : Fin (t+1) → ℕ) = weight φ h' * φ k := by
              intro t h' k
              simp [weight, Fin.prod_univ_castSucc]
            have hsum_snoc : ∀ (t : ℕ) (f : (Fin (t+1) → ℕ) → ℝ≥0∞),
                ∑' h, f h = ∑' k, ∑' (h' : Fin t → ℕ), f (Fin.snoc h' k) := by
              intro t f
              rw [← (Fin.snocEquiv (fun _ => ℕ)).tsum_eq]
              exact ENNReal.tsum_prod (f := fun k h' => f (Fin.snoc h' k))
            have hw_one : ∀ t, ∑' (h : Fin t → ℕ), weight φ h = 1 := by
              intro t
              induction t with
              | zero => simp [weight]
              | succ t ih =>
                rw [hsum_snoc]
                simp_rw [hw_snoc, ENNReal.tsum_mul_right, ih, one_mul]
                exact φ.tsum_coe
            have hdiff : Monotone (fun y : ℤ => G (y + 1) - G y) := by
              apply monotone_int_of_le_succ
              intro y
              simpa [show y + 1 + 1 = y + 2 by omega] using hconv y
            have hG_right : MonotoneOn G (Set.Ici (SLow G)) := by
              apply monotoneOn_of_le_add_one (s := Set.Ici (SLow G)) (Set.ordConnected_Ici)
              intro y _ hy _
              have h₀ := hSLmem (SLow G + 1)
              have h₁ := hdiff hy
              dsimp at h₁
              linarith
            have hG_left : AntitoneOn G (Set.Iic (SLow G)) := by
              apply antitoneOn_of_add_one_le (s := Set.Iic (SLow G)) (Set.ordConnected_Iic)
              intro y _ _ hy
              have h₀ := hSLmem (SLow G - 1)
              have h₁ := hdiff (show y ≤ SLow G - 1 by simpa using hy)
              dsimp at h₁
              have heq : SLow G - 1 + 1 = SLow G := by omega
              rw [heq] at h₁
              linarith
            have hstat_rule : ∀ s S t, UsesRule (stationary s S) t s S := by
              intro s S t x h
              cases t <;> rfl
            have hstat_adm : ∀ s S : ℤ, s ≤ S → Admissible (stationary s S) := by
              intro s S hs t x h
              rw [hstat_rule s S t x h]
              unfold sSRule
              split_ifs with hlt
              · omega
              · rfl
            let KC : (ℤ → ℝ) → Prop := fun F => ∀ x y z : ℤ, x ≤ y → y ≤ z →
              ((z - x : ℤ) : ℝ) * (F y - F x) ≤ ((y - x : ℤ) : ℝ) * (F z - F x + K)
            have hsec_up : ∀ x y : ℤ, x ≤ y →
                G y - G x ≤ ((y - x : ℤ) : ℝ) * (G (y + 1) - G y) := by
              intro x y hxy
              induction y, hxy using Int.leInduction with
              | base => simp
              | succ y hxy ih =>
                have hd := hdiff (show y ≤ y + 1 by omega)
                have hn : (0 : ℝ) ≤ ((y - x : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hxy
                have hm := mul_le_mul_of_nonneg_left hd hn
                dsimp at hm
                push_cast at *
                nlinarith only [ih,hd,hm]
            have hsec_low : ∀ x y : ℤ, x ≤ y →
                ((y - x : ℤ) : ℝ) * (G (x + 1) - G x) ≤ G y - G x := by
              intro x y hxy
              induction y, hxy using Int.leInduction with
              | base => simp
              | succ y hxy ih =>
                have hd := hdiff hxy
                dsimp at hd
                push_cast at *
                nlinarith only [ih,hd]
            have hG_C : ∀ x y z : ℤ, x ≤ y → y ≤ z →
                ((z - x : ℤ) : ℝ) * (G y - G x) ≤ ((y - x : ℤ) : ℝ) * (G z - G x) := by
              intro x y z hxy hyz
              have h₁ := mul_le_mul_of_nonneg_left (hsec_up x y hxy)
                (show (0 : ℝ) ≤ ((z - y : ℤ) : ℝ) by exact_mod_cast sub_nonneg.mpr hyz)
              have h₂ := mul_le_mul_of_nonneg_left (hsec_low y z hyz)
                (show (0 : ℝ) ≤ ((y - x : ℤ) : ℝ) by exact_mod_cast sub_nonneg.mpr hxy)
              push_cast at *
              nlinarith only [h₁,h₂]
            have hsLm : sLow G K ≤ SLow G := hsL_le.trans hsH_le
            have hsL_strict : ∀ x : ℤ, x < sLow G K → G (SLow G) + K < G x := by
              intro x hx
              by_contra h
              have hm : sLow G K ≤ x := csInf_le (hbdd _) (le_of_not_gt h)
              omega
            have hselection : ∀ F : ℤ → ℝ, KC F →
                Filter.Tendsto F Filter.atTop Filter.atTop →
                Filter.Tendsto F Filter.atBot Filter.atTop →
                ∃ s S : ℤ, s ≤ S ∧
                  (∀ x y : ℤ, x ≤ y →
                    (if x < sSRule s S x then K else 0) + F (sSRule s S x) ≤
                      (if x < y then K else 0) + F y) ∧
                  KC (fun x => if x < s then K + F S else F x) ∧
                  (∀ x, F S ≤ if x < s then K + F S else F x) ∧
                  (∀ a : ℤ, ∃ C : ℝ, ∀ x ≤ a, (if x < s then K + F S else F x) ≤ C) ∧
                  (∀ z, F S ≤ F z) ∧ (∀ x < s, F S + K < F x) ∧ F s ≤ F S + K := by
              intro F hF hFt hFb
              have hb : ∀ c : ℝ, BddBelow {y : ℤ | F y ≤ c} := by
                intro c
                obtain ⟨N, hN⟩ := Filter.eventually_atBot.1
                  (hFb.eventually (Filter.eventually_gt_atTop c))
                refine ⟨N, fun y hy => ?_⟩
                by_contra h
                push Not at h
                exact absurd (hN y h.le) (not_lt.2 hy)
              obtain ⟨N, hN⟩ := Filter.eventually_atBot.1
                (hFb.eventually (Filter.eventually_gt_atTop (F 0)))
              obtain ⟨P, hP⟩ := Filter.eventually_atTop.1
                (hFt.eventually (Filter.eventually_gt_atTop (F 0)))
              obtain ⟨S, hSmem, hSmin⟩ := Finset.exists_min_image
                (Finset.Icc (min N 0) (max P 0)) F (show (Finset.Icc (min N 0) (max P 0)).Nonempty from ⟨0, by simp⟩)
              have hS : ∀ z, F S ≤ F z := by
                intro z
                by_cases hz : z ∈ Finset.Icc (min N 0) (max P 0)
                · exact hSmin z hz
                · have h0 : F S ≤ F 0 := hSmin 0 (by simp)
                  simp only [Finset.mem_Icc, not_and_or, not_le] at hz
                  rcases hz with hz | hz
                  · exact h0.trans (hN z (le_of_lt (lt_of_lt_of_le hz (min_le_left _ _)))).le
                  · exact h0.trans (hP z (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hz))).le
              let s : ℤ := sInf {y : ℤ | F y ≤ F S + K}
              have hne : ({y : ℤ | F y ≤ F S + K}).Nonempty := ⟨S, by dsimp; linarith⟩
              have hsS : s ≤ S := csInf_le (hb _) (by dsimp; linarith)
              have hs : F s ≤ F S + K := Int.csInf_mem hne (hb _)
              have hbefore : ∀ x < s, F S + K < F x := by
                intro x hx
                by_contra hn
                have hle : s ≤ x := csInf_le (hb _) (le_of_not_gt hn)
                omega
              have hbetween : ∀ x, s ≤ x → x ≤ S → F x ≤ F S + K := by
                intro x hsx hxS
                by_cases heq : s = S
                · have hx : x = S := by omega
                  rw [hx]
                  linarith
                · have h := hF s x S hsx hxS
                  have hmul := mul_nonneg
                    (show (0 : ℝ) ≤ ((S - x : ℤ) : ℝ) by exact_mod_cast sub_nonneg.mpr hxS)
                    (sub_nonneg.mpr hs)
                  have hpos : (0 : ℝ) < ((S - s : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr (lt_of_le_of_ne hsS heq)
                  push_cast at *
                  nlinarith only [h,hmul,hpos]
              have hafter : ∀ x y, S ≤ x → x ≤ y → F x ≤ F y + K := by
                intro x y hSx hxy
                by_cases heq : y = S
                · have hx : x = S := by omega
                  rw [hx, heq]
                  linarith
                · have h := hF S x y hSx hxy
                  have hmul := mul_nonneg
                    (show (0 : ℝ) ≤ ((y - x : ℤ) : ℝ) by exact_mod_cast sub_nonneg.mpr hxy)
                    (show 0 ≤ F y - F S + K by linarith [hS y])
                  have hpos : (0 : ℝ) < ((y - S : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr (by omega : S < y)
                  push_cast at *
                  nlinarith only [h,hmul,hpos]
              refine ⟨s, S, hsS, ?_, ?_, ?_, ?_, hS, hbefore, hs⟩
              · intro x y hxy
                by_cases hx : x < s
                · rw [sSRule, if_pos hx, if_pos (lt_of_lt_of_le hx hsS)]
                  by_cases hlt : x < y
                  · rw [if_pos hlt]
                    linarith [hS y]
                  · have heq : y = x := by omega
                    rw [heq, if_neg (lt_irrefl x)]
                    linarith [hbefore x hx]
                · rw [sSRule, if_neg hx, if_neg (lt_irrefl x), zero_add]
                  by_cases hlt : x < y
                  · rw [if_pos hlt]
                    by_cases hxS : x ≤ S
                    · linarith [hbetween x (le_of_not_gt hx) hxS, hS y]
                    · linarith [hafter x y (le_of_not_ge hxS) hxy]
                  · have heq : y = x := by omega
                    simp [heq]
              · intro x y z hxy hyz
                by_cases hx : x < s
                · by_cases hy : y < s
                  · by_cases hz : z < s
                    · simp only [if_pos hx, if_pos hy, if_pos hz, sub_self, mul_zero, zero_add]
                      exact mul_nonneg (by exact_mod_cast sub_nonneg.mpr hxy) hK
                    · simp only [if_pos hx, if_pos hy, if_neg hz, sub_self, mul_zero]
                      apply mul_nonneg (by exact_mod_cast sub_nonneg.mpr hxy)
                      linarith [hS z]
                  · have hz : ¬z < s := by omega
                    simp only [if_pos hx, if_neg hy, if_neg hz]
                    by_cases hyS : y ≤ S
                    · have hl := mul_nonpos_of_nonneg_of_nonpos
                        (show (0 : ℝ) ≤ ((z - x : ℤ) : ℝ) by exact_mod_cast sub_nonneg.mpr (hxy.trans hyz))
                        (show F y - (K + F S) ≤ 0 by linarith [hbetween y (le_of_not_gt hy) hyS])
                      have hr := mul_nonneg
                        (show (0 : ℝ) ≤ ((y - x : ℤ) : ℝ) by exact_mod_cast sub_nonneg.mpr hxy)
                        (show 0 ≤ F z - (K + F S) + K by linarith [hS z])
                      exact hl.trans hr
                    · have h := hF S y z (le_of_not_ge hyS) hyz
                      have hD : 0 ≤ F z + K - F y := by linarith [hafter y z (le_of_not_ge hyS) hyz]
                      have hm₁ := mul_nonneg
                        (show (0 : ℝ) ≤ ((S - x : ℤ) : ℝ) by exact_mod_cast sub_nonneg.mpr (by omega : x ≤ S)) hD
                      have hm₂ := mul_nonneg
                        (show (0 : ℝ) ≤ ((z - y : ℤ) : ℝ) by exact_mod_cast sub_nonneg.mpr hyz) hK
                      push_cast at *
                      nlinarith only [h,hm₁,hm₂]
                · have hy : ¬y < s := by omega
                  have hz : ¬z < s := by omega
                  simpa only [if_neg hx, if_neg hy, if_neg hz] using hF x y z hxy hyz
              · intro x
                split_ifs <;> linarith [hS x]
              · intro a
                obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image (Finset.Icc s (max s a)) F
                  (show (Finset.Icc s (max s a)).Nonempty from ⟨s, by simp⟩)
                refine ⟨max (K + F S) (F b), fun x hxa => ?_⟩
                split_ifs with hx
                · exact le_max_left _ _
                · exact (hmax x (by simp only [Finset.mem_Icc]; omega)).trans (le_max_right _ _)
            let PB : (ℤ → ℝ) → Prop := fun V =>
              (∃ L : ℝ, ∀ x, L ≤ V x) ∧ (∀ a : ℤ, ∃ C : ℝ, ∀ x ≤ a, V x ≤ C)
            let Ex : (ℤ → ℝ) → ℤ → ℝ := fun V y =>
              ∫ k : ℕ, V (y - (k : ℤ)) ∂φ.toMeasure
            have hEx_int : ∀ V : ℤ → ℝ, PB V → ∀ y : ℤ,
                MeasureTheory.Integrable (fun k : ℕ => V (y - (k : ℤ))) φ.toMeasure := by
              intro V hV y
              obtain ⟨⟨L, hL⟩, hU⟩ := hV
              obtain ⟨C, hC⟩ := hU y
              apply (MeasureTheory.integrable_const (max |L| |C|)).mono'
                (measurable_of_countable _).aestronglyMeasurable
              apply Filter.Eventually.of_forall
              intro k
              rw [Real.norm_eq_abs, abs_le]
              constructor
              · have ha : -max |L| |C| ≤ L := by
                  have h₁ := neg_abs_le L
                  have h₂ := le_max_left |L| |C|
                  linarith
                exact ha.trans (hL _)
              · exact (hC _ (by omega)).trans ((le_abs_self C).trans (le_max_right _ _))
            have hEx_lower : ∀ V : ℤ → ℝ, PB V → ∀ L : ℝ, (∀ x, L ≤ V x) →
                ∀ y, L ≤ Ex V y := by
              intro V hV L hL y
              have h := MeasureTheory.integral_mono (MeasureTheory.integrable_const L) (hEx_int V hV y)
                (fun k : ℕ => hL (y - (k : ℤ)))
              simpa [Ex] using h
            have hEx_upper : ∀ V : ℤ → ℝ, PB V → ∀ y C, (∀ x ≤ y, V x ≤ C) →
                Ex V y ≤ C := by
              intro V hV y C hC
              have h := MeasureTheory.integral_mono (hEx_int V hV y) (MeasureTheory.integrable_const C)
                (fun k : ℕ => hC (y - (k : ℤ)) (by omega))
              simpa [Ex] using h
            have hEx_KC : ∀ V : ℤ → ℝ, KC V → PB V → KC (Ex V) := by
              intro V hV hB x y z hxy hyz
              have hiX := hEx_int V hB x
              have hiY := hEx_int V hB y
              have hiZ := hEx_int V hB z
              have hiZX : MeasureTheory.Integrable (fun k : ℕ => V (z - (k : ℤ)) - V (x - (k : ℤ))) φ.toMeasure := hiZ.sub hiX
              have hm := MeasureTheory.integral_mono
                ((hiY.sub hiX).const_mul (((z - x : ℤ) : ℝ)))
                ((hiZX.add (MeasureTheory.integrable_const K)).const_mul (((y - x : ℤ) : ℝ)))
                (show ∀ k : ℕ,
                  ((z - x : ℤ) : ℝ) * (V (y - (k : ℤ)) - V (x - (k : ℤ))) ≤
                    ((y - x : ℤ) : ℝ) * (V (z - (k : ℤ)) - V (x - (k : ℤ)) + K) from
                  fun k => by
                    simpa only [sub_sub_sub_cancel_right] using hV (x - (k : ℤ)) (y - (k : ℤ)) (z - (k : ℤ)) (by omega) (by omega))
              simp only [Pi.sub_apply, Pi.add_apply] at hm
              rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
                MeasureTheory.integral_sub hiY hiX,
                MeasureTheory.integral_add hiZX (MeasureTheory.integrable_const K),
                MeasureTheory.integral_sub hiZ hiX] at hm
              simpa [Ex] using hm
            have hBellman_KC : ∀ V : ℤ → ℝ, KC V → PB V → KC (fun y => G y + α * Ex V y) := by
              intro V hV hB x y z hxy hyz
              have hG := hG_C x y z hxy hyz
              have hE := mul_le_mul_of_nonneg_left (hEx_KC V hV hB x y z hxy hyz) hα₀
              have hm := mul_nonneg
                (show (0 : ℝ) ≤ ((y - x : ℤ) : ℝ) by exact_mod_cast sub_nonneg.mpr hxy)
                (show 0 ≤ (1 - α) * K by positivity)
              dsimp
              nlinarith only [hG,hE,hm]
            have hBellman_coercive : ∀ V : ℤ → ℝ, PB V →
                Filter.Tendsto (fun y => G y + α * Ex V y) Filter.atTop Filter.atTop ∧
                Filter.Tendsto (fun y => G y + α * Ex V y) Filter.atBot Filter.atTop := by
              intro V hB
              obtain ⟨L, hL⟩ := hB.1
              have hl : ∀ y, G y + α * L ≤ G y + α * Ex V y := by
                intro y
                exact add_le_add_right (mul_le_mul_of_nonneg_left (hEx_lower V hB L hL y) hα₀) _
              exact ⟨Filter.tendsto_atTop_mono hl (Filter.tendsto_atTop_add_const_right _ _ hG_top),
                Filter.tendsto_atTop_mono hl (Filter.tendsto_atTop_add_const_right _ _ hG_bot)⟩
            let Good : (ℤ → ℝ) → Prop := fun V => KC V ∧ PB V ∧
              AntitoneOn V (Set.Iic (SLow G)) ∧ (∀ x y : ℤ, x ≤ y → V x ≤ K + V y)
            have hEx_anti : ∀ V : ℤ → ℝ, Good V →
                AntitoneOn (Ex V) (Set.Iic (SLow G)) := by
              intro V hV x hx y hy hxy
              apply MeasureTheory.integral_mono (hEx_int V hV.2.1 y) (hEx_int V hV.2.1 x)
              intro k
              change x ≤ SLow G at hx
              change y ≤ SLow G at hy
              apply hV.2.2.1
              · change x - (k : ℤ) ≤ SLow G
                omega
              · change y - (k : ℤ) ≤ SLow G
                omega
              · omega
            have hEx_cross : ∀ V : ℤ → ℝ, Good V → ∀ x y : ℤ, x ≤ y → Ex V x ≤ K + Ex V y := by
              intro V hV x y hxy
              have hm := MeasureTheory.integral_mono (hEx_int V hV.2.1 x)
                ((MeasureTheory.integrable_const K).add (hEx_int V hV.2.1 y))
                (fun k : ℕ => hV.2.2.2 (x - (k : ℤ)) (y - (k : ℤ)) (by omega))
              simp only [Pi.add_apply] at hm
              rw [MeasureTheory.integral_add (MeasureTheory.integrable_const K) (hEx_int V hV.2.1 y)] at hm
              simpa [Ex] using hm
            have hG_strict : ∀ x < SLow G, G (SLow G) < G x := by
              intro x hx
              apply lt_of_le_of_ne (hSLmem x)
              intro heq
              have hm : SLow G ≤ x := csInf_le hMbdd (fun z => heq.symm.le.trans (hSLmem z))
              omega
            have hSHmem : G (SLow G) + α * K ≤ G (SHigh G K α + 1) := by
              apply (Int.csInf_mem hSH_ne _).2
              exact ⟨SLow G, fun y hy => hy.1⟩
            have hstep : ∀ V : ℤ → ℝ, Good V →
                ∃ s S : ℤ, sLow G K ≤ s ∧ s ≤ sHigh G K α ∧
                  SLow G ≤ S ∧ S ≤ SHigh G K α ∧
                  Good (fun x => if x < s then K + (G S + α * Ex V S) else G x + α * Ex V x) ∧
                  (∀ x y : ℤ, x ≤ y →
                    (if x < s then K + (G S + α * Ex V S) else G x + α * Ex V x) ≤
                      (if x < y then K else 0) + G y + α * Ex V y) := by
              intro V hV
              let F : ℤ → ℝ := fun y => G y + α * Ex V y
              have hFc := hBellman_KC V hV.1 hV.2.1
              have hFt := hBellman_coercive V hV.2.1
              obtain ⟨s, T, hsT, hopt, hkc, hlo, hup, hT, hbef, hsmem⟩ :=
                hselection F hFc hFt.1 hFt.2
              have hFanti : AntitoneOn F (Set.Iic (SLow G)) := by
                intro x hx y hy hxy
                have h₁ := hG_left hx hy hxy
                have h₂ := mul_le_mul_of_nonneg_left (hEx_anti V hV hx hy hxy) hα₀
                dsimp [F]
                linarith only [h₁,h₂]
              have hmT : SLow G ≤ T := by
                by_contra h
                have hlt : T < SLow G := lt_of_not_ge h
                have h₁ := hG_strict T hlt
                have h₂ := mul_le_mul_of_nonneg_left
                  (hEx_anti V hV hlt.le (show SLow G ≤ SLow G from le_rfl) hlt.le) hα₀
                have h₃ := hT (SLow G)
                dsimp [F] at h₃
                linarith only [h₁,h₂,h₃]
              have hs_hi : s ≤ sHigh G K α := by
                by_contra h
                have hlt : sHigh G K α < s := lt_of_not_ge h
                have h₁ := mul_le_mul_of_nonneg_left
                  (hEx_cross V hV (sHigh G K α) T (hsH_le.trans hmT)) hα₀
                have h₂ := hbef _ hlt
                have h₃ := hSLmem T
                dsimp [F] at h₂
                nlinarith only [h₁,h₂,h₃,hsHmem]
              have hs_low : sLow G K ≤ s := by
                by_contra h
                have hlt : s < sLow G K := lt_of_not_ge h
                have h₁ := hsL_strict s hlt
                have h₂ := mul_le_mul_of_nonneg_left
                  (hEx_anti V hV (hlt.le.trans hsLm) (show SLow G ≤ SLow G from le_rfl) (hlt.le.trans hsLm)) hα₀
                have h₃ := hT (SLow G)
                dsimp [F] at h₃ hsmem
                linarith only [h₁,h₂,h₃,hsmem]
              have hFhigh : ∀ y : ℤ, SHigh G K α < y → F (SLow G) ≤ F y := by
                intro y hy
                have h₁ := hG_right (by omega : SLow G ≤ SHigh G K α + 1)
                  (by omega : SLow G ≤ y) (by omega : SHigh G K α + 1 ≤ y)
                have h₂ := mul_le_mul_of_nonneg_left
                  (hEx_cross V hV (SLow G) y (by omega)) hα₀
                dsimp [F]
                nlinarith only [h₁,h₂,hSHmem]
              let S : ℤ := if T ≤ SHigh G K α then T else SLow G
              have hSlo : SLow G ≤ S := by dsimp [S]; split_ifs <;> omega
              have hShi : S ≤ SHigh G K α := by dsimp [S]; split_ifs <;> omega
              have hFeq : F S = F T := by
                dsimp [S]
                split_ifs with h
                · rfl
                · exact le_antisymm (hFhigh T (lt_of_not_ge h)) (hT _)
              have hsS : s ≤ S := hs_hi.trans (hsH_le.trans hSlo)
              have hval : ∀ x, (if x < sSRule s S x then K else 0) + F (sSRule s S x) =
                  if x < s then K + F T else F x := by
                intro x
                by_cases hx : x < s
                · simp only [sSRule, if_pos hx, if_pos (hx.trans_le hsS), hFeq]
                · simp only [sSRule, if_neg hx, if_neg (lt_irrefl x), zero_add]
              have hvalT : ∀ x, (if x < sSRule s T x then K else 0) + F (sSRule s T x) =
                  if x < s then K + F T else F x := by
                intro x
                by_cases hx : x < s
                · simp only [sSRule, if_pos hx, if_pos (hx.trans_le hsT)]
                · simp only [sSRule, if_neg hx, if_neg (lt_irrefl x), zero_add]
              have hoptV : ∀ x y : ℤ, x ≤ y → (if x < s then K + F T else F x) ≤
                  (if x < y then K else 0) + F y := by
                intro x y hxy
                simpa only [hvalT] using hopt x y hxy
              have hVanti : AntitoneOn (fun x => if x < s then K + F T else F x) (Set.Iic (SLow G)) := by
                intro x hx y hy hxy
                by_cases hylt : y < s
                · have hxlt : x < s := by omega
                  simp [hylt, hxlt]
                · by_cases hxlt : x < s
                  · simp only [if_neg hylt, if_pos hxlt]
                    have h := hFanti (hs_hi.trans hsH_le) hy (le_of_not_gt hylt)
                    linarith only [h,hsmem]
                  · simpa only [if_neg hylt, if_neg hxlt] using hFanti hx hy hxy
              have hVcross : ∀ x y : ℤ, x ≤ y → (if x < s then K + F T else F x) ≤
                  K + (if y < s then K + F T else F y) := by
                intro x y hxy
                have hay : y ≤ sSRule s S y := by unfold sSRule; split_ifs <;> omega
                have hm := hoptV x (sSRule s S y) (hxy.trans hay)
                have hv := hval y
                have hc : (if x < sSRule s S y then K else 0) ≤ K := by split_ifs <;> linarith
                have hd : 0 ≤ (if y < sSRule s S y then K else 0) := by split_ifs <;> positivity
                linarith only [hm,hv,hc,hd]
              refine ⟨s, S, hs_low, hs_hi, hSlo, hShi, ?_, ?_⟩
              · change Good (fun x => if x < s then K + F S else F x)
                simp only [hFeq]
                exact ⟨hkc, ⟨⟨F T, hlo⟩, hup⟩, hVanti, hVcross⟩
              · intro x y hxy
                change (if x < s then K + F S else F x) ≤ _
                rw [hFeq]
                simpa only [F, add_assoc] using hoptV x y hxy
            choose selS selT hselL hselH hselm hselSH hselgood hselopt using hstep
            have hzero : Good (fun _ : ℤ => 0) := by
              refine ⟨?_, ⟨⟨0, fun _ => le_rfl⟩, fun _ => ⟨0, fun _ _ => le_rfl⟩⟩, ?_, ?_⟩
              · intro x y z hxy hyz
                simp only [sub_self, mul_zero, zero_add]
                exact mul_nonneg (by exact_mod_cast sub_nonneg.mpr hxy) hK
              · intro x hx y hy hxy
                exact le_rfl
              · intro x y hxy
                simpa using hK
            let nxt : {V : ℤ → ℝ // Good V} → {V : ℤ → ℝ // Good V} := fun p =>
              ⟨fun x => if x < selS p.1 p.2 then K + (G (selT p.1 p.2) + α * Ex p.1 (selT p.1 p.2))
                else G x + α * Ex p.1 x, hselgood p.1 p.2⟩
            let D : ℕ → {V : ℤ → ℝ // Good V} := Nat.rec ⟨fun _ => 0, hzero⟩ (fun _ p => nxt p)
            let V : ℕ → ℤ → ℝ := fun n => (D n).1
            let ss : ℕ → ℤ := fun n => selS (D n).1 (D n).2
            let SS : ℕ → ℤ := fun n => selT (D n).1 (D n).2
            have hVgood : ∀ n, Good (V n) := fun n => (D n).2
            have hsslo : ∀ n, sLow G K ≤ ss n := fun n => hselL (D n).1 (D n).2
            have hsshi : ∀ n, ss n ≤ sHigh G K α := fun n => hselH (D n).1 (D n).2
            have hSSlo : ∀ n, SLow G ≤ SS n := fun n => hselm (D n).1 (D n).2
            have hSShi : ∀ n, SS n ≤ SHigh G K α := fun n => hselSH (D n).1 (D n).2
            have hssSS : ∀ n, ss n ≤ SS n := fun n => (hsshi n).trans (hsH_le.trans (hSSlo n))
            have hV0 : ∀ x, V 0 x = 0 := fun _ => rfl
            have hVsucc : ∀ n x, V (n + 1) x =
                if x < ss n then K + (G (SS n) + α * Ex (V n) (SS n)) else G x + α * Ex (V n) x := by
              intro n x
              rfl
            have hVineq : ∀ n x y, x ≤ y → V (n + 1) x ≤
                (if x < y then K else 0) + G y + α * Ex (V n) y := by
              intro n x y hxy
              exact hselopt (D n).1 (D n).2 x y hxy
            have hVaction : ∀ n x, V (n + 1) x =
                (if x < sSRule (ss n) (SS n) x then K else 0) +
                  G (sSRule (ss n) (SS n) x) + α * Ex (V n) (sSRule (ss n) (SS n) x) := by
              intro n x
              rw [hVsucc]
              by_cases hx : x < ss n
              · simp only [sSRule, if_pos hx, if_pos (hx.trans_le (hssSS n)), add_assoc]
              · simp only [sSRule, if_neg hx, if_neg (lt_irrefl x), zero_add]
            let L : ℕ → ℤ → (t : ℕ) → (Fin t → ℕ) → ℤ := fun n x =>
              Nat.rec (motive := fun t => (Fin t → ℕ) → ℤ)
                (fun _ => sSRule (ss (n - 1)) (SS (n - 1)) x)
                (fun t prev h => sSRule (ss (n - 1 - (t + 1))) (SS (n - 1 - (t + 1)))
                  (prev (Fin.init h) - (h (Fin.last t) : ℤ)))
            let P : ℕ → Policy := fun n t x h => L n x t h
            have hP_rule : ∀ n t, UsesRule (P n) t (ss (n - 1 - t)) (SS (n - 1 - t)) := by
              intro n t x h
              cases t <;> rfl
            have hP_adm : ∀ n, Admissible (P n) := by
              intro n t x h
              rw [hP_rule]
              unfold sSRule
              split_ifs with hx
              · exact hx.le.trans (hssSS _)
              · exact le_rfl
            have hP_ss : ∀ n, IsSSPolicy n (P n) := by
              intro n
              exact ⟨fun t => ss (n - 1 - t), fun t => SS (n - 1 - t),
                fun t ht => ⟨hssSS _, hP_rule n t⟩⟩
            let EE : {ι : Type} → PMF ι → (ι → ℝ) → EReal := fun {_} p f =>
              ((∑' i, p i * ENNReal.ofReal (f i) : ℝ≥0∞) : EReal) -
                ((∑' i, p i * ENNReal.ofReal (-f i) : ℝ≥0∞) : EReal)
            have hEEshift : ∀ (ι : Type) (p : PMF ι) (f : ι → ℝ) (c : ℝ), (∀ i, c ≤ f i) →
                EE p f = ((∑' i, p i * ENNReal.ofReal (f i - c) : ℝ≥0∞) : EReal) + (c : EReal) := by
              intro ι p f c hf
              let R : ℝ≥0∞ := ∑' i, p i * ENNReal.ofReal (f i - c)
              let N : ℝ≥0∞ := ∑' i, p i * ENNReal.ofReal (-f i)
              let Q : ℝ≥0∞ := ∑' i, p i * ENNReal.ofReal (f i)
              have hid : ∀ a : ℝ, c ≤ a →
                  ENNReal.ofReal (a - c) + ENNReal.ofReal (-a) + ENNReal.ofReal c =
                    ENNReal.ofReal a + ENNReal.ofReal (-c) := by
                intro a ha
                by_cases hc : 0 ≤ c
                · have ha0 : 0 ≤ a := hc.trans ha
                  simp only [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr ha0),
                    ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hc), add_zero]
                  rw [← ENNReal.ofReal_add (sub_nonneg.mpr ha) hc, sub_add_cancel]
                · have hc0 : c ≤ 0 := le_of_not_ge hc
                  by_cases ha0 : 0 ≤ a
                  · simp only [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr ha0),
                      ENNReal.ofReal_of_nonpos hc0, add_zero]
                    exact ENNReal.ofReal_add ha0 (neg_nonneg.mpr hc0)
                  · have ha1 : a ≤ 0 := le_of_not_ge ha0
                    simp only [ENNReal.ofReal_of_nonpos ha1, ENNReal.ofReal_of_nonpos hc0, add_zero, zero_add]
                    rw [← ENNReal.ofReal_add (sub_nonneg.mpr ha) (neg_nonneg.mpr ha1)]
                    congr 1
                    ring
              have hsum : R + N + ENNReal.ofReal c = Q + ENNReal.ofReal (-c) := by
                calc
                  R + N + ENNReal.ofReal c = ∑' i, p i *
                      (ENNReal.ofReal (f i - c) + ENNReal.ofReal (-f i) + ENNReal.ofReal c) := by
                    simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul, R, N]
                  _ = ∑' i, p i * (ENNReal.ofReal (f i) + ENNReal.ofReal (-c)) := by
                    congr 1
                    funext i
                    rw [hid _ (hf i)]
                  _ = Q + ENNReal.ofReal (-c) := by
                    simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul, Q]
              have hNle : N ≤ ENNReal.ofReal (-c) := by
                calc
                  N ≤ ∑' i, p i * ENNReal.ofReal (-c) := ENNReal.tsum_le_tsum
                    (fun i => mul_le_mul_right (ENNReal.ofReal_le_ofReal (neg_le_neg (hf i))) _)
                  _ = ENNReal.ofReal (-c) := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
              have hNfin : N ≠ ⊤ := ne_of_lt (hNle.trans_lt ENNReal.ofReal_lt_top)
              let b : ℝ := N.toReal
              have hNb : (N : EReal) = (b : EReal) := (EReal.coe_ennreal_toReal hNfin).symm
              have hsumE := congrArg (fun z : ℝ≥0∞ => (z : EReal)) hsum
              simp only [EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal, hNb] at hsumE
              have hR : (R : EReal) = (Q : EReal) + ((max (-c) 0 - b - max c 0 : ℝ) : EReal) := by
                have hh := congrArg (fun z : EReal => z + ((-(b + max c 0) : ℝ) : EReal)) hsumE
                simpa only [add_assoc, ← EReal.coe_add,
                  show b + (max c 0 + -(b + max c 0)) = 0 by ring,
                  show max (-c) 0 + -(b + max c 0) = max (-c) 0 - b - max c 0 by ring,
                  EReal.coe_zero, add_zero] using hh
              have hcmax : max c 0 - max (-c) 0 = c := by
                by_cases hc : 0 ≤ c
                · simp [max_eq_left hc, max_eq_right (neg_nonpos.mpr hc)]
                · have hc' : c ≤ 0 := le_of_not_ge hc
                  simp [max_eq_right hc', max_eq_left (neg_nonneg.mpr hc')]
              change (Q : EReal) - (N : EReal) = (R : EReal) + (c : EReal)
              rw [hNb, hR, add_assoc, ← EReal.coe_add,
                show max (-c) 0 - b - max c 0 + c = -b by linarith [hcmax], EReal.coe_neg]
              rfl
            let c : ℕ → ℝ := Nat.rec 0 (fun _ r => G (SLow G) + α * r)
            have hc0 : c 0 = 0 := rfl
            have hcsucc : ∀ n, c (n + 1) = G (SLow G) + α * c n := fun _ => rfl
            have hVlower : ∀ n x, c n ≤ V n x := by
              intro n
              induction n with
              | zero => intro x; simp only [hc0, hV0, le_refl]
              | succ n ih =>
                intro x
                rw [hVaction, hcsucc]
                have hg := hSLmem (sSRule (ss n) (SS n) x)
                have he := mul_le_mul_of_nonneg_left
                  (hEx_lower (V n) (hVgood n).2.1 (c n) ih (sSRule (ss n) (SS n) x)) hα₀
                have ho : 0 ≤ (if x < sSRule (ss n) (SS n) x then K else 0) := by split_ifs <;> positivity
                linarith only [hg,he,ho]
            let W : ℕ → ℤ → ℝ := fun n x => V n x - c n
            let a : ℝ≥0∞ := ENNReal.ofReal α
            have hWnonneg : ∀ n x, 0 ≤ W n x := fun n x => sub_nonneg.mpr (hVlower n x)
            have hWint : ∀ n y, MeasureTheory.Integrable (fun k : ℕ => W n (y - (k : ℤ))) φ.toMeasure := by
              intro n y
              exact (hEx_int (V n) (hVgood n).2.1 y).sub (MeasureTheory.integrable_const (c n))
            have hWE : ∀ n y, (∫ k : ℕ, W n (y - (k : ℤ)) ∂φ.toMeasure) = Ex (V n) y - c n := by
              intro n y
              rw [show (fun k : ℕ => W n (y - (k : ℤ))) =
                (fun k : ℕ => V n (y - (k : ℤ)) - c n) from rfl,
                MeasureTheory.integral_sub (hEx_int (V n) (hVgood n).2.1 y) (MeasureTheory.integrable_const (c n))]
              simp [Ex]
            have hWsum : ∀ n y, ENNReal.ofReal (Ex (V n) y - c n) =
                ∑' k : ℕ, φ k * ENNReal.ofReal (W n (y - (k : ℤ))) := by
              intro n y
              rw [← hWE]
              rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hWint n y)
                (Filter.Eventually.of_forall (fun k => hWnonneg n (y - (k : ℤ))))]
              rw [MeasureTheory.lintegral_countable']
              apply tsum_congr
              intro k
              rw [PMF.toMeasure_apply_singleton φ k (MeasurableSet.singleton k), mul_comm]
            have hWineq : ∀ n x y, x ≤ y → ENNReal.ofReal (W (n + 1) x) ≤
                ENNReal.ofReal ((if x < y then K else 0) + G y - G (SLow G)) +
                  a * ∑' k : ℕ, φ k * ENNReal.ofReal (W n (y - (k : ℤ))) := by
              intro n x y hxy
              rw [← hWsum]
              have hh : 0 ≤ (if x < y then K else 0) + G y - G (SLow G) := by
                have hg := hSLmem y
                split_ifs <;> linarith
              have he : 0 ≤ Ex (V n) y - c n := by
                rw [← hWE]
                exact MeasureTheory.integral_nonneg (fun k => hWnonneg n _)
              rw [← ENNReal.ofReal_mul hα₀, ← ENNReal.ofReal_add hh (mul_nonneg hα₀ he)]
              apply ENNReal.ofReal_le_ofReal
              have hv := hVineq n x y hxy
              dsimp [W]
              rw [hcsucc]
              linarith only [hv]
            have hWeq : ∀ n x, ENNReal.ofReal (W (n + 1) x) =
                ENNReal.ofReal ((if x < sSRule (ss n) (SS n) x then K else 0) +
                  G (sSRule (ss n) (SS n) x) - G (SLow G)) +
                  a * ∑' k : ℕ, φ k * ENNReal.ofReal (W n (sSRule (ss n) (SS n) x - (k : ℤ))) := by
              intro n x
              rw [← hWsum]
              have hh : 0 ≤ (if x < sSRule (ss n) (SS n) x then K else 0) +
                  G (sSRule (ss n) (SS n) x) - G (SLow G) := by
                have hg := hSLmem (sSRule (ss n) (SS n) x)
                split_ifs <;> linarith
              have he : 0 ≤ Ex (V n) (sSRule (ss n) (SS n) x) - c n := by
                rw [← hWE]
                exact MeasureTheory.integral_nonneg (fun k => hWnonneg n _)
              rw [← ENNReal.ofReal_mul hα₀, ← ENNReal.ofReal_add hh (mul_nonneg hα₀ he)]
              congr 1
              dsimp [W]
              rw [hVaction, hcsucc]
              ring
            let B : Policy → ℤ → ℕ → ℝ≥0∞ := fun Y x t =>
              ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal
                ((if state Y x t h < Y t x h then K else 0) + G (Y t x h) - G (SLow G))
            let H : Policy → ℤ → ℕ → ℕ → ℝ≥0∞ := fun Y x n t =>
              ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (W n (state Y x t h))
            have hHrec : ∀ Y x n t,
                (∑' h : Fin t → ℕ, weight φ h *
                  (∑' k : ℕ, φ k * ENNReal.ofReal (W n (Y t x h - (k : ℤ))))) = H Y x n (t + 1) := by
              intro Y x n t
              dsimp [H]
              rw [hsum_snoc, ENNReal.tsum_comm]
              simp only [hw_snoc, state, Fin.init_snoc, Fin.snoc_last, mul_assoc, ENNReal.tsum_mul_left]
            have hHlin : ∀ Y x n t,
                (∑' h : Fin t → ℕ, weight φ h *
                  (ENNReal.ofReal ((if state Y x t h < Y t x h then K else 0) + G (Y t x h) - G (SLow G)) +
                    a * ∑' k : ℕ, φ k * ENNReal.ofReal (W n (Y t x h - (k : ℤ))))) =
                  B Y x t + a * H Y x n (t + 1) := by
              intro Y x n t
              simp only [mul_add, ENNReal.tsum_add]
              congr 1
              calc
                _ = a * ∑' h : Fin t → ℕ, weight φ h *
                    (∑' k : ℕ, φ k * ENNReal.ofReal (W n (Y t x h - (k : ℤ)))) := by
                  simp only [mul_left_comm, ENNReal.tsum_mul_left]
                _ = _ := by rw [hHrec]
            have hHle : ∀ Y, Admissible Y → ∀ x n t, H Y x (n + 1) t ≤ B Y x t + a * H Y x n (t + 1) := by
              intro Y hY x n t
              rw [← hHlin]
              apply ENNReal.tsum_le_tsum
              intro h
              exact mul_le_mul_right (hWineq n _ _ (hY t x h)) (weight φ h)
            have hHeq : ∀ N x n t, n + 1 + t = N →
                H (P N) x (n + 1) t = B (P N) x t + a * H (P N) x n (t + 1) := by
              intro N x n t hcount
              rw [← hHlin]
              apply tsum_congr
              intro h
              congr 1
              have hr := hP_rule N t x h
              have he : N - 1 - t = n := by omega
              rw [he] at hr
              rw [hr]
              exact hWeq n _
            have hBsum : ∀ Y x n t,
                (∑ i ∈ Finset.range (n + 1), a ^ i * B Y x (t + i)) =
                  B Y x t + a * ∑ i ∈ Finset.range n, a ^ i * B Y x (t + 1 + i) := by
              intro Y x n t
              rw [Finset.sum_range_succ', Finset.mul_sum]
              simp only [pow_zero, one_mul, Nat.add_zero]
              rw [add_comm]
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              rw [show t + (i + 1) = t + 1 + i by omega, pow_succ]
              ring
            have hH0 : ∀ Y x t, H Y x 0 t = 0 := by
              intro Y x t
              simp [H, W, hV0, hc0]
            have hHbound : ∀ Y, Admissible Y → ∀ x n t,
                H Y x n t ≤ ∑ i ∈ Finset.range n, a ^ i * B Y x (t + i) := by
              intro Y hY x n
              induction n with
              | zero => intro t; simp [hH0]
              | succ n ih =>
                intro t
                rw [hBsum]
                exact (hHle Y hY x n t).trans
                  (add_le_add_right (mul_le_mul_right (ih (t + 1)) a) (B Y x t))
            have hHattain : ∀ N x n t, n + t = N →
                H (P N) x n t = ∑ i ∈ Finset.range n, a ^ i * B (P N) x (t + i) := by
              intro N x n
              induction n with
              | zero => intro t ht; simp [hH0]
              | succ n ih =>
                intro t ht
                rw [hHeq N x n t (by omega), ih (t + 1) (by omega), hBsum]
            have hHinitial : ∀ Y x n, H Y x n 0 = ENNReal.ofReal (W n x) := by
              intro Y x n
              simp [H, weight, state]
            have hNCoptimal : ∀ n Y, Admissible Y → ∀ x,
                (∑ i ∈ Finset.range n, a ^ i * B (P n) x i) ≤
                  ∑ i ∈ Finset.range n, a ^ i * B Y x i := by
              intro n Y hY x
              have he := hHattain n x n 0 (by omega)
              have hl := hHbound Y hY x n 0
              simp only [Nat.add_zero, Nat.zero_add, hHinitial] at he hl
              exact he.symm.le.trans hl
            let hp : (t : ℕ) → PMF (Fin t → ℕ) := fun t =>
              ⟨weight φ, by simpa only [hw_one] using (ENNReal.summable (f := weight φ (t := t))).hasSum⟩
            have hBsplit : ∀ Y x t, B Y x t = ENNReal.ofReal K * orderProb φ Y x t +
                ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (Y t x h) - G (SLow G)) := by
              intro Y x t
              dsimp [B, orderProb]
              rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
              apply tsum_congr
              intro h
              have ho : 0 ≤ (if state Y x t h < Y t x h then K else 0) := by split_ifs <;> positivity
              have hg : 0 ≤ G (Y t x h) - G (SLow G) := sub_nonneg.mpr (hSLmem _)
              rw [show (if state Y x t h < Y t x h then K else 0) + G (Y t x h) - G (SLow G) =
                (if state Y x t h < Y t x h then K else 0) + (G (Y t x h) - G (SLow G)) by ring,
                ENNReal.ofReal_add ho hg, mul_add]
              split_ifs <;> simp [mul_comm]
            have hp_shift : ∀ Y x t, periodCost φ G K Y x t = (B Y x t : EReal) + (G (SLow G) : EReal) := by
              intro Y x t
              have he := hEEshift (Fin t → ℕ) (hp t) (fun h => G (Y t x h)) (G (SLow G))
                (fun h => hSLmem (Y t x h))
              change expectedG φ G Y x t =
                ((∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (Y t x h) - G (SLow G)) : ℝ≥0∞) : EReal) +
                  (G (SLow G) : EReal) at he
              rw [periodCost, he, hBsplit, EReal.coe_ennreal_add, EReal.coe_ennreal_mul,
                EReal.coe_ennreal_ofReal, max_eq_left hK]
              simp only [add_assoc]
            have hcostshift : ∀ Y x n, cost φ G K α n x Y =
                ((∑ i ∈ Finset.range n, a ^ i * B Y x i : ℝ≥0∞) : EReal) +
                  ((∑ i ∈ Finset.range n, α ^ i * G (SLow G) : ℝ) : EReal) := by
              intro Y x n
              induction n with
              | zero => simp [cost]
              | succ n ih =>
                rw [show cost φ G K α (n + 1) x Y = cost φ G K α n x Y +
                    ((α ^ n : ℝ) : EReal) * periodCost φ G K Y x n by
                      simp only [cost, Finset.sum_range_succ]]
                rw [ih, hp_shift,
                  EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast pow_nonneg hα₀ n) (EReal.coe_ne_top _)]
                rw [Finset.sum_range_succ, Finset.sum_range_succ, EReal.coe_ennreal_add, EReal.coe_add]
                have ha : ((a ^ n : ℝ≥0∞) : EReal) = ((α ^ n : ℝ) : EReal) := by
                  rw [show a ^ n = ENNReal.ofReal (α ^ n) from (ENNReal.ofReal_pow hα₀ n).symm,
                    EReal.coe_ennreal_ofReal, max_eq_left (pow_nonneg hα₀ n)]
                rw [EReal.coe_ennreal_mul, ha, EReal.coe_mul]
                ac_rfl
            have hP_optimal : ∀ n, IsOptimal φ G K α n (P n) := by
              intro n
              refine ⟨hP_adm n, fun Y hY x => ?_⟩
              rw [hcostshift, hcostshift]
              exact add_le_add_left (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hNCoptimal n Y hY x)) _
            have hfinite : ∀ n : ℕ, 2 ≤ n →
                ∃ (Y : Policy) (sn Sn : ℤ), IsOptimal φ G K α n Y ∧ IsSSPolicy n Y ∧
                  sn ≤ Sn ∧ UsesRule Y 0 sn Sn ∧
                  sLow G K ≤ sn ∧ sn ≤ sHigh G K α ∧ sHigh G K α ≤ SLow G ∧
                  SLow G ≤ Sn ∧ Sn ≤ SHigh G K α := by
              intro n hn
              refine ⟨P n, ss (n - 1), SS (n - 1), hP_optimal n, hP_ss n, hssSS _, ?_,
                hsslo _, hsshi _, hsH_le, hSSlo _, hSShi _⟩
              simpa only [Nat.sub_zero] using hP_rule n 0
            refine ⟨hfinite, ?_⟩
            have hQNC : ∀ n x, ENNReal.ofReal (W n x) = ∑ i ∈ Finset.range n, a ^ i * B (P n) x i := by
              intro n x
              simpa only [hHinitial, Nat.zero_add] using hHattain n x n 0 (by omega)
            have hQmono : ∀ x, Monotone (fun n => ENNReal.ofReal (W n x)) := by
              intro x
              apply monotone_nat_of_le_succ
              intro n
              rw [hQNC n, hQNC (n + 1)]
              exact (hNCoptimal n (P (n + 1)) (hP_adm _) x).trans
                (by rw [Finset.sum_range_succ]; exact le_self_add)
            let U : ℤ → ℝ≥0∞ := fun x => ⨆ n : ℕ, ENNReal.ofReal (W n x)
            let C := ↥(Finset.Icc (sLow G K) (sHigh G K α) ×ˢ Finset.Icc (SLow G) (SHigh G K α))
            let q : ℕ → C := fun n => ⟨(ss n, SS n), by
              simp only [Finset.mem_product, Finset.mem_Icc]
              exact ⟨⟨hsslo n, hsshi n⟩, ⟨hSSlo n, hSShi n⟩⟩⟩
            obtain ⟨p, hpinfinite⟩ := Finite.exists_infinite_fiber q
            have hpinf : (q ⁻¹' {p}).Infinite := Set.infinite_coe_iff.mp hpinfinite
            let sStar : ℤ := p.1.1
            let SStar : ℤ := p.1.2
            have hpbound : sLow G K ≤ sStar ∧ sStar ≤ sHigh G K α ∧
                SLow G ≤ SStar ∧ SStar ≤ SHigh G K α := by
              have hp := p.2
              simp only [Finset.mem_product, Finset.mem_Icc] at hp
              exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
            have hsr : sStar ≤ SStar := hpbound.2.1.trans (hsH_le.trans hpbound.2.2.1)
            have hrecur : ∀ n : ℕ, ∃ j : ℕ, n ≤ j ∧ ss j = sStar ∧ SS j = SStar := by
              intro n
              obtain ⟨j, hj, hnj⟩ := hpinf.exists_gt n
              have he : q j = p := hj
              have h₁ := congrArg (fun z : C => z.1.1) he
              have h₂ := congrArg (fun z : C => z.1.2) he
              exact ⟨j, hnj.le, h₁, h₂⟩
            have hsupsum : ∀ f : ℕ → ℕ → ℝ≥0∞, (∀ k, Monotone (fun n => f n k)) →
                (∑' k : ℕ, ⨆ n : ℕ, f n k) = ⨆ n : ℕ, ∑' k : ℕ, f n k := by
              intro f hf
              have hm := MeasureTheory.lintegral_iSup (μ := MeasureTheory.Measure.count)
                (fun n => measurable_of_countable (f n)) (fun n m hnm k => hf k hnm)
              simpa only [MeasureTheory.lintegral_count] using hm
            have hUineq : ∀ x y : ℤ, x ≤ y → U x ≤
                ENNReal.ofReal ((if x < y then K else 0) + G y - G (SLow G)) +
                  a * ∑' k : ℕ, φ k * U (y - (k : ℤ)) := by
              intro x y hxy
              apply iSup_le
              intro n
              cases n with
              | zero => simp [W, hV0, hc0]
              | succ n =>
                apply (hWineq n x y hxy).trans
                exact add_le_add_right
                  (mul_le_mul_right (ENNReal.tsum_le_tsum (fun k : ℕ =>
                    mul_le_mul_right (le_iSup (fun n => ENNReal.ofReal (W n (y - (k : ℤ)))) n) (φ k))) a)
                  (ENNReal.ofReal ((if x < y then K else 0) + G y - G (SLow G)))
            have hUeq : ∀ x : ℤ, U x =
                ENNReal.ofReal ((if x < sSRule sStar SStar x then K else 0) + G (sSRule sStar SStar x) - G (SLow G)) +
                  a * ∑' k : ℕ, φ k * U (sSRule sStar SStar x - (k : ℤ)) := by
              intro x
              apply le_antisymm (hUineq x _ (by unfold sSRule; split_ifs <;> omega))
              have hu : ∀ n : ℕ,
                  ENNReal.ofReal ((if x < sSRule sStar SStar x then K else 0) + G (sSRule sStar SStar x) - G (SLow G)) +
                    a * ∑' k : ℕ, φ k * ENNReal.ofReal (W n (sSRule sStar SStar x - (k : ℤ))) ≤ U x := by
                intro n
                obtain ⟨j, hnj, hjs, hjS⟩ := hrecur n
                calc
                  _ ≤ ENNReal.ofReal ((if x < sSRule sStar SStar x then K else 0) + G (sSRule sStar SStar x) - G (SLow G)) +
                      a * ∑' k : ℕ, φ k * ENNReal.ofReal (W j (sSRule sStar SStar x - (k : ℤ))) := by
                    exact add_le_add_right
                      (mul_le_mul_right (ENNReal.tsum_le_tsum (fun k : ℕ =>
                        mul_le_mul_right (hQmono (sSRule sStar SStar x - (k : ℤ)) hnj) (φ k))) a) _
                  _ = ENNReal.ofReal (W (j + 1) x) := by rw [hWeq j x, hjs, hjS]
                  _ ≤ U x := le_iSup (fun n => ENNReal.ofReal (W n x)) (j + 1)
              have hm : ∀ k : ℕ, Monotone (fun n => φ k * ENNReal.ofReal (W n (sSRule sStar SStar x - (k : ℤ)))) := by
                intro k i j hij
                exact mul_le_mul_right (hQmono _ hij) _
              have he : (∑' k : ℕ, φ k * U (sSRule sStar SStar x - (k : ℤ))) =
                  ⨆ n : ℕ, ∑' k : ℕ, φ k * ENNReal.ofReal (W n (sSRule sStar SStar x - (k : ℤ))) := by
                change (∑' k : ℕ, φ k * (⨆ n : ℕ, ENNReal.ofReal (W n (sSRule sStar SStar x - (k : ℤ))))) = _
                simp_rw [ENNReal.mul_iSup]
                exact hsupsum _ hm
              rw [he, ENNReal.mul_iSup, ENNReal.add_iSup]
              exact iSup_le hu
            let Z : Policy := stationary sStar SStar
            let J : ℤ → ℕ → ℝ≥0∞ := fun x t => ∑' h : Fin t → ℕ, weight φ h * U (state Z x t h)
            have hJrec : ∀ x t, J x t = B Z x t + a * J x (t + 1) := by
              intro x t
              calc
                J x t = ∑' h : Fin t → ℕ, weight φ h *
                    (ENNReal.ofReal ((if state Z x t h < Z t x h then K else 0) + G (Z t x h) - G (SLow G)) +
                      a * ∑' k : ℕ, φ k * U (Z t x h - (k : ℤ))) := by
                  apply tsum_congr
                  intro h
                  congr 1
                  rw [show Z t x h = sSRule sStar SStar (state Z x t h) from hstat_rule _ _ t x h]
                  exact hUeq _
                _ = B Z x t + a * (∑' h : Fin t → ℕ, weight φ h *
                    (∑' k : ℕ, φ k * U (Z t x h - (k : ℤ)))) := by
                  simp only [B, mul_add, ENNReal.tsum_add, mul_left_comm, ENNReal.tsum_mul_left]
                _ = B Z x t + a * J x (t + 1) := by
                  congr 1
                  congr 1
                  dsimp [J]
                  rw [hsum_snoc, ENNReal.tsum_comm]
                  simp only [hw_snoc, state, Fin.init_snoc, Fin.snoc_last, mul_assoc, ENNReal.tsum_mul_left]
            have hJbound : ∀ x n t, (∑ i ∈ Finset.range n, a ^ i * B Z x (t + i)) ≤ J x t := by
              intro x n
              induction n with
              | zero => intro t; simp
              | succ n ih =>
                intro t
                rw [hBsum, hJrec x t]
                exact add_le_add_right (mul_le_mul_right (ih (t + 1)) a) _
            have htotal : ∀ Y, Admissible Y → ∀ x,
                (∑' t : ℕ, a ^ t * B Z x t) ≤ ∑' t : ℕ, a ^ t * B Y x t := by
              intro Y hY x
              apply le_trans (b := U x)
              · rw [ENNReal.tsum_eq_iSup_nat]
                apply iSup_le
                intro n
                have h := hJbound x n 0
                simpa [J, weight, state] using h
              · apply iSup_le
                intro n
                have h := hHbound Y hY x n 0
                simp only [hHinitial, Nat.zero_add] at h
                exact h.trans (ENNReal.sum_le_tsum (Finset.range n))
            have hdisc_cost : α < 1 → ∀ Y x, discountedCost φ G K α x Y =
                ((∑' t : ℕ, a ^ t * B Y x t : ℝ≥0∞) : EReal) +
                  (((1 - α)⁻¹ * G (SLow G) : ℝ) : EReal) := by
              intro hαlt Y x
              have h₁ : Filter.Tendsto
                  (fun n : ℕ => ((∑ i ∈ Finset.range n, a ^ i * B Y x i : ℝ≥0∞) : EReal))
                  Filter.atTop (nhds ((∑' i : ℕ, a ^ i * B Y x i : ℝ≥0∞) : EReal)) :=
                EReal.tendsto_coe_ennreal.mpr (ENNReal.tendsto_nat_tsum _)
              have h₂ : Filter.Tendsto
                  (fun n : ℕ => ((∑ i ∈ Finset.range n, α ^ i * G (SLow G) : ℝ) : EReal))
                  Filter.atTop (nhds (((1 - α)⁻¹ * G (SLow G) : ℝ) : EReal)) :=
                EReal.tendsto_coe.mpr (((hasSum_geometric_of_lt_one hα₀ hαlt).mul_right (G (SLow G))).tendsto_sum_nat)
              have hadd := (EReal.continuousAt_add
                (p := (((∑' i : ℕ, a ^ i * B Y x i : ℝ≥0∞) : EReal),
                  (((1 - α)⁻¹ * G (SLow G) : ℝ) : EReal)))
                (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))).tendsto.comp (h₁.prodMk_nhds h₂)
              have hc : Filter.Tendsto (fun n : ℕ => cost φ G K α n x Y) Filter.atTop
                  (nhds (((∑' t : ℕ, a ^ t * B Y x t : ℝ≥0∞) : EReal) +
                    (((1 - α)⁻¹ * G (SLow G) : ℝ) : EReal))) := by
                exact hadd.congr' (Filter.Eventually.of_forall (fun n => (hcostshift Y x n).symm))
              exact hc.liminf_eq
            by_cases hαlt : α < 1
            · refine ⟨sStar, SStar, ?_, hpbound.1, hpbound.2.1, hsH_le, hpbound.2.2.1, hpbound.2.2.2⟩
              refine ⟨hstat_adm sStar SStar hsr, fun Y hY x => ?_⟩
              simp only [infCost, if_pos hαlt]
              rw [hdisc_cost hαlt, hdisc_cost hαlt]
              exact add_le_add_left (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (htotal Y hY x)) _
            · have hαeq : α = 1 := le_antisymm hα₁ (le_of_not_gt hαlt)
              have hφlt : (φ 0).toReal < 1 := by simpa only [hαeq, one_mul] using hφ0
              let r : ℕ → ℝ := fun n => V n (sLow G K - 1)
              have hflat : ∀ n x, x < sLow G K → V n x = r n := by
                intro n x hx
                cases n with
                | zero => simp [r, hV0]
                | succ n =>
                  rw [hVsucc, show r (n + 1) = V (n + 1) (sLow G K - 1) from rfl, hVsucc]
                  have h₁ : x < ss n := hx.trans_le (hsslo n)
                  have h₂ : sLow G K - 1 < ss n := by have := hsslo n; omega
                  rw [if_pos h₁, if_pos h₂]
              have hr_lower : ∀ n x, r n - K ≤ V n x := by
                intro n x
                by_cases hx : x < sLow G K
                · rw [hflat n x hx]
                  linarith only [hK]
                · have hh := (hVgood n).2.2.2 (sLow G K - 1) x (by omega)
                  change r n ≤ K + V n x at hh
                  linarith only [hh]
              have hr_below : ∀ n x, x ≤ SLow G → V n x ≤ r n := by
                intro n x hx
                by_cases hxl : x < sLow G K
                · exact (hflat n x hxl).le
                · exact (hVgood n).2.2.1 (show sLow G K - 1 ≤ SLow G by omega) hx (by omega)
              have hr_succ : ∀ n, G (SLow G) + r n ≤ r (n + 1) := by
                intro n
                have hs : sLow G K - 1 < ss n := by have := hsslo n; omega
                change G (SLow G) + r n ≤ V (n + 1) (sLow G K - 1)
                rw [hVsucc, if_pos hs, hαeq, one_mul]
                have hl := hEx_lower (V n) (hVgood n).2.1 (r n - K) (hr_lower n) (SS n)
                linarith only [hl,hSLmem (SS n)]
              let I : ℕ → ℝ := fun k => if k = 0 then 0 else 1
              have hIint : MeasureTheory.Integrable I φ.toMeasure := by
                apply (MeasureTheory.integrable_const (1 : ℝ)).mono'
                  (measurable_of_countable _).aestronglyMeasurable
                apply Filter.Eventually.of_forall
                intro k
                dsimp [I]
                split_ifs <;> norm_num
              have hIval : (∫ k : ℕ, I k ∂φ.toMeasure) = 1 - (φ 0).toReal := by
                let T : ℕ → ℝ := Set.indicator {0} (fun _ => 1)
                have hTint : MeasureTheory.Integrable T φ.toMeasure :=
                  (MeasureTheory.integrable_const (1 : ℝ)).indicator (MeasurableSet.singleton 0)
                have hTval : (∫ k : ℕ, T k ∂φ.toMeasure) = (φ 0).toReal := by
                  rw [show T = Set.indicator {0} (fun _ : ℕ => (1 : ℝ)) from rfl,
                    MeasureTheory.integral_indicator (MeasurableSet.singleton 0)]
                  simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
                    MeasureTheory.Measure.restrict_apply_univ,
                    PMF.toMeasure_apply_singleton φ 0 (MeasurableSet.singleton 0)]
                have hsum : (fun k : ℕ => I k + T k) = fun _ => (1 : ℝ) := by
                  funext k
                  simp only [I, T, Set.indicator_apply, Set.mem_singleton_iff]
                  split_ifs <;> norm_num
                have hh := congrArg (fun f : ℕ → ℝ => ∫ k : ℕ, f k ∂φ.toMeasure) hsum
                rw [MeasureTheory.integral_add hIint hTint, hTval] at hh
                simpa using (show (∫ k : ℕ, I k ∂φ.toMeasure) = 1 - (φ 0).toReal by simpa using eq_sub_iff_add_eq.mpr hh)
              have hspan : ∀ M : ℤ, SLow G ≤ M → ∃ C : ℝ, 0 ≤ C ∧
                  ∀ n x, x ≤ M → V n x ≤ r n + C * ((max (x - SLow G) 0 : ℤ) : ℝ) := by
                intro M hM
                let C : ℝ := (G M - G (SLow G)) / (1 - (φ 0).toReal)
                have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr (hSLmem M)) (sub_pos.mpr hφlt).le
                have hCeq : C * (1 - (φ 0).toReal) = G M - G (SLow G) := by
                  dsimp [C]
                  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hφlt))
                refine ⟨C, hC, ?_⟩
                intro n
                induction n with
                | zero =>
                  intro x hx
                  simp only [hV0, r, zero_add]
                  exact mul_nonneg hC (by exact_mod_cast (le_max_right (x - SLow G) 0))
                | succ n ih =>
                  intro x hx
                  by_cases hxm : x ≤ SLow G
                  · exact (hr_below (n + 1) x hxm).trans (le_add_of_nonneg_right (mul_nonneg hC (by exact_mod_cast (le_max_right (x - SLow G) 0))))
                  · have hmx : SLow G + 1 ≤ x := by omega
                    have hd : ((max (x - SLow G) 0 : ℤ) : ℝ) = ((x - SLow G : ℤ) : ℝ) := by rw [max_eq_left (by omega)]
                    have hpoint : ∀ k : ℕ, V n (x - (k : ℤ)) ≤
                        r n + C * (((x - SLow G : ℤ) : ℝ) - I k) := by
                      intro k
                      apply (ih (x - (k : ℤ)) (by omega)).trans
                      apply add_le_add_right
                      apply mul_le_mul_of_nonneg_left _ hC
                      by_cases hk : k = 0
                      · simp [I, hk, max_eq_left (by omega : 0 ≤ x - SLow G)]
                      · have hki : (1 : ℤ) ≤ (k : ℤ) := by omega
                        have hh : max (x - (k : ℤ) - SLow G) 0 ≤ x - SLow G - 1 := by omega
                        simpa only [I, if_neg hk, Int.cast_sub, Int.cast_one] using (Int.cast_le.mpr hh :
                          ((max (x - (k : ℤ) - SLow G) 0 : ℤ) : ℝ) ≤ ((x - SLow G - 1 : ℤ) : ℝ))
                    have hiR : MeasureTheory.Integrable
                        (fun k : ℕ => r n + C * (((x - SLow G : ℤ) : ℝ) - I k)) φ.toMeasure :=
                      (MeasureTheory.integrable_const (r n)).add
                        (((MeasureTheory.integrable_const (((x - SLow G : ℤ) : ℝ))).sub hIint).const_mul C)
                    have he := MeasureTheory.integral_mono (hEx_int (V n) (hVgood n).2.1 x) hiR hpoint
                    have hiD : MeasureTheory.Integrable (fun k : ℕ => (((x - SLow G : ℤ) : ℝ)) - I k) φ.toMeasure :=
                      (MeasureTheory.integrable_const (((x - SLow G : ℤ) : ℝ))).sub hIint
                    rw [MeasureTheory.integral_add (MeasureTheory.integrable_const (r n)) (hiD.const_mul C),
                      MeasureTheory.integral_const_mul,
                      MeasureTheory.integral_sub (MeasureTheory.integrable_const (((x - SLow G : ℤ) : ℝ))) hIint,
                      hIval] at he
                    simp only [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul] at he
                    change Ex (V n) x ≤ r n + C * (((x - SLow G : ℤ) : ℝ) - (1 - (φ 0).toReal)) at he
                    have hv := hVineq n x x le_rfl
                    simp only [lt_self_iff_false, if_false, zero_add, hαeq, one_mul] at hv
                    have hg := hG_right (by omega : SLow G ≤ x) hM hx
                    rw [hd]
                    nlinarith only [hr_succ n, hCeq, hv, he, hg]
              have hprop_one : ∀ i j : ℕ, ∀ d : ℝ, ∀ M : ℤ, SHigh G K α ≤ M →
                  (∀ x ≤ M, V i x + d ≤ V j x) → ∀ x ≤ M, V (i + 1) x + d ≤ V (j + 1) x := by
                intro i j d M hM hij x hx
                let y := sSRule (ss j) (SS j) x
                have hy : y ≤ M := by dsimp [y, sSRule]; split_ifs <;> have := hSShi j <;> omega
                have hxy : x ≤ y := by dsimp [y, sSRule]; split_ifs <;> have := hssSS j <;> omega
                have hi := hVineq i x y hxy
                have hj := hVaction j x
                have he := MeasureTheory.integral_mono
                  ((hEx_int (V i) (hVgood i).2.1 y).add (MeasureTheory.integrable_const d))
                  (hEx_int (V j) (hVgood j).2.1 y) (fun k : ℕ => hij (y - (k : ℤ)) (by omega))
                simp only [Pi.add_apply] at he
                rw [MeasureTheory.integral_add (hEx_int (V i) (hVgood i).2.1 y) (MeasureTheory.integrable_const d)] at he
                simp only [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul] at he
                change Ex (V i) y + d ≤ Ex (V j) y at he
                change V (j + 1) x = (if x < y then K else 0) + G y + α * Ex (V j) y at hj
                rw [hαeq, one_mul] at hi hj
                linarith only [hi,hj,he]
              have hprop : ∀ i j : ℕ, ∀ d : ℝ, ∀ M : ℤ, SHigh G K α ≤ M →
                  (∀ x ≤ M, V i x + d ≤ V j x) →
                  ∀ n x, x ≤ M → V (i + n) x + d ≤ V (j + n) x := by
                intro i j d M hM hij n
                induction n with
                | zero => simpa only [Nat.add_zero] using hij
                | succ n ih =>
                  simpa only [Nat.add_succ] using hprop_one (i + n) (j + n) d M hM ih
              obtain ⟨Cspan, hCspan, hspan_bound⟩ := hspan (SHigh G K α) hSL_le
              let R : ℝ := Cspan * ((max (SHigh G K α - SLow G) 0 : ℤ) : ℝ)
              have hR : 0 ≤ R := mul_nonneg hCspan (by exact_mod_cast le_max_right (SHigh G K α - SLow G) 0)
              have hspan_uniform : ∀ n x, x ≤ SHigh G K α → V n x ≤ r n + R := by
                intro n x hx
                apply (hspan_bound n x hx).trans
                apply add_le_add_right
                apply mul_le_mul_of_nonneg_left _ hCspan
                exact_mod_cast max_le_max_right 0 (sub_le_sub_right hx (SLow G))
              let Dd : ℝ := max K R
              have hDd : 0 ≤ Dd := hK.trans (le_max_left _ _)
              have hr0 : r 0 = 0 := hV0 _
              have hr_quasi : ∀ n m : ℕ,
                  r n + r m - Dd ≤ r (n + m) ∧ r (n + m) ≤ r n + r m + Dd := by
                intro n m
                have hl := hprop 0 m (r m - K) (SHigh G K α) le_rfl
                  (fun x hx => by simpa only [hV0, zero_add] using hr_lower m x) n
                  (sLow G K - 1) (by omega)
                have hu := hprop m 0 (-(r m + R)) (SHigh G K α) le_rfl
                  (fun x hx => by rw [hV0]; linarith only [hspan_uniform m x hx]) n
                  (sLow G K - 1) (by omega)
                simp only [Nat.zero_add, Nat.add_comm m n] at hl hu
                change r n + (r m - K) ≤ r (n + m) at hl
                change r (n + m) + -(r m + R) ≤ r n at hu
                have hDK : K ≤ Dd := le_max_left _ _
                have hDR : R ≤ Dd := le_max_right _ _
                constructor <;> linarith only [hl,hu,hDK,hDR]
              have hr_linear_lower : ∀ n : ℕ, (n : ℝ) * G (SLow G) ≤ r n := by
                intro n
                induction n with
                | zero => simp [hr0]
                | succ n ih =>
                  have hh := hr_succ n
                  push_cast
                  nlinarith only [hh, ih]
              have hr_linear_upper : ∀ n : ℕ, r n ≤ (n : ℝ) * (r 1 + Dd) := by
                intro n
                induction n with
                | zero => simp [hr0]
                | succ n ih =>
                  have hh := (hr_quasi n 1).2
                  push_cast
                  nlinarith only [hh, ih]
              have hsub : Subadditive (fun n : ℕ => r n + Dd) := by
                intro n m
                linarith only [(hr_quasi n m).2]
              have hsubneg : Subadditive (fun n : ℕ => -r n + Dd) := by
                intro n m
                linarith only [(hr_quasi n m).1]
              have hb_sub : BddBelow (Set.range (fun n : ℕ => (r n + Dd) / (n : ℝ))) := by
                refine ⟨min 0 (G (SLow G)), ?_⟩
                rintro y ⟨n, rfl⟩
                by_cases hn : n = 0
                · simp [hn]
                · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
                  apply (min_le_right _ _).trans
                  apply (le_div_iff₀ hnpos).mpr
                  linarith only [hr_linear_lower n, hDd]
              have hb_subneg : BddBelow (Set.range (fun n : ℕ => (-r n + Dd) / (n : ℝ))) := by
                refine ⟨min 0 (-(r 1 + Dd)), ?_⟩
                rintro y ⟨n, rfl⟩
                by_cases hn : n = 0
                · simp [hn]
                · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
                  apply (min_le_right _ _).trans
                  apply (le_div_iff₀ hnpos).mpr
                  linarith only [hr_linear_upper n, hDd]
              let g : ℝ := hsub.lim
              have hrtend : Filter.Tendsto (fun n : ℕ => r n / (n : ℝ)) Filter.atTop (nhds g) := by
                have hh := (hsub.tendsto_lim hb_sub).sub
                  (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
                    Filter.Tendsto (fun n : ℕ => Dd / (n : ℝ)) Filter.atTop (nhds 0))
                convert hh using 1
                · funext n
                  ring
                · simp [g]
              have hgneg : hsubneg.lim = -g := by
                have hh := hrtend.neg.add
                  (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
                    Filter.Tendsto (fun n : ℕ => Dd / (n : ℝ)) Filter.atTop (nhds 0))
                have he : Filter.Tendsto (fun n : ℕ => (-r n + Dd) / (n : ℝ)) Filter.atTop (nhds (-g)) := by
                  convert hh using 1
                  · funext n
                    ring
                  · simp
                exact tendsto_nhds_unique (hsubneg.tendsto_lim hb_subneg) he
              have hr_deviation : ∀ n : ℕ, -Dd ≤ r n - (n : ℝ) * g ∧ r n - (n : ℝ) * g ≤ Dd := by
                intro n
                by_cases hn : n = 0
                · simp [hn, hr0, hDd]
                · have h₁ := hsub.lim_le_div hb_sub hn
                  have h₂ := hsubneg.lim_le_div hb_subneg hn
                  rw [hgneg] at h₂
                  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
                  have ha := (le_div_iff₀ hnpos).mp h₁
                  have hb := (le_div_iff₀ hnpos).mp h₂
                  change g * (n : ℝ) ≤ r n + Dd at ha
                  constructor <;> linarith only [ha,hb]
              have hGood_sub : ∀ F : ℤ → ℝ, Good F → ∀ d : ℝ, Good (fun x => F x - d) := by
                intro F hF d
                rcases hF with ⟨hC, ⟨⟨L,hL⟩,hU⟩,hA,hX⟩
                refine ⟨?_, ⟨⟨L-d, fun x => sub_le_sub_right (hL x) d⟩, ?_⟩, ?_, ?_⟩
                · intro x y z hxy hyz
                  simpa only [sub_sub_sub_cancel_right] using hC x y z hxy hyz
                · intro a
                  obtain ⟨C,hC⟩ := hU a
                  exact ⟨C-d, fun x hx => sub_le_sub_right (hC x hx) d⟩
                · intro x hx y hy hxy
                  exact sub_le_sub_right (hA hx hy hxy) d
                · intro x y hxy
                  linarith only [hX x y hxy]
              let f : ℕ → ℤ → ℝ := fun n x => V n x - (n : ℝ) * g
              have hfGood : ∀ n, Good (f n) := fun n => hGood_sub _ (hVgood n) _
              have hflo : ∀ n x, -Dd-K ≤ f n x := by
                intro n x
                dsimp [f]
                linarith only [hr_lower n x, (hr_deviation n).1]
              have hfup : ∀ M : ℤ, SLow G ≤ M → ∃ C : ℝ, ∀ n x, x ≤ M → f n x ≤ C := by
                intro M hM
                obtain ⟨C,hC,hb⟩ := hspan M hM
                refine ⟨Dd + C * ((max (M-SLow G) 0 : ℤ) : ℝ), ?_⟩
                intro n x hx
                have hm : C * ((max (x-SLow G) 0 : ℤ) : ℝ) ≤ C * ((max (M-SLow G) 0 : ℤ) : ℝ) :=
                  mul_le_mul_of_nonneg_left (by exact_mod_cast max_le_max_right 0 (sub_le_sub_right hx _)) hC
                dsimp [f]
                linarith only [hb n x hx, (hr_deviation n).2, hm]
              have hsupGood : ∀ F : ℕ → ℤ → ℝ, (∀ n, Good (F n)) →
                  (∃ L : ℝ, ∀ n x, L ≤ F n x) →
                  (∀ a : ℤ, ∃ C : ℝ, ∀ n x, x ≤ a → F n x ≤ C) →
                  Good (fun x => ⨆ n, F n x) := by
                intro F hF hL hU
                obtain ⟨L,hL⟩ := hL
                have hb : ∀ x, BddAbove (Set.range (fun n => F n x)) := by
                  intro x
                  obtain ⟨C,hC⟩ := hU x
                  exact ⟨C, by rintro _ ⟨n,rfl⟩; exact hC n x le_rfl⟩
                have hle : ∀ n x, F n x ≤ ⨆ n, F n x := fun n x => le_ciSup (hb x) n
                refine ⟨?_, ⟨⟨L,fun x => (hL 0 x).trans (hle 0 x)⟩, ?_⟩, ?_, ?_⟩
                · intro x y z hxy hyz
                  by_cases hxz : x = z
                  · have hy : y = x := by omega
                    subst z; subst y
                    simp
                  · have hp : (0 : ℝ) < ((z-x : ℤ) : ℝ) := by exact_mod_cast (by omega : 0 < z-x)
                    have hxy' : (0 : ℝ) ≤ ((y-x : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hxy
                    have hzy' : (0 : ℝ) ≤ ((z-y : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hyz
                    have hh : (⨆ n, F n y) ≤
                        ((((y-x : ℤ) : ℝ) * ((⨆ n, F n z) + K) +
                          ((z-y : ℤ) : ℝ) * (⨆ n, F n x)) / ((z-x : ℤ) : ℝ)) := by
                      apply ciSup_le
                      intro n
                      apply (le_div_iff₀ hp).mpr
                      have h₁ := (hF n).1 x y z hxy hyz
                      have h₂ := mul_le_mul_of_nonneg_left (hle n z) hxy'
                      have h₃ := mul_le_mul_of_nonneg_left (hle n x) hzy'
                      push_cast at *
                      nlinarith only [h₁,h₂,h₃]
                    have hh' := (le_div_iff₀ hp).mp hh
                    push_cast at *
                    nlinarith only [hh']
                · intro a
                  obtain ⟨C,hC⟩ := hU a
                  exact ⟨C, fun x hx => ciSup_le (fun n => hC n x hx)⟩
                · intro x hx y hy hxy
                  exact ciSup_le (fun n => ((hF n).2.2.1 hx hy hxy).trans (hle n x))
                · intro x y hxy
                  exact ciSup_le (fun n => by linarith only [(hF n).2.2.2 x y hxy, hle n y])
              have hlimGood : ∀ (F : ℕ → ℤ → ℝ) (H : ℤ → ℝ),
                  (∀ n, Good (F n)) → (∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (H x))) →
                  (∃ L : ℝ, ∀ n x, L ≤ F n x) →
                  (∀ a : ℤ, ∃ C : ℝ, ∀ n x, x ≤ a → F n x ≤ C) → Good H := by
                intro F H hF ht hL hU
                obtain ⟨L,hL⟩ := hL
                refine ⟨?_, ⟨⟨L,fun x => ge_of_tendsto (ht x) (Filter.Eventually.of_forall (fun n => hL n x))⟩, ?_⟩, ?_, ?_⟩
                · intro x y z hxy hyz
                  exact le_of_tendsto_of_tendsto
                    (tendsto_const_nhds.mul ((ht y).sub (ht x)))
                    (tendsto_const_nhds.mul (((ht z).sub (ht x)).add_const K))
                    (Filter.Eventually.of_forall (fun n => (hF n).1 x y z hxy hyz))
                · intro a
                  obtain ⟨C,hC⟩ := hU a
                  exact ⟨C, fun x hx => le_of_tendsto (ht x) (Filter.Eventually.of_forall (fun n => hC n x hx))⟩
                · intro x hx y hy hxy
                  exact le_of_tendsto_of_tendsto (ht y) (ht x)
                    (Filter.Eventually.of_forall (fun n => (hF n).2.2.1 hx hy hxy))
                · intro x y hxy
                  exact le_of_tendsto_of_tendsto (ht x) (tendsto_const_nhds.add (ht y))
                    (Filter.Eventually.of_forall (fun n => (hF n).2.2.2 x y hxy))
              have hfu : ∀ a : ℤ, ∃ C : ℝ, ∀ n x, x ≤ a → f n x ≤ C := by
                intro a
                obtain ⟨C,hC⟩ := hfup (max a (SLow G)) (le_max_right _ _)
                exact ⟨C,fun n x hx => hC n x (hx.trans (le_max_left _ _))⟩
              have hfb : ∀ x, BddAbove (Set.range (fun n => f n x)) := by
                intro x
                obtain ⟨C,hC⟩ := hfu x
                exact ⟨C, by rintro _ ⟨n,rfl⟩; exact hC n x le_rfl⟩
              let A : ℕ → ℤ → ℝ := fun N x => ⨆ n : ℕ, f (N+n) x
              have hAb : ∀ N x, BddAbove (Set.range (fun n => f (N+n) x)) :=
                fun N x => (hfb x).mono (by rintro _ ⟨n,rfl⟩; exact ⟨N+n,rfl⟩)
              have hAle : ∀ N n x, f (N+n) x ≤ A N x := fun N n x => le_ciSup (hAb N x) n
              have hAG : ∀ N, Good (A N) := by
                intro N
                exact hsupGood _ (fun n => hfGood (N+n)) ⟨-Dd-K,fun n x => hflo (N+n) x⟩
                  (fun a => by obtain ⟨C,hC⟩ := hfu a; exact ⟨C,fun n x hx => hC (N+n) x hx⟩)
              have hAlo : ∀ N x, -Dd-K ≤ A N x := fun N x => (hflo N x).trans (by simpa only [Nat.add_zero] using hAle N 0 x)
              have hAu : ∀ a : ℤ, ∃ C : ℝ, ∀ N x, x ≤ a → A N x ≤ C := by
                intro a
                obtain ⟨C,hC⟩ := hfu a
                exact ⟨C,fun N x hx => ciSup_le (fun n => hC (N+n) x hx)⟩
              have hAanti : ∀ x, Antitone (fun N => A N x) := by
                intro x
                apply antitone_nat_of_succ_le
                intro N
                apply ciSup_le
                intro n
                simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hAle N (n+1) x
              let v : ℤ → ℝ := fun x => ⨅ N, A N x
              have hvt : ∀ x, Filter.Tendsto (fun N => A N x) Filter.atTop (nhds (v x)) :=
                fun x => tendsto_atTop_ciInf (hAanti x) ⟨-Dd-K,by rintro _ ⟨n,rfl⟩; exact hAlo n x⟩
              have hvG : Good v := hlimGood A v hAG hvt ⟨-Dd-K,hAlo⟩ hAu
              have hvlo : ∀ x, -Dd-K ≤ v x := fun x => ge_of_tendsto (hvt x) (Filter.Eventually.of_forall (fun N => hAlo N x))
              have hExf : ∀ n y, Ex (f n) y = Ex (V n) y - (n : ℝ)*g := by
                intro n y
                dsimp [Ex, f]
                rw [MeasureTheory.integral_sub (hEx_int (V n) (hVgood n).2.1 y) (MeasureTheory.integrable_const _)]
                simp
              have hAineq : ∀ N x y, x ≤ y → A (N+1) x ≤
                  (if x < y then K else 0) + G y - g + Ex (A N) y := by
                intro N x y hxy
                apply ciSup_le
                intro n
                have he := MeasureTheory.integral_mono (hEx_int (f (N+n)) (hfGood _).2.1 y)
                  (hEx_int (A N) (hAG N).2.1 y) (fun k => hAle N n (y-(k:ℤ)))
                change Ex (f (N+n)) y ≤ Ex (A N) y at he
                rw [hExf] at he
                have hh := hVineq (N+n) x y hxy
                rw [hαeq, one_mul] at hh
                dsimp [f]
                have hn : ((N+1+n : ℕ) : ℝ) = (N+n : ℕ)+1 := by push_cast; ring
                rw [show N+1+n = (N+n)+1 by omega, Nat.cast_add, Nat.cast_one]
                nlinarith only [hh,he]
              have hvineq : ∀ x y, x ≤ y → v x ≤ (if x < y then K else 0) + G y - g + Ex v y := by
                intro x y hxy
                have he : Filter.Tendsto (fun N => Ex (A N) y) Filter.atTop (nhds (Ex v y)) :=
                  MeasureTheory.integral_tendsto_of_tendsto_of_antitone
                    (fun N => hEx_int (A N) (hAG N).2.1 y) (hEx_int v hvG.2.1 y)
                    (Filter.Eventually.of_forall (fun k => hAanti (y-(k:ℤ))))
                    (Filter.Eventually.of_forall (fun k => hvt (y-(k:ℤ))))
                have hl : Filter.Tendsto (fun N => A (N+1) x) Filter.atTop (nhds (v x)) :=
                  (hvt x).comp (Filter.tendsto_add_atTop_nat 1)
                exact le_of_tendsto_of_tendsto hl (tendsto_const_nhds.add he)
                  (Filter.Eventually.of_forall (fun N => hAineq N x y hxy))
              let Tg : {F : ℤ → ℝ // Good F} → {F : ℤ → ℝ // Good F} :=
                fun p => ⟨fun x => (nxt p).1 x - g, hGood_sub _ (nxt p).2 g⟩
              let O : ℕ → {F : ℤ → ℝ // Good F} := Nat.rec ⟨v,hvG⟩ (fun _ p => Tg p)
              let F : ℕ → ℤ → ℝ := fun n => (O n).1
              let bs : ℕ → ℤ := fun n => selS (O n).1 (O n).2
              let bS : ℕ → ℤ := fun n => selT (O n).1 (O n).2
              have hFG : ∀ n, Good (F n) := fun n => (O n).2
              have hbs : ∀ n, sLow G K ≤ bs n ∧ bs n ≤ sHigh G K α ∧
                  SLow G ≤ bS n ∧ bS n ≤ SHigh G K α := by
                intro n
                exact ⟨hselL _ (O n).2, hselH _ (O n).2, hselm _ (O n).2, hselSH _ (O n).2⟩
              have hbsS : ∀ n, bs n ≤ bS n := fun n => (hbs n).2.1.trans (hsH_le.trans (hbs n).2.2.1)
              have hFopt : ∀ n x y, x ≤ y → F (n+1) x ≤
                  (if x < y then K else 0) + G y + Ex (F n) y - g := by
                intro n x y hxy
                have hh := hselopt (O n).1 (O n).2 x y hxy
                change (if x < bs n then K + (G (bS n) + α * Ex (F n) (bS n))
                  else G x + α * Ex (F n) x) - g ≤ _
                simpa only [hαeq, one_mul] using (sub_le_sub_right hh g)
              have hFact : ∀ n x, F (n+1) x =
                  (if x < sSRule (bs n) (bS n) x then K else 0) +
                    G (sSRule (bs n) (bS n) x) + Ex (F n) (sSRule (bs n) (bS n) x) - g := by
                intro n x
                change (if x < bs n then K + (G (bS n) + α * Ex (F n) (bS n))
                  else G x + α * Ex (F n) x) - g = _
                rw [hαeq]
                by_cases hx : x < bs n
                · simp [sSRule, hx, hx.trans_le (hbsS n), add_assoc]
                · simp [sSRule, hx]
              have hFmono : ∀ x, Monotone (fun n => F n x) := by
                have hh : ∀ n x, F n x ≤ F (n+1) x := by
                  intro n
                  induction n with
                  | zero =>
                    intro x
                    rw [hFact]
                    have hxy : x ≤ sSRule (bs 0) (bS 0) x := by unfold sSRule; split_ifs <;> have := hbsS 0 <;> omega
                    change v x ≤ (if x < sSRule (bs 0) (bS 0) x then K else 0) + G (sSRule (bs 0) (bS 0) x) + Ex v (sSRule (bs 0) (bS 0) x) - g
                    linarith only [hvineq x _ hxy]
                  | succ n ih =>
                    intro x
                    let y := sSRule (bs (n+1)) (bS (n+1)) x
                    have hxy : x ≤ y := by dsimp [y,sSRule]; split_ifs <;> have := hbsS (n+1) <;> omega
                    have hi := hFopt n x y hxy
                    have hj := hFact (n+1) x
                    have he := MeasureTheory.integral_mono (hEx_int (F n) (hFG n).2.1 y)
                      (hEx_int (F (n+1)) (hFG (n+1)).2.1 y) (fun k => ih (y-(k:ℤ)))
                    change Ex (F n) y ≤ Ex (F (n+1)) y at he
                    change F (n+1+1) x = (if x < y then K else 0) + G y + Ex (F (n+1)) y - g at hj
                    linarith only [hi,hj,he]
                exact fun x => monotone_nat_of_le_succ (fun n => hh n x)
              have hFcompare : ∀ M : ℤ, SHigh G K α ≤ M → ∀ C : ℝ,
                  (∀ x ≤ M, v x ≤ C) → ∀ n x, x ≤ M → F n x ≤ f n x + C := by
                intro M hM C hC n
                induction n with
                | zero => intro x hx; simpa [F,O,f,hV0] using hC x hx
                | succ n ih =>
                  intro x hx
                  let y := sSRule (ss n) (SS n) x
                  have hy : y ≤ M := by dsimp [y,sSRule]; split_ifs <;> have := hSShi n <;> omega
                  have hxy : x ≤ y := by dsimp [y,sSRule]; split_ifs <;> have := hssSS n <;> omega
                  have hi := hFopt n x y hxy
                  have hj := hVaction n x
                  rw [hαeq, one_mul] at hj
                  have he := MeasureTheory.integral_mono (hEx_int (F n) (hFG n).2.1 y)
                    ((hEx_int (f n) (hfGood n).2.1 y).add (MeasureTheory.integrable_const C))
                    (fun k => ih (y-(k:ℤ)) (by omega))
                  simp only [Pi.add_apply] at he
                  rw [MeasureTheory.integral_add (hEx_int (f n) (hfGood n).2.1 y)
                    (MeasureTheory.integrable_const C)] at he
                  simp only [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul] at he
                  change Ex (F n) y ≤ Ex (f n) y + C at he
                  rw [hExf] at he
                  change V (n+1) x = (if x < y then K else 0) + G y + Ex (V n) y at hj
                  dsimp [f]
                  push_cast
                  nlinarith only [hi,hj,he]
              have hFu : ∀ a : ℤ, ∃ C : ℝ, ∀ n x, x ≤ a → F n x ≤ C := by
                intro a
                let M := max a (SHigh G K α)
                obtain ⟨C,hC⟩ := hvG.2.1.2 M
                obtain ⟨D,hD⟩ := hfu M
                refine ⟨D+C, fun n x hx => ?_⟩
                have hxM : x ≤ M := hx.trans (le_max_left _ _)
                exact (hFcompare M (le_max_right _ _) C hC n x hxM).trans (add_le_add (hD n x hxM) le_rfl)
              have hFlo : ∀ n x, -Dd-K ≤ F n x := fun n x => (hvlo x).trans (hFmono x (Nat.zero_le n))
              let u : ℤ → ℝ := fun x => ⨆ n, F n x
              have huG : Good u := hsupGood F hFG ⟨-Dd-K,hFlo⟩ hFu
              have hut : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (u x)) := by
                intro x
                obtain ⟨C,hC⟩ := hFu x
                exact tendsto_atTop_ciSup (hFmono x) ⟨C, by rintro _ ⟨n,rfl⟩; exact hC n x le_rfl⟩
              have hEut : ∀ y, Filter.Tendsto (fun n => Ex (F n) y) Filter.atTop (nhds (Ex u y)) := by
                intro y
                exact MeasureTheory.integral_tendsto_of_tendsto_of_monotone
                  (fun n => hEx_int (F n) (hFG n).2.1 y) (hEx_int u huG.2.1 y)
                  (Filter.Eventually.of_forall (fun k => hFmono (y-(k:ℤ))))
                  (Filter.Eventually.of_forall (fun k => hut (y-(k:ℤ))))
              let qq : ℕ → C := fun n => ⟨(bs n,bS n), by
                simp only [Finset.mem_product,Finset.mem_Icc]; exact ⟨⟨(hbs n).1,(hbs n).2.1⟩,(hbs n).2.2⟩⟩
              obtain ⟨pp,hpp⟩ := Finite.exists_infinite_fiber qq
              have hpp' : (qq ⁻¹' {pp}).Infinite := Set.infinite_coe_iff.mp hpp
              let s : ℤ := pp.1.1
              let S : ℤ := pp.1.2
              have hbounds : sLow G K ≤ s ∧ s ≤ sHigh G K α ∧ SLow G ≤ S ∧ S ≤ SHigh G K α := by
                have hh := pp.2
                simp only [Finset.mem_product,Finset.mem_Icc] at hh
                exact ⟨hh.1.1,hh.1.2,hh.2.1,hh.2.2⟩
              have hsS : s ≤ S := hbounds.2.1.trans (hsH_le.trans hbounds.2.2.1)
              have hrec : ∀ n : ℕ, ∃ j, n ≤ j ∧ bs j = s ∧ bS j = S := by
                intro n
                obtain ⟨j,hj,hnj⟩ := hpp'.exists_gt n
                have he : qq j = pp := hj
                exact ⟨j,hnj.le,congrArg (fun z : C => z.1.1) he,congrArg (fun z : C => z.1.2) he⟩
              choose j hj hjs hjS using hrec
              have hjt : Filter.Tendsto j Filter.atTop Filter.atTop := Filter.tendsto_atTop_mono hj Filter.tendsto_id
              have hueq : ∀ x, g + u x = (if x < sSRule s S x then K else 0) + G (sSRule s S x) + Ex u (sSRule s S x) := by
                intro x
                have h₁ := ((hut x).comp (Filter.tendsto_add_atTop_nat 1)).comp hjt
                have h₂ := ((Filter.Tendsto.const_add ((if x < sSRule s S x then K else 0) + G (sSRule s S x)) (hEut (sSRule s S x))).sub_const g).comp hjt
                have he : (fun n => F (j n+1) x) = (fun n =>
                  (if x < sSRule s S x then K else 0) + G (sSRule s S x) + Ex (F (j n)) (sSRule s S x) - g) := by
                  funext n
                  rw [hFact, hjs, hjS]
                change Filter.Tendsto (fun n => F (j n+1) x) Filter.atTop (nhds (u x)) at h₁
                rw [he] at h₁
                have hh := tendsto_nhds_unique h₁ h₂
                linarith only [hh]
              have hgc : G (SLow G) ≤ g := by
                apply ge_of_tendsto hrtend
                filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
                apply (le_div_iff₀ (by exact_mod_cast (by omega : 0 < n) : (0 : ℝ) < n)).mpr
                simpa only [mul_comm] using hr_linear_lower n
              let Z' : Policy := stationary s S
              let L : ℝ := -Dd-K
              have huL : ∀ x, L ≤ u x := by
                intro x
                exact (hFlo 0 x).trans (le_ciSup (by
                  obtain ⟨C,hC⟩ := hFu x
                  exact ⟨C,by rintro _ ⟨n,rfl⟩; exact hC n x le_rfl⟩) 0)
              let Rb : ℤ → ℝ := fun x => u x - L
              have hRb : ∀ x, 0 ≤ Rb x := fun x => sub_nonneg.mpr (huL x)
              have hRbint : ∀ y, MeasureTheory.Integrable (fun k : ℕ => Rb (y-(k:ℤ))) φ.toMeasure :=
                fun y => (hEx_int u huG.2.1 y).sub (MeasureTheory.integrable_const L)
              have hRbE : ∀ y, (∫ k : ℕ, Rb (y-(k:ℤ)) ∂φ.toMeasure) = Ex u y - L := by
                intro y
                dsimp [Rb,Ex]
                rw [MeasureTheory.integral_sub (hEx_int u huG.2.1 y) (MeasureTheory.integrable_const L)]
                simp
              have hRbsum : ∀ y, ENNReal.ofReal (Ex u y-L) = ∑' k : ℕ, φ k * ENNReal.ofReal (Rb (y-(k:ℤ))) := by
                intro y
                rw [← hRbE, MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hRbint y)
                  (Filter.Eventually.of_forall (fun k => hRb (y-(k:ℤ))))]
                rw [MeasureTheory.lintegral_countable']
                apply tsum_congr
                intro k
                rw [PMF.toMeasure_apply_singleton φ k (MeasurableSet.singleton k),mul_comm]
              let d : ℝ≥0∞ := ENNReal.ofReal (g-G (SLow G))
              have hbell : ∀ x, ENNReal.ofReal ((if x < sSRule s S x then K else 0) +
                    G (sSRule s S x) - G (SLow G)) +
                  (∑' k : ℕ, φ k * ENNReal.ofReal (Rb (sSRule s S x-(k:ℤ)))) = d + ENNReal.ofReal (Rb x) := by
                intro x
                rw [← hRbsum]
                have hc : 0 ≤ (if x < sSRule s S x then K else 0) + G (sSRule s S x) - G (SLow G) := by
                  have hh := hSLmem (sSRule s S x)
                  split_ifs <;> linarith only [hK,hh]
                have he : 0 ≤ Ex u (sSRule s S x)-L := by
                  rw [← hRbE]
                  exact MeasureTheory.integral_nonneg (fun k => hRb _)
                rw [← ENNReal.ofReal_add hc he, ← ENNReal.ofReal_add (sub_nonneg.mpr hgc) (hRb x)]
                congr 1
                dsimp [Rb]
                linarith only [hueq x]
              let Qb : ℤ → ℕ → ℝ≥0∞ := fun x t =>
                ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (Rb (state Z' x t h))
              have hQbrec : ∀ x t, B Z' x t + Qb x (t+1) = d + Qb x t := by
                intro x t
                have hrec : Qb x (t+1) = ∑' h : Fin t → ℕ, weight φ h *
                    (∑' k : ℕ, φ k * ENNReal.ofReal (Rb (Z' t x h-(k:ℤ)))) := by
                  dsimp [Qb]
                  rw [hsum_snoc, ENNReal.tsum_comm]
                  simp only [hw_snoc,state,Fin.init_snoc,Fin.snoc_last,mul_assoc,ENNReal.tsum_mul_left]
                rw [hrec]
                change (∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal
                  ((if state Z' x t h < Z' t x h then K else 0) + G (Z' t x h)-G (SLow G))) + _ = _
                rw [← ENNReal.tsum_add]
                calc
                  _ = ∑' h : Fin t → ℕ, weight φ h * (d + ENNReal.ofReal (Rb (state Z' x t h))) := by
                    apply tsum_congr
                    intro h
                    have hz : Z' t x h = sSRule s S (state Z' x t h) := hstat_rule s S t x h
                    rw [← mul_add, hz, hbell]
                  _ = d + Qb x t := by
                    simp only [mul_add,ENNReal.tsum_add,ENNReal.tsum_mul_right,hw_one,one_mul,Qb]
              have hQb0 : ∀ x, Qb x 0 = ENNReal.ofReal (Rb x) := by intro x; simp [Qb,weight,state]
              have htel : ∀ x n, (∑ i ∈ Finset.range n, B Z' x i) + Qb x n = (n : ℝ≥0∞)*d + ENNReal.ofReal (Rb x) := by
                intro x n
                induction n with
                | zero => simp [hQb0]
                | succ n ih =>
                  rw [Finset.sum_range_succ,add_assoc,hQbrec,← add_assoc,
                    add_right_comm _ d,ih]
                  push_cast
                  ring
              have hboundcost : ∀ x n, cost φ G K 1 n x Z' ≤ ((n : ℝ)*g + Rb x : ℝ) := by
                intro x n
                have hh : (∑ i ∈ Finset.range n, B Z' x i) ≤ (n : ℝ≥0∞)*d + ENNReal.ofReal (Rb x) := by
                  rw [← htel x n]
                  exact le_self_add
                have he := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hh
                have hshift := hcostshift Z' x n
                rw [hαeq] at hshift
                simp only [a,hαeq,ENNReal.ofReal_one,one_pow,one_mul,Finset.sum_const,
                  Finset.card_range,nsmul_eq_mul] at hshift
                rw [hshift]
                have hn : (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := by simp
                rw [hn,show d = ENNReal.ofReal (g-G (SLow G)) from rfl,
                  ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
                  ← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hgc)) (hRb x),
                  EReal.coe_ennreal_ofReal,
                  max_eq_left (add_nonneg (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hgc)) (hRb x))] at he
                have hc := add_le_add_left he (((n : ℝ)*G (SLow G) : ℝ) : EReal)
                rw [← EReal.coe_add] at hc
                convert hc using 1 <;> congr 1 <;> ring
              have hPvalue : ∀ n x, cost φ G K 1 n x (P n) = (V n x : EReal) := by
                intro n x
                have hh := hcostshift (P n) x n
                rw [hαeq] at hh
                rw [← hQNC] at hh
                rw [EReal.coe_ennreal_ofReal, max_eq_left (hWnonneg n x)] at hh
                have hc : ∀ n, c n = ∑ i ∈ Finset.range n, (1 : ℝ)^i * G (SLow G) := by
                  intro n
                  induction n with
                  | zero => simp [hc0]
                  | succ n ih => rw [hcsucc,hαeq,one_mul,ih,Finset.sum_range_succ]; simp; ring
                rw [← hc] at hh
                rw [← EReal.coe_add] at hh
                convert hh using 1
                dsimp [W]
                congr 1
                ring
              have hlowercost : ∀ Y, Admissible Y → ∀ x n, ((r n-K : ℝ) : EReal) ≤ cost φ G K 1 n x Y := by
                intro Y hY x n
                have hh := (hP_optimal n).2 Y hY x
                rw [hαeq,hPvalue] at hh
                exact (EReal.coe_le_coe_iff.mpr (hr_lower n x)).trans hh
              have hupperAvg : ∀ x, averageCost φ G K x Z' ≤ (g : EReal) := by
                intro x
                have ht : Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ * ((n : ℝ)*g + Rb x) : ℝ))
                    Filter.atTop (nhds g) := by
                  have hh := Filter.Tendsto.const_add g
                    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
                      Filter.Tendsto (fun n : ℕ => Rb x / (n : ℝ)) Filter.atTop (nhds 0))
                  have he : (fun n : ℕ => (n : ℝ)⁻¹ * ((n : ℝ)*g+Rb x)) =ᶠ[Filter.atTop]
                      (fun n : ℕ => g+Rb x/(n:ℝ)) := by
                    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
                    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
                    field_simp
                  simpa using hh.congr' he.symm
                have hte := EReal.tendsto_coe.mpr ht
                rw [averageCost]
                rw [← hte.liminf_eq]
                refine Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n => ?_))
                rw [EReal.coe_mul]
                exact mul_le_mul_of_nonneg_left (hboundcost x n) (by exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg n : (0:ℝ) ≤ n))
              have hlowerAvg : ∀ Y, Admissible Y → ∀ x, (g : EReal) ≤ averageCost φ G K x Y := by
                intro Y hY x
                have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (r n-K)) Filter.atTop (nhds g) := by
                  have hh := hrtend.sub
                    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
                      Filter.Tendsto (fun n : ℕ => K/(n:ℝ)) Filter.atTop (nhds 0))
                  convert hh using 1
                  · funext n; ring
                  · simp
                have hte := EReal.tendsto_coe.mpr ht
                rw [averageCost,← hte.liminf_eq]
                refine Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n => ?_))
                rw [EReal.coe_mul]
                exact mul_le_mul_of_nonneg_left (hlowercost Y hY x n) (by exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg n : (0:ℝ) ≤ n))
              refine ⟨s,S,?_,hbounds.1,hbounds.2.1,hsH_le,hbounds.2.2.1,hbounds.2.2.2⟩
              refine ⟨hstat_adm s S hsS,fun Y hY x => ?_⟩
              simp only [infCost,if_neg hαlt]
              exact (hupperAvg x).trans (hlowerAvg Y hY x)
