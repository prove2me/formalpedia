-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.lowPt_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:16.221461+00:00
-- url     : https://prove2.me/submissions/d5346033-ff59-48f6-8782-468f78ebe6e2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_u_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lam_gap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_parEps_adj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_at
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_gt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
private theorem gapAtLeast_of_adjacent_sign_change_ge {n : ℕ} (ε : Fin n → Bool) (L : Fin n → ℝ) (h : ℝ)
    (hL : StrictAnti L)
    (hadj : ∀ a c : Fin n, c.val = a.val + 1 → ε a ≠ ε c → h ≤ L a - L c) :
    GapAtLeast ε L h := by
  have key : ∀ (d : ℕ) (a c : Fin n), c.val = a.val + d + 1 → ε a ≠ ε c → h ≤ L a - L c := by
    intro d
    induction d with
    | zero =>
      intro a c hac hne
      exact hadj a c (by omega) hne
    | succ d ih =>
      intro a c hac hne
      have hm : a.val + 1 < n := by have := c.isLt; omega
      obtain ⟨m, hmv⟩ : ∃ m : Fin n, m.val = a.val + 1 := ⟨⟨a.val + 1, hm⟩, rfl⟩
      have ham : a < m := Fin.lt_def.mpr (by omega)
      have hmc : m < c := Fin.lt_def.mpr (by omega)
      have h1 : L m < L a := hL ham
      have h2 : L c < L m := hL hmc
      by_cases hε : ε a = ε m
      · have h3 := ih m c (by omega) (fun heq => hne (hε.trans heq))
        linarith
      · have h3 := hadj a m hmv hε
        linarith
  intro a c hne
  rcases lt_trichotomy a.val c.val with hac | hac | hac
  · have h1 := key (c.val - a.val - 1) a c (by omega) hne
    have h2 : L c < L a := hL (Fin.lt_def.mpr hac)
    rw [abs_of_nonneg (show (0 : ℝ) ≤ L a - L c by linarith)]
    exact h1
  · exact absurd (congrArg ε (Fin.ext hac)) hne
  · have h1 := key (a.val - c.val - 1) c a (by omega) (Ne.symm hne)
    have h2 : L a < L c := hL (Fin.lt_def.mpr hac)
    rw [abs_of_neg (show L a - L c < 0 by linarith)]
    linarith
end ReciprocityTheory.ChartRestriction.DS.Lap
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} {h : ℝ}
    (hk : 1 ≤ k) (hHC : IsHCPar (parLam k r v b)) (hI : Interlaces k r u v b)
    (hH : HalfInts k r u v b) (hG : LowGaps r b h) (i : ℕ) (hi : i < k) (hin : i < 2 * r + k + 1)
    (x : ℝ) (m : ℤ) (hx : x = parLam k r v b ⟨i, hin⟩ + m) (hlo : parLam k r v b ⟨i, hin⟩ ≤ x)
    (hhi : x ≤ u ⟨i, hi⟩ - 1 / 2) :
    IsHCPar (lowPt k r u v b i x) ∧ GapAtLeast (parEps k r) (lowPt k r u v b i x) h := by
  obtain ⟨hanti0, hint0⟩ := hHC
  have hLlt : ∀ (a : Fin (2 * r + k + 1)) (ha : a.val < i),
      lowPt k r u v b i x a = u ⟨a.val, by omega⟩ - 1 / 2 :=
    fun a ha => lowPt_lt i x hi a ha
  have hLgt : ∀ (a : Fin (2 * r + k + 1)), i < a.val → lowPt k r u v b i x a = parLam k r v b a :=
    fun a ha => lowPt_gt i x a ha
  have hLeq : ∀ (a : Fin (2 * r + k + 1)), a.val = i → lowPt k r u v b i x a = x := by
    intro a ha
    obtain rfl : a = ⟨i, hin⟩ := Fin.ext ha
    exact lowPt_at u v b i x hin
  have hu : ∀ (a : Fin (2 * r + k + 1)) (ha : a.val < i), u ⟨i, hi⟩ < u ⟨a.val, by omega⟩ :=
    fun a ha => u_lt hI ⟨a.val, by omega⟩ ⟨i, hi⟩ ha
  have hP : ∀ c : Fin (2 * r + k + 1), i < c.val → parLam k r v b c < parLam k r v b ⟨i, hin⟩ :=
    fun c hc => hanti0 (show (⟨i, hin⟩ : Fin (2 * r + k + 1)) < c from Fin.lt_def.mpr hc)
  have hanti : StrictAnti (lowPt k r u v b i x) := by
    intro a c hac
    have hac' : a.val < c.val := Fin.lt_def.mp hac
    rcases lt_trichotomy c.val i with hc | hc | hc
    · have ha : a.val < i := by omega
      rw [hLlt a ha, hLlt c hc]
      have h1 := u_lt hI ⟨a.val, by omega⟩ ⟨c.val, by omega⟩ hac'
      linarith
    · have ha : a.val < i := by omega
      rw [hLlt a ha, hLeq c hc]
      have h1 := hu a ha
      linarith
    · rw [hLgt c hc]
      have h1 := hP c hc
      rcases lt_trichotomy a.val i with ha | ha | ha
      · rw [hLlt a ha]
        have h2 := hu a ha
        linarith
      · rw [hLeq a ha]
        linarith
      · rw [hLgt a ha]
        exact hanti0 hac
  have hint : ∀ a : Fin (2 * r + k + 1),
      ∃ m : ℤ, lowPt k r u v b i x a - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 = (m : ℝ) := by
    intro a
    obtain ⟨m0, hm0⟩ := hint0 a
    rcases lt_trichotomy a.val i with ha | ha | ha
    · obtain ⟨m1, hm1⟩ := hH ⟨a.val, by omega⟩ a
      refine ⟨m0 + m1, ?_⟩
      rw [hLlt a ha, Int.cast_add]
      linarith
    · obtain ⟨m1, hm1⟩ := hint0 ⟨i, hin⟩
      refine ⟨m1 + m, ?_⟩
      rw [hLeq a ha, hx, Int.cast_add]
      linarith
    · rw [hLgt a ha]
      exact ⟨m0, hm0⟩
  have hadj : ∀ a c : Fin (2 * r + k + 1), c.val = a.val + 1 → parEps k r a ≠ parEps k r c →
      h ≤ lowPt k r u v b i x a - lowPt k r u v b i x c := by
    intro a c hcv hne
    have hc : a.val + 1 < 2 * r + k + 1 := by have := c.isLt; omega
    have hcE : c = ⟨a.val + 1, hc⟩ := Fin.ext hcv
    rw [hcE] at hne ⊢
    have hka := parEps_adj a hc hne
    have hg := lam_gap (v := v) hk hG a hc hka
    rw [hLgt ⟨a.val + 1, hc⟩ (show i < a.val + 1 by omega)]
    rcases lt_or_eq_of_le (show i ≤ a.val by omega) with ha | ha
    · rw [hLgt a ha]
      exact hg
    · rw [hLeq a ha.symm]
      have haE : a = ⟨i, hin⟩ := Fin.ext ha.symm
      have hPa : parLam k r v b a = parLam k r v b ⟨i, hin⟩ := by rw [haE]
      linarith
  exact ⟨And.intro hanti hint, gapAtLeast_of_adjacent_sign_change_ge _ _ _ hanti hadj⟩
end ReciprocityTheory.ChartRestriction.DS.Lap
