-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.raiseStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:30.035732+00:00
-- url     : https://prove2.me/submissions/9ce590b4-855b-4862-89e8-124be33ce5fa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_RsParLamMinus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsExt_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsPt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsPt_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsPt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsG_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsF_step
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsParLam_minus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
private lemma strictAnti_lt_of_succ_lt (g : ℕ → ℝ) (n : ℕ) (hg : ∀ x, x + 1 < n → g (x + 1) < g x) :
    ∀ x y, x < y → y < n → g y < g x := by
  intro x y hxy hy
  induction y with
  | zero => omega
  | succ y ih =>
    rcases Nat.lt_or_ge x y with h1 | h1
    · exact lt_trans (hg y hy) (ih h1 (by omega))
    · have : x = y := by omega
      subst this
      exact hg x hy
private lemma gap_lemma_2 (g : ℕ → ℝ) (n c : ℕ) (h : ℝ)
    (hanti : ∀ x y, x < y → y < n → g y < g x)
    (hgap : ∀ x, x + 1 < n → c ≤ x → h ≤ g x - g (x + 1))
    (x y : ℕ) (hxy : x < y) (hy : y < n) (hc : c < y) : h ≤ g x - g y := by
  have h1 := hgap (y - 1) (by omega) (by omega)
  have e : y - 1 + 1 = y := by omega
  rw [e] at h1
  rcases Nat.lt_or_ge x (y - 1) with h2 | h2
  · have := hanti x (y - 1) h2 (by omega)
    linarith
  · have : x = y - 1 := by omega
    rw [this]
    exact h1
end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution : RaiseStepStatement := by
  intro k r u v b h t P hk hpar hint hhalf hlow hSC j hj hj2 hP
  have hBlt : ∀ q, q + 1 < 2 * r + 2 → rsExt b q < rsExt b (q + 1) := by
    intro q hq
    have hq0 : q + (k - 1) < 2 * r + k + 1 := by omega
    have hq1 : q + (k - 1) + 1 < 2 * r + k + 1 := by omega
    have h1 := hpar.1 (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _) :
      (⟨q + (k - 1), hq0⟩ : Fin (2 * r + k + 1)) < ⟨q + (k - 1) + 1, hq1⟩)
    rw [rsParLam_minus k r v b ⟨q + (k - 1) + 1, hq1⟩ (show k - 1 ≤ q + (k - 1) + 1 by omega),
      rsParLam_minus k r v b ⟨q + (k - 1), hq0⟩ (show k - 1 ≤ q + (k - 1) by omega)] at h1
    have e1 : (⟨q + (k - 1), hq0⟩ : Fin (2 * r + k + 1)).val - (k - 1) = q := by
      show q + (k - 1) - (k - 1) = q
      omega
    have e2 : (⟨q + (k - 1) + 1, hq1⟩ : Fin (2 * r + k + 1)).val - (k - 1) = q + 1 := by
      show q + (k - 1) + 1 - (k - 1) = q + 1
      omega
    rw [e1, e2] at h1
    linarith
  have hBgap : ∀ q, q + 1 < 2 * r + 2 → h ≤ rsExt b (q + 1) - rsExt b q := by
    intro q hq
    rw [← rsExt_mk b (q + 1) hq, ← rsExt_mk b q (by omega)]
    exact hlow ⟨q, by omega⟩ hq
  have hUlt : ∀ x, x + 1 < k → rsExt u (x + 1) < rsExt u x := by
    intro x hx
    rw [← rsExt_mk u (x + 1) hx, ← rsExt_mk u x (by omega)]
    have h1 := hint.1 ⟨x, by omega⟩
    exact lt_trans h1.2 h1.1
  have hUhalf : -rsExt b 0 ≤ rsExt u (k - 1) - 1 / 2 := by
    have hk0 : k - 1 < k := by omega
    have h1 := hint.2 (by omega)
    obtain ⟨z, hz⟩ := hhalf ⟨k - 1, hk0⟩ ⟨k - 1, by omega⟩
    rw [rsParLam_minus k r v b ⟨k - 1, by omega⟩ (le_refl _)] at hz
    have e0 : rsExt b ((⟨k - 1, by omega⟩ : Fin (2 * r + k + 1)).val - (k - 1)) =
        b ⟨0, by omega⟩ := by
      show rsExt b (k - 1 - (k - 1)) = _
      rw [Nat.sub_self, ← rsExt_mk b 0 (by omega)]
    rw [e0] at hz
    rw [← rsExt_mk u (k - 1) hk0, ← rsExt_mk b 0 (by omega)]
    have hz0 : (-1 : ℤ) < z := by
      have : ((-1 : ℤ) : ℝ) < (z : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hz1 : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show (0 : ℤ) ≤ z by omega)
    linarith
  have hstep : ∀ m, m ≤ j * t → ∀ x, x + 1 < 2 * r + k + 1 →
      rsF k (rsExt u) (rsExt b) t j m (x + 1) < rsF k (rsExt u) (rsExt b) t j m x ∧
      (k - 1 ≤ x → h ≤ rsF k (rsExt u) (rsExt b) t j m x - rsF k (rsExt u) (rsExt b) t j m (x + 1)) :=
    fun m hm x hx => rsF_step k r (rsExt u) (rsExt b) h t j m x hk hm hBlt hBgap hUlt hUhalf hx
  have hanti : ∀ m, m ≤ j * t → ∀ x y, x < y → y < 2 * r + k + 1 →
      rsF k (rsExt u) (rsExt b) t j m y < rsF k (rsExt u) (rsExt b) t j m x :=
    fun m hm => strictAnti_lt_of_succ_lt (fun z => rsF k (rsExt u) (rsExt b) t j m z) (2 * r + k + 1)
      (fun x hx => (hstep m hm x hx).1)
  have hepsc : ∀ x y : Fin (2 * r + k + 1), x.val < y.val → parEps k r x ≠ parEps k r y →
      k - 1 < y.val := by
    intro x y hxy hne
    by_contra hcon
    apply hne
    have e1 : parEps k r x = true := by
      show (if x.val < k - 1 then true else decide ((x.val - (k - 1)) % 2 = 0)) = true
      rw [if_pos (show x.val < k - 1 by omega)]
    have e2 : parEps k r y = true := by
      show (if y.val < k - 1 then true else decide ((y.val - (k - 1)) % 2 = 0)) = true
      split_ifs with h1
      · rfl
      · have : y.val - (k - 1) = 0 := by omega
        simp [this]
    rw [e1, e2]
  have hGap : ∀ m, m ≤ j * t → GapAtLeast (parEps k r) (rsPt k r u b t j m) h := by
    intro m hm x y hne
    have hg := gap_lemma_2 (fun z => rsF k (rsExt u) (rsExt b) t j m z) (2 * r + k + 1) (k - 1) h
      (hanti m hm) (fun z hz hc => (hstep m hm z hz).2 hc)
    rcases lt_trichotomy x.val y.val with h1 | h1 | h1
    · exact le_trans (hg x.val y.val h1 y.isLt (hepsc x y h1 hne)) (le_abs_self _)
    · exact absurd (congrArg (parEps k r) (Fin.ext h1)) hne
    · rw [abs_sub_comm]
      exact le_trans (hg y.val x.val h1 x.isLt (hepsc y x h1 (Ne.symm hne))) (le_abs_self _)
  have hHC : ∀ m, m ≤ j * t → IsHCPar (rsPt k r u b t j m) := by
    intro m hm
    refine ⟨fun x y hxy => hanti m hm x.val y.val hxy y.isLt, fun x => ?_⟩
    obtain ⟨z2, hz2⟩ := hpar.2 x
    by_cases hx : x.val < k
    · obtain ⟨z1, hz1⟩ := hhalf ⟨x.val, hx⟩ x
      refine ⟨z1 + z2, ?_⟩
      show rsF k (rsExt u) (rsExt b) t j m x.val - _ = _
      rw [rsF, if_pos hx, ← rsExt_mk u x.val hx, Int.cast_add]
      linarith
    · obtain ⟨z3, hz3⟩ := rsG_int (rsExt b) t j m (x.val - (k - 1))
      have hl := rsParLam_minus k r v b x (by omega)
      refine ⟨z3 + z2, ?_⟩
      show rsF k (rsExt u) (rsExt b) t j m x.val - _ = _
      rw [rsF, if_neg hx, hz3, Int.cast_add]
      linarith
  have key : ∀ m, m ≤ j * t → P (rsPt k r u b t j m) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [rsPt_zero]
      exact hP
    | succ m ih =>
      intro hm
      have hm' : m ≤ j * t := by omega
      rw [rsPt_succ k r u b t j m hk hj hj2]
      refine hSC.2 _ _ (hHC m hm') (hGap m hm') ?_ ?_ ?_ (ih hm')
      · rw [← rsPt_succ k r u b t j m hk hj hj2]
        exact hHC (m + 1) hm
      · rw [← rsPt_succ k r u b t j m hk hj hj2]
        exact hGap (m + 1) hm
      · intro i heq
        have hi : i.val < j + k - 1 := by have := i.isLt; omega
        have hlt := (hHC m hm').1 (Fin.mk_lt_mk.mpr hi :
          (⟨i.val, by omega⟩ : Fin (2 * r + k + 1)) < ⟨j + k - 1, by omega⟩)
        have hv : rsPt k r u b t j m ⟨i.val, by omega⟩ = u i - 1 / 2 := by
          show rsF k (rsExt u) (rsExt b) t j m i.val = u i - 1 / 2
          rw [rsF, if_pos i.isLt, ← rsExt_mk u i.val i.isLt]
        linarith
  have := key (j * t) le_rfl
  rwa [rsPt_top] at this
end ReciprocityTheory.ChartRestriction.DS.Lap
