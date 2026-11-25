-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.lowerStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:48.588257+00:00
-- url     : https://prove2.me/submissions/a0942482-079b-4b51-a888-f1e87d258d91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lam_lt_u
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_at
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_walkPar_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_bot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_ok
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_no_cross

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution : LowerStepStatement := by
  unfold LowerStepStatement
  intro k r u v b h P hk hHC hI hH hG hSC i hi hP
  have hin : i < 2 * r + k + 1 := by omega
  have e1 : walkPar k r u v b (i + 1) = lowPt k r u v b i (u ⟨i, hi⟩ - 1 / 2) := by
    have h0 := walkPar_add u v b i hi hin 0
    rw [zero_smul, add_zero, add_zero] at h0
    exact h0
  rw [← lowPt_bot u v b i hi hin]
  obtain ⟨m, hm⟩ := hH ⟨i, hi⟩ ⟨i, hin⟩
  have hlt := lam_lt_u hI i hi hin
  have hm0 : 0 ≤ m := by
    by_contra hneg
    have h1 : m ≤ -1 := by omega
    have h2 : (m : ℝ) ≤ -1 := by exact_mod_cast h1
    linarith
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, m = N := ⟨m.toNat, (Int.toNat_of_nonneg hm0).symm⟩
  have hm' : u ⟨i, hi⟩ - parLam k r v b ⟨i, hin⟩ = (N : ℝ) + 1 / 2 := by exact_mod_cast hm
  have ok : ∀ t : ℕ, t ≤ N →
      IsHCPar (lowPt k r u v b i (parLam k r v b ⟨i, hin⟩ + (t : ℝ))) ∧
      GapAtLeast (parEps k r) (lowPt k r u v b i (parLam k r v b ⟨i, hin⟩ + (t : ℝ))) h := by
    intro t ht
    have htN : (t : ℝ) ≤ N := by exact_mod_cast ht
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    exact lowPt_ok hk hHC hI hH hG i hi hin _ (t : ℤ) (by simp) (by linarith) (by linarith)
  have key : ∀ t : ℕ, t ≤ N → P (lowPt k r u v b i (parLam k r v b ⟨i, hin⟩ + (t : ℝ))) →
      P (lowPt k r u v b i (parLam k r v b ⟨i, hin⟩)) := by
    intro t
    induction t with
    | zero =>
      intro _ hp
      simpa using hp
    | succ t ih =>
      intro ht hp
      apply ih (by omega)
      have hy := ok (t + 1) ht
      have hy' := ok t (by omega)
      have hsub := lowPt_sub u v b i hin (parLam k r v b ⟨i, hin⟩ + ((t + 1 : ℕ) : ℝ))
      have e : parLam k r v b ⟨i, hin⟩ + ((t + 1 : ℕ) : ℝ) - 1 =
          parLam k r v b ⟨i, hin⟩ + (t : ℝ) := by
        rw [Nat.cast_succ]
        ring
      rw [e] at hsub
      have hnc : ∀ l, u l ≠
          lowPt k r u v b i (parLam k r v b ⟨i, hin⟩ + ((t + 1 : ℕ) : ℝ)) ⟨i, hin⟩ - 1 / 2 := by
        intro l
        rw [lowPt_at]
        have htN : ((t + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast ht
        have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
        have hc : ((t + 1 : ℕ) : ℝ) = t + 1 := Nat.cast_succ t
        exact no_cross hI i hi hin _ (by linarith) (by linarith) l
      have h3 := hSC.1 _ ⟨i, hin⟩ hy.1 hy.2 (by rw [hsub]; exact hy'.1) (by rw [hsub]; exact hy'.2)
        hnc hp
      rw [hsub] at h3
      exact h3
  have e2 : parLam k r v b ⟨i, hin⟩ + ((N : ℕ) : ℝ) = u ⟨i, hi⟩ - 1 / 2 := by linarith
  apply key N le_rfl
  rw [e2, ← e1]
  exact hP
end ReciprocityTheory.ChartRestriction.DS.Lap
