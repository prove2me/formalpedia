-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ext_intl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:32.453252+00:00
-- url     : https://prove2.me/submissions/d2410814-35cd-417a-9b08-a4945fa4ae35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_cl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {k : ℕ} (μ : Fin (k + 1) → ℤ) (hμ : 0 ≤ μ (Fin.last k)) (g : sq_UU k μ) :
    sq_Intl (sq_ext μ g.1) := by
  have hsum := sq_ext_sum μ hμ g
  obtain ⟨g, hI, hb⟩ := g
  rw [sq_mem_interl] at hb
  simp only at hsum
  intro l j hlj a
  induction l using Fin.lastCases with
  | last => exfalso; have := j.isLt; simp at hlj; omega
  | cast l =>
    induction a using Fin.lastCases with
    | last =>
      rw [sq_sum_le_last, sq_sum_lt_last]
      simp only [sq_ext_cc]
      have hj : j = l.succ := Fin.ext (by simpa using hlj)
      have h1 := hsum j
      have h2 := (hb l).1
      rw [← hj, ← h1] at h2
      exact_mod_cast h2
    | cast a =>
      rw [sq_sum_le_castSucc, sq_sum_lt_castSucc]
      simp only [sq_ext_cc]
      induction j using Fin.lastCases with
      | last => simp [sq_ext_cl]
      | cast j =>
        simp only [sq_ext_cc]
        exact hI l j (by simpa using hlj) a
end ReciprocityTheory.ChartRestriction.TR.Weyl
