-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ext_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:47:45.777109+00:00
-- url     : https://prove2.me/submissions/f5260ba7-cec3-4341-9450-e39b4a1f3ef1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_cl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_lc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_ll

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
theorem _root_.solution {k : ℕ} (μ : Fin (k + 1) → ℤ) (hμ : 0 ≤ μ (Fin.last k)) (g : sq_UU k μ)
    (t : Fin (k + 1)) : ((∑ a, sq_ext μ g.1 a t : ℕ) : ℤ) = μ t := by
  obtain ⟨g, hI, hb⟩ := g
  rw [sq_mem_interl] at hb
  rw [Fin.sum_univ_castSucc]
  induction t using Fin.lastCases with
  | last =>
    simp only [sq_ext_cl, sq_ext_ll, Finset.sum_const_zero, zero_add]
    exact Int.toNat_of_nonneg hμ
  | cast t =>
    simp only [sq_ext_cc, sq_ext_lc]
    have h := (hb t).2
    omega
end ReciprocityTheory.ChartRestriction.TR.Weyl
