-- Prove2me | solution 1 for Sendov.sendov_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:04:51.80738+00:00
-- url     : https://prove2.me/submissions/2476b395-ac9b-4945-b595-5497cf5e92cf

import Definitions.Def_Sendov_Analytic_OriginExact
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Reduction_Main
import Definitions.Def_Sendov_Interior
import Theorems.Thm_Sendov_Fprod_zero
import Theorems.Thm_Sendov_exists_crit_multiset
import Theorems.Thm_Sendov_exists_root_multiset
import Theorems.Thm_Sendov_gg0_length
import Theorems.Thm_Sendov_gg1_length
import Theorems.Thm_Sendov_gg2_length
import Theorems.Thm_Sendov_l1_cons
import Theorems.Thm_Sendov_l1_nil
import Theorems.Thm_Sendov_l1row_cons
import Theorems.Thm_Sendov_l1row_nil
import Theorems.Thm_Sendov_norm_prod_le_one
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_pevZ_cons
import Theorems.Thm_Sendov_pevZ_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_prod_sub_mul_prod
import Theorems.Thm_Sendov_qrow_length
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_rowZ_cons
import Theorems.Thm_Sendov_rowZ_length
import Theorems.Thm_Sendov_rowZ_nil
import Theorems.Thm_Sendov_rscale_length
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_unpackN_succ
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackZ_succ
import Theorems.Thm_Sendov_unpackZ_zero
import Theorems.Thm_Sendov_wsumZ_cons
import Theorems.Thm_Sendov_wsumZ_nil
import Theorems.Thm_Sendov_wsum_cons
import Theorems.Thm_Sendov_wsum_nil
attribute [local simp] Sendov.Fprod_zero
attribute [local simp] Sendov.gg0_length
attribute [local simp] Sendov.gg1_length
attribute [local simp] Sendov.gg2_length
attribute [local simp] Sendov.l1_cons
attribute [local simp] Sendov.l1_nil
attribute [local simp] Sendov.l1row_cons
attribute [local simp] Sendov.l1row_nil
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.pevZ_cons
attribute [local simp] Sendov.pevZ_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.qrow_length
attribute [local simp] Sendov.rev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.rowZ_cons
attribute [local simp] Sendov.rowZ_length
attribute [local simp] Sendov.rowZ_nil
attribute [local simp] Sendov.rscale_length
attribute [local simp] Sendov.sumEraseProdC_zero
attribute [local simp] Sendov.sumEraseProd_zero
attribute [local simp] Sendov.unpackN_succ
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackZ_succ
attribute [local simp] Sendov.unpackZ_zero
attribute [local simp] Sendov.wsumZ_cons
attribute [local simp] Sendov.wsumZ_nil
attribute [local simp] Sendov.wsum_cons
attribute [local simp] Sendov.wsum_nil



set_option autoImplicit false
open Sendov
open Polynomial
open Complex (I)
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp0 : p.eval 0 = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ‖ < 1 := by
  by_contra hcon
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - (0 : ℂ)‖ := by
    intro w hw
    rw [sub_zero]
    by_contra hlt
    exact hcon ⟨w, hw, not_le.1 hlt⟩
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hp0
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn hdeg hcrit
  have hpne : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hpne
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (0 : ℂ) - v⁻¹)).map (fun w => X - C w)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  -- `p'(0)` two ways
  have hkey := prod_sub_mul_prod (c := p.leadingCoeff) (a := (0 : ℂ)) (n := n) (z := z) (q := q)
    (p := p) hc0 hq0 hpz hpq'
  have hnorm := congrArg norm hkey
  rw [norm_mul] at hnorm
  have h1 : ‖q.prod‖ ≤ 1 := norm_prod_le_one q hq1
  have h2 : ‖(z.map (fun w => (0 : ℂ) - w)).prod‖ ≤ 1 := by
    refine norm_prod_le_one _ ?_
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hu
    simpa using hz1 w hw
  have h3 : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [h3] at hnorm
  have h4 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [hnorm, h1, h2, norm_nonneg q.prod, norm_nonneg (z.map (fun w => (0 : ℂ) - w)).prod]
end Sendov
