-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.phi_decay_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:16:34.494066+00:00
-- url     : https://prove2.me/submissions/d9989079-3cec-4f9f-8320-b58111658a06

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecALogLower
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiDecayCore
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_decA_lead_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_decA_log_lower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_decA_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dec_weighted
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_exp_noncompactPart_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lead_posDef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ν : Fin n → ℝ) (hν : Antitone ν) {g : ℝ}
    (hg : ∀ a b : Fin n, ε a ≠ ε b → b < a → g ≤ ν b - ν a) (hq : 1 ≤ q0 ε) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : inP ε Y) :
    phiReal ν (NormedSpace.exp Y) ≤
      Real.exp (-(g / 8) * min (hs Y) (Real.sqrt (hs Y) / Real.sqrt (2 * q0 ε))) := by
  classical
  by_cases h0 : hs Y = 0
  · have hY0 : Y = 0 := by
      ext a b
      have hsum := (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg ‖Y a b‖)).mp h0 a (Finset.mem_univ _)
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg ‖Y a b‖)).mp hsum b (Finset.mem_univ _)
      simpa using this
    subst hY0
    have hl : ∀ i : Fin n, lead ((i : ℕ) + 1) (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := fun i => by
      unfold lead
      rw [dif_pos (show (i : ℕ) + 1 ≤ n from i.isLt), Matrix.submatrix_one _ (Fin.castLE_injective _),
        Matrix.det_one]
    unfold phiReal
    rw [NormedSpace.exp_zero, h0]
    simp [hl]
  have hpos : 0 < hs Y := lt_of_le_of_ne (by unfold hs; positivity) (Ne.symm h0)
  obtain ⟨U, y, hU, hYe⟩ := decA_spec hY
  have hq' : (0 : ℝ) < 2 * q0 ε := by
    have : (1 : ℝ) ≤ q0 ε := by exact_mod_cast hq
    linarith
  set R := Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y) with hRdef
  have hR : 0 < R := mul_pos (Real.sqrt_pos.mpr hq') (Real.sqrt_pos.mpr hpos)
  set t := min 1 (1 / R) with htdef
  have ht0 : 0 ≤ t := le_min zero_le_one (by positivity)
  set V : Fin n → ℝ := fun i =>
    ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ‖Y a b‖ ^ 2 else 0 with hVdef
  have hx := exp_noncompactPart_posDef hY
  set c : Fin n → ℝ := fun i => (lead ((i : ℕ) + 1) (NormedSpace.exp Y)).re with hcdef
  have hc : ∀ i, 0 < c i := fun i => (lead_posDef hx _ i.isLt).1
  have hterm : ∀ i : Fin n, (ν i - nuNext ν i) * (t * V i / 4) ≤ (ν i - nuNext ν i) * Real.log (c i) := by
    intro i
    by_cases hlast : (i : ℕ) + 1 < n
    · have hnn : 0 ≤ ν i - nuNext ν i := by
        simp only [nuNext, dif_pos hlast]
        exact sub_nonneg.mpr (hν (show i ≤ ⟨(i : ℕ) + 1, hlast⟩ from Fin.le_def.mpr (by simp)))
      apply mul_le_mul_of_nonneg_left _ hnn
      have h := decA_log_lower hY hU hYe hq hpos ((i : ℕ) + 1) i.isLt
      simp only [Nat.lt_add_one_iff, Nat.add_one_le_iff] at h
      exact h
    · have hV : V i = 0 :=
        Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => if_neg (by have := a.isLt; omega)
      have hn : (i : ℕ) + 1 = n := by have := i.isLt; omega
      have hL : c i = 1 := by
        simp only [hcdef, hn]
        exact decA_lead_last hY hU hYe
      rw [hV, hL, Real.log_one]
      simp
  have hsum : t * (g * hs Y / 2) / 4 ≤ ∑ i, (ν i - nuNext ν i) * Real.log (c i) := by
    have hw := dec_weighted ν hν hg hY
    calc t * (g * hs Y / 2) / 4 ≤ t * (∑ i, (ν i - nuNext ν i) * V i) / 4 := by
          have := mul_le_mul_of_nonneg_left hw ht0
          linarith
      _ = ∑ i, (ν i - nuNext ν i) * (t * V i / 4) := by
          rw [Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i
  have hphi : phiReal ν (NormedSpace.exp Y) = Real.exp (-∑ i, (ν i - nuNext ν i) * Real.log (c i)) := by
    unfold phiReal
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.rpow_def_of_pos (hc i)]
    congr 1
    ring
  have hmin : t * hs Y = min (hs Y) (Real.sqrt (hs Y) / Real.sqrt (2 * q0 ε)) := by
    rw [htdef, min_mul_of_nonneg _ _ hpos.le, one_mul]
    congr 1
    have hs2 : hs Y = Real.sqrt (hs Y) * Real.sqrt (hs Y) := (Real.mul_self_sqrt hpos.le).symm
    have hsq : 0 < Real.sqrt (hs Y) := Real.sqrt_pos.mpr hpos
    have hsq2 : 0 < Real.sqrt (2 * q0 ε) := Real.sqrt_pos.mpr hq'
    rw [hRdef]
    field_simp
    nlinarith [Real.sq_sqrt hpos.le, Real.mul_self_sqrt hpos.le]
  rw [hphi]
  apply Real.exp_le_exp.mpr
  rw [← hmin]
  nlinarith [hsum]
end ReciprocityTheory.ChartRestriction.DS.S7
