-- Prove2me | solution 1 for RobustMDP.EntropyInner.dualFn_at_top
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:56:35.727499+00:00
-- url     : https://prove2.me/submissions/9e08a044-3d6c-47a0-aa08-149715bd7c05

import Definitions.Def_RobustMDP_EntropyInner_dualFunction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic
open RobustMDP.EntropyInner Filter Topology

theorem solution {n : ℕ} (q v : Fin n → ℝ) (β : ℝ)
    (hq : q∈stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β) :
    Tendsto (fun lam => dualFn q v β lam-((∑ j, q j*v j)+β*lam)) atTop (𝓝 0) := by
  let Z : ℝ → ℝ := fun t => ∑ j, q j*Real.exp (v j*t)
  have hZ0 : Z 0=1 := by simp [Z,hq.2]
  have hd : HasDerivAt Z (∑ j, q j*v j) 0 := by
    have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (((hasDerivAt_id (0 : ℝ)).const_mul (v j)).exp).const_mul (q j))
    simpa [Z] using hh
  have hlog : HasDerivAt (fun t => Real.log (Z t)) (∑ j, q j*v j) 0 := by
    simpa [hZ0] using hd.log (by rw [hZ0]; norm_num)
  have ht := hlog.tendsto_slope_zero_right.comp tendsto_inv_atTop_nhdsGT_zero
  have ht' : Tendsto (fun lam => lam*Real.log (Z lam⁻¹)) atTop (𝓝 (∑ j, q j*v j)) := by
    simpa [Function.comp_def,hZ0] using ht
  have hh := ht'.sub_const (∑ j, q j*v j)
  convert! hh using 1
  · funext lam
    simp only [dualFn,Z,div_eq_mul_inv]
    ring
  · simp

