-- Prove2me | solution 1 for PositivityTheory.HtPt.Siua.form_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:30:44.213923+00:00
-- url     : https://prove2.me/submissions/284098f5-c7da-4900-89db-0a8e649f14d1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_SiuaNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.HtPt PositivityTheory.HtPt.Siua
open Filter Topology
namespace PositivityTheory.HtPt.Siua
theorem _root_.solution {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap ℤ (fun _ : Fin n => M) ℤ) (μ e : M)
    (x y : Fin n → ℚ) (a : ℚ) :
    form f μ e (fun i => a * x i) (fun i => a * y i) = a ^ n * form f μ e x y := by
  simp only [PositivityTheory.HtPt.Siua.form, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hprod : ∏ i, (if i ∈ s then a * x i else a * y i) = a ^ n * ∏ i, (if i ∈ s then x i else y i) := by
    calc ∏ i, (if i ∈ s then a * x i else a * y i)
        = ∏ i, a * (if i ∈ s then x i else y i) :=
          Finset.prod_congr rfl fun i _ => (mul_ite _ _ _ _).symm
      _ = (∏ _i : Fin n, a) * ∏ i, (if i ∈ s then x i else y i) := Finset.prod_mul_distrib
      _ = a ^ n * ∏ i, (if i ∈ s then x i else y i) := by simp
  rw [hprod, mul_assoc]
end PositivityTheory.HtPt.Siua
