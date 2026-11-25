-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.levi_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:20.927966+00:00
-- url     : https://prove2.me/submissions/a6e8aee2-cba2-4da6-8703-c149b05cec75

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_db_comm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_db_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ) (hg : Holo n z g) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => ‖g y‖ ^ 2) x ξ = ((‖dDot n z g x ξ‖ ^ 2 : ℝ) : ℂ) := by
  have hs : Smooth n z g := Holo.smooth n z g hg
  have hC : ∀ k, Ck n z k g := fun k => Smooth.ck n z k g hs
  have hconj : ∀ k, Ck n z k (fun y => (starRingEnd ℂ) (g y)) := fun k => Ck.conj n z k g (hC k)
  have e0 : (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ)) = fun y => g y * (starRingEnd ℂ) (g y) := by
    funext y; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hdb : ∀ k, db n z k (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ)) =
      fun y => g y * (starRingEnd ℂ) (d n z k g y) := by
    intro k; funext y
    rw [e0, db_mul n z _ _ (hC 1) (hconj 1) k y, Holo.db_eq_zero n z g hg k y, db_conj]
    ring
  have hdb0 : ∀ j, db n z j g = fun _ => 0 := fun j => funext (Holo.db_eq_zero n z g hg j)
  have hd : ∀ j k, d n z j (db n z k (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ))) x =
      d n z j g x * (starRingEnd ℂ) (d n z k g x) := by
    intro j k
    rw [hdb k, d_mul n z _ _ (hC 1) (Ck.conj n z 1 _ (Ck.d n z 1 k g (hC _))) j x, d_conj,
      ← d_db_comm n z g (hC 2) k j x, hdb0 j, d_const]
    simp
  simp only [Levi, hd, dDot]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  simp only [map_mul]
  ring
end ReciprocityTheory.L2DbarEstimates
