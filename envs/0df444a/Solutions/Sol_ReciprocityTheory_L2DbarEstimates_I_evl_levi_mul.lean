-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_levi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:26.522739+00:00
-- url     : https://prove2.me/submissions/42d43026-f56d-4b54-9545-74167060ae38

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℝ)
    (hf : CkR n z 2 f) (hg : CkR n z 2 g) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => f y * g y) x ξ =
      Levi n z f x ξ * (g x : ℂ) + (f x : ℂ) * Levi n z g x ξ +
        conj (dDot n z (fun y => (f y : ℂ)) x ξ) * dDot n z (fun y => (g y : ℂ)) x ξ +
        dDot n z (fun y => (f y : ℂ)) x ξ * conj (dDot n z (fun y => (g y : ℂ)) x ξ) := by
  have hf1 : Ck n z 1 (fun y => (f y : ℂ)) := Ck.mono n z 1 2 (by norm_num) _ hf
  have hg1 : Ck n z 1 (fun y => (g y : ℂ)) := Ck.mono n z 1 2 (by norm_num) _ hg
  have h1 : ∀ k, db n z k (fun y => ((f y * g y : ℝ) : ℂ)) =
      fun y => db n z k (fun y => (f y : ℂ)) y * (g y : ℂ) +
        (f y : ℂ) * db n z k (fun y => (g y : ℂ)) y := by
    intro k; funext y
    have := db_mul n z _ _ hf1 hg1 k y
    simpa only [Complex.ofReal_mul] using this
  have h2 : ∀ j k, d n z j (db n z k (fun y => ((f y * g y : ℝ) : ℂ))) x =
      d n z j (db n z k (fun y => (f y : ℂ))) x * (g x : ℂ)
      + conj (d n z k (fun y => (f y : ℂ)) x) * d n z j (fun y => (g y : ℂ)) x
      + d n z j (fun y => (f y : ℂ)) x * conj (d n z k (fun y => (g y : ℂ)) x)
      + (f x : ℂ) * d n z j (db n z k (fun y => (g y : ℂ))) x := by
    intro j k
    have hdbf : Ck n z 1 (db n z k (fun y => (f y : ℂ))) := Ck.db n z 1 k _ hf
    have hdbg : Ck n z 1 (db n z k (fun y => (g y : ℂ))) := Ck.db n z 1 k _ hg
    have hp1 := Ck.mul n z 1 _ _ hdbf hg1
    have hp2 := Ck.mul n z 1 _ _ hf1 hdbg
    rw [h1 k, d_add n z _ _ hp1 hp2 j x, d_mul n z _ _ hdbf hg1 j x, d_mul n z _ _ hf1 hdbg j x,
      db_ofReal n z f k x, db_ofReal n z g k x]
    ring
  have c1 : conj (dDot n z (fun y => (f y : ℂ)) x ξ) * dDot n z (fun y => (g y : ℂ)) x ξ =
      ∑ j, ∑ k, conj (d n z k (fun y => (f y : ℂ)) x) * d n z j (fun y => (g y : ℂ)) x *
        ξ j * conj (ξ k) := by
    unfold dDot
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul]; ring
  have c2 : dDot n z (fun y => (f y : ℂ)) x ξ * conj (dDot n z (fun y => (g y : ℂ)) x ξ) =
      ∑ j, ∑ k, d n z j (fun y => (f y : ℂ)) x * conj (d n z k (fun y => (g y : ℂ)) x) *
        ξ j * conj (ξ k) := by
    unfold dDot
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul]; ring
  rw [c1, c2]
  unfold Levi
  simp only [h2, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end ReciprocityTheory.L2DbarEstimates.I
