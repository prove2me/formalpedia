-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.tStarIbp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:35:27.592937+00:00
-- url     : https://prove2.me/submissions/9b6911ce-1a21-4c1f-b7e9-5b0ec3aaf50a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_TstarNormSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_ck_expNeg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_hasCompactSupport_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integrable_of_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_db_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : TStarIbpStatement n M := by
  intro z hz ph₁ ph₂ g f _hph₁ hph₂ hg hf
  have hE := ck_expNeg n z 1 ph₂ hph₂
  have hF : ∀ j, Ck n z 1 (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) :=
    fun j => Ck.mul n z 1 _ _ hE (hf j).1
  have hFc : ∀ j, HasCompactSupport (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) :=
    fun j => (hf j).2.mul_left
  have hG : ∀ j, Ck n z 1 (fun y => conj ((Real.exp (-ph₂ y) : ℂ) * f y j)) :=
    fun j => Ck.conj n z 1 _ (hF j)
  have hGc : ∀ j, HasCompactSupport (fun y => conj ((Real.exp (-ph₂ y) : ℂ) * f y j)) :=
    fun j => (hFc j).comp_left (map_zero (starRingEnd ℂ))
  have hj : ∀ j, ∫ x, db n z j g x * conj ((Real.exp (-ph₂ x) : ℂ) * f x j) ∂vol n z =
      -∫ x, g x * conj (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x) ∂vol n z := by
    intro j
    rw [integral_db_mul n z hz j g _ hg (hG j) (hGc j)]
    congr 2
    funext x
    rw [db_conj]
  have hint1 : ∀ j ∈ (Finset.univ : Finset (Fin n)), Integrable
      (fun x => db n z j g x * conj ((Real.exp (-ph₂ x) : ℂ) * f x j)) (vol n z) := by
    intro j _
    apply integrable_of_continuous n z hz
    · exact (Ck.continuous n z hz 0 _ (Ck.db n z 0 j g hg)).mul
        (Ck.continuous n z hz 1 _ (hG j))
    · exact (hGc j).mul_left
  have hint2 : ∀ j ∈ (Finset.univ : Finset (Fin n)), Integrable
      (fun x => g x * conj (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x)) (vol n z) := by
    intro j _
    apply integrable_of_continuous n z hz
    · exact (Ck.continuous n z hz 1 _ hg).mul
        (Ck.continuous n z hz 0 _ (Ck.conj n z 0 _ (Ck.d n z 0 j _ (hF j))))
    · exact ((hasCompactSupport_d n z j _ (hFc j)).comp_left (map_zero (starRingEnd ℂ))).mul_left
  have lhs : ∫ x, (∑ j, db n z j g x * conj (f x j)) * (Real.exp (-ph₂ x) : ℂ) ∂vol n z =
      ∑ j, ∫ x, db n z j g x * conj ((Real.exp (-ph₂ x) : ℂ) * f x j) ∂vol n z := by
    rw [← integral_finsetSum _ hint1]
    congr 1
    funext x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have rhs : ∫ x, g x * conj (tstar n z ph₁ ph₂ f x) * (Real.exp (-ph₁ x) : ℂ) ∂vol n z =
      ∑ j, -∫ x, g x * conj (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x) ∂vol n z := by
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ hint2, ← integral_neg]
    congr 1
    funext x
    have he : (Real.exp (ph₁ x) : ℂ) * (Real.exp (-ph₁ x) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
    unfold tstar
    rw [← Finset.mul_sum]
    simp only [map_neg, map_mul, map_sum, Complex.conj_ofReal]
    generalize (∑ j : Fin n, conj (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x)) = S
    linear_combination (-(g x * S)) * he
  rw [lhs, rhs]
  exact Finset.sum_congr rfl (fun j _ => hj j)
end ReciprocityTheory.L2DbarEstimates.E
