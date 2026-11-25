-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_isWeightedHomogeneous_sepBlock_9e2d0892eba8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:30.405888+00:00
-- url     : https://prove2.me/submissions/53e5d57b-70f2-4626-a5b9-b97f5d8f89f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution (k₀ : ι) {q : MvPolynomial (Coord n) ℤ} {m : ι → ℕ}
    (hq : IsWeightedHomogeneous (coordDeg n) q m) :
    IsWeightedHomogeneous (coordDeg n) (sepBlock k₀ q) (Function.update m k₀ 0) := by
  classical
  rw [q.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun ν hν ↦ ?_
  have hw : Finsupp.weight (coordDeg n) ν = m := hq (mem_support_iff.mp hν)
  have hvar : ∀ v : Coord n, IsWeightedHomogeneous (coordDeg n)
      ((if h : v.1 = k₀ then C (X ⟨(), Fin.cast (by rw [h]) v.2⟩) else X v :
        MvPolynomial (Coord n) (BlockRing n k₀))) (Function.update (coordDeg n v) k₀ 0) := by
    rintro ⟨k, i⟩
    by_cases h : k = k₀
    · subst h
      simp only [dite_true]
      convert isWeightedHomogeneous_C (coordDeg n) _ using 1
      funext j
      by_cases hj : j = k
      · subst hj; simp
      · simp [coordDeg, hj]
    · simp only [h, dite_false]
      convert isWeightedHomogeneous_X (BlockRing n k₀) (coordDeg n) (⟨k, i⟩ : Coord n) using 1
      funext j
      by_cases hj : j = k₀
      · subst hj; simp [coordDeg, Ne.symm h]
      · simp [Function.update_of_ne hj]
  have hc : IsWeightedHomogeneous (coordDeg n)
      (algebraMap ℤ (MvPolynomial (Coord n) (BlockRing n k₀)) (coeff ν q)) 0 := by
    rw [MvPolynomial.algebraMap_apply]
    exact isWeightedHomogeneous_C _ _
  rw [sepBlock, aeval_monomial, Finsupp.prod]
  convert hc.mul (IsWeightedHomogeneous.prod ν.support _
    (fun v ↦ ν v • Function.update (coordDeg n v) k₀ 0) fun v _ ↦ (hvar v).pow (ν v)) using 1
  rw [← hw, zero_add]
  funext j
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = k₀
  · subst hj; simp
  · simp [Function.update_of_ne hj]
end GroundTheory.Heights₂.Heights.BlockSurjectivity
