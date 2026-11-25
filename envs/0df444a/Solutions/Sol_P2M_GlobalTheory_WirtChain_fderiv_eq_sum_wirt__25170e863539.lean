-- Prove2me | solution 1 for P2M_GlobalTheory_WirtChain_fderiv_eq_sum_wirt__25170e863539
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:00.84656+00:00
-- url     : https://prove2.me/submissions/3128a1ef-9b4e-4056-bda6-758cab41a9b5

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpComp
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub
attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.WirtChain
open Complex
variable {Φ I : Type} [Fintype Φ] [Fintype I]
open Classical
namespace GlobalTheory.WirtChain
theorem _root_.solution (h : (Φ → ℂ) → ℂ) (y u : Φ → ℂ) :
    fderiv ℝ h y u = ∑ τ, (u τ * wirt τ false h y + (starRingEnd ℂ) (u τ) * wirt τ true h y) := by
  have hu : u = ∑ τ, ((u τ).re • (Pi.single τ (1:ℂ) : Φ → ℂ) + (u τ).im • (Pi.single τ I : Φ → ℂ)) := by
    ext τ'
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp [Complex.re_add_im]
  conv_lhs => rw [hu]
  rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_add, map_smul, map_smul]
  simp only [wirt, Bool.false_eq_true, if_false, if_true, real_smul]
  set A := fderiv ℝ h y (Pi.single τ 1)
  set B := fderiv ℝ h y (Pi.single τ I)
  have hc : (starRingEnd ℂ) (u τ) = (u τ).re - (u τ).im * I := by
    apply Complex.ext <;> simp
  have hu' : u τ = (u τ).re + (u τ).im * I := (Complex.re_add_im _).symm
  have key : ∀ (a c : ℝ) (A B : ℂ), (a:ℂ) * A + (c:ℂ) * B =
      ((a:ℂ) + (c:ℂ) * I) * ((A + -I * B) / 2) + ((a:ℂ) - (c:ℂ) * I) * ((A + I * B) / 2) := by
    intro a c A B
    ring_nf
    rw [I_sq]
    ring
  have := key (u τ).re (u τ).im A B
  rw [← hu', ← hc] at this
  linear_combination this
end GlobalTheory.WirtChain
