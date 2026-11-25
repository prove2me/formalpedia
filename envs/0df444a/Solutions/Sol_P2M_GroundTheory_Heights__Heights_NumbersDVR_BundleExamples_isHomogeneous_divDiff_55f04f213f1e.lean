-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isHomogeneous_divDiff_55f04f213f1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:49.588803+00:00
-- url     : https://prove2.me/submissions/8702b41f-6ede-49e2-b97a-02da5c1e5ad8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_sum_split_24529285042b
import Theorems.Thm_GroundTheory_Arith_Iwasawa_IsDistinguished_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
set_option linter.unusedSectionVars false
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
theorem _root_.solution {r : ℕ} (l : Fin r) {G : MvPolynomial (Fin r) ℤ} {d : ℕ}
    (hG : G.IsHomogeneous (d + 1)) : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G).IsHomogeneous d := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff
  apply IsHomogeneous.sum
  intro μ hμ
  have hdeg : ∑ j, μ j = d + 1 := by
    have h := hG (mem_support_iff.mp hμ)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa using h
  by_cases h0 : μ l = 0
  · simp only [h0, Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul]
    exact isHomogeneous_zero _ _ _
  · have hA := IsHomogeneous.prod (Finset.univ.filter fun j => j < l)
      (fun j => (X (Fin.natAdd r j) : MvPolynomial (Fin (r + r)) ℤ) ^ μ j) (fun j => μ j)
      fun j _ => isHomogeneous_X_pow _ _
    have hB := IsHomogeneous.prod (Finset.univ.filter fun j => l < j)
      (fun j => (X (Fin.castAdd r j) : MvPolynomial (Fin (r + r)) ℤ) ^ μ j) (fun j => μ j)
      fun j _ => isHomogeneous_X_pow _ _
    have hM : (∑ a ∈ Finset.range (μ l), (X (Fin.castAdd r l) : MvPolynomial (Fin (r + r)) ℤ) ^ a *
        X (Fin.natAdd r l) ^ (μ l - 1 - a)).IsHomogeneous (μ l - 1) := by
      apply IsHomogeneous.sum
      intro a ha
      have h := (isHomogeneous_X_pow (R := ℤ) (Fin.castAdd r l) a).mul
        (isHomogeneous_X_pow (R := ℤ) (Fin.natAdd r l) (μ l - 1 - a))
      have ha' := Finset.mem_range.mp ha
      rwa [show a + (μ l - 1 - a) = μ l - 1 by omega] at h
    have h := (((isHomogeneous_C _ (G.coeff μ)).mul hA).mul hM).mul hB
    have hs := sum_split l μ
    rw [hdeg] at hs
    convert h using 1
    omega
end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
