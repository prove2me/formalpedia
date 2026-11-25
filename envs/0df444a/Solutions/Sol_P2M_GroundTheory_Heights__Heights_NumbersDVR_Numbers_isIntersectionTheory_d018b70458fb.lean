-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_isIntersectionTheory_d018b70458fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:23:37.502247+00:00
-- url     : https://prove2.me/submissions/b9f3763a-90d0-4db0-9a22-5b82ebd869c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumIsFieldIntersection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumRatSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_proof_2e980415e0ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_ringKrullDim_eq_of_relDim_b46a94ec49e5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_finsum_mul_eq_sum_e68a1b9f81ed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumUnique_proof_a93d885aebf6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumIsFieldIntersection_proof_69885316002f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_proof_19b16af12153
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumRatSection_proof_1f2dabfb1efd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiHomog_iff_f0c1440da5d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiProjPrime_iff_a67b98d88a86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabDivCycle_proof_3cb2a32c78c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabMultiHomogIdeal_proof_6afd59a7e16a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabMultiHomog_proof_8751c6dffe37


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
theorem _root_.solution (hPt : IntNumPoint.Statement.{u})
    (hBase : FieldNumbers.IntNumBase.Statement.{u}) {I : IFamily F ι}
    (hI : IsFieldIntersection I) : FieldNumbers.IsIntersectionTheory F I where
  base P hP h0 := by
    have hdim := ringKrullDim_eq_of_relDim P 0 (by rw [h0]; rfl)
    choose i hi using hP.relevant
    rw [hI.1 P ![] i ⟨(Objects.isMultiProjPrime_iff P).mp hP, hdim⟩ hi,
      ← hPt F K ι P i hP hdim hi]
    obtain ⟨-, h2⟩ := hBase F K ι P hP h0
    rw [h2, FieldNumbers.resDeg, dif_pos hP.isPrime]
  cut P n hP hdim bf bg f g hf hg hfP hgP bs := by
    have hd := ringKrullDim_eq_of_relDim P (n + 1) hdim
    have hs : IsRatSection P (fun k => (bf k : ℤ) - bg k) f g :=
      ⟨bf, bg, (Objects.isMultiHomog_iff f bf).mp hf, (Objects.isMultiHomog_iff g bg).mp hg,
        hfP, hgP, fun k => rfl⟩
    rw [hI.2 P n bs _ f g ⟨(Objects.isMultiProjPrime_iff P).mp hP, hd⟩ hs]
    have hD : ∀ W, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv P f g W = ratDiv P f g W := by
      intro W
      simp only [ratDiv, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]
      rw [VocabDivCycle.proof F K ι P f W, VocabDivCycle.proof F K ι P g W]
    simp only [cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, ← hD]
    exact (finsum_mul_eq_sum _ _).symm
end GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
