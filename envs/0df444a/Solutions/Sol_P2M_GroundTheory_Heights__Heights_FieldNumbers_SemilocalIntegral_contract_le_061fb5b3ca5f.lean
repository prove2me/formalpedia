-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_contract_le_061fb5b3ca5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:47.211944+00:00
-- url     : https://prove2.me/submissions/52c9e8db-6db1-478e-86cd-d2966a0a391c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsValuativeCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_algebraMap_39d4c423cc7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_prod_pow_5715147e4abb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_not_mem_269c9461ec4e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral
variable {F : Type u} [Field F] {K K' : Type} [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] {j : K ↪ K'} {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K'] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral
theorem _root_.solution {P' : Ideal (MRing ι' F)} [P'.IsPrime] {W : Ideal (MRing (fun k => ι' (j k)) F)}
    (hPW : contractPrime j P' ≤ W) (R : ValuationSubring (FractionRing (MRing ι' F ⧸ P')))
    (hR : ∀ a ∈ degZeroLoc (contractPrime j P') {W}, contractFracMap j P' a ∈ R)
    {y : Ideal (MRing ι' F)} (hy : IsMultiProjPrime y) (hP'y : P' ≤ y)
    (hcen : ∀ (b : K' → ℕ) (f g : MRing ι' F), IsMultiHomog f b → IsMultiHomog g b → g ∉ y →
      algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' f) /
          algebraMap (MRing ι' F ⧸ P') _ (Ideal.Quotient.mk P' g) ∈ R ∧
        (f ∈ y ↔ algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))
            (Ideal.Quotient.mk P' f) / algebraMap (MRing ι' F ⧸ P') _ (Ideal.Quotient.mk P' g) ∈
          R.nonunits)) :
    contractPrime j y ≤ W := by
  have hy₀ := isMultiProjPrime_contractPrime j ι' hy
  intro a ha
  rw [← sum_weightedHomogeneousComponent (blockWeight _) a]
  refine finsum_induction (· ∈ W) W.zero_mem (fun _ _ => W.add_mem) (fun c => ?_)
  have hac := hy₀.multiHomog a ha c
  have hf : IsMultiHomog (weightedHomogeneousComponent (blockWeight _) c a) c :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  by_contra hfW
  choose i hi using hy₀.relevant
  have hu := isMultiHomog_prod_pow (R := F) i c
  have huy := (haveI := hy₀.isPrime; prod_pow_not_mem _ i hi c)
  have hmem := hR _ (div_mem_degZeroLoc _ {W} hu hf (fun h => hfW (hPW h))
    (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hfW))
  rw [map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap] at hmem
  have h2 := ((hcen _ _ _ (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hu) huy).2).mp hac
  have hne : ∀ g, g ∉ P' → algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))
      (Ideal.Quotient.mk P' g) ≠ 0 := fun g hg => by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have ha0 := hne _ (fun h => hfW (hPW h))
  have hu0 := hne _ (fun h => huy (hP'y h))
  rw [ValuationSubring.mem_nonunits_iff] at h2
  have h3 := (R.valuation_le_one_iff _).mpr hmem
  have h4 := mul_lt_one_of_lt_of_le h2 h3
  rw [← map_mul, div_mul_div_cancel₀ hu0, div_self ha0, map_one] at h4
  exact lt_irrefl _ h4
end GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral
