-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_polyNum_eq_classNum_8d89639b44f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:51.809787+00:00
-- url     : https://prove2.me/submissions/8c40b342-869a-4817-baef-d5a8892bb6bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_monoList_eq_277864d5c7d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_intNum_get_cast_f4b2aff776c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_classList_mapDomain_perm_2bdfcbd7ae9e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_intNumL_perm_6fa0b4475d01
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_length_monoList_15dd32156d22
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_monoList_perm_282dba544287


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
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m : ℕ} (deg : Fin m → K → ℤ) {τ : Type*} [DecidableEq τ] (e : Fin m ≃ τ) (cls : τ → K → ℤ)
    (hcls : cls ∘ e = deg) {H : MvPolynomial (Fin m) ℤ} {d : ℕ} (hH : H.IsHomogeneous d)
    (W : Ideal (MRing ι O)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ L => intNum (IsLocalRing.ResidueField O) V L)
                              (specialIdeal W) d deg H = classNum cls (rename e H) [] W := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum classNum
  rw [support_rename_of_injective e.injective,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective e.injective h]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [coeff_rename_mapDomain _ e.injective]
  congr 1
  have hlen : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ).length = d := by
    rw [monoList_eq, List.length_map, FlagTypings.length_monoList hH hμ]
  rw [dif_pos hlen]
  refine (intNum_get_cast _ _ _ _ hlen).trans ?_
  rw [List.append_nil]
  refine FlagTypings.intNumL_perm _ _ ?_
  rw [monoList_eq]
  refine ((FlagTypings.monoList_perm deg μ).trans ?_)
  rw [← hcls]
  exact (classList_mapDomain_perm e cls μ).symm
end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
