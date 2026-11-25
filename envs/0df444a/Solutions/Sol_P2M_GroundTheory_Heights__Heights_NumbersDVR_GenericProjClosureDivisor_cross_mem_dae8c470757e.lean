-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_cross_mem_dae8c470757e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:09:55.842593+00:00
-- url     : https://prove2.me/submissions/92a7215c-f00b-4647-8081-26d3f232266d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_mem_of_homog_344f22dd36be

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {O : Type} [CommRing O] {Φ : Type} [Field Φ] [Algebra O Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
theorem _root_.solution {z : (Σ k, ι k) → Φ} {f g f' g' : MRing ι O} {bf bg bf' bg' : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg) (hf' : IsMultiHomog f' bf')
    (hg' : IsMultiHomog g' bg') (hdeg : ∀ k, (bf k : ℤ) - bg k = bf' k - bg' k)
    (hv : aeval z f = aeval z g) (hv' : aeval z f' = aeval z g') :
    f * g' - f' * g ∈ pointIdeal O z := by
  have hd : bf + bg' = bf' + bg := by
    funext k
    have := hdeg k
    simp only [Pi.add_apply]
    omega
  have h1 : IsWeightedHomogeneous (blockWeight ι) (f * g') (bf + bg') := IsWeightedHomogeneous.mul hf hg'
  have h2 : IsWeightedHomogeneous (blockWeight ι) (f' * g) (bf + bg') := by
    rw [hd]; exact IsWeightedHomogeneous.mul hf' hg
  refine mem_of_homog (b := bf + bg') ?_ ?_
  · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (sub_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1)
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
  · rw [map_sub, map_mul, map_mul, hv, hv']
    ring
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
