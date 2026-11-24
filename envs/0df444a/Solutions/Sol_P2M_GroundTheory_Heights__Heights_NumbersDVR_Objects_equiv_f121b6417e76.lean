-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_equiv_f121b6417e76
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:50.785345+00:00
-- url     : https://prove2.me/submissions/e25b83b7-cb76-4c09-a483-6d1ddffd5662

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiHomog_iff_f0c1440da5d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiProjPrime_iff_a67b98d88a86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_intCyc_divCycle_0b46b449395b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_divO_eq_ratDiv_c8baeb4d1a16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_redEval_eq_cycEval_59148029e95c

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.Objects
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.Objects
theorem _root_.solution (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    (∀ (f : MRing ι O) (b : K → ℕ), IsMultiHomog f b ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b) ∧
    (∀ P : Ideal (MRing ι O), IsMultiProjPrime P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P) ∧
    (∀ (P : Ideal (MRing ι O)) (s : MRing ι O) (W : Ideal (MRing ι O)),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.intCyc (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W =
        divCycle P s W) ∧
    (∀ (P : Ideal (MRing ι O)) (f g : MRing ι O) (W : Ideal (MRing ι O)),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.divO P f g W = ratDiv P f g W) ∧
    (∀ (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ) (Z : Ideal (MRing ι O) →₀ ℤ),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.redEval J Z =
        cycEval (fun W => J (specialIdeal W)) Z) :=
  ⟨isMultiHomog_iff, isMultiProjPrime_iff, intCyc_divCycle, divO_eq_ratDiv, redEval_eq_cycEval⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.Objects
