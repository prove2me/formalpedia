-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_component_mem_f04e3a930347
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:11.136259+00:00
-- url     : https://prove2.me/submissions/6d4528fa-6208-46ac-a3d0-a7dea43c5e41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mConeMap_monomial_00b34a9717a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_coe_mapDomain_fst_cfb4929795a1

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.CoordinateConeArithVar
theorem _root_.solution [DecidableEq K] (y : (Σ k, ι k) → Ω) (f : MRing ι)
    (hf : f ∈ mCoordIdeal y) (m : K → ℕ) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight ι) m f ∈ mCoordIdeal y := by
  classical
  set φ := mConeMap y
  set m' : K →₀ ℕ := Finsupp.equivFunOnFinite.symm m
  have hdeg : ∀ e : (Σ k, ι k) →₀ ℕ,
      e.mapDomain Sigma.fst = m' ↔ Finsupp.weight (NumbersDVR.blockWeight ι) e = m := by
    intro e
    rw [← coe_mapDomain_fst, ← DFunLike.coe_fn_eq, Finsupp.coe_equivFunOnFinite_symm]
  set S := f.support.filter fun e ↦ Finsupp.weight (NumbersDVR.blockWeight ι) e = m
  have himg : φ (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) m f) =
      monomial m' (∑ e ∈ S, ((coeff e f : ℤ) : Ω) * e.prod fun p n ↦ y p ^ n) := by
    rw [weightedHomogeneousComponent_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    rw [mConeMap_monomial, (hdeg e).2 (Finset.mem_filter.1 he).2]
  have hcoeff : coeff m' (φ f) = ∑ e ∈ S, ((coeff e f : ℤ) : Ω) * e.prod fun p n ↦ y p ^ n := by
    conv_lhs => rw [f.as_sum, map_sum]
    rw [coeff_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [mConeMap_monomial, coeff_monomial]
    exact if_congr (hdeg e) rfl rfl
  have hzero : φ f = 0 := (RingHom.mem_ker).1 hf
  rw [mCoordIdeal, RingHom.mem_ker]
  show φ _ = 0
  rw [himg, ← hcoeff, hzero, coeff_zero, monomial_zero]
end GroundTheory.Heights₂.Heights.CoordinateConeArithVar
