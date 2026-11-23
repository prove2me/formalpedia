-- Prove2me | solution 1 for P2M_Formalism_DivisionValues_localization_map__fc10c1f056d1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:31.273278+00:00
-- url     : https://prove2.me/submissions/44b6b974-e7c3-4040-b747-9343b64791da

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Theorems.Thm_Formalism_DivisionValues_imageLcv_mem_locP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.DivisionValues
theorem _root_.solution (p : Ideal R) [p.IsPrime] (f : W ≃ₗ[R] W) (A : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ p (A.map (f : W →ₗ[R] W)) = (Formalism.HermitianLatticesTheory.localization₂ p A).map (f : W →ₗ[R] W) := by
  ext x
  rw [Submodule.mem_map_equiv, imageLcv_mem_locP, imageLcv_mem_locP]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mem_map_equiv] at hx
    simpa [map_smul] using hx
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mem_map_equiv]
    simpa [map_smul] using hx
end Formalism.DivisionValues
