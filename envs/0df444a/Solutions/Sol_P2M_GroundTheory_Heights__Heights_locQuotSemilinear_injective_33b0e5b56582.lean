-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_locQuotSemilinear_injective_33b0e5b56582
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:06.300351+00:00
-- url     : https://prove2.me/submissions/2c9549d7-b79d-4dab-be23-88f84241c5eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_locQuotSemilinear_apply_1c8e21b617b3

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {A A' : Type*} [CommRing A] [CommRing A'] (σ : A ≃+* A')
variable (J V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : Function.Injective (locQuotSemilinear σ J V) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using LocalizedModule.induction_on with | h m s => ?_
  rw [locQuotSemilinear_apply, locQuotMap_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hx
  obtain ⟨u, hu⟩ := hx
  rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def] at hu
  have hu' : σ.symm u ∈ V.primeCompl := Ideal.mem_primeCompl_iff.2 fun h' =>
    Ideal.mem_primeCompl_iff.1 u.2 (by simpa using (mem_map_ringEquiv_iff σ V _).2 h')
  rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
  refine ⟨⟨σ.symm u, hu'⟩, ?_⟩
  rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def]
  apply (quotEquivMap σ J).injective
  rw [quotEquivMap_smul, map_zero, RingEquiv.apply_symm_apply]
  exact hu
end GroundTheory.Heights₂.Heights
