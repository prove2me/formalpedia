-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_locQuotSemilinear_surjective_746a40a56a06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:38.424646+00:00
-- url     : https://prove2.me/submissions/4c744980-1fd8-4354-a01a-7315451fa682

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
theorem _root_.solution : Function.Surjective (locQuotSemilinear σ J V) := by
  intro x
  induction x using LocalizedModule.induction_on with | h m s => ?_
  have hs : σ.symm s ∈ V.primeCompl := Ideal.mem_primeCompl_iff.2 fun h' =>
    Ideal.mem_primeCompl_iff.1 s.2 (by simpa using (mem_map_ringEquiv_iff σ V _).2 h')
  refine ⟨LocalizedModule.mk ((quotEquivMap σ J).symm m) ⟨σ.symm s, hs⟩, ?_⟩
  rw [locQuotSemilinear_apply, locQuotMap_mk, RingEquiv.apply_symm_apply]
  congr 1
  ext
  simp
end GroundTheory.Heights₂.Heights
