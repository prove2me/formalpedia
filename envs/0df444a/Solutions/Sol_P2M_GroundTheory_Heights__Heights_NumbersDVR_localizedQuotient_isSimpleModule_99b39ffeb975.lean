-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_isSimpleModule_99b39ffeb975
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:52.114582+00:00
-- url     : https://prove2.me/submissions/8119d5b4-921a-44ef-8808-9b8c2619b348

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultAtPrimeAtMinimal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_mk_eq_zero_872d818a74de

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
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (W : Ideal A) [W.IsPrime] :
    IsSimpleModule (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ W)) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨⟨LocalizedModule.mk (Ideal.Quotient.mk W 1) 1, 0, fun h => ?_⟩, ?_⟩
  · exact ‹W.IsPrime›.ne_top ((Ideal.eq_top_iff_one W).mpr (localizedQuotient_mk_eq_zero W 1 1 h))
  intro x hx z
  induction x using LocalizedModule.induction_on with | h m s => ?_
  induction z using LocalizedModule.induction_on with | h m' t => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m'
  have ha : a ∈ W.primeCompl := fun haW => hx (by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr haW, LocalizedModule.zero_mk])
  refine ⟨Localization.mk ((s : A) * b) (⟨a, ha⟩ * t), ?_⟩
  rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul]
  congr 1
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR
