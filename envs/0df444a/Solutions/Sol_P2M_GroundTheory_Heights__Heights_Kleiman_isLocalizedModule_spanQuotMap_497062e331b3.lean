-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isLocalizedModule_spanQuotMap_497062e331b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:56.430821+00:00
-- url     : https://prove2.me/submissions/18966d3b-4a9d-432d-9e2c-d27974a9eb95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenericRestrLen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_smul_mem_of_mem_span_29fc736ee8a8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] [IsFractionRing S F]
  {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (A B : Submodule S Ω) :
    IsLocalizedModule (nonZeroDivisors S) (spanQuotMap F A B) where
  map_units s := by
    rw [← (Algebra.lsmul S (A := F) S _).commutes]; exact (IsLocalization.map_units F s).map _
  surj y := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨t, ht, hz⟩ := exists_smul_mem_of_mem_span A z.2
    exact ⟨(Submodule.Quotient.mk ⟨t • (z : Ω), hz⟩, ⟨t, ht⟩), rfl⟩
  exists_of_eq {a₁ a₂} h := by
    obtain ⟨a₁, rfl⟩ := Submodule.Quotient.mk_surjective _ a₁
    obtain ⟨a₂, rfl⟩ := Submodule.Quotient.mk_surjective _ a₂
    have hB : (a₁ : Ω) - a₂ ∈ Submodule.span F (B : Set Ω) := (Submodule.Quotient.eq
      ((Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype)).mp h
    obtain ⟨t, ht, htB⟩ := exists_smul_mem_of_mem_span B hB
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq]
    change t • (a₁ : Ω) - t • (a₂ : Ω) ∈ B
    rwa [← smul_sub]
end GroundTheory.Heights₂.Heights.Kleiman
