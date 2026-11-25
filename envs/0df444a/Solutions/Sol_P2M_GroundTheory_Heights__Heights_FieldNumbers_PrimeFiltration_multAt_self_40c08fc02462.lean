-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_self_40c08fc02462
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:53:26.964209+00:00
-- url     : https://prove2.me/submissions/80f47fd4-0be8-4957-a60d-4b78551c7b36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_smul_quot_mk_2882e2e1b3cb

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
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} {ι : K → Type} {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution (W : Ideal (MRing ι F)) [hW : W.IsPrime] : multAt W W = 1 := by
  unfold multAt
  have hφ : ∀ x : Localization.AtPrime W,
      LinearMap.toSpanSingleton (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (MRing ι F ⧸ W))
        (LocalizedModule.mk 1 1) x = x • LocalizedModule.mk 1 1 := fun x => rfl
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton (Localization.AtPrime W)
      (LocalizedModule W.primeCompl (MRing ι F ⧸ W)) (LocalizedModule.mk 1 1)) := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      refine ⟨Localization.mk m t, ?_⟩
      rw [hφ, LocalizedModule.mk_smul_mk, mul_one, ← map_one (Ideal.Quotient.mk W),
        smul_quot_mk, mul_one]
  have hle : IsLocalRing.maximalIdeal (Localization.AtPrime W) ≤ LinearMap.ker
      (LinearMap.toSpanSingleton (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (MRing ι F ⧸ W)) (LocalizedModule.mk 1 1)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro w hw
    rw [Ideal.mem_comap, LinearMap.mem_ker, hφ, algebraMap_smul, LocalizedModule.smul'_mk,
      ← map_one (Ideal.Quotient.mk W), smul_quot_mk, mul_one,
      (Ideal.Quotient.eq_zero_iff_mem).mpr hw, LocalizedModule.zero_mk]
  have hne : LinearMap.ker (LinearMap.toSpanSingleton (Localization.AtPrime W)
      (LocalizedModule W.primeCompl (MRing ι F ⧸ W)) (LocalizedModule.mk 1 1)) ≠ ⊤ := by
    intro h
    have h1 := (LinearMap.mem_ker).mp (h ▸ Submodule.mem_top : (1 : Localization.AtPrime W) ∈ _)
    rw [hφ, one_smul, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h1
    obtain ⟨u, hu⟩ := h1
    rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Submonoid.coe_one,
      one_smul, ← map_one (Ideal.Quotient.mk W), smul_quot_mk, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hu
    exact u.2 hu
  have hker := ((IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime W)).eq_of_le hne hle).symm
  rw [← (LinearMap.quotKerEquivOfSurjective _ hsurj).length_eq]
  have : IsSimpleModule (Localization.AtPrime W) (Localization.AtPrime W ⧸ LinearMap.ker
      (LinearMap.toSpanSingleton (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (MRing ι F ⧸ W)) (LocalizedModule.mk 1 1))) := by
    rw [isSimpleModule_iff_isCoatom, hker]
    exact Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _)
  exact Module.length_eq_one _ _
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
