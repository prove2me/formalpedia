-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_eq_zero_89948f02be2c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:53:23.641149+00:00
-- url     : https://prove2.me/submissions/a3912640-24c1-4069-8e9a-4fd7f2865fa3

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
theorem _root_.solution {A W : Ideal (MRing ι F)} [W.IsPrime] (h : ¬ A ≤ W) : multAt A W = 0 := by
  obtain ⟨q, hqA, hqW⟩ := Set.not_subset.mp h
  have hz : ∀ z : LocalizedModule W.primeCompl (MRing ι F ⧸ A), z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
      refine ⟨⟨q, Ideal.mem_primeCompl_iff.mpr hqW⟩, ?_⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, smul_smul,
        smul_quot_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact A.mul_mem_right _ (A.mul_mem_right _ hqA)
  have : Subsingleton (LocalizedModule W.primeCompl (MRing ι F ⧸ A)) :=
    ⟨fun x y => by rw [hz x, hz y]⟩
  exact Module.length_eq_zero
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
