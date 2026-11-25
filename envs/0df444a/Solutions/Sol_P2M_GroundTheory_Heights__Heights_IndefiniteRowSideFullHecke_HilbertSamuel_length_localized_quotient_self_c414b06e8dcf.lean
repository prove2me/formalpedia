-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_quotient_self_c414b06e8dcf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:33:21.749799+00:00
-- url     : https://prove2.me/submissions/46304dd3-d00f-4658-aebd-5b4bfc00738d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
theorem _root_.solution (p : Ideal R) [hp : p.IsPrime] :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ p)) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  have hne : ∀ (r : R) (s : p.primeCompl),
      LocalizedModule.mk (Ideal.Quotient.mk p r) s = 0 → r ∈ p := by
    intro r s h
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
    obtain ⟨u, hu⟩ := h
    rw [one_smul, smul_zero, smul_zero, Submonoid.smul_def, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hu
    exact (hp.mem_or_mem hu).resolve_left u.2
  refine ⟨⟨LocalizedModule.mk (Ideal.Quotient.mk p 1) 1, 0,
    fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr (hne 1 1 h))⟩, ?_⟩
  intro x hx y
  induction x using LocalizedModule.induction_on with
  | h m s =>
  induction y using LocalizedModule.induction_on with
  | h m' t =>
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective m'
  have hr : r ∉ p := fun hr => hx (by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, LocalizedModule.zero_mk])
  refine ⟨Localization.mk (r' * s) ⟨r * t, p.primeCompl.mul_mem hr t.2⟩, ?_⟩
  rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul]
  congr 1
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
