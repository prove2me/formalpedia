-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_quotient_eq_zero_506f8fa2ab32
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:57:27.620852+00:00
-- url     : https://prove2.me/submissions/a58412f9-7c76-4a8b-aca1-9eb9aca43768

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
theorem _root_.solution (p q : Ideal R) [p.IsPrime] (h : ¬ q ≤ p) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ q)) = 0 := by
  obtain ⟨t, htq, htp⟩ := Set.not_subset.mp h
  have key : ∀ y : LocalizedModule p.primeCompl (R ⧸ q), y = 0 := by
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
      refine ⟨⟨t, htp⟩, ?_⟩
      rw [one_smul, smul_zero, smul_zero, Submonoid.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact q.mul_mem_right r htq
  have : Subsingleton (LocalizedModule p.primeCompl (R ⧸ q)) :=
    ⟨fun a b => by rw [key a, key b]⟩
  exact Module.length_eq_zero
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
