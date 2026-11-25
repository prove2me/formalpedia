-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_exists_locToFrac_33b3ccc2644e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:35.661221+00:00
-- url     : https://prove2.me/submissions/e9fb6b13-52a5-428e-837f-0cc12ee61639

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PNormalisationModelLocalizationX
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_injective_a51db807acbc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_comp_d16046651bb1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_zero_not_mem_normalModelSubmonoid_47a2efab4a46


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
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalisationModelLocalization
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
variable (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
variable {M}
variable (M)
namespace GroundTheory.Heights₂.Heights.NormalisationModelLocalization
theorem _root_.solution (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (x : FractionRing (curveLocalRing J q))
    (hx : IsIntegral (curveLocalRing J q) x) : ∃ z, locToFrac M hJ hq z = x := by
  have := isDomain hJ hq
  have := M.isPrime
  haveI : IsIntegrallyClosed (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) := M.isIntegrallyClosed
  letI : Algebra (Localization (normalModelSubmonoid M q)) (FractionRing (curveLocalRing J q)) :=
    (locToFrac M hJ hq).toAlgebra
  have hinj := locToFrac_injective M hJ hq
  haveI : IsDomain (Localization (normalModelSubmonoid M q)) :=
    Function.Injective.isDomain (locToFrac M hJ hq) hinj
  haveI : IsIntegrallyClosed (Localization (normalModelSubmonoid M q)) :=
    isIntegrallyClosed_of_isLocalization _ (normalModelSubmonoid M q)
      (fun s hs => mem_nonZeroDivisors_of_ne_zero (fun h0 => zero_not_mem_normalModelSubmonoid M q hq (h0 ▸ hs)))
  haveI : IsFractionRing (Localization (normalModelSubmonoid M q)) (FractionRing (curveLocalRing J q)) := by
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · intro y
      refine isUnit_iff_ne_zero.2 (fun h0 => nonZeroDivisors.coe_ne_zero y ?_)
      exact (injective_iff_map_eq_zero _).1 hinj _ h0
    · intro z
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (curveLocalRing J q)) z
      have hb : locToModel M (b : curveLocalRing J q) ≠ 0 := by
        intro h0
        have h1 := congrArg (locToFrac M hJ hq) h0
        rw [← RingHom.comp_apply, locToFrac_comp, map_zero] at h1
        exact nonZeroDivisors.coe_ne_zero b ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective _ _) _ h1)
      refine ⟨⟨locToModel M a, ⟨locToModel M b, mem_nonZeroDivisors_of_ne_zero hb⟩⟩, ?_⟩
      change z * locToFrac M hJ hq (locToModel M b) = locToFrac M hJ hq (locToModel M a)
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, locToFrac_comp]
      exact hab
    · intro a b hab
      exact ⟨1, by rw [hinj hab]⟩
  have hx' : IsIntegral (Localization (normalModelSubmonoid M q)) x := by
    obtain ⟨p, hpm, hp⟩ := hx
    refine ⟨p.map (locToModel M), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.algebraMap_toAlgebra, locToFrac_comp]
    exact hp
  exact (IsIntegrallyClosed.isIntegral_iff (K := FractionRing (curveLocalRing J q))).1 hx'
end GroundTheory.Heights₂.Heights.NormalisationModelLocalization
