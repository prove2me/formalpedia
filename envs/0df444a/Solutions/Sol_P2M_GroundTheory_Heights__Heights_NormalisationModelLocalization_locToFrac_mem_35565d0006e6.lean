-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_mem_35565d0006e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:36.936235+00:00
-- url     : https://prove2.me/submissions/df9bf2fd-446c-440a-87e6-08ae243de7a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PNormalisationModelLocalizationX
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_toFracModel_mem_e173d248237c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_curveLocalRing_358a5a627391


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
theorem _root_.solution (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (z : Localization (normalModelSubmonoid M q)) :
    locToFrac M hJ hq z ∈ integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (normalModelSubmonoid M q) z
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨f, hf, hfs⟩ := s.2
  have hs : (s : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = Ideal.Quotient.mk M.ideal (rename Sum.inl f) :=
    hfs.symm
  obtain ⟨u, hu⟩ := isUnit_algebraMap_curveLocalRing J q f (fun h0 => hf (RingHom.mem_ker.2 h0))
  have key : locToFrac M hJ hq (IsLocalization.mk' _ (Ideal.Quotient.mk M.ideal h) s) =
      toFracModel M q h * algebraMap (curveLocalRing J q) (FractionRing (curveLocalRing J q)) ↑u⁻¹ := by
    rw [locToFrac, IsLocalization.lift_mk'_spec, hs, modelToFrac_mk, modelToFrac_mk, toFracModel_rename, toFrac,
      RingHom.comp_apply, ← hu, mul_left_comm, ← map_mul, Units.mul_inv, map_one, mul_one]
  rw [key]
  exact mul_mem (toFracModel_mem M hJ hq h) (Subalgebra.algebraMap_mem _ _)
end GroundTheory.Heights₂.Heights.NormalisationModelLocalization
