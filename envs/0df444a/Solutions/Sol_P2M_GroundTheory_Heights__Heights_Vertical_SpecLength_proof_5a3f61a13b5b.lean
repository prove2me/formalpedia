-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecLength_proof_5a3f61a13b5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:21.202467+00:00
-- url     : https://prove2.me/submissions/8d0ab9a4-a76b-4ef1-ae79-296947837c2a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_length_quot_map_of_flat_44aaab1f2176
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_secLin_eq_mk_map_f2e6b79d7132

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace SpecLength
theorem _root_.solution (h1 : SpecChart.Statement) (h2 : FiniteOrd.Statement)
    (h3 : ParDVRIsDVR.Statement) (h4 : SecBFinite.Statement) (h5 : SecBLinInj.Statement) :
    SpecLength.Statement := by
  classical
  intro K _ _ n e I f u v hI hf hu 𝔫 W hW hWn
  have hWp : W.IsPrime := hW.1.1.1
  obtain ⟨ψ, hψ, hloc, hflat, hmax⟩ := h1 K n e I v hI 𝔫 W hW hWn
  have := h3 K e n v
  have := h4 K n e I f v hI hf
  have hfin := h2 (ParDVR e n v) (SecB e I v) _ (h5 K n e I f u v hI hf hu) 𝔫
  have hx : algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
      (secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j))) =
      (ψ.comp (Ideal.Quotient.mk _)) (algebraMap _ (Localization.AtPrime W) (linForm u)) := by
    rw [RingHom.comp_apply, hψ]
    exact congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)) (secLin_eq_mk_map I v u)
  have hlen0 := length_quot_map_of_flat (A := Localization.AtPrime W)
    (L := Localization.AtPrime 𝔫.asIdeal)
    (P := (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
    (J := Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)}) (ψ := ψ) hloc hflat
  have hlen := hlen0 hmax
  rw [Ideal.map_span, Set.image_singleton, ← hx] at hlen
  have hmult : localMult (integralModel I ⊔ Ideal.span {linForm u}) W =
      (Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸
        ((integralModel I).map (algebraMap _ (Localization.AtPrime W)) ⊔
          Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)}))).toNat := by
    rw [localMult, dif_pos hWp, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  unfold Ring.ord at hfin ⊢
  rw [hlen] at hfin ⊢
  split_ifs with hlW
  · rw [hmult, ENat.natCast_toNat hfin]
  · have hunit : IsUnit (algebraMap _ (Localization.AtPrime W) (linForm u)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ W _).mpr hlW
    have htop : (integralModel I).map (algebraMap _ (Localization.AtPrime W)) ⊔
        Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)} = ⊤ :=
      eq_top_iff.mpr (le_sup_of_le_right (Ideal.span_singleton_eq_top.mpr hunit).ge)
    rw [htop]
    have : Subsingleton (Localization.AtPrime W ⧸ (⊤ : Ideal (Localization.AtPrime W))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.length_eq_zero
end SpecLength
end GroundTheory.Heights₂.Heights.Vertical
