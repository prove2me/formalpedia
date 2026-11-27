-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveNormalisationLength_proof_765dbfa8dadd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:41.377235+00:00
-- url     : https://prove2.me/submissions/a82374b2-0109-467a-a2b8-a734e04b19d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StExtensionQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveNormalisationLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_localization_eq_length_curveLocalRing_faee7f29f935
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_quotient_ne_top_f3409cf43927
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_proof_ad84518a0f0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_algebraMap_curveNormalisation_injective_fe83821bff87


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
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace CurveNormalisationLength
theorem _root_.solution (hFin : CurveNormalisationFinite.Statement)
    (hQ : CurveNormalisationQuotientLength.Statement) (hE : ExtensionQuotientLength.Statement) :
    CurveNormalisationLength.Statement := by
  intro n I q f hrad hdim hf
  set O := curveLocalRing I q
  set f' := algebraMap (MvPolynomial (Fin n) ℂ) O f
  have : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have : IsLocalRing O := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : Module.Finite O (curveNormalisation I q) := hFin n I q hrad
  have hfin := length_quotient_ne_top hdim hf

  have hnzd : algebraMap O (curveNormalisation I q) f' ∈ nonZeroDivisors (curveNormalisation I q) := by
    let ι : curveNormalisation I q →+* FractionRing O :=
      (integralClosure O (FractionRing O)).val.toRingHom
    refine mem_nonZeroDivisors_of_injective (f := ι) Subtype.val_injective ?_
    exact (IsLocalization.map_units (FractionRing O) (⟨f', hf⟩ : nonZeroDivisors O)).mem_nonZeroDivisors
  have hEq := hE O (curveNormalisation I q) f' (algebraMap_curveNormalisation_injective I q) hnzd
    (hQ n I q hrad hdim)
  rw [localMult, dif_pos (isPrime_ker_eval q), length_localization_eq_length_curveLocalRing,
    ENat.natCast_toNat hfin, hEq]
  exact GroundTheory.Heights₂.Heights.Vertical.LengthDecomp.proof O (curveNormalisation I q) _ (hEq ▸ hfin)
end CurveNormalisationLength
end GroundTheory.Heights₂.Heights
