-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HeightOfCycle_finsum_log_gaussNorm_map_49e491896c3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:54.792535+00:00
-- url     : https://prove2.me/submissions/28891c45-3284-41ec-b846-41565688930b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfCycle_gaussNorm_eq_iSup_6f64d070639a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_iSup_algebraMap_ec5718db4e82


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
open MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.HeightOfCycle
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.HeightOfCycle
theorem _root_.solution {E : Type*} [Field E] [NumberField E] [Algebra E K] {ι : Type*}
    {P : MvPolynomial ι E} (hP : P ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (P.map (algebraMap E K))) =
      Module.finrank E K *
        ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Real.log (gaussNorm v P) := by
  have hPK : P.map (algebraMap E K) ≠ 0 :=
    fun h0 ↦ hP (MvPolynomial.map_injective _ (algebraMap E K).injective (by rw [h0, _root_.map_zero]))
  obtain ⟨m0, hm0⟩ := support_nonempty.mpr hP
  have hy : (fun m : P.support ↦ P.coeff m) ≠ 0 :=
    Function.ne_iff.mpr ⟨⟨m0, hm0⟩, mem_support_iff.mp hm0⟩
  have eK : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      gaussNorm v (P.map (algebraMap E K)) =
        ⨆ m : P.support, FinitePlace.equivHeightOneSpectrum.symm v (algebraMap E K (P.coeff m)) :=
    fun v ↦ by
      rw [gaussNorm_eq_iSup v hPK P.support (support_map_subset _ _)]
      simp_rw [coeff_map]
  have eE : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      gaussNorm v P = ⨆ m : P.support, FinitePlace.equivHeightOneSpectrum.symm v (P.coeff m) :=
    fun v ↦ gaussNorm_eq_iSup v hP P.support subset_rfl
  simp_rw [eK, eE]
  rw [finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w : FinitePlace K ↦ Real.log (⨆ m : P.support, w (algebraMap E K (P.coeff m)))),
    finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w : FinitePlace E ↦ Real.log (⨆ m : P.support, w (P.coeff m)))]
  exact finsum_log_iSup_algebraMap hy
end GroundTheory.Heights₂.Heights.HeightOfCycle
