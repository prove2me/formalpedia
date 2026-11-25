-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_residue_surj_a014fc5c050d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:29:55.972428+00:00
-- url     : https://prove2.me/submissions/fc2b7458-3181-4c8f-ba85-0b69902c031b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecIdealOfPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_residue_algebraMap_79a42e5ee542

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
open GroundTheory.Heights₂.Heights.Vertical.SecIdealOfPrime
namespace GroundTheory.Heights₂.Heights.Vertical.SecIdealOfPrime
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (z : (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField) :
    ∃ a b, z = eval₂Hom (resToKappa e n v) (parYκ e n v) a / eval₂Hom (resToKappa e n v) (parYκ e n v) b := by
  obtain ⟨r, rfl⟩ := Ideal.algebraMap_residueField_surjective (IsLocalRing.maximalIdeal (ParDVR e n v)) z
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (parPrime e n v).primeCompl r
  refine ⟨a.map (algebraMap (𝓞 K) v.asIdeal.ResidueField),
    (s : MvPolynomial (Par e n) (𝓞 K)).map (algebraMap (𝓞 K) v.asIdeal.ResidueField), ?_⟩
  have hs : algebraMap (ParDVR e n v) (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField
      (algebraMap _ (ParDVR e n v) (s : MvPolynomial (Par e n) (𝓞 K))) ≠ 0 :=
    ((IsLocalization.map_units (ParDVR e n v) s).map _).ne_zero
  rw [← residue_algebraMap, ← residue_algebraMap, eq_div_iff hs, ← map_mul, IsLocalization.mk'_spec]
end GroundTheory.Heights₂.Heights.Vertical.SecIdealOfPrime
