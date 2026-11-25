-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_residue_algebraMap_79a42e5ee542
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:22.36046+00:00
-- url     : https://prove2.me/submissions/c93f2552-b7b2-4a1c-b90f-46b87025b6e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecIdealOfPrime

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
    (a : MvPolynomial (Par e n) (𝓞 K)) :
    algebraMap (ParDVR e n v) (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField
        (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) a) =
      eval₂Hom (resToKappa e n v) (parYκ e n v) (a.map (algebraMap (𝓞 K) v.asIdeal.ResidueField)) := by
  have h : (algebraMap (ParDVR e n v) (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField).comp
        (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v)) =
      (eval₂Hom (resToKappa e n v) (parYκ e n v)).comp
        (MvPolynomial.map (algebraMap (𝓞 K) v.asIdeal.ResidueField)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun p => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C, eval₂Hom_C]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact (Ideal.ResidueField.map_algebraMap v.asIdeal (IsLocalRing.maximalIdeal (ParDVR e n v))
        (algebraMap (𝓞 K) (ParDVR e n v)) (comap_maximalIdeal_parDVR e n v).symm c).symm
    · simp only [RingHom.comp_apply, MvPolynomial.map_X, eval₂Hom_X']
      rfl
  exact RingHom.congr_fun h a
end GroundTheory.Heights₂.Heights.Vertical.SecIdealOfPrime
