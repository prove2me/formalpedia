-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_gaussNorm_map_of_coeff_notMem_1963a33cdafd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:40.487217+00:00
-- url     : https://prove2.me/submissions/994223fc-15ff-4719-a2fb-c3f80700bfb6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussDVR
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35


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
open MvPolynomial NumberField IsDedekindDomain WithZero
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) {σ : Type*}
    (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by
  obtain ⟨m, hm⟩ := hg
  apply le_antisymm
  · refine gaussNormOf_le _ zero_le_one fun d => ?_
    rw [coeff_map, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one K (v := v) (g.coeff d)
  · have h1 := le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v)
      (g.map (algebraMap (𝓞 K) K)) m
    rw [coeff_map, ← FinitePlace.norm_embedding,
      (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm] at h1
    exact h1
end GroundTheory.Heights₂.Heights.Vertical
