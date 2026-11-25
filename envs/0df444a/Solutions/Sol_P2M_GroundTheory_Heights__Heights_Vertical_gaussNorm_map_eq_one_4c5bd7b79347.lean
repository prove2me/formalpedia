-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_gaussNorm_map_eq_one_4c5bd7b79347
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:39.736874+00:00
-- url     : https://prove2.me/submissions/ea393ef4-18a8-49c5-b2b6-e857c676982c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussEq
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
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {σ : Type*} (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by
  obtain ⟨m, hm⟩ := hg
  apply le_antisymm
  · refine gaussNormOf_le _ zero_le_one fun d => ?_
    rw [coeff_map, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one K (v := v) (g.coeff d)
  · have h1 := le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v) (g.map (algebraMap (𝓞 K) K)) m
    rw [coeff_map, ← FinitePlace.norm_embedding, (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm] at h1
    exact h1
end GroundTheory.Heights₂.Heights.Vertical
