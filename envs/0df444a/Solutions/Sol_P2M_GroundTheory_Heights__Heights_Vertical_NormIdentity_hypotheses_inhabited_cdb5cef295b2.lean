-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormIdentity_hypotheses_inhabited_cdb5cef295b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:28.196131+00:00
-- url     : https://prove2.me/submissions/dc8a1922-7be9-496d-8756-36797c2c88f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_pointForm_map_c29aef258094
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_one_not_mem_point_805b757dbb4c


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
namespace NormIdentity
theorem _root_.solution (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (pointForm.map (algebraMap (𝓞 ℚ) ℚ)) ∧
      linForm (fun j => (((fun _ => (1 : 𝓞 ℚ)) : Fin 1 → 𝓞 ℚ) j : ℚ)) ∉
        (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      ∃ m, pointForm.coeff m ∉ v.asIdeal := by
  refine ⟨isProjPrime_point ℚ, by rw [pointForm_map]; exact isChowForm_point ℚ, ?_, ?_⟩
  · simpa using linForm_one_not_mem_point ℚ
  · refine ⟨Finsupp.single (0, 0) 1, ?_⟩
    have h1 : pointForm.coeff (Finsupp.single (0, 0) 1) = 1 := by simp [pointForm]
    rw [h1]
    exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
end NormIdentity
end GroundTheory.Heights₂.Heights.Vertical
