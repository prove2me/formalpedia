-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_le_originIdeal_of_isHomogeneous_7394c352b960
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:40.980052+00:00
-- url     : https://prove2.me/submissions/8839ec00-592a-4ea0-9524-aef9515d3135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_eq_ker_34d48b0f5439


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hne : I ≠ ⊤) : I ≤ originIdeal n := by
  intro f hf
  rw [originIdeal_eq_ker, RingHom.mem_ker]
  by_contra h0
  have h1 : homogeneousComponent 0 f ∈ I := by
    have := hI 0 hf
    rwa [show (DirectSum.decompose (homogeneousSubmodule (Fin n) ℂ) f 0 : MvPolynomial (Fin n) ℂ)
      = homogeneousComponent 0 f from decomposition.decompose'_apply _ _] at this
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h1
  exact hne (I.eq_top_of_isUnit_mem h1 (isUnit_iff_ne_zero.2 h0 |>.map C))
end GroundTheory.Heights₂.Heights.ComplexSets
