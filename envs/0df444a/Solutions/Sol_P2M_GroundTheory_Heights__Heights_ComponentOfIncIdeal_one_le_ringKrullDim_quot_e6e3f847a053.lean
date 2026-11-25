-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_one_le_ringKrullDim_quot_e6e3f847a053
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:39:37.198164+00:00
-- url     : https://prove2.me/submissions/9fc5156f-c0fb-46c0-80b0-f3f80a768ddd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PComponentOfIncIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_ringKrullDim_quot_add_one_le_6d257a8d96e5

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
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComponentOfIncIdeal
namespace GroundTheory.Heights₂.Heights.ComponentOfIncIdeal
theorem _root_.solution {F : Type} [Field F] {n : ℕ} {W : Ideal (MvPolynomial (Fin n) F)}
    (hW : IsProjPrime W) : (1 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ W) := by
  have hWp := hW.isPrime
  set m : Ideal (MvPolynomial (Fin n) F) := RingHom.ker (constantCoeff : MvPolynomial (Fin n) F →+* F)
  have hmp : m.IsPrime := RingHom.ker_isPrime _
  have hle : W ≤ m := by
    intro f hf
    rw [RingHom.mem_ker]
    by_contra h
    have h0 := hW.isHomog f hf 0
    rw [homogeneousComponent_zero] at h0
    have hc : coeff 0 f ≠ 0 := by rwa [← constantCoeff_eq]
    exact hWp.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit hc).map C))
  have hne : W ≠ m := by
    obtain ⟨j, hj⟩ := hW.isRelevant
    intro h
    exact hj (h ▸ (by simp [m] : (X j : MvPolynomial (Fin n) F) ∈ m))
  have h := ringKrullDim_quot_add_one_le hle hne
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ m) :=
    ringKrullDim_nonneg_of_nontrivial
  exact (le_add_of_nonneg_left h0).trans h
end GroundTheory.Heights₂.Heights.ComponentOfIncIdeal
