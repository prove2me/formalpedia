-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_zeroSetEuc_subsingleton_of_dim_zero_78a54154e23d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:41:01.032508+00:00
-- url     : https://prove2.me/submissions/062cbf52-05b4-41cc-94d8-c56277646dcc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarWirtinger
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyLelongMono

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
open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((0 : ℕ) : WithBot ℕ∞))
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ zeroSetEuc J) :
    ∀ y ∈ zeroSetEuc J, y = z := by
  have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) := Ring.krullDimLE_iff.2 (le_of_eq hdim)
  have hmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain
  obtain ⟨p, hp⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton (K := ℂ)).1 hmax
  have hcoord : ∀ w ∈ zeroSetEuc J, ∀ i, w i = p i := by
    intro w hw i
    have hmem : (X i - C (p i) : MvPolynomial (Fin n) ℂ) ∈ J := by
      rw [hp, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    have := hw _ hmem
    simp only [map_sub, eval_X, eval_C] at this
    exact sub_eq_zero.1 this
  intro y hy
  ext i
  rw [hcoord y hy i, hcoord z hz i]
end GroundTheory.Heights₂.Heights
