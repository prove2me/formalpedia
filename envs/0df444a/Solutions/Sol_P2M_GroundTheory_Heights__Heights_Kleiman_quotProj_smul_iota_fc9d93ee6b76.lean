-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_smul_iota_fc9d93ee6b76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:24.660326+00:00
-- url     : https://prove2.me/submissions/73d7fcaa-0c1a-46ed-80e8-a1f4131df4ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
variable (M₁ M₂ : FinGradedSub (S := S) (x := x) E)
variable {M₁ M₂}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (r : Poly S N) {e : ℤ} (g : M₁.piece e) (c : ℤ) :
    quotProj M₁ M₂ c (r • quotIota M₁ M₂ e g) = ∑ i ∈ Finset.range (r.totalDegree + 1),
      if e + i = c then homogeneousComponent i r • quotIota M₁ M₂ e g else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent r, Finset.sum_smul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · subst h
    rw [smul_quotIota M₁ M₂ (homogeneousComponent_isHomogeneous i r), quotProj_iota_self]
  · rw [smul_quotIota M₁ M₂ (homogeneousComponent_isHomogeneous i r), quotProj_iota_ne M₁ M₂ h]
end GroundTheory.Heights₂.Heights.Kleiman
