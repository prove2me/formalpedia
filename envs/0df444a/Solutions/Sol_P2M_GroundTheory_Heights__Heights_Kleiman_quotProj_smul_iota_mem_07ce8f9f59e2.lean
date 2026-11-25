-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_smul_iota_mem_07ce8f9f59e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:44:55.023248+00:00
-- url     : https://prove2.me/submissions/c6ac42b7-629a-414b-b802-e32cd3ff2779

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_smul_iota_fc9d93ee6b76

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
    quotProj M₁ M₂ c (r • quotIota M₁ M₂ e g) ∈ Submodule.span (Poly S N) {quotIota M₁ M₂ e g} := by
  rw [quotProj_smul_iota]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman
