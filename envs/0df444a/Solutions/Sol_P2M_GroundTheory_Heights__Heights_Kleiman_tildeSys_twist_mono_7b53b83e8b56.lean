-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_tildeSys_twist_mono_7b53b83e8b56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:21.487806+00:00
-- url     : https://prove2.me/submissions/93a6623d-1ce2-40b7-954f-f0cefa2f30de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotTransSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoPieceSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepTwoReduce

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
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
omit [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {M M' : FinGradedSub (S := S) (x := x) E} (h : ∀ c, M.piece c ≤ M'.piece c)
    (Q : SubSystem S x Ω) (I : Chart x) :
    ((M.tildeSys 0).twist Q).sub I ≤ ((M'.tildeSys 0).twist Q).sub I := by
  refine Submodule.span_mono ?_
  rintro _ ⟨q, hq, y, hy, rfl⟩
  refine ⟨q, hq, y, ?_, rfl⟩
  change y ∈ M'.tilde 0 I
  change y ∈ M.tilde 0 I at hy
  refine Submodule.span_mono ?_ hy
  rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
  exact ⟨m, s, a, e, hs, hse, h a hm, hae, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman
