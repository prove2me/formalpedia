-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_eval__mem_closure_7f74352ff210
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:47.234556+00:00
-- url     : https://prove2.me/submissions/70af32be-0602-4aef-acb1-f62dc59bc644

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_QuotientLiftInjective

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
open GroundTheory.Heights₂.Heights.GenericFibreModelTransport
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.GenericFibreModelTransport
theorem _root_.solution {σ F : Type*} [Field F] (c : ℤ →+* F) (y : σ → F) (f : MvPolynomial σ ℤ) :
    eval₂ c y f ∈ Subfield.closure (Set.range y) := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [eval₂_C, eq_intCast]; exact intCast_mem _ a
  | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
  | mul_X p n hp => rw [eval₂_mul, eval₂_X]; exact mul_mem hp (Subfield.subset_closure ⟨n, rfl⟩)
end GroundTheory.Heights₂.Heights.GenericFibreModelTransport
