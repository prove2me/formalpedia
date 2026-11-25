-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twist_hyps_bc69208ec540
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:02:31.68394+00:00
-- url     : https://prove2.me/submissions/2f0e7ef1-9861-443b-97a7-a61062311977

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_twistBundle_one_62fb03cd3d01
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_span_range_eq_twistMod_one_cf9eb67143e0


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
open MvPolynomial TensorProduct
noncomputable section
universe u v w
variable (k : Type u) [Field k] (N : ℕ)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {Ω : Type w} [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω) :
    (∀ j, x j ∈ (twistBundle k x 1).secs) ∧
    ∀ I, Submodule.span (chartRing k x I) (Set.range x) = (twistBundle k x 1).sub I :=
  ⟨mem_secs_twistBundle_one, span_range_eq_twistMod_one⟩
end GroundTheory.Heights₂.Heights.Kleiman
