-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_top_77cd259be07e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:28.988717+00:00
-- url     : https://prove2.me/submissions/56526491-48b6-4b38-b2fa-7649be89e6e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThree

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
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (I : Chart x) : idealChart (x := x) (⊤ : Ideal (Poly k N)) I = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  refine Submodule.subset_span ⟨1, 1, 0, Submodule.mem_top, one_mem _, isHomogeneous_one _ _,
    isHomogeneous_one _ _, ?_⟩
  simp
end GroundTheory.Heights₂.Heights.Kleiman
