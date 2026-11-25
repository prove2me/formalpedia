-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_eulerCharQuot_self_9762b655af6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:51.45308+00:00
-- url     : https://prove2.me/submissions/72b4b18c-1b56-460e-9900-227b8dfda228

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper

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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F : SubSystem k x E) : eulerCharQuot k F F = 0 := by
  unfold eulerCharQuot
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : ∀ I, Subsingleton (F.sub I ⧸ SubSystem.quotSub F F I) := fun I =>
    Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun y _ => y.2)
  have h2 : Subsingleton (Cech.Cochain (fun I => F.sub I ⧸ SubSystem.quotSub F F I) i) := by
    unfold Cech.Cochain; infer_instance
  have h3 : Subsingleton (SubSystem.quotH F F i) := by
    unfold SubSystem.quotH Cech.H
    infer_instance
  simp [Module.finrank_zero_of_subsingleton]
end GroundTheory.Heights₂.Heights.Kleiman
