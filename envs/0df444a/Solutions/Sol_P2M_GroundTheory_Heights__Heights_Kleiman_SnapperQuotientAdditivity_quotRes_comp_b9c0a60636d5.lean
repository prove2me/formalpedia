-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotRes_comp_b9c0a60636d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:08.920378+00:00
-- url     : https://prove2.me/submissions/f6ed561e-bf7e-4a27-ba0c-0b05ec9419b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd

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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
theorem _root_.solution (F₁ F₂ : SubSystem k x E) (I J K : Chart x) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1) :
    (SubSystem.quotRes F₁ F₂ J K hJK).comp (SubSystem.quotRes F₁ F₂ I J hIJ) =
      SubSystem.quotRes F₁ F₂ I K (hIJ.trans hJK) :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
