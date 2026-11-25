-- Prove2me | solution 1 for PI.Dv.HermitianFormEquivalence.io_j_asAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:58.073798+00:00
-- url     : https://prove2.me/submissions/5ca07236-7a18-4ffc-bd26-f1cc389379d2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_FormEqImage
import Theorems.Thm_PI_Dv_HermitianFormEquivalence_asAlg_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.HermitianFormEquivalence
open PI.Dv
variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}
namespace PI.Dv.HermitianFormEquivalence
theorem _root_.solution (M : GMap K σ G T EE ρE) (a : MonoidAlgebra K G) (x : M.VK) :
    M.io (M.j (M.rhoK.asAlgebraHom a x)) = ∑ g : G, σ (a.coeff g) • ρE g (M.io (M.j x)) := by
  rw [asAlg_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.map_smulₛₗ, map_smul, M.j_eq, M.io_eq]
end PI.Dv.HermitianFormEquivalence
