-- Prove2me | solution 1 for PI.LevelKSplit.W.ExS.existSAll_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:28.95429+00:00
-- url     : https://prove2.me/submissions/156dedd6-b7af-48cc-b2fa-a413625b7028

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SubgroupLocallyCompactHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProdHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
import Theorems.Thm_PI_LevelKSplit_W_ExS_existS_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.ExS
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open PI.VolSemiDirect.W
open scoped TensorProduct
namespace PI.LevelKSplit.W.ExS
theorem _root_.solution (hPr : ProdHaarG) (hsc : SCAf) (hS : SemiNHSAll) (hCo : ConjNHAll) :
    ExistSAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    apply τ.injective
    rw [hσ.2.2.2 τ (σ x), hσ.2.2.2 τ x, star_star]
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact existS_of hJ hinv hPr (hsc F) (hS F E σ hσ M J hJ) (hCo F E σ hσ M J hJ)
end PI.LevelKSplit.W.ExS
