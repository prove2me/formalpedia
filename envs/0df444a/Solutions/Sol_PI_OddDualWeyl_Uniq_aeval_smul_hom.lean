-- Prove2me | solution 1 for PI.OddDualWeyl.Uniq.aeval_smul_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:59:29.757926+00:00
-- url     : https://prove2.me/submissions/495f0558-a038-41fb-a298-003dff23b197

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Lemmata_GeneralBFactRightAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightVectorUnique
import Theorems.Thm_Bl_general_b_fact_right_alt_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Uniq
namespace PI.OddDualWeyl.Uniq
theorem _root_.solution {K S : Type*} [CommRing K] [CommRing S] [Algebra K S] {ι : Type*} [Fintype ι]
    {G : MvPolynomial ι K} {d : ℕ} (hG : IsHomogeneous G d) (c : S) (f : ι → S) :
    aeval (fun v => c * f v) G = c ^ d * aeval f G := by
  first | exact Bl.general_b_fact_right_alt.goal1 .. | (apply Bl.general_b_fact_right_alt.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_alt.goal1 <;> assumption)
end PI.OddDualWeyl.Uniq
