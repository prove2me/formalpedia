-- Prove2me | solution 1 for PI.OddDualWeyl.LowA.expo_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:59.078295+00:00
-- url     : https://prove2.me/submissions/3d2e46be-affc-405b-b71c-daed0b21c07e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightDualOf
import Theorems.Thm_PI_OddDualWeyl_LowA_nuNext_castSucc
import Theorems.Thm_PI_OddDualWeyl_LowA_nuStar_apply

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
open PI PI.OddDualWeyl PI.OddDualWeyl.LowA
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.LowA
theorem _root_.solution {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (s : Fin m) :
    nuOf (lamStar lam) s.castSucc - nuNext (nuOf (lamStar lam)) s.castSucc =
      nuOf lam s.rev.castSucc - nuNext (nuOf lam) s.rev.castSucc := by
  rw [nuNext_castSucc, nuNext_castSucc]
  simp only [nuStar_apply, Fin.rev_castSucc, Fin.rev_succ]
  simp only [PI.OddDualWeyl.nuOf]
  have h1 := hlam (Fin.zero_le s.rev.castSucc)
  have h2 := hlam (show s.rev.castSucc ≤ s.rev.succ from Fin.castSucc_lt_succ.le)
  have h3 := hlam (Fin.le_last s.rev.succ)
  omega
end PI.OddDualWeyl.LowA
