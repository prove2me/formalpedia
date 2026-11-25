-- Prove2me | solution 1 for PI.Dv.ProjGramW.transvec_colOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:28.093897+00:00
-- url     : https://prove2.me/submissions/2f4bad9f-64b7-4c46-9b5a-993bfc1dc896

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution {d : ℕ} (i j : Fin d) (hij : i ≠ j) (c : K) :
    Matrix.transvection i j c =
      colOp j (fun p => (if p = j then 1 else 0) + (if p = i then c else 0)) := by
  ext p q
  simp only [Matrix.transvection, colOp, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hq : q = j
  · subst hq
    by_cases hp : p = q
    · subst hp; simp [hij, Ne.symm hij]
    · by_cases hpi : p = i
      · subst hpi; simp [hp]
      · simp [hp, hpi, Ne.symm hpi]
  · by_cases hp : p = q
    · subst hp; simp [hq, Ne.symm hq]
    · simp [hp, hq, Ne.symm hq]
end PI.Dv.ProjGramW
