-- Prove2me | solution 1 for PIW.AdelClassFin.SpO.cat_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:14.752241+00:00
-- url     : https://prove2.me/submissions/eab32b0b-a725-42bf-93c0-b5f0848fbac9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartSplitOfOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SpComp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SpDen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SplHformZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartBetween
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_BlkMulVecCat
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
open PIW PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
open PIW.AdelClassFin.SpO
namespace PIW.AdelClassFin.SpO
theorem _root_.solution {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (c : Fin k → E) :
    cat e c 0 = ∑ i, c i • (Pi.single (e (Sum.inl i)) (1 : E) : Fin m → E) := by
  funext r
  obtain ⟨t, rfl⟩ := e.surjective r
  cases t with
  | inl a => simp [cat, Finset.sum_apply, Pi.single_apply, e.injective.eq_iff]
  | inr b => simp [cat, Finset.sum_apply, Pi.single_apply, e.injective.eq_iff]
end PIW.AdelClassFin.SpO
