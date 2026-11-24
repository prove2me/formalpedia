-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmStar.qminor_rev_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:31:35.507058+00:00
-- url     : https://prove2.me/submissions/27c2d949-c7d0-48e3-9010-6a78e0e8d429

import Definitions.Def_Formalism_PeriodIntegrals_QmStar
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds
import Theorems.Thm_Formalism_REAL_quantumMinorRowSkew_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmStar
namespace PI.UnitaryGroupMassFormula.QmStar
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin t → Fin n) (u : ℂ) : qminor E (a ∘ Fin.rev) (b ∘ Fin.rev) u = qminor E a b u := by
  show qminor E (a ∘ (Fin.revPerm : Equiv.Perm (Fin t))) (b ∘ (Fin.revPerm : Equiv.Perm (Fin t))) u = _
  rw [quantumMinorRowSkew_holds A n t E a (b ∘ (Fin.revPerm : Equiv.Perm (Fin t))) Fin.revPerm u,
    quantumMinorColSkew_holds A n t E hE a b Fin.revPerm u, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
end PI.UnitaryGroupMassFormula.QmStar
