-- Prove2me | solution 1 for PIW.AdelClassFin.spl_cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:57:24.135066+00:00
-- url     : https://prove2.me/submissions/a12c53e3-7ed5-4b82-b859-934438140928

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartSplitOfOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SplHformZero
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
namespace PIW.AdelClassFin
theorem _root_.solution {E : Type} [Field E] [StarRing E] {m k n : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (V : Matrix (Fin m) (Fin k) E) (U : Matrix (Fin m) (Fin n) E) (h : cT (starRingEnd E) V * J * U = 0)
    (c : Fin k → E) (w : Fin n → E) : hform (starRingEnd E) J (V *ᵥ c) (U *ᵥ w) = 0 := by
  have e1 : ∀ x y : Fin m → E,
      hform (starRingEnd E) J x y = (fun i => starRingEnd E (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e2 : (fun i => starRingEnd E ((V *ᵥ c) i)) =
      (V.map (starRingEnd E)) *ᵥ (fun k => starRingEnd E (c k)) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  have h' : (V.map (starRingEnd E))ᵀ * J * U = 0 := h
  rw [e1, e2, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h', Matrix.zero_mulVec, dotProduct_zero]
end PIW.AdelClassFin
