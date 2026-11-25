-- Prove2me | solution 1 for PIW.AdelClassFin.svR_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:18:54.53234+00:00
-- url     : https://prove2.me/submissions/d26e795f-178c-4944-9bb7-81bc911695c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField Matrix
open scoped ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
namespace PIW.AdelClassFin
theorem _root_.solution {o : Type*} [Fintype o] (X : Matrix o κ ℂ) (A : Matrix o o ℂ) (v : κ → ℂ) :
    star (X *ᵥ v) ⬝ᵥ (A *ᵥ (X *ᵥ v)) = star v ⬝ᵥ ((Xᴴ * A * X) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]
end PIW.AdelClassFin
