-- Prove2me | solution 1 for PIW.AdelClassFin.DictGen.nLam_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:50.340195+00:00
-- url     : https://prove2.me/submissions/9cbd1941-3604-46ff-9e5a-e849f466e1ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
import Theorems.Thm_PIW_AdelClassFin_DictGen_iv_nsmul
import Theorems.Thm_PIW_AdelClassFin_DictGen_fmat_mul_inv

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
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictGen
variable (I : AutInst)
namespace PIW.AdelClassFin.DictGen
theorem _root_.solution (hInt : LInter) (x : I.Gf) (N : ℕ)
    (hN : ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf)
    {v : Fin I.n → I.E} (hv : v ∈ abelian₂ I x) : N • v ∈ I.L := by
  apply hInt I
  have hv' : I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf := hv
  have e : iv I v = I.fmat x *ᵥ (I.fmat x⁻¹ *ᵥ iv I v) := by
    rw [Matrix.mulVec_mulVec, fmat_mul_inv, Matrix.one_mulVec]
  rw [iv_nsmul, e]
  exact (hN _ hv').1
end PIW.AdelClassFin.DictGen
