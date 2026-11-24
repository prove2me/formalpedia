-- Prove2me | solution 1 for PIW.AdelClassFin.DictGen.nL_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:35:44.563234+00:00
-- url     : https://prove2.me/submissions/05c9e2f0-5a20-4f68-8a13-94d0ac4b2d2d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
import Theorems.Thm_PIW_AdelClassFin_DictGen_iv_mem
import Theorems.Thm_PIW_AdelClassFin_DictGen_iv_nsmul

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
theorem _root_.solution (x : I.Gf) (N : ℕ)
    (hN : ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf)
    {l : Fin I.n → I.E} (hl : l ∈ I.L) : N • l ∈ abelian₂ I x := by
  show I.fmat x⁻¹ *ᵥ iv I (N • l) ∈ I.Lf
  rw [iv_nsmul, Matrix.mulVec_smul]
  exact (hN _ (iv_mem I hl)).2
end PIW.AdelClassFin.DictGen
