-- Prove2me | solution 1 for PIW.AdelClassFin.DictGen.exists_denominator_fmat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:43.547801+00:00
-- url     : https://prove2.me/submissions/f5b3814b-7f23-4730-b459-996c132f8535

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
import Theorems.Thm_PIW_AdelClassFin_DictGen_natSmul_mem
import Theorems.Thm_PIW_AdelClassFin_DictGen_denom

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
theorem _root_.solution (hD : LDenom) (x : I.Gf) : ∃ N : ℕ, 0 < N ∧ ∀ y ∈ I.Lf,
    (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf := by
  obtain ⟨N1, h1, hN1⟩ := denom I hD (I.fmat x)
  obtain ⟨N2, h2, hN2⟩ := denom I hD (I.fmat x⁻¹)
  refine ⟨N1 * N2, Nat.mul_pos h1 h2, fun y hy => ⟨?_, ?_⟩⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact natSmul_mem I _ (hN1 y hy)
  · rw [Nat.cast_mul, mul_smul]
    exact natSmul_mem I _ (hN2 y hy)
end PIW.AdelClassFin.DictGen
