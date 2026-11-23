-- Prove2me | solution 1 for PI.Dv.TIW.epsS_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:23.168321+00:00
-- url     : https://prove2.me/submissions/093e46f2-08c2-4106-ae47-b40ab6a382f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TraceMemOfIntR
import Theorems.Thm_PI_Dv_TIW_card_H_pos
import Theorems.Thm_PI_Dv_TIW_eps_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W)
namespace PI.Dv.TIW
theorem _root_.solution (P : Pair K G) : epsS P = ((Nat.card P.H : ℕ) : K) • eps P := by
  have : ((Nat.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast (card_H_pos P).ne'
  rw [eps_eq, smul_smul, mul_inv_cancel₀ this, one_smul]
end PI.Dv.TIW
