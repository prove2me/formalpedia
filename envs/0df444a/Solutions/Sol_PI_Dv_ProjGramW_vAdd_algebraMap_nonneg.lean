-- Prove2me | solution 1 for PI.Dv.ProjGramW.vAdd_algebraMap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:22.648645+00:00
-- url     : https://prove2.me/submissions/58142571-56f9-4350-a130-4d419d8962ef

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
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
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    0 ≤ vAdd w (algebraMap (𝓞 K) K r) := by
  unfold Formalism.BasicNotions.vAdd
  have h1 : w.valuation K (algebraMap (𝓞 K) K r) ≤ 1 := w.valuation_le_one r
  by_cases h0 : w.valuation K (algebraMap (𝓞 K) K r) = 0
  · rw [h0, WithZero.log_zero]
    simp
  · have h2 : WithZero.exp (WithZero.log (w.valuation K (algebraMap (𝓞 K) K r))) ≤ WithZero.exp 0 := by
      rw [WithZero.exp_log h0, WithZero.exp_zero]
      exact h1
    rw [WithZero.exp_le_exp] at h2
    omega
end PI.Dv.ProjGramW
