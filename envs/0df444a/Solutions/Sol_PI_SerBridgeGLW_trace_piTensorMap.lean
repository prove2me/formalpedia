-- Prove2me | solution 1 for PI.SerBridgeGLW.trace_piTensorMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:47:02.689042+00:00
-- url     : https://prove2.me/submissions/639ddb31-3120-4340-974e-6b526d520ab2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.SerBridgeGLW
namespace PI.SerBridgeGLW
theorem _root_.solution {s : ℕ} {M : Fin s → Type} [∀ c, AddCommGroup (M c)] [∀ c, Module ℂ (M c)]
    [∀ c, Module.Finite ℂ (M c)] (f : ∀ c, M c →ₗ[ℂ] M c) :
    LinearMap.trace ℂ (PiTensorProduct ℂ M) (PiTensorProduct.map f) =
      ∏ c, LinearMap.trace ℂ (M c) (f c) := by
  classical
  let b := fun c => Module.Free.chooseBasis ℂ (M c)
  have hc : ∀ c, LinearMap.trace ℂ (M c) (f c) = ∑ i, (b c).repr (f c (b c i)) i := by
    intro c
    rw [LinearMap.trace_eq_matrix_trace ℂ (b c)]
    simp [Matrix.trace, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [LinearMap.trace_eq_matrix_trace ℂ (Basis.piTensorProduct b)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
    PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]
end PI.SerBridgeGLW
