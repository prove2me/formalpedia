-- Prove2me | solution 1 for PI.GGConvScalarW.gam_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:28.005308+00:00
-- url     : https://prove2.me/submissions/cbdd50cf-48d7-40b6-8ac6-765520093439

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic Finset
namespace PI.GGConvScalarW
theorem _root_.solution {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) (g x : GL (Fin k) F) :
    gam ψ₀ (g * x * g⁻¹) = gam ψ₀ x := by
  unfold gam
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight g) (fun y => psiNat ψ₀ (y * x * y⁻¹))]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Equiv.coe_mulRight]
  congr 1
  group
end PI.GGConvScalarW
