-- Prove2me | solution 1 for P2M_GlobalTheory_qExpansion_E__026e1fb3b144
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:57.108913+00:00
-- url     : https://prove2.me/submissions/0eb9bb77-5d77-49b0-a7ed-d2bdd825ae2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real ArithmeticFunction.sigma
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
namespace GlobalTheory
theorem _root_.solution : qExpansion 1 E₄ =
    PowerSeries.map (Int.castRingHom ℂ) (1 + 240 * PowerSeries.mk fun n ↦ (σ 3 n : ℤ)) := by
  ext m
  rw [EisensteinSeries.E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]
  rw [coeff_map, show (240 : ℤ⟦X⟧) = C 240 from rfl, map_add, coeff_C_mul, coeff_one]
  split_ifs with hm
  · simp [hm]
  · simp; norm_num
end GlobalTheory
