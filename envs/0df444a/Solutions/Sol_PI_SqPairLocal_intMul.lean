-- Prove2me | solution 1 for PI.SqPairLocal.intMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:43.58586+00:00
-- url     : https://prove2.me/submissions/15ac1045-0dc6-42bb-9887-185476baf4a3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Lemmata_GeneralBFactLeftBis_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsDenFg
import Theorems.Thm_PI_SqPairLocal_exists_den_fg
import Theorems.Thm_PI_SqPairLocal_nat_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
namespace PI.SqPairLocal
theorem _root_.solution : IntMul := by
  intro E _ _ _ N L' L'' h' h'' n hn
  obtain ⟨d1, hd1, k1⟩ := exists_den_fg L' L'' h'.1 h''.2.1
  obtain ⟨d2, hd2, k2⟩ := exists_den_fg L'' L' h''.1 h'.2.1
  obtain ⟨D', hD', hD0⟩ := nat_mul (d1 * d2) (mul_ne_zero hd1 hd2)
  obtain ⟨n', hn', hn0⟩ := nat_mul n hn
  refine ⟨Ideal.absNorm (Ideal.span {d1 * d2}) * Ideal.absNorm (Ideal.span {n}),
    mul_ne_zero hD0 hn0, fun y hy => ?_⟩
  have hDy : (d1 * d2) • y ∈ L' ∧ (d1 * d2) • y ∈ L'' := by
    rcases hy with hy | hy
    · have e : (d1 * d2) • y = d2 • (d1 • y) := by rw [smul_smul, mul_comm]
      exact ⟨L'.smul_mem _ hy, e ▸ L''.smul_mem d2 (k1 y hy)⟩
    · have e : (d1 * d2) • y = d1 • (d2 • y) := by rw [smul_smul]
      exact ⟨e ▸ L'.smul_mem d1 (k2 y hy), L''.smul_mem _ hy⟩
  refine ⟨(D' * n') • ((d1 * d2) • y), L'.smul_mem _ hDy.1, L''.smul_mem _ hDy.2, ?_⟩
  rw [Nat.cast_mul, hD', hn', smul_smul, smul_smul]
  congr 1
  ring
end PI.SqPairLocal
