-- Prove2me | solution 1 for PI.KerIso.FourSqW.from_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:02.390258+00:00
-- url     : https://prove2.me/submissions/5ba36bab-ea1e-4ac1-a51b-829df783dfc6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QmapInjective
import Theorems.Thm_PI_KerIso_FourSqW_qmap_apply
import Theorems.Thm_PI_KerIso_FourSqW_qmap_injective
import Theorems.Thm_PI_KerFourSqW_exists_quat
import Theorems.Thm_PI_KerFourSqW_quat_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open PI PI.KerIso PI.KerIso.FourSqW
open PI.KerFourSqW
namespace PI.KerIso.FourSqW
theorem _root_.solution : FromDiag := by
  intro K E _ _ _ _ _ cj n _ b q hq hb
  choose Q hQ using fun i => exists_quat (q i) (hq i)
  have : Module.Finite K E := Module.Finite.of_basis b
  have hdim : Module.finrank K (Fin 4 → E) = Module.finrank K (Fin 4 × n → K) := by
    rw [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis b,
      Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  refine ⟨(qmap b Q).linearEquivOfInjective (qmap_injective b Q q hq hQ) hdim, ?_⟩
  intro x y
  simp only [LinearMap.linearEquivOfInjective_apply]
  rw [map_sum]
  unfold DiagId at hb
  simp_rw [hb]
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_comm (γ := Fin 4)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : ∀ c, algebraMap K E (qmap b Q x (c, i))
      = ∑ a, (Q i c a : E) * algebraMap K E (b.repr (x a) i) := by
    intro c
    rw [qmap_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_ratCast]
  have hy : ∀ c, algebraMap K E (qmap b Q y (c, i))
      = ∑ a, (Q i c a : E) * algebraMap K E (b.repr (y a) i) := by
    intro c
    rw [qmap_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_ratCast]
  simp_rw [hx, hy]
  rw [quat_herm cj (Q i) (q i) (hQ i), Finset.mul_sum]
end PI.KerIso.FourSqW
