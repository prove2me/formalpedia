-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_pX_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:56.884197+00:00
-- url     : https://prove2.me/submissions/189f8b7c-f5dd-4ee3-934e-601541a3dac7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable {D : Dat A n r}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution {y : n → A} (hy : ∀ b, D.h (D.e b) y = 0) (u : n → A) : D.h (D.pX u) y = 0 := by
  have hy' : ∀ b, ∑ x, ∑ x_1, D.σA (D.e b x) * D.JA x x_1 * y x_1 = 0 := fun b => hy b
  simp only [Dat.h, hform, Dat.pX.eq_1, LinearMap.sum_apply, LinearMap.smulRight_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset (Fin r)))]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [← mul_zero (D.σA ((D.hL (D.f d)) u)), ← hy' d, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x1 _ => ?_
  ring
end PI.VolSemiDirect.W.PG.Dat
