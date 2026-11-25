-- Prove2me | solution 1 for PI.GGMatBoundW.sum_beta_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:27.565093+00:00
-- url     : https://prove2.me/submissions/fc3f33f2-f953-4c9c-bd61-1c7b8b0cfc6c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_ProdFormula
import Theorems.Thm_PI_GGMatBoundW_beta_insert
import Theorems.Thm_PI_GGMatBoundW_placeOp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PI.GGMatBoundW
theorem _root_.solution (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    {a : ι} {s : Finset ι} (ha : a ∉ s) (w : V) :
    ∑ x, beta ψ (insert a s) x • π x w = placeOp ψ π a (∑ x, beta ψ s x • π x w) := by
  rw [placeOp_apply]
  simp_rw [beta_insert ψ ha, Finset.sum_smul, map_sum, map_smul, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Fintype.sum_equiv (Equiv.mulLeft (Pi.mulSingle a y)⁻¹) _ _ fun z => ?_
  simp only [Equiv.coe_mulLeft]
  have hπ : π (Pi.mulSingle a y) (π ((Pi.mulSingle a y)⁻¹ * z) w) = π z w := by
    have h2 := congrArg (fun f => f w) (map_mul π (Pi.mulSingle a y) ((Pi.mulSingle a y)⁻¹ * z))
    simp only [mul_inv_cancel_left] at h2
    exact h2.symm
  rw [hπ, mul_smul]
end PI.GGMatBoundW
