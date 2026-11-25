-- Prove2me | solution 1 for PI.GGMatBoundW.totOp_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:56:37.872697+00:00
-- url     : https://prove2.me/submissions/786dc99e-3458-4506-ae56-bb31e6bcf2da

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_JointEigenvectorExists
import Theorems.Thm_PI_GGMatBoundW_gamProd_conj

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
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}
namespace PI.GGMatBoundW
theorem _root_.solution (ψ : ∀ v, AddChar (Fq v) ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V) (g : ∀ v, GL (Fin k) (Fq v)) :
    π g ∘ₗ totOp ψ π = totOp ψ π ∘ₗ π g := by
  unfold totOp
  show π g * (∑ x, gamProd ψ x • π x) = (∑ x, gamProd ψ x • π x) * π g
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ (fun x => ?_)
  simp only [mul_smul_comm, smul_mul_assoc, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_apply]
  rw [gamProd_conj]
  congr 1
  rw [← map_mul, ← map_mul]
  congr 1
  group
end PI.GGMatBoundW
