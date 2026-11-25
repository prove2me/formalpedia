-- Prove2me | solution 1 for PI.GGMatBoundW.placeOp_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:39.6533+00:00
-- url     : https://prove2.me/submissions/e7925f8d-e29b-4e55-b01e-05bed508e002

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_JointEigenvectorExists
import Theorems.Thm_PI_GGMatBoundW_mulSingle_conj
import Theorems.Thm_PI_GGConvScalarW_gam_conj


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
    (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V) (v : ι) (g : ∀ v, GL (Fin k) (Fq v)) :
    π g ∘ₗ placeOp ψ π v = placeOp ψ π v ∘ₗ π g := by
  unfold placeOp
  show π g * (∑ y, gam (ψ v) y • π (Pi.mulSingle v y)) = (∑ y, gam (ψ v) y • π (Pi.mulSingle v y)) * π g
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (MulAut.conj (g v)).toEquiv _ _ (fun y => ?_)
  simp only [mul_smul_comm, smul_mul_assoc, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_apply]
  rw [PI.GGConvScalarW.gam_conj]
  congr 1
  rw [← map_mul, ← map_mul, ← mulSingle_conj]
  congr 1
  group
end PI.GGMatBoundW
