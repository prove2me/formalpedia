-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.latHat_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:12:43.574701+00:00
-- url     : https://prove2.me/submissions/ac299297-b540-4014-8bc4-1c3a0e6cd0f3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (L : Set (Fin M → E)) {a : Af F} (ha : a ∈ intAf F) {y : Fin M → Af F ⊗[F] E}
    (hy : y ∈ latHat F E L) : (a ⊗ₜ[F] (1 : E)) • y ∈ latHat F E L := by
  unfold latHat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    have hmul : a * a' ∈ intAf F := by
      unfold intAf at ha ha' ⊢
      intro v
      rw [map_mul]
      exact mul_mem (ha v) (ha' v)
    refine ⟨a * a', hmul, x, hx, ?_⟩
    funext i
    simp [Pi.smul_apply, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y1 y2 _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg y _ h => rw [smul_neg]; exact neg_mem h
end PI.UnitaryGroupMassFormula.UJClassFin
