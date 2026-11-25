-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.Oh_smul_latHat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:02.57169+00:00
-- url     : https://prove2.me/submissions/863ee3f0-deb6-47c5-b503-e263ae4f9bd5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_intAf_mul
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
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (L : Set (Fin M → E)) (hL : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ L, e • x ∈ L)
    {z : Af F ⊗[F] E} (hz : z ∈ PI.UnitaryGroupMassFormula.UJClassFin.Oh F E) {y : Fin M → Af F ⊗[F] E}
    (hy : y ∈ latHat F E L) : z • y ∈ latHat F E L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hz
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, hc, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * c, PI.UnitaryGroupMassFormula.UJClassFin.intAf_mul ha hc, t • x, hL t ht x hx, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, smul_eq_mul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add y w _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [smul_neg]; exact neg_mem h1
  | zero => rw [zero_smul]; exact zero_mem _
  | add z w _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg z _ h1 => rw [neg_smul]; exact neg_mem h1
end PI.UnitaryGroupMassFormula.UJClassMass
