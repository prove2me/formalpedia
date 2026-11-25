-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.finMat_patch_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:27:13.088059+00:00
-- url     : https://prove2.me/submissions/037eecf0-6a59-439e-ade1-8a88eb0ce654

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_finE_inclR
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
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) :
    finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹ =
      ∑ i, finE F E (e i) • ((γ i)⁻¹ : GL (Fin M) E).val.map (inclR (Af F)) := by
  have h0 : finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹ =
      (∑ i, e i • incM (F := F) (γ i)⁻¹).map (finE F E) := rfl
  rw [h0]
  ext a c
  simp [Matrix.map_apply, Matrix.sum_apply, incM, map_sum, map_mul, finE_inclR]
end PI.UnitaryGroupMassFormula.UJClassMass
