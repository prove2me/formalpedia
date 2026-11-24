-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.latHat_Oh_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:11:11.838669+00:00
-- url     : https://prove2.me/submissions/a3a4b2ed-a6c5-4c34-8eb7-cb1d97d2a781

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crd_smul
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
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {o : Af F ⊗[F] E}
    (ho : o ∈ Oh F E) {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E (crdOf b L0)) :
    o • y ∈ latHat F E (crdOf b L0) := by
  induction ho using AddSubgroup.closure_induction with
  | mem o ho =>
    obtain ⟨a, ha, e, he, rfl⟩ := ho
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a', ha', x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * a', intAf_mul ha ha', e • x, crd_smul b L0 he hx, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add y y' _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [smul_neg]; exact neg_mem h1
  | zero => rw [zero_smul]; exact zero_mem _
  | add o o' _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg o _ h1 => rw [neg_smul]; exact neg_mem h1
end PI.UnitaryGroupMassFormula.UJClassMass
