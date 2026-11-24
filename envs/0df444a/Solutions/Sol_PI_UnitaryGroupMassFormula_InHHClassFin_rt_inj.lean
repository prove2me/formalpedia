-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.rt_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:34:32.841798+00:00
-- url     : https://prove2.me/submissions/ad59650c-ac2e-4364-9b7b-51979c217a8e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_RtUnitaryOf
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
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
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) : Function.Injective (rtι I) := by
  haveI : Nonempty (HeightOneSpectrum (𝓞 I.F)) := by
    obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.mp (RingOfIntegers.not_isField I.F)
    exact ⟨⟨p, hp, hp0⟩⟩
  haveI : Nontrivial (FiniteAdeleRing (𝓞 I.F) I.F) := by
    obtain ⟨v⟩ := ‹Nonempty (HeightOneSpectrum (𝓞 I.F))›
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h2 := congrArg (fun x : FiniteAdeleRing (𝓞 I.F) I.F => x v) h
    first
    | exact zero_ne_one (α := v.adicCompletion I.F) h2
    | exact zero_ne_one (α := v.adicCompletion I.F) (by simpa using h2)
  first
  | (have h1 : ⇑(rtι I) = (LinearMap.lTensor I.E (Algebra.linearMap I.F (FiniteAdeleRing (𝓞 I.F) I.F))) ∘
        (TensorProduct.rid I.F I.E).symm := by
      funext a
      simp [rtι, inclE]
     rw [h1]
     exact (Module.Flat.lTensor_preserves_injective_linearMap _ (algebraMap I.F _).injective).comp
       (TensorProduct.rid I.F I.E).symm.injective)
  | exact Algebra.TensorProduct.includeLeft_injective (R := I.F) (S := I.F) (algebraMap I.F _).injective
end PI.UnitaryGroupMassFormula.InHHClassFin
