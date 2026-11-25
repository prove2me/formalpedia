-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.SD.mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:18.977661+00:00
-- url     : https://prove2.me/submissions/e54a62d0-2884-40c2-862f-1c682a8817e2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_SD_p_pair
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_SD_ext
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_tens_iff
import Theorems.Thm_PI_OmFibreUniq_W_SdCore_key
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv
import Theorems.Thm_split_integral_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
variable {σ v}
open PI.UnitaryGroupMassFormula.LocJacTyp.SD
variable (D : SD σ v)
namespace PI.UnitaryGroupMassFormula.LocJacTyp.SD
theorem _root_.solution (x : Fv F v ⊗[F] E) :
    x ∈ OEv (E := E) v ↔ D.p 0 x ∈ v.adicCompletionIntegers F ∧ D.p 1 x ∈ v.adicCompletionIntegers F := by
  let f : (Fv F v ⊗[F] E) →ₐ[Fv F v] Fv F v × Fv F v := (D.p 0).prod (D.p 1)
  have hinj : Function.Injective f := fun z w h => D.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hsurj : Function.Surjective f := fun ab =>
    ⟨ab.1 • D.e + ab.2 • (1 - D.e), Prod.ext (D.p_pair _ _).1 (D.p_pair _ _).2⟩
  let spl : E ⊗[F] Fv F v ≃+* Fv F v × Fv F v :=
    (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.trans (RingEquiv.ofBijective f ⟨hinj, hsurj⟩)
  have hspl : ∀ a : Fv F v, spl ((1 : E) ⊗ₜ[F] a) = (a, a) := by
    intro a
    have h1 : spl ((1 : E) ⊗ₜ[F] a) = f (Algebra.TensorProduct.comm F E (Fv F v) ((1 : E) ⊗ₜ[F] a)) := rfl
    rw [h1, Algebra.TensorProduct.comm_tmul,
      show (a ⊗ₜ[F] (1 : E) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) a from rfl,
      AlgHom.commutes]
    rfl
  have key := split_integral_local F E v spl hspl ((Algebra.TensorProduct.comm F E (Fv F v)).symm x)
  have hx : spl ((Algebra.TensorProduct.comm F E (Fv F v)).symm x) = f x := by
    show f (Algebra.TensorProduct.comm F E (Fv F v) ((Algebra.TensorProduct.comm F E (Fv F v)).symm x)) = f x
    rw [AlgEquiv.apply_symm_apply]
  rw [hx, tens_iff] at key
  exact key
end PI.UnitaryGroupMassFormula.LocJacTyp.SD
