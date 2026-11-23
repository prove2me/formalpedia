-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.image_latSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:27.27075+00:00
-- url     : https://prove2.me/submissions/3602505c-e477-45b1-b099-87015dce102a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_equivFun_linOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V)
    (L0 : Submodule (𝓞 E) V) (U : GL (Fin M) E) (g : HA (AF F) σ J) :
    (linOf b U : V → V) '' latSet σ J b L0 g =
      {v | b.equivFun v ∈ (fun x => (U : Matrix (Fin M) (Fin M) E).mulVec x) ''
        PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J (crdOf b L0) g} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨b.equivFun w, hw, ?_⟩
    rw [equivFun_linOf]
  · rintro ⟨x, hx, hxv⟩
    refine ⟨b.equivFun.symm x, ?_, ?_⟩
    · show b.equivFun (b.equivFun.symm x) ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J (crdOf b L0) g
      rwa [LinearEquiv.apply_symm_apply]
    · apply b.equivFun.injective
      change b.equivFun (linOf b _ _) = _
      rw [equivFun_linOf, LinearEquiv.apply_symm_apply]
      exact hxv
end PI.UnitaryGroupMassFormula.UJClassMass
