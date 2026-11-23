-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.equivStep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:36.139326+00:00
-- url     : https://prove2.me/submissions/51e1c477-949e-45ed-adbb-d8c90284db8b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_emb_ratU
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Lam_mul_sfin
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_equivFun_linOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_Lam_emb_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution : EquivStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 _ _ _ _ _ _ _ g γ k
  ext v
  change b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0)
      ((γ : HA (AF F) σ (gramOf h b)) * g * (k : HA (AF F) σ (gramOf h b))) ↔
    v ∈ (iotaG σ (gramOf h b) b γ : V → V) '' latSet σ (gramOf h b) b L0 g
  rw [Lam_mul_sfin, ← emb_ratU, PI.UnitaryGroupMassFormula.UJClassFin.Lam_emb_mul]
  constructor
  · rintro ⟨x, hx, hxv⟩
    refine ⟨b.equivFun.symm x, ?_, ?_⟩
    · show b.equivFun (b.equivFun.symm x) ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g
      rwa [LinearEquiv.apply_symm_apply]
    · apply b.equivFun.injective
      change b.equivFun (linOf b _ _) = _
      rw [equivFun_linOf, LinearEquiv.apply_symm_apply]
      exact hxv
  · rintro ⟨w, hw, rfl⟩
    refine ⟨b.equivFun w, hw, ?_⟩
    change _ = b.equivFun (linOf b _ _)
    rw [equivFun_linOf]
    rfl
end PI.UnitaryGroupMassFormula.UJClassMass
