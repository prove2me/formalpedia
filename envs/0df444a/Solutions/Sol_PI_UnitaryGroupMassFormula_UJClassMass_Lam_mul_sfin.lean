-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.Lam_mul_sfin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:43.391085+00:00
-- url     : https://prove2.me/submissions/3e1fb10b-ad3b-4067-b887-0c4b2e036b23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E))
    (g : HA (AF F) σ J) (k : SFin σ J L) :
    PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J L (g * k) = PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J L g := by
  have hk : ∀ y, y ∈ latHat F E L ↔
      (finMat σ J ((k : HA (AF F) σ J)⁻¹)).mulVec y ∈ latHat F E L := (k⁻¹).2
  ext x
  simp only [UJClassFin.abelian₂, Set.mem_setOf_eq, mul_inv_rev]
  unfold finMat at hk ⊢
  unfold HA.mat at hk ⊢
  simp only [Subgroup.coe_mul, Units.val_mul, ← AlgHom.mapMatrix_apply, map_mul] at hk ⊢
  have e : ∀ a c : HA (AF F) σ J, (a * c).1 = a.1 * c.1 := fun a c => rfl
  rw [e, Units.val_mul, map_mul]
  simp only [AlgHom.mapMatrix_apply, ← Matrix.mulVec_mulVec] at hk ⊢
  exact (hk _).symm
end PI.UnitaryGroupMassFormula.UJClassMass
