-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.sfin_of_Lam_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:17.847079+00:00
-- url     : https://prove2.me/submissions/b0fec42d-98f5-4581-86dd-31c1fdb47ebc

import Definitions.Def_Formalism_PeriodIntegrals_UJClassFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (L : Set (Fin M → E))
    (hR : ∀ (h : HA (AF F) σ J) (y : Fin M → Af F ⊗[F] E),
      (finMat σ J h⁻¹).mulVec y ∈ latHat F E L ↔ y ∈ latHat F E (abelian₂ σ J L h))
    (h h' : HA (AF F) σ J) (he : abelian₂ σ J L h = abelian₂ σ J L h') : h⁻¹ * h' ∈ SFin σ J L := by
  intro y
  rw [finMat_mul, ← Matrix.mulVec_mulVec]
  have e1 : (finMat σ J h'⁻¹).mulVec ((finMat σ J h').mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, ← finMat_mul, inv_mul_cancel, finMat_one, Matrix.one_mulVec]
  rw [hR h, he, ← hR h', e1]
end PI.UnitaryGroupMassFormula.UJClassFin
