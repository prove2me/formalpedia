-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.gram_linOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:44:58.188916+00:00
-- url     : https://prove2.me/submissions/f80ea7b5-2e6e-4fe4-9f06-e2bbd5c93e9d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_linOf_basis


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
variable {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {F : Type} [Field F] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) (U : GL (Fin M) E) (i j : Fin M) :
    h (linOf b U (b i)) (linOf b U (b j)) =
      (cT (σ : E →+* E) (U : Matrix (Fin M) (Fin M) E) * gramOf h b * (U : Matrix (Fin M) (Fin M) E)) i j := by
  rw [linOf_basis, linOf_basis]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, cT, Matrix.map_apply, Matrix.transpose_apply, gramOf, Finset.mul_sum,
    Finset.sum_mul, AlgHom.coe_toRingHom, hσ, starRingEnd_apply]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  simp only [RingHom.id_apply]
  ring
end PI.UnitaryGroupMassFormula.UJClassMass
