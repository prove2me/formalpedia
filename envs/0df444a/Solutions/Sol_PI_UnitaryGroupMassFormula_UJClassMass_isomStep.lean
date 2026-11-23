-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.isomStep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:40.369044+00:00
-- url     : https://prove2.me/submissions/714f2330-99e8-47a6-8e37-e1d0756d72e3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
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
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution : IsomStep := by
  unfold IsomStep
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hsymm hnd hlat hsig γ
  unfold iotaG isom
  set u := ratMat σ (gramOf h b) γ with hu
  have hU : Formalism.UG.cT (σ : E →+* E) (u : Matrix (Fin M) (Fin M) E) * gramOf h b *
      (u : Matrix (Fin M) (Fin M) E) = gramOf h b := (ratMat_spec σ (gramOf h b) γ).1
  have hG : ∀ k l, gramOf h b k l = h (b k) (b l) := fun k l => rfl
  have key : (h.comp (linOf b u : V →ₗ[E] V)).compl₂ (linOf b u : V →ₗ[E] V) = h := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, linOf_basis]
    rw [show h (b i) (b j) = gramOf h b i j from (hG i j).symm, ← hU]
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hG,
      AlgHom.coe_toRingHom, RingHom.coe_coe, hσ, Finset.sum_mul, Finset.mul_sum, map_sum,
      map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
      RingHom.id_apply]
    first
    | exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    | (rw [Finset.sum_comm]
       exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
  show ∀ x y, h (linOf b u x) (linOf b u y) = h x y
  intro x y
  conv_rhs => rw [← key]
  rfl
end PI.UnitaryGroupMassFormula.UJClassMass
