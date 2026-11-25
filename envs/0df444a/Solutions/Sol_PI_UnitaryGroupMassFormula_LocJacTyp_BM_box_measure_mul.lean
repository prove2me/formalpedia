-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.BM.box_measure_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:53:09.428964+00:00
-- url     : https://prove2.me/submissions/c52356c1-d9db-45f6-bed1-9c6d3a13a101

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_Transport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiagonalOneJacobian
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_mulL_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_det_mulL
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_absV_prod
import Theorems.Thm_PI_NglqJacSplitW_diagonal_one_jacobian
import Theorems.Thm_PI_NglqJacSplitW_linModulusV_of
import Theorems.Thm_PI_NglqJacSplitW_linModulus_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_locallyCompact_Fv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_modF_Fv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_secondCountable_Fv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.BM
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp
open scoped TensorProduct ENNReal NNReal
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM
theorem _root_.solution : BoxMul (E := E) v := by
  classical
  intro ι _ μ _ y hy
  haveI := locallyCompact_Fv v
  haveI := secondCountable_Fv v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  let b := Module.finBasis (Fv F v) (Fv F v ⊗[F] E)
  let eR : (Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { b.equivFun with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eR.toHomeomorph.secondCountableTopology
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (ι → Fv F v ⊗[F] E) := Pi.borelSpace
  let e0 : (ι → Fv F v ⊗[F] E) ≃ₗ[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    (LinearEquiv.piCongrRight fun _ : ι => b.equivFun).trans
      (LinearEquiv.curry (Fv F v) (Fv F v) ι (Fin _)).symm
  let eV : (ι → Fv F v ⊗[F] E) ≃L[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  let u : ι → (Fv F v ⊗[F] E)ˣ := fun i => (hy i).unit
  let z : ι → Fv F v ⊗[F] E := fun i => ((u i)⁻¹ : (Fv F v ⊗[F] E)ˣ)
  let h : (ι → Fv F v ⊗[F] E) ≃ₜ (ι → Fv F v ⊗[F] E) :=
    { toFun := mulL v y
      invFun := mulL v z
      left_inv := fun c => by
        funext i
        simp only [mulL_apply, z, ← mul_assoc]
        rw [show ((u i)⁻¹ : (Fv F v ⊗[F] E)ˣ).1 * y i = 1 from (u i).inv_mul, one_mul]
      right_inv := fun c => by
        funext i
        simp only [mulL_apply, z, ← mul_assoc]
        rw [show y i * ((u i)⁻¹ : (Fv F v ⊗[F] E)ˣ).1 = 1 from (u i).mul_inv, one_mul]
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (mulL v y)
      continuous_invFun := IsModuleTopology.continuous_of_linearMap (mulL v z) }
  let Em := h.toMeasurableEquiv
  have hNz : ∀ i, Algebra.norm (Fv F v) (z i) * Algebra.norm (Fv F v) (y i) = 1 := fun i => by
    rw [← map_mul, show z i * y i = 1 from (u i).inv_mul, map_one]
  have hdet0 : (∏ i, Algebra.norm (Fv F v) (z i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => left_ne_zero_of_mul_eq_one (hNz i)
  have hLM := PI.NglqJacSplitW.linModulusV_of
    (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)
  set c := PI.NglqJacSplitW.modF (Fv F v) (∏ i, Algebra.norm (Fv F v) (z i)) with hc
  have hmap : μ.map Em = c • μ := by
    ext X hX
    rw [MeasurableEquiv.map_apply, Measure.smul_apply, smul_eq_mul]
    have hpre : Em ⁻¹' X = mulL v z '' X := by
      ext x
      constructor
      · intro hx
        exact ⟨h x, hx, h.left_inv x⟩
      · rintro ⟨w, hw, rfl⟩
        show h (h.symm w) ∈ X
        rw [h.apply_symm_apply]; exact hw
    rw [hpre, hLM (Fv F v) (ι → Fv F v ⊗[F] E) (ι × Fin _) ⟨eV⟩ (mulL v z)
      (by rw [det_mulL]; exact hdet0) μ inferInstance X hX, det_mulL]
  have hS : (Set.univ.pi fun i => {c | y i * c ∈ OEv (E := E) v}) = Em ⁻¹' Obox (E := E) v ι := by
    ext x
    simp [Obox, Em, h, mulL_apply]
  rw [hS, ← MeasurableEquiv.map_apply, hmap, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    hc, modF_Fv v _ hdet0, absV_prod, ENNReal.toReal_ofReal
      (Finset.prod_nonneg fun i _ => (absV_pos v (left_ne_zero_of_mul_eq_one (hNz i))).le),
    mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [eq_inv_of_mul_eq_one_left (hNz i), absV_inv]
end PI.UnitaryGroupMassFormula.LocJacTyp.BM
