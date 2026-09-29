-- Prove2me | solution 1 for WeierstrassProjModel.kw_lrSixU_addZ_ychartR_partialEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8fc3734c-2d84-534d-a551-13c38462f70d

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Theorems.Thm_WeierstrassProjModel_kw_lrAdd_Z_aeval_right_infty
import Theorems.Thm_WeierstrassProjModel_kwYChartEval_gen_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_lrSixU_addZ_ychartR_partialEval

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSimpArgs false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem solution (i : Fin 3) :
    ∃ (φ : ((𝒜 i) ⊗[R] (𝒜 1)) →+* (𝒜 i)),
      φ (kw_lrSixU W i 1 (.inl 2)) = (kw_lrChart_gen W i 2) ^ 2 := by

  let ψY : (𝒜 1) →ₐ[R] (𝒜 i) :=
    { toRingHom := (algebraMap R (𝒜 i)).comp (kwYChartEval R W)
      commutes' := fun r => by
        show (algebraMap R (𝒜 i)) (kwYChartEval R W (algebraMap R (𝒜 1) r)) = algebraMap R (𝒜 i) r
        congr 1
        exact RingHom.congr_fun (kwYChartEval_section R W) r }

  refine ⟨(Algebra.TensorProduct.productMap (AlgHom.id R (𝒜 i)) ψY).toRingHom, ?_⟩

  have hkey : ∀ p, (Algebra.TensorProduct.productMap (AlgHom.id R (𝒜 i)) ψY)
        (kw_lrChart_ev W i 1 p)
      = MvPolynomial.aeval (R := R)
          (Sum.elim (kw_lrChart_gen W i) (fun m => ψY (kw_lrChart_gen W 1 m))) p := by
    suffices h : (Algebra.TensorProduct.productMap (AlgHom.id R (𝒜 i)) ψY).comp
          (kw_lrChart_ev W i 1)
        = MvPolynomial.aeval (R := R)
            (Sum.elim (kw_lrChart_gen W i) (fun m => ψY (kw_lrChart_gen W 1 m)))
      from DFunLike.congr_fun h
    refine MvPolynomial.algHom_ext fun s => ?_
    rcases s with m | m
    · simp only [AlgHom.comp_apply, kw_lrChart_ev, aeval_X, Sum.elim_inl,
        kw_lrChart_inL, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.productMap_left_apply, AlgHom.id_apply]
    · simp only [AlgHom.comp_apply, kw_lrChart_ev, aeval_X, Sum.elim_inr,
        kw_lrChart_inR, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.productMap_right_apply]

  have hψY : ∀ m, ψY (kw_lrChart_gen W 1 m) = ![(0:𝒜 i), 1, 0] m := by
    intro m
    show (algebraMap R (𝒜 i)) (kwYChartEval R W (kw_lrChart_gen W 1 m)) = _
    rw [kwYChartEval_gen_eq R W m]
    fin_cases m
    · exact map_zero _
    · exact map_one _
    · exact map_zero _

  show (Algebra.TensorProduct.productMap (AlgHom.id R (𝒜 i)) ψY) (kw_lrChart_u W i 1 2) = _
  rw [kw_lrChart_u, kw_lrChart_ev', Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  refine (hkey (kw_lrAdd_vec W 2)).trans ?_

  have heq : (Sum.elim (kw_lrChart_gen W i) (fun m => ψY (kw_lrChart_gen W 1 m)))
      = Sum.elim (kw_lrChart_gen W i) ![(0:𝒜 i), 1, 0] := by
    funext s; rcases s with m | m
    · rfl
    · exact hψY m
  rw [heq]
  exact kw_lrAdd_Z_aeval_right_infty W (kw_lrChart_gen W i)

end

end S_WeierstrassProjModel_kw_lrSixU_addZ_ychartR_partialEval
end P2MW
export P2MW.S_WeierstrassProjModel_kw_lrSixU_addZ_ychartR_partialEval (solution)
