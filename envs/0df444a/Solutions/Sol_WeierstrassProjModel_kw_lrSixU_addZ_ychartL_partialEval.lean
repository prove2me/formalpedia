-- Prove2me | solution 1 for WeierstrassProjModel.kw_lrSixU_addZ_ychartL_partialEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0a0f077d-6c7a-5acf-8d93-09265d6cf749

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Theorems.Thm_WeierstrassProjModel_kw_lrAdd_Z_aeval_left_infty
import Theorems.Thm_WeierstrassProjModel_kwYChartEval_gen_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_lrSixU_addZ_ychartL_partialEval

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

theorem solution (j : Fin 3) :
    ∃ (φ : ((𝒜 1) ⊗[R] (𝒜 j)) →+* (𝒜 j)),
      φ (kw_lrSixU W 1 j (.inl 2)) = -(kw_lrChart_gen W j 2) ^ 2 := by

  let ψY : (𝒜 1) →ₐ[R] (𝒜 j) :=
    { toRingHom := (algebraMap R (𝒜 j)).comp (kwYChartEval R W)
      commutes' := fun r => by
        show (algebraMap R (𝒜 j)) (kwYChartEval R W (algebraMap R (𝒜 1) r)) = algebraMap R (𝒜 j) r
        congr 1
        exact RingHom.congr_fun (kwYChartEval_section R W) r }

  refine ⟨(Algebra.TensorProduct.productMap ψY (AlgHom.id R (𝒜 j))).toRingHom, ?_⟩

  have hkey : ∀ p, (Algebra.TensorProduct.productMap ψY (AlgHom.id R (𝒜 j)))
        (kw_lrChart_ev W 1 j p)
      = MvPolynomial.aeval (R := R)
          (Sum.elim (fun m => ψY (kw_lrChart_gen W 1 m)) (kw_lrChart_gen W j)) p := by
    suffices h : (Algebra.TensorProduct.productMap ψY (AlgHom.id R (𝒜 j))).comp
          (kw_lrChart_ev W 1 j)
        = MvPolynomial.aeval (R := R)
            (Sum.elim (fun m => ψY (kw_lrChart_gen W 1 m)) (kw_lrChart_gen W j))
      from DFunLike.congr_fun h
    refine MvPolynomial.algHom_ext fun s => ?_
    rcases s with m | m
    · simp only [AlgHom.comp_apply, kw_lrChart_ev, aeval_X, Sum.elim_inl,
        kw_lrChart_inL, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.productMap_left_apply]
    · simp only [AlgHom.comp_apply, kw_lrChart_ev, aeval_X, Sum.elim_inr,
        kw_lrChart_inR, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.productMap_right_apply, AlgHom.id_apply]

  have hψY : ∀ m, ψY (kw_lrChart_gen W 1 m) = ![(0:𝒜 j), 1, 0] m := by
    intro m
    show (algebraMap R (𝒜 j)) (kwYChartEval R W (kw_lrChart_gen W 1 m)) = _
    rw [kwYChartEval_gen_eq R W m]
    fin_cases m
    · exact map_zero _
    · exact map_one _
    · exact map_zero _

  show (Algebra.TensorProduct.productMap ψY (AlgHom.id R (𝒜 j))) (kw_lrChart_u W 1 j 2) = _
  rw [kw_lrChart_u, kw_lrChart_ev', Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  refine (hkey (kw_lrAdd_vec W 2)).trans ?_
  have heq : (Sum.elim (fun m => ψY (kw_lrChart_gen W 1 m)) (kw_lrChart_gen W j))
      = Sum.elim ![(0:𝒜 j), 1, 0] (kw_lrChart_gen W j) := by
    funext s; rcases s with m | m
    · exact hψY m
    · rfl
  rw [heq]
  exact kw_lrAdd_Z_aeval_left_infty W (kw_lrChart_gen W j)

end

end S_WeierstrassProjModel_kw_lrSixU_addZ_ychartL_partialEval
end P2MW
export P2MW.S_WeierstrassProjModel_kw_lrSixU_addZ_ychartL_partialEval (solution)
