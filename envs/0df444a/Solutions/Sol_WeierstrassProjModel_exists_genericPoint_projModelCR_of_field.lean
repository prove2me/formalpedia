-- Prove2me | solution 1 for WeierstrassProjModel.exists_genericPoint_projModelCR_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6828a94c-8a73-5a6d-9a14-c2fe74ef4b73

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_ProjectiveWeierstrassPolynomialPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_genericPoint_projModelCR_of_field

set_option autoImplicit false
set_option Elab.async false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal ProjModelRingCR projModelGradingCR"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

section FieldCase

variable {K : Type u} [Field K] (V : WeierstrassCurve.Projective K)

private theorem ha3i_mk_X_mem_one (i : Fin 3) :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X i : MvPolynomial (Fin 3) K)
      ∈ projModelGradingCR V 1 :=
  mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X K i))

private scoped instance ha3i_isDomain_projModelRingCR : IsDomain (ProjModelRingCR V) := by
  show IsDomain (MvPolynomial (Fin 3) K ⧸ (projModelHomogeneousIdealCR V).toIdeal)
  rw [projModelHomogeneousIdealCR_toIdeal]
  exact isDomain_quotient_span_polynomial V

private theorem ha3i_X1_not_mem_span :
    (X 1 : MvPolynomial (Fin 3) K) ∉ (projModelHomogeneousIdealCR V).toIdeal := by
  rw [projModelHomogeneousIdealCR_toIdeal, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have h0 : eval ![(0 : K), 1, 0] V.polynomial = 0 :=
    WeierstrassCurve.Projective.equation_zero (W' := V)
  have heval := congrArg (eval ![(0 : K), 1, 0]) hc
  rw [map_mul, h0, zero_mul, eval_X] at heval
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at heval
  exact one_ne_zero heval

private theorem ha3i_mk_X1_ne_zero :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
      (X 1 : MvPolynomial (Fin 3) K) ≠ 0 := by
  intro h
  exact ha3i_X1_not_mem_span V (Ideal.Quotient.eq_zero_iff_mem.mp h)

private def ha3i_genericPoint : Proj (projModelGradingCR V) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]
    exact Ideal.isPrime_bot
  not_irrelevant_le := fun hle => by
    have hmem : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 1 : MvPolynomial (Fin 3) K)
          ∈ (⊥ : HomogeneousIdeal (projModelGradingCR V)).toIdeal :=
      hle (HomogeneousIdeal.mem_irrelevant_of_mem (𝒜 := projModelGradingCR V) one_pos
        (ha3i_mk_X_mem_one V 1))
    exact ha3i_mk_X1_ne_zero V (by simp at hmem; exact hmem)

private theorem ha3i_closure_genericPoint_eq_univ :
    closure ({ha3i_genericPoint V} : Set (Proj (projModelGradingCR V))) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  exact (ProjectiveSpectrum.le_iff_mem_closure (𝒜 := projModelGradingCR V)
      (ha3i_genericPoint V) y).mp
    ((ProjectiveSpectrum.as_ideal_le_as_ideal (𝒜 := projModelGradingCR V)
        (ha3i_genericPoint V) y).mp bot_le)

end FieldCase

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_genericPoint_projModelCR_of_field.WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem solution
    {K : Type u} [Field K] (V : WeierstrassCurve.Projective K) :
    ∃ η : AlgebraicGeometry.Proj (WeierstrassProjModel.projModelGradingCR V),
      η.asHomogeneousIdeal = ⊥ ∧
      closure ({η} : Set (AlgebraicGeometry.Proj (WeierstrassProjModel.projModelGradingCR V)))
        = Set.univ :=
  ⟨WeierstrassProjModel.ha3i_genericPoint V, rfl,
    WeierstrassProjModel.ha3i_closure_genericPoint_eq_univ V⟩

end
end S_WeierstrassProjModel_exists_genericPoint_projModelCR_of_field
end P2MW
export P2MW.S_WeierstrassProjModel_exists_genericPoint_projModelCR_of_field (solution)
