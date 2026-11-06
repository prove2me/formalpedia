-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints.complexPolynomialMaximal_exists_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:18.008575+00:00
-- url     : https://prove2.me/submissions/14baabde-e8c0-4df9-9c7a-bee1480c7cb0

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_PolynomialMaximalPoints

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
theorem _root_.solution (M : Ideal (Polynomial ℂ))
    [M.IsMaximal] : ∃ a : ℂ, ∀ p : Polynomial ℂ, p ∈ M ↔ p.eval a = 0 := by
  let φ : ℂ →+* Polynomial ℂ ⧸ M := (Ideal.Quotient.mk M).comp Polynomial.C
  have hφ : φ.IsIntegral := Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing M
  obtain ⟨a, ha⟩ := (IsAlgClosed.ringHom_bijective_of_isIntegral φ hφ).2
    (Ideal.Quotient.mk M Polynomial.X)
  have hx : Polynomial.X - Polynomial.C a ∈ M := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr ha.symm
  let L : Ideal (Polynomial ℂ) := Ideal.span {Polynomial.X - Polynomial.C a}
  have hL : L.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible
    (Polynomial.irreducible_X_sub_C a)
  have hLM : L ≤ M := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have heq : L = M := hL.eq_of_le (Ideal.IsMaximal.ne_top inferInstance) hLM
  refine ⟨a, fun p => ?_⟩
  rw [←heq,Ideal.mem_span_singleton,Polynomial.dvd_iff_isRoot]
  rfl
end QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
