-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cokernel_eq_sum_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:31:56.204296+00:00
-- url     : https://prove2.me/submissions/65735f36-f53a-4520-8106-3c1804537ad9

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialSmithMatrix
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PiTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cyclicQuotient_of_multiplicity_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_eq_of_intertwining
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_pi_eq_sum_diagonal
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


section
open scoped Polynomial
namespace QEC.Coding.AlgebraicGeometry
open Module
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [IsDomain R] [IsPrincipalIdealRing R]
@[simp]
private theorem smithCokernelEquiv_mk
    {n : ℕ} (source target : Basis (Fin n) R M)
    (a : Fin n → R) (f : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (x : M) :
    smithCokernelEquiv source target a f hdiag
        (Submodule.Quotient.mk x) =
      fun i => Ideal.Quotient.mk (Ideal.span ({a i} : Set R))
        (target.repr x i) :=
  rfl
private theorem smithCokernelEquiv_symm_single_mk
    {n : ℕ} (source target : Basis (Fin n) R M)
    (a : Fin n → R) (f : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (i : Fin n) (r : R) :
    (smithCokernelEquiv source target a f hdiag).symm
        (LinearMap.single R
          (fun j => R ⧸ Ideal.span ({a j} : Set R)) i
          (Ideal.Quotient.mk (Ideal.span ({a i} : Set R)) r)) =
      Submodule.Quotient.mk (r • target i) := by
  apply (smithCokernelEquiv source target a f hdiag).injective
  rw [LinearEquiv.apply_symm_apply]
  apply funext
  intro j
  rw [smithCokernelEquiv_mk]
  by_cases hij : i = j
  · subst j
    simp only [LinearMap.single_apply, Pi.single_eq_same, map_smul,
      Basis.repr_self, Finsupp.smul_single, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
  · simp [LinearMap.single_apply, Pi.single_apply, map_smul,
      Basis.repr_self, hij]
private theorem piDiagonalBlock_conj_smithCokernelEquiv
    {n : ℕ} (source target : Basis (Fin n) R M)
    (a : Fin n → R) (f g : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f) (i : Fin n) :
    piDiagonalBlock
        ((smithCokernelEquiv source target a f hdiag).conj
          (cokernelEndomorphism f g hcomm)) i =
      cyclicQuotientMul (a i)
        (LinearMap.toMatrix target target g i i) := by
  apply LinearMap.ext
  intro z
  induction z using Quotient.inductionOn' with
  | _ r =>
      change
        (smithCokernelEquiv source target a f hdiag
          (cokernelEndomorphism f g hcomm
            ((smithCokernelEquiv source target a f hdiag).symm
              (LinearMap.single R
                (fun j => R ⧸ Ideal.span ({a j} : Set R)) i
                (Ideal.Quotient.mk (Ideal.span ({a i} : Set R)) r))))) i =
          Ideal.Quotient.mk (Ideal.span ({a i} : Set R))
            (LinearMap.toMatrix target target g i i * r)
      rw [smithCokernelEquiv_symm_single_mk,
        cokernelEndomorphism_mk, smithCokernelEquiv_mk]
      rw [map_smul, map_smul]
      change Ideal.Quotient.mk (Ideal.span ({a i} : Set R))
          (r * target.repr (g (target i)) i) =
        Ideal.Quotient.mk (Ideal.span ({a i} : Set R))
          (LinearMap.toMatrix target target g i i * r)
      rw [LinearMap.toMatrix_apply]
      congr 1
      ring
variable {k : Type*} [Field k] [Finite k]
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Module
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
attribute [local instance] QEC.Coding.AlgebraicGeometry.cokernelModuleFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.cyclicQuotientModuleFinite
variable [IsDomain R] [IsPrincipalIdealRing R]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] [Module.Finite R M] {n : ℕ}
    (source target : Basis (Fin n) R M)
    (a : Fin n → R) (ha : ∀ i, a i ≠ 0)
    (f g : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (q : R) (hq : Irreducible q) [hmax : (Ideal.span {q}).IsMaximal]
    (depth : ℕ) (hdepth : ∀ i, multiplicity q (a i) ≤ depth) :
    primaryTorsionTrace (Ideal.span {q})
        (cokernelEndomorphism f g hcomm) depth =
      ∑ i, (multiplicity q (a i) : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q})
          (LinearMap.toMatrix target target g i i) := by
  let E := smithCokernelEquiv source target a f hdiag
  let G := E.conj (cokernelEndomorphism f g hcomm)
  have hintertwines : (E : (M ⧸ LinearMap.range f) →ₗ[R]
      ∀ i, R ⧸ Ideal.span ({a i} : Set R)).comp
        (cokernelEndomorphism f g hcomm) =
      G.comp (E : (M ⧸ LinearMap.range f) →ₗ[R]
        ∀ i, R ⧸ Ideal.span ({a i} : Set R)) := by
    apply LinearMap.ext
    intro x
    simp only [G, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  calc
    primaryTorsionTrace (Ideal.span {q})
        (cokernelEndomorphism f g hcomm) depth =
      primaryTorsionTrace (Ideal.span {q}) G depth :=
        primaryTorsionTrace_eq_of_intertwining
          (Ideal.span {q}) E (cokernelEndomorphism f g hcomm)
            G hintertwines depth
    _ = ∑ i, primaryTorsionTrace (Ideal.span {q})
        (piDiagonalBlock G i) depth :=
      primaryTorsionTrace_pi_eq_sum_diagonal (Ideal.span {q}) G depth
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [piDiagonalBlock_conj_smithCokernelEquiv
        source target a f g hdiag hcomm i]
      exact primaryTorsionTrace_cyclicQuotient_of_multiplicity_le
        q (a i) (LinearMap.toMatrix target target g i i)
          hq (ha i) depth (hdepth i)
end QEC.Coding.AlgebraicGeometry
