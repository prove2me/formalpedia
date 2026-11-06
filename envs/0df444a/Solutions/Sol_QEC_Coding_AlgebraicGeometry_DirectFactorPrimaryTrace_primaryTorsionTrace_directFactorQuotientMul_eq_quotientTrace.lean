-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace.primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:17:15.601879+00:00
-- url     : https://prove2.me/submissions/00955199-c953-4dce-b923-673ba7ab4cb3

import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_AnnihilatedTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorPrimaryTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_restrictScalars_eq_trace_of_annihilated

section
namespace QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
private theorem map_basePrime_le_directFactor
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≤
      (P : Ideal (B k F)) := by
  exact Ideal.le_of_dvd
    (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2))
private theorem directFactorQuotient_annihilated
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    Module.IsTorsionBySet (R k) (B k F ⧸ (P : Ideal (B k F)))
      p.asIdeal := by
  intro x r
  have hrP : algebraMap (R k) (B k F) (r : R k) ∈
      (P : Ideal (B k F)) :=
    map_basePrime_le_directFactor k F p P
      (Ideal.mem_map_of_mem (algebraMap (R k) (B k F)) r.property)
  calc
    (r : R k) • x = algebraMap (R k) (B k F) (r : R k) • x :=
      (IsScalarTower.algebraMap_smul (B k F) (r : R k) x).symm
    _ = 0 := by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk (P : Ideal (B k F))
        (algebraMap (R k) (B k F) (r : R k) * y) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        ((P : Ideal (B k F)).mul_mem_right y hrP)
end QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace._p2m_local_instance_a98a1bf31e_44
namespace QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    primaryTorsionTrace p.asIdeal
        (Algebra.lmul (R k) (B k F ⧸ (P : Ideal (B k F)))
          (Ideal.Quotient.mk (P : Ideal (B k F)) b)) depth =
      Algebra.trace (R k ⧸ p.asIdeal)
        (B k F ⧸ (P : Ideal (B k F)))
        (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
  classical
  let fP := Algebra.lmul (R k ⧸ p.asIdeal)
    (B k F ⧸ (P : Ideal (B k F)))
    (Ideal.Quotient.mk (P : Ideal (B k F)) b)
  have hrestrict : fP.restrictScalars (R k) =
      Algebra.lmul (R k) (B k F ⧸ (P : Ideal (B k F)))
        (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
    apply LinearMap.ext
    intro x
    rfl
  calc
    primaryTorsionTrace p.asIdeal
        (Algebra.lmul (R k) (B k F ⧸ (P : Ideal (B k F)))
          (Ideal.Quotient.mk (P : Ideal (B k F)) b)) depth =
      primaryTorsionTrace p.asIdeal
        (fP.restrictScalars (R k)) depth := by rw [hrestrict]
    _ = LinearMap.trace (R k ⧸ p.asIdeal)
        (B k F ⧸ (P : Ideal (B k F))) fP :=
      primaryTorsionTrace_restrictScalars_eq_trace_of_annihilated
        p.asIdeal (directFactorQuotient_annihilated k F p P)
          fP depth hdepth
    _ = _ := (Algebra.trace_apply (R k ⧸ p.asIdeal)
      (Ideal.Quotient.mk (P : Ideal (B k F)) b)).symm
end QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace
