-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue.directFactorPlace_order_semilocalMultiplier_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:43:10.629064+00:00
-- url     : https://prove2.me/submissions/7c72bc39-775b-4226-98d3-555e82114452

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalMultiplier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_order_of_integral_eq_multiplicity


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue._p2m_local_instance_af27c6fddd_36
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue._p2m_local_instance_af27c6fddd_38
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue._p2m_local_instance_af27c6fddd_48
open DirectIntegralDifferentialResidue DirectFactorTraceResidue
namespace QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t : B k F) (ht : t ≠ 0)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J) :
    GlobalPlace.order
        (AffinePlace.globalPlace k F (directFactorPlace k F p P))
        (algebraMap (B k F) F t) = 1 := by
  have hP_ne : (P : Ideal (B k F)) ≠ 0 :=
    Ideal.Factors.ne_bot p.asIdeal P
  have hP_prime : Prime (P : Ideal (B k F)) :=
    Ideal.prime_of_isPrime hP_ne (Ideal.Factors.isPrime p.asIdeal P)
  have hmap : Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≤
      (P : Ideal (B k F)) := by
    exact Ideal.le_of_dvd
      (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2))
  have hPJ : IsCoprime (P : Ideal (B k F)) J := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup_right hmap J
  have hP_not_dvd_J : ¬(P : Ideal (B k F)) ∣ J := by
    rw [Ideal.dvd_iff_le]
    intro hJ_le
    have hP_top : (P : Ideal (B k F)) = ⊤ := by
      calc
        (P : Ideal (B k F)) = (P : Ideal (B k F)) ⊔ J :=
          (sup_eq_left.mpr hJ_le).symm
        _ = ⊤ := hPJ.sup_eq
    exact (Ideal.Factors.isPrime p.asIdeal P).ne_top hP_top
  have hspan_ne : Ideal.span ({t} : Set (B k F)) ≠ 0 :=
    Submodule.span_singleton_eq_bot.mp.mt ht
  have hprod_ne : (P : Ideal (B k F)) * J ≠ 0 := by
    rw [← hspan]
    exact hspan_ne
  have hfinite : FiniteMultiplicity (P : Ideal (B k F))
      ((P : Ideal (B k F)) * J) :=
    FiniteMultiplicity.of_prime_left hP_prime hprod_ne
  have hmultiplicity :
      multiplicity (P : Ideal (B k F))
          (Ideal.span ({t} : Set (B k F))) = 1 := by
    calc
      multiplicity (P : Ideal (B k F))
          (Ideal.span ({t} : Set (B k F))) =
          multiplicity (P : Ideal (B k F))
            ((P : Ideal (B k F)) * J) := by rw [hspan]
      _ = multiplicity (P : Ideal (B k F)) (P : Ideal (B k F)) +
          multiplicity (P : Ideal (B k F)) J :=
        multiplicity_mul hP_prime hfinite
      _ = 1 := by
        rw [multiplicity_self, multiplicity_eq_zero.mpr hP_not_dvd_J, add_zero]
  rw [AffinePlace.globalPlace_order_of_integral_eq_multiplicity k F
    (directFactorPlace k F p P) ht, directFactorPlace_asIdeal]
  exact_mod_cast hmultiplicity
end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue
