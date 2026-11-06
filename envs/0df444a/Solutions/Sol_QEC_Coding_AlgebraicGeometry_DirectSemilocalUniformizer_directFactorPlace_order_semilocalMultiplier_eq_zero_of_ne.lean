-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer.directFactorPlace_order_semilocalMultiplier_eq_zero_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:43:55.351536+00:00
-- url     : https://prove2.me/submissions/69064593-95e8-4838-a281-254b5e4d5fac

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_order_of_integral_eq_multiplicity


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
open DirectIntegralDifferentialResidue
open DirectFactorSemilocalLogarithmicResidue
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer._p2m_local_instance_46770e045f_37
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer._p2m_local_instance_46770e045f_42
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P Q : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (hQP : Q ≠ P)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t : B k F) (ht : t ≠ 0)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J) :
    GlobalPlace.order
        (AffinePlace.globalPlace k F (directFactorPlace k F p Q))
        (algebraMap (B k F) F t) = 0 := by
  let M : Ideal (B k F) :=
    Ideal.map (algebraMap (R k) (B k F)) p.asIdeal
  have hP_ne : (P : Ideal (B k F)) ≠ 0 :=
    Ideal.Factors.ne_bot p.asIdeal P
  have hQ_ne : (Q : Ideal (B k F)) ≠ 0 :=
    Ideal.Factors.ne_bot p.asIdeal Q
  have hQ_prime : Prime (Q : Ideal (B k F)) :=
    Ideal.prime_of_isPrime hQ_ne (Ideal.Factors.isPrime p.asIdeal Q)
  have hP_max : (P : Ideal (B k F)).IsMaximal :=
    (Ideal.Factors.isPrime p.asIdeal P).isMaximal hP_ne
  have hQ_ne_top : (Q : Ideal (B k F)) ≠ ⊤ :=
    (Ideal.Factors.isPrime p.asIdeal Q).ne_top
  have hQ_not_dvd_P : ¬(Q : Ideal (B k F)) ∣ (P : Ideal (B k F)) := by
    rw [Ideal.dvd_iff_le]
    intro hP_le_Q
    have hPQ : (P : Ideal (B k F)) = (Q : Ideal (B k F)) :=
      hP_max.eq_of_le hQ_ne_top hP_le_Q
    apply hQP
    exact Subtype.ext hPQ.symm
  have hM_le_Q : M ≤ (Q : Ideal (B k F)) := by
    exact Ideal.le_of_dvd
      (dvd_of_mem_factors (Multiset.mem_toFinset.mp Q.2))
  have hQJ : IsCoprime (Q : Ideal (B k F)) J := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup_right hM_le_Q J
  have hQ_not_dvd_J : ¬(Q : Ideal (B k F)) ∣ J := by
    rw [Ideal.dvd_iff_le]
    intro hJ_le_Q
    have hQ_top : (Q : Ideal (B k F)) = ⊤ := by
      calc
        (Q : Ideal (B k F)) = (Q : Ideal (B k F)) ⊔ J :=
          (sup_eq_left.mpr hJ_le_Q).symm
        _ = ⊤ := hQJ.sup_eq
    exact hQ_ne_top hQ_top
  have hspan_ne : Ideal.span ({t} : Set (B k F)) ≠ 0 :=
    Submodule.span_singleton_eq_bot.mp.mt ht
  have hprod_ne : (P : Ideal (B k F)) * J ≠ 0 := by
    rw [← hspan]
    exact hspan_ne
  have hfinite : FiniteMultiplicity (Q : Ideal (B k F))
      ((P : Ideal (B k F)) * J) :=
    FiniteMultiplicity.of_prime_left hQ_prime hprod_ne
  have hmultiplicity :
      multiplicity (Q : Ideal (B k F))
          (Ideal.span ({t} : Set (B k F))) = 0 := by
    calc
      multiplicity (Q : Ideal (B k F))
          (Ideal.span ({t} : Set (B k F))) =
          multiplicity (Q : Ideal (B k F))
            ((P : Ideal (B k F)) * J) := by rw [hspan]
      _ = multiplicity (Q : Ideal (B k F)) (P : Ideal (B k F)) +
          multiplicity (Q : Ideal (B k F)) J :=
        multiplicity_mul hQ_prime hfinite
      _ = 0 := by
        rw [multiplicity_eq_zero.mpr hQ_not_dvd_P,
          multiplicity_eq_zero.mpr hQ_not_dvd_J, zero_add]
  rw [AffinePlace.globalPlace_order_of_integral_eq_multiplicity k F
    (directFactorPlace k F p Q) ht, directFactorPlace_asIdeal]
  exact_mod_cast hmultiplicity
end QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer
