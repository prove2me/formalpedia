-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier.exists_directFactorSemilocalMultiplier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:37:17.501291+00:00
-- url     : https://prove2.me/submissions/30bbb310-0794-4522-b5a9-a04244e66d12

import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalMultiplier

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier._p2m_local_instance_e0603924bb_41
namespace QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    ∃ t : B k F, t ≠ 0 ∧ ∃ J : Ideal (B k F),
      Ideal.span ({t} : Set (B k F)) = (P : Ideal (B k F)) * J ∧
        IsCoprime
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J := by
  classical
  let M : Ideal (B k F) :=
    Ideal.map (algebraMap (R k) (B k F)) p.asIdeal
  have hP_ne : (P : Ideal (B k F)) ≠ 0 :=
    Ideal.Factors.ne_bot p.asIdeal P
  have hM_ne : M ≠ 0 := by
    exact Ideal.map_ne_bot_of_ne_bot p.ne_bot
  have hPM_le : (P : Ideal (B k F)) * M ≤ (P : Ideal (B k F)) :=
    Ideal.mul_le_left
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_sup_span_eq hPM_le
    (mul_ne_zero hP_ne hM_ne)
  have hspan_le : Ideal.span ({t} : Set (B k F)) ≤
      (P : Ideal (B k F)) :=
    le_sup_right.trans_eq ht
  obtain ⟨J, hspan⟩ := Ideal.dvd_iff_le.mpr hspan_le
  have hsup : M ⊔ J = ⊤ := by
    apply mul_left_cancel₀ hP_ne
    rw [Ideal.mul_sup, ← hspan, ht, Ideal.mul_top]
  have hM_le : M ≤ (P : Ideal (B k F)) := by
    exact Ideal.le_of_dvd
      (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2))
  have hM_ne_top : M ≠ ⊤ := by
    intro hM
    exact (Ideal.Factors.isPrime p.asIdeal P).ne_top
      (top_unique (hM ▸ hM_le))
  have ht_ne : t ≠ 0 := by
    intro ht_zero
    have hPM_eq : (P : Ideal (B k F)) * M = (P : Ideal (B k F)) := by
      simpa only [ht_zero, Set.singleton_zero, Ideal.span_zero, sup_bot_eq] using ht
    have hM_top : M = ⊤ := by
      apply mul_left_cancel₀ hP_ne
      simpa only [Ideal.mul_top] using hPM_eq
    exact hM_ne_top hM_top
  exact ⟨t, ht_ne, J, hspan, Ideal.isCoprime_iff_sup_eq.mpr hsup⟩
end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier
