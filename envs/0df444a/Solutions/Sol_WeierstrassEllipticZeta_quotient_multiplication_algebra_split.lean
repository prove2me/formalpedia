-- Prove2me | solution 1 for WeierstrassEllipticZeta.quotient_multiplication_algebra_split
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T01:21:50.604868+00:00
-- url     : https://prove2.me/submissions/57094fa9-cf20-478c-a02f-5c67e4f0208f

import Theorems.Thm_WeierstrassEllipticZeta_comaximal_residual_decomposition
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Tactic.Ring

noncomputable section


theorem solution
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (I : Ideal A) (d : ℕ) (β : Module.Basis (Fin d) ℂ (A ⧸ I))
    (ρ : A →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hρ : ∀ p : A, ρ p = Algebra.leftMulMatrix β (Ideal.Quotient.mk I p))
    (hstable : ∀ p : A,
      LinearMap.range ((ρ p) ^ (2 * d)).mulVecLin =
        LinearMap.range ((ρ p) ^ d).mulVecLin) :
    ∀ p : A,
      let J := I ⊔ Ideal.span {p ^ d}
      let R := I.colon {p ^ d}
      J ⊔ R = ⊤ ∧ J ⊓ R = I ∧ J * R = I ∧
      Nonempty ((A ⧸ I) ≃ₐ[ℂ] (A ⧸ J) × (A ⧸ R)) ∧
      (Ideal.Quotient.mk J p) ^ d = 0 ∧ IsUnit (Ideal.Quotient.mk R p) ∧
      ∃ e : A,
        e ∈ J ∧ 1 - e ∈ R ∧ e * e - e ∈ I ∧
        J = I ⊔ Ideal.span {e} ∧ R = I ⊔ Ideal.span {1 - e} := by
  classical
  intro p
  let J := I ⊔ Ideal.span {p ^ d}
  let R := I.colon {p ^ d}
  have haction (n : ℕ) (a : A) :
      ((ρ p) ^ n).mulVec (β.equivFun (Ideal.Quotient.mk I a)) =
        β.equivFun (Ideal.Quotient.mk I (p ^ n * a)) := by
    rw [← map_pow, hρ]
    simp only [Module.Basis.equivFun_apply, Algebra.leftMulMatrix_mulVec_repr, map_mul]
  have hm : β.equivFun (Ideal.Quotient.mk I (p ^ d)) ∈
      LinearMap.range ((ρ p) ^ (2 * d)).mulVecLin := by
    rw [hstable p]
    refine ⟨β.equivFun (Ideal.Quotient.mk I 1), ?_⟩
    simpa only [Matrix.mulVecLin_apply, mul_one] using haction d 1
  obtain ⟨v, hv⟩ := hm
  obtain ⟨b, hb⟩ := (Ideal.Quotient.mk_surjective (I := I)) (β.equivFun.symm v)
  have hvb : β.equivFun (Ideal.Quotient.mk I b) = v := by
    rw [hb]
    exact β.equivFun.apply_symm_apply v
  rw [← hvb, Matrix.mulVecLin_apply, haction] at hv
  have hrel : p ^ d - p ^ (2 * d) * b ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    exact sub_eq_zero.mpr (β.equivFun.injective hv).symm
  have hpJ : p ^ d ∈ J :=
    (show Ideal.span {p ^ d} ≤ J from le_sup_right) (Ideal.subset_span (by simp))
  have heJ : p ^ d * b ∈ J := J.mul_mem_right b hpJ
  have heR : 1 - p ^ d * b ∈ R := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    convert hrel using 1
    ring
  have htop : J ⊔ R = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    exact Submodule.mem_sup.mpr ⟨p ^ d * b, heJ, 1 - p ^ d * b, heR, by ring⟩
  have hcolon : I.colon (J : Set A) = R := by
    ext x
    constructor
    · intro hx
      exact Submodule.mem_colon_singleton.mpr
        (Submodule.mem_colon.mp hx (p ^ d) hpJ)
    · intro hx
      apply Submodule.mem_colon.mpr
      intro y hy
      obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hc
      have hxp : x * p ^ d ∈ I := Submodule.mem_colon_singleton.mp hx
      simpa only [smul_eq_mul, mul_add, mul_assoc] using
        I.add_mem (I.mul_mem_left x ha) (I.mul_mem_right z hxp)
  have hsplit := WeierstrassEllipticZeta.comaximal_residual_decomposition A I J le_sup_left
  rw [hcolon] at hsplit
  obtain ⟨hinf, hmul, hE, he⟩ := hsplit htop
  have hunitpow : IsUnit ((Ideal.Quotient.mk R p) ^ d) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk R b, ?_⟩
    have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr heR
    rw [map_sub, map_one] at hzero
    simpa only [map_mul, map_pow] using (sub_eq_zero.mp hzero).symm
  have hunit : IsUnit (Ideal.Quotient.mk R p) := by
    by_cases hd : d = 0
    · have h10 : (1 : A ⧸ I) = 0 := β.equivFun.injective (by
        ext i
        exact Fin.elim0 (hd ▸ i))
      have hItop : I = ⊤ := Ideal.Quotient.zero_eq_one_iff.mp h10.symm
      have hRtop : R = ⊤ := top_unique (hItop ▸ Ideal.le_colon)
      have : Subsingleton (A ⧸ R) := Ideal.Quotient.subsingleton_iff.mpr hRtop
      exact isUnit_of_subsingleton _
    · exact (isUnit_pow_iff hd).mp hunitpow
  refine ⟨htop, hinf, hmul, hE, ?_, hunit, he⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact hpJ

