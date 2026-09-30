-- Prove2me | solution 1 for WeierstrassEllipticZeta.comaximal_residual_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T14:13:39.760155+00:00
-- url     : https://prove2.me/submissions/b1133db1-4048-49c9-8519-4dece67f4ef1

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

noncomputable section


theorem solution
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (I J : Ideal A) (hIJ : I ≤ J) :
    let R := I.colon (J : Set A)
    J ⊔ R = ⊤ →
      J ⊓ R = I ∧ J * R = I ∧
      Nonempty ((A ⧸ I) ≃ₐ[ℂ] (A ⧸ J) × (A ⧸ R)) ∧
      ∃ p : A,
        p ∈ J ∧ 1 - p ∈ R ∧ p * p - p ∈ I ∧
        J = I ⊔ Ideal.span {p} ∧ R = I ⊔ Ideal.span {1 - p} := by
  classical
  dsimp only
  let R := I.colon (J : Set A)
  intro htop
  have hcop : IsCoprime J R := Ideal.isCoprime_iff_sup_eq.mpr htop
  have hprod : J * R ≤ I := by
    apply Ideal.mul_le.mpr
    intro p hp q hq
    simpa only [smul_eq_mul, mul_comm] using (Submodule.mem_colon.mp hq p hp)
  have hinf : J ⊓ R = I := le_antisymm
    ((Ideal.mul_eq_inf_of_isCoprime hcop).symm.trans_le hprod)
    (le_inf hIJ Ideal.le_colon)
  have hmul : J * R = I := (Ideal.mul_eq_inf_of_isCoprime hcop).trans hinf
  let E : (A ⧸ J ⊓ R) ≃ₐ[ℂ] (A ⧸ J) × (A ⧸ R) :=
    { Ideal.quotientInfEquivQuotientProd J R hcop with
      commutes' := fun z => Prod.ext
        (Ideal.quotientInfEquivQuotientProd_fst J R hcop (algebraMap ℂ (A ⧸ J ⊓ R) z))
        (Ideal.quotientInfEquivQuotientProd_snd J R hcop (algebraMap ℂ (A ⧸ J ⊓ R) z)) }
  have hone : (1 : A) ∈ J ⊔ R := by rw [htop]; trivial
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hone
  have h1p : 1 - p ∈ R := by
    rw [← hpq, add_sub_cancel_left]
    exact hq
  have hidem : p * p - p ∈ I := by
    have hm := hprod (Ideal.mul_mem_mul hp h1p)
    convert I.neg_mem hm using 1
    ring
  have hgenJ : J = I ⊔ Ideal.span {p} := by
    apply le_antisymm
    · intro x hx
      have hrest : x * (1 - p) ∈ I := hprod (Ideal.mul_mem_mul hx h1p)
      have hxp : x * p ∈ Ideal.span ({p} : Set A) :=
        Ideal.mul_mem_left _ x (Ideal.subset_span (by simp))
      exact Submodule.mem_sup.mpr ⟨x * (1 - p), hrest, x * p, hxp, by ring⟩
    · exact sup_le hIJ ((Ideal.span_singleton_le_iff_mem J).mpr hp)
  have hgenR : R = I ⊔ Ideal.span {1 - p} := by
    apply le_antisymm
    · intro x hx
      have hrest : x * p ∈ I := Submodule.mem_colon.mp hx p hp
      have hxp : x * (1 - p) ∈ Ideal.span ({1 - p} : Set A) :=
        Ideal.mul_mem_left _ x (Ideal.subset_span (by simp))
      exact Submodule.mem_sup.mpr ⟨x * p, hrest, x * (1 - p), hxp, by ring⟩
    · exact sup_le Ideal.le_colon ((Ideal.span_singleton_le_iff_mem R).mpr h1p)
  exact ⟨hinf, hmul, ⟨(Ideal.quotientEquivAlgOfEq ℂ hinf.symm).trans E⟩,
    p, hp, h1p, hidem, hgenJ, hgenR⟩

