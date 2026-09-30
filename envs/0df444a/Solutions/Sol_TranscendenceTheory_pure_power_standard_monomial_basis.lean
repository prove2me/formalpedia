-- Prove2me | solution 1 for TranscendenceTheory.pure_power_standard_monomial_basis
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T05:32:15.32411+00:00
-- url     : https://prove2.me/submissions/b7e8d595-11d1-4577-a26e-ad5dc46c2f8c

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic

noncomputable section

namespace TranscendenceTheory

open MvPolynomial
open scoped MonomialOrder

/-- A family with a different pure leading power for each variable satisfies
the leading-monomial criterion on every finite subfamily. -/
theorem pure_power_leading_divisibility
    {K σ : Type*} [Field K]
    (o : MonomialOrder σ) (d : σ → ℕ) (b : σ → MvPolynomial σ K)
    (hu : ∀ i, IsUnit (o.leadingCoeff (b i)))
    (hd : ∀ i, o.degree (b i) = Finsupp.single i (d i))
    (s : Finset σ) (f : MvPolynomial σ K)
    (hf : f ∈ Ideal.span (b '' (s : Set σ))) (hf0 : f ≠ 0) :
    ∃ i ∈ s, Finsupp.single i (d i) ≤ o.degree f := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
    simp only [Finset.coe_empty, Set.image_empty, Ideal.span_empty, Ideal.mem_bot] at hf
    exact (hf0 hf).elim
  | @insert i s hi ih =>
    rw [Finset.coe_insert, Set.image_insert_eq, Ideal.mem_span_insert] at hf
    obtain ⟨a, h, hh, hfh⟩ := hf
    obtain ⟨g, r, har, -, hr⟩ := o.div (fun j : s => hu j.val) a
    let c := Finsupp.linearCombination (MvPolynomial σ K) (fun j : s => b j.val) g
    have hc : c ∈ Ideal.span (b '' (s : Set σ)) := by
      dsimp [c]
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      apply Ideal.sum_mem
      intro j _
      apply Ideal.mul_mem_left
      exact Ideal.subset_span ⟨j.val, j.property, rfl⟩
    let h' := c * b i + h
    have hh' : h' ∈ Ideal.span (b '' (s : Set σ)) :=
      Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc) hh
    have hsum : f = h' + r * b i := by
      dsimp [h']
      rw [hfh, har]
      change (c + r) * b i + h = c * b i + h + r * b i
      ring
    have hbi : b i ≠ 0 := o.isUnit_leadingCoeff.mp (hu i)
    by_cases hr0 : r = 0
    · rw [hr0, zero_mul, add_zero] at hsum
      obtain ⟨j, hj, hjd⟩ := ih h' hh' (hsum ▸ hf0)
      exact ⟨j, Finset.mem_insert_of_mem hj, hsum ▸ hjd⟩
    have hmul : o.degree (r * b i) = o.degree r + Finsupp.single i (d i) := by
      rw [o.degree_mul hr0 hbi, hd i]
    have hid : Finsupp.single i (d i) ≤ o.degree (r * b i) := by
      rw [hmul, Finsupp.single_le_iff]
      simp
    by_cases hh0 : h' = 0
    · rw [hh0, zero_add] at hsum
      exact ⟨i, Finset.mem_insert_self _ _, hsum ▸ hid⟩
    obtain ⟨j, hj, hjd⟩ := ih h' hh' hh0
    have hji : j ≠ i := fun hji => hi (hji ▸ hj)
    have hne : o.degree h' ≠ o.degree (r * b i) := by
      intro heq
      have hrj := hr (o.degree r) (o.degree_mem_support hr0) ⟨j, hj⟩
      apply hrj
      rw [hd j, Finsupp.single_le_iff]
      rw [heq, hmul, Finsupp.single_le_iff] at hjd
      simpa [Finsupp.single_apply, hji, Ne.symm hji] using hjd
    have hne' : o.toSyn (o.degree h') ≠ o.toSyn (o.degree (r * b i)) :=
      fun heq => hne (o.toSyn.injective heq)
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have heq : o.degree f = o.degree (r * b i) := by
        rw [hsum, add_comm, o.degree_add_of_lt hlt]
      exact ⟨i, Finset.mem_insert_self _ _, heq ▸ hid⟩
    · have heq : o.degree f = o.degree h' := by
        rw [hsum, o.degree_add_of_lt hgt]
      exact ⟨j, Finset.mem_insert_of_mem hj, heq ▸ hjd⟩

theorem pure_power_reduced_mem_ideal_eq_zero
    {K σ : Type*} [Field K] [Fintype σ]
    (o : MonomialOrder σ) (d : σ → ℕ) (b : σ → MvPolynomial σ K)
    (hu : ∀ i, IsUnit (o.leadingCoeff (b i)))
    (hd : ∀ i, o.degree (b i) = Finsupp.single i (d i))
    (f : MvPolynomial σ K) (hf : f ∈ Ideal.span (Set.range b))
    (hn : ∀ c ∈ f.support, ∀ i, c i < d i) : f = 0 := by
  classical
  by_contra hf0
  have hmem : f ∈ Ideal.span (b '' ((Finset.univ : Finset σ) : Set σ)) := by simpa using hf
  obtain ⟨i, _, hi⟩ := pure_power_leading_divisibility o d b hu hd Finset.univ f hmem hf0
  rw [Finsupp.single_le_iff] at hi
  exact (hn (o.degree f) (o.degree_mem_support hf0) i).not_ge hi

theorem pure_power_remainder_exists
    {K σ : Type*} [Field K]
    (o : MonomialOrder σ) (d : σ → ℕ) (b : σ → MvPolynomial σ K)
    (hu : ∀ i, IsUnit (o.leadingCoeff (b i)))
    (hd : ∀ i, o.degree (b i) = Finsupp.single i (d i))
    (f : MvPolynomial σ K) :
    ∃ r, (∀ c ∈ r.support, ∀ i, c i < d i) ∧
      f - r ∈ Ideal.span (Set.range b) := by
  classical
  obtain ⟨g, r, hfr, _, hr⟩ := o.div hu f
  refine ⟨r, ?_, ?_⟩
  · intro c hc i
    have h := hr c hc i
    rw [hd i, Finsupp.single_le_iff] at h
    exact lt_of_not_ge h
  · rw [hfr, add_sub_cancel_right, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))


end TranscendenceTheory

open TranscendenceTheory
open MvPolynomial
theorem solution
    (K σ : Type*) [Field K] [Fintype σ]
    (o : MonomialOrder σ) (d : σ → ℕ) (b : σ → MvPolynomial σ K)
    (hu : ∀ i, IsUnit (o.leadingCoeff (b i)))
    (hd : ∀ i, o.degree (b i) = Finsupp.single i (d i)) :
    let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range b)
    Module.Finite K (MvPolynomial σ K ⧸ J) ∧
      (∃ β : Module.Basis (∀ i, Fin (d i)) K (MvPolynomial σ K ⧸ J),
        ∀ a, β a = Ideal.Quotient.mk J
          (monomial (Finsupp.equivFunOnFinite.symm (fun i => (a i).val)) 1)) ∧
      Module.finrank K (MvPolynomial σ K ⧸ J) = ∏ i, d i ∧
      ∀ f : MvPolynomial σ K, ∃! r,
        (∀ c ∈ r.support, ∀ i, c i < d i) ∧ f - r ∈ J := by
  classical
  dsimp only
  let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range b)
  let q := Ideal.Quotient.mkₐ K J
  let e : (∀ i, Fin (d i)) → (σ →₀ ℕ) :=
    fun a => Finsupp.equivFunOnFinite.symm (fun i => (a i).val)
  let v : (∀ i, Fin (d i)) → MvPolynomial σ K := fun a => monomial (e a) 1
  let V := restrictSupport K {c : σ →₀ ℕ | ∀ i, c i < d i}
  have he : Function.Injective e := by
    intro a a' haa'
    funext i
    apply Fin.ext
    exact congrArg (fun c : σ →₀ ℕ => c i) haa'
  have hlin : LinearIndependent K v :=
    (basisMonomials σ K).linearIndependent.comp e he
  have hV : Submodule.span K (Set.range v) ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact (monomial_mem_restrictSupport K).mpr (Or.inl (fun i => (a i).isLt))
  have hdis : Disjoint (Submodule.span K (Set.range v)) (LinearMap.ker q.toLinearMap) := by
    apply Submodule.disjoint_def.mpr
    intro f hv hq
    apply pure_power_reduced_mem_ideal_eq_zero o d b hu hd f
    · exact Ideal.Quotient.eq_zero_iff_mem.mp hq
    · exact (mem_restrictSupport_iff K).mp (hV hv)
  have hli : LinearIndependent K (q ∘ v) := hlin.map hdis
  have hspan : Submodule.span K (Set.range (q ∘ v)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨r, hr, hfr⟩ := pure_power_remainder_exists o d b hu hd f
    have hqr : q f = q r := sub_eq_zero.mp (by
      rw [← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hfr)
    change q f ∈ Submodule.span K (Set.range (q ∘ v))
    rw [hqr, r.as_sum, map_sum]
    apply Submodule.sum_mem
    intro c hc
    let a : ∀ i, Fin (d i) := fun i => ⟨c i, hr c hc i⟩
    have hea : e a = c := by ext i; simp [e, a]
    have hv : q (monomial c 1) ∈ Submodule.span K (Set.range (q ∘ v)) :=
      Submodule.subset_span ⟨a, by dsimp [v]; rw [hea]⟩
    have hcoeff : q (monomial c (coeff c r)) = coeff c r • q (monomial c 1) := by
      rw [← map_smul]
      apply congrArg q
      simp only [smul_monomial, smul_eq_mul, mul_one]
    rw [hcoeff]
    exact Submodule.smul_mem _ _ hv
  let β := Module.Basis.mk hli hspan.ge
  have hfinite : Module.Finite K (MvPolynomial σ K ⧸ J) := Module.Finite.of_basis β
  have hdim : Module.finrank K (MvPolynomial σ K ⧸ J) = ∏ i, d i := by
    rw [Module.finrank_eq_card_basis β]
    simp
  refine ⟨hfinite, ⟨β, fun _ => Module.Basis.mk_apply _ _ _⟩, hdim, ?_⟩
  intro f
  obtain ⟨r, hr, hfr⟩ := pure_power_remainder_exists o d b hu hd f
  refine ⟨r, ⟨hr, hfr⟩, ?_⟩
  rintro r' ⟨hr', hfr'⟩
  apply sub_eq_zero.mp
  apply pure_power_reduced_mem_ideal_eq_zero o d b hu hd (r' - r)
  · have h := J.sub_mem hfr hfr'
    simpa only [sub_sub_sub_cancel_left] using h
  · exact (mem_restrictSupport_iff K).mp
      (V.sub_mem ((mem_restrictSupport_iff K).mpr hr') ((mem_restrictSupport_iff K).mpr hr))
