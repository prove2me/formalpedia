-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IntegerToRational.coheight_eQ_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:48.542245+00:00
-- url     : https://prove2.me/submissions/7397bbbe-983e-449c-9c70-ececb0a7acea

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatB
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_chZero_comap
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_comap_map_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_comap_strictMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
private lemma isJacobsonRing_int_regular_local_rings : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  refine le_antisymm ?_ Ideal.le_jacobson
  by_cases hb : P = ⊥
  · subst hb
    intro m hm
    rw [Ideal.mem_jacobson_bot] at hm
    rw [Ideal.mem_bot]
    have h1 := Int.isUnit_iff.mp (hm 1)
    have h2 := Int.isUnit_iff.mp (hm 2)
    omega
  · have hmax : P.IsMaximal := by
      first
        | exact Ideal.IsPrime.isMaximal hP hb
        | exact hP.isMaximal hb
        | exact Ideal.IsPrime.to_maximal_ideal hb
        | exact Ring.DimensionLEOne.maximalOfPrime hb hP
    exact sInf_le ⟨le_rfl, hmax⟩
private lemma not_isMaximal_of_chZero (Q : Ideal (MvPolynomial σ ℤ)) (hQ : ChZero Q) :
    ¬ Q.IsMaximal := by
  intro hmax
  haveI := hmax
  haveI := isJacobsonRing_int_regular_local_rings
  letI : Field (MvPolynomial σ ℤ ⧸ Q) := Ideal.Quotient.field Q
  have hint := MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
    (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  have hfe : (Ideal.Quotient.mk Q).comp (MvPolynomial.C) =
      algebraMap ℤ (MvPolynomial σ ℤ ⧸ Q) := RingHom.ext_int _ _
  haveI : Algebra.IsIntegral ℤ (MvPolynomial σ ℤ ⧸ Q) := by
    constructor
    intro x
    have hx := hint x
    rw [hfe] at hx
    exact hx
  have hinj : Function.Injective (algebraMap ℤ (MvPolynomial σ ℤ ⧸ Q)) := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    rw [← hfe, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hm
    exact hQ m hm
  have hF : IsField ℤ := isField_of_isIntegral_of_isField hinj
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mp hmax)
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel (two_ne_zero : (2 : ℤ) ≠ 0)
  omega
end ReciprocityTheory.AnForm.R.IntegerToRational
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R.IntegerToRational
theorem _root_.solution (P : PrimeSpectrum (MvPolynomial σ ℤ)) (hP : ChZero P.asIdeal) :
    Order.coheight (eQ P hP) + 1 ≤ Order.coheight P := by
  let φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)
  let g : PrimeSpectrum (MvPolynomial σ ℚ) → PrimeSpectrum (MvPolynomial σ ℤ) :=
    fun Q => ⟨Q.asIdeal.comap φ, inferInstance⟩
  have hg : StrictMono g := by
    intro a b hab
    show a.asIdeal.comap φ < b.asIdeal.comap φ
    exact comap_strictMono (show a.asIdeal < b.asIdeal from hab)
  have hg0 : g (eQ P hP) = P := PrimeSpectrum.ext (comap_map_eq P.asIdeal hP)
  have hup : ∀ L : PrimeSpectrum (MvPolynomial σ ℚ), ∃ M, g L < M := by
    intro L
    have hQ : ChZero (g L).asIdeal := chZero_comap L.asIdeal
    have hnm := not_isMaximal_of_chZero (g L).asIdeal hQ
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (g L).asIdeal (g L).isPrime.ne_top
    refine ⟨⟨M, hM.isPrime⟩, ?_⟩
    show (g L).asIdeal < M
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hnm
    rw [heq]
    exact hM
  have key : ∀ n : ℕ, (n : ℕ∞) ≤ Order.coheight (eQ P hP) →
      ((n + 1 : ℕ) : ℕ∞) ≤ Order.coheight P := by
    intro n hn
    obtain ⟨p, hph, hpl⟩ := Order.exists_series_of_le_coheight (eQ P hP) hn
    obtain ⟨M, hM⟩ := hup p.last
    have hlast : (p.map g hg).last < M := hM
    let q := (p.map g hg).snoc M hlast
    have hqh : q.head = P := by
      rw [RelSeries.head_snoc]
      show g p.head = P
      rw [hph]
      exact hg0
    have hql : q.length = n + 1 := by
      rw [← hpl]
      rfl
    rw [← hql, ← hqh]
    exact Order.length_le_coheight_head
  rcases eq_or_ne (Order.coheight (eQ P hP)) ⊤ with h | h
  · have htop : Order.coheight P = ⊤ := by
      by_contra hne
      have h1 := key (Order.coheight P).toNat (by rw [h]; exact le_top)
      have h2 : (((Order.coheight P).toNat + 1 : ℕ) : ℕ∞) ≤ ((Order.coheight P).toNat : ℕ∞) := by
        rw [ENat.coe_toNat hne]
        exact h1
      have h3 := (Nat.cast_le (α := ℕ∞)).mp h2
      omega
    rw [htop]
    exact le_top
  · have h1 := key (Order.coheight (eQ P hP)).toNat (by rw [ENat.coe_toNat h])
    rw [← ENat.coe_toNat h]
    exact_mod_cast h1
end ReciprocityTheory.AnForm.R.IntegerToRational
