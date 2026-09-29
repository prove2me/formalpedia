-- Prove2me | solution 1 for QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.exists_algHom_matrix_ratClosure_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/69518ea6-930f-59ac-ad85-4791492227fc

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_BaseChange
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Theorems.Thm_ValuationSubring_exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_algHom_matrix_ratClosure_injective

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re coe_algebraMap imK imJ imI IsDefiniteRamifiedExactlyAt nrd mul_star_eq_coe_nrd star_mul_eq_coe_nrd baseChangeRight nonempty_algEquiv_matrix_of_normForm_eq_zero"
namespace SplitRat
p2m_open "QuaternionAlgebra"

theorem isMaximal_span_natCast_of_prime {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsMaximal := by
  have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpO : _root_.Prime (p : 𝓞 ℚ) := by
    have : (p : 𝓞 ℚ) = e.symm (p : ℤ) := by rw [map_natCast]
    rw [this]
    exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ
  have hprime : (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsPrime := (Ideal.span_singleton_prime hpO.ne_zero).mpr hpO
  refine hprime.isMaximal ?_
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

def placeOfPrime (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  ⟨Ideal.span {(p : 𝓞 ℚ)}, (isMaximal_span_natCast_of_prime hp).isPrime, by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero⟩

theorem natCast_mem_placeOfPrime (p : ℕ) (hp : p.Prime) : ((p : ℕ) : 𝓞 ℚ) ∈ (placeOfPrime p hp).asIdeal :=
  Ideal.subset_span (Set.mem_singleton _)

theorem natCast_not_mem_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hq'
  have hcop : IsCoprime (p : 𝓞 ℚ) (q : 𝓞 ℚ) := by
    have := (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq) : IsCoprime (p : ℤ) (q : ℤ))
    simpa using this.map (Int.castRingHom (𝓞 ℚ))
  obtain ⟨x, y, hxy⟩ := hcop
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hxy]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hv) (Ideal.mul_mem_left _ _ hq')

theorem isUnit_of_nrd_ne_zero {K : Type} [Field K] {a' b' : K} (x : ℍ[K, a', b'])
    (hx : QuaternionAlgebra.nrd x ≠ 0) : IsUnit x := by
  refine ⟨⟨x, (QuaternionAlgebra.nrd x)⁻¹ • star x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe_nrd]
    ext <;> simp [hx]
  · rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe_nrd]
    ext <;> simp [hx]

theorem eq_zero_of_nrd_eq_zero {a b : ℚ} (ha : a < 0) (hb : b < 0) (x : ℍ[ℚ, a, b])
    (hx : QuaternionAlgebra.nrd x = 0) : x = 0 := by
  have h1 : 0 ≤ x.re ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (-a) * x.imI ^ 2 := mul_nonneg (neg_nonneg.mpr ha.le) (sq_nonneg _)
  have h3 : 0 ≤ (-b) * x.imJ ^ 2 := mul_nonneg (neg_nonneg.mpr hb.le) (sq_nonneg _)
  have h4 : 0 ≤ (a * b) * x.imK ^ 2 := mul_nonneg (mul_pos_of_neg_of_neg ha hb).le (sq_nonneg _)
  have hx' : x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2 = 0 := hx
  have hsum : x.re ^ 2 + (-a) * x.imI ^ 2 + (-b) * x.imJ ^ 2 + (a * b) * x.imK ^ 2 = 0 := by linarith
  have e1 : x.re ^ 2 = 0 := by linarith
  have e2 : (-a) * x.imI ^ 2 = 0 := by linarith
  have e3 : (-b) * x.imJ ^ 2 = 0 := by linarith
  have e4 : (a * b) * x.imK ^ 2 = 0 := by linarith
  have ha0 : (-a) ≠ 0 := (neg_pos.mpr ha).ne'
  have hb0 : (-b) ≠ 0 := (neg_pos.mpr hb).ne'
  have hab0 : a * b ≠ 0 := (mul_pos_of_neg_of_neg ha hb).ne'
  ext
  · exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp e1
  · exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ((mul_eq_zero.mp e2).resolve_left ha0)
  · exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ((mul_eq_zero.mp e3).resolve_left hb0)
  · exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ((mul_eq_zero.mp e4).resolve_left hab0)

theorem main {a b : ℚ} {q : ℕ} [Fact q.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A), Function.Injective ι := by
  classical
  have hr : r.Prime := Fact.out
  have hqp : q.Prime := Fact.out
  obtain ⟨ha, hb, hram⟩ := hdef

  set v := placeOfPrime r hr with hv_def
  have hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := natCast_mem_placeOfPrime r hr
  have hqv : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := natCast_not_mem_of_ne hr hqp hrq hv
  have hndiv : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x := fun h => hqv ((hram v).mp h)
  push_neg at hndiv
  obtain ⟨x, hx0, hxu⟩ := hndiv

  set K := v.adicCompletion ℚ with hK
  set ψ := (QuaternionAlgebra.baseChangeRight (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    rfl (map_zero _) rfl) with hψ
  set y : ℍ[K, algebraMap ℚ K a, algebraMap ℚ K b] := ψ x with hy
  have hy0 : y ≠ 0 := by
    intro h; apply hx0
    have : ψ x = ψ 0 := by rw [← hy, h, map_zero]
    exact ψ.injective this
  have hyu : ¬ IsUnit y := by
    intro h; apply hxu
    have := h.map ψ.symm
    rwa [hy, AlgEquiv.symm_apply_apply] at this
  have hnrd : QuaternionAlgebra.nrd y = 0 := by
    by_contra h; exact hyu (isUnit_of_nrd_ne_zero y h)
  have hcomp : ¬ (y.re = 0 ∧ y.imI = 0 ∧ y.imJ = 0 ∧ y.imK = 0) := by
    rintro ⟨h1, h2, h3, h4⟩; apply hy0; exact QuaternionAlgebra.ext h1 h2 h3 h4
  have h0 : y.re ^ 2 - algebraMap ℚ K a * y.imI ^ 2 - algebraMap ℚ K b * y.imJ ^ 2 +
      algebraMap ℚ K a * algebraMap ℚ K b * y.imK ^ 2 = 0 := hnrd
  have ha' : algebraMap ℚ K a ≠ 0 := by rw [map_ne_zero_iff _ (algebraMap ℚ K).injective]; exact ha.ne
  have hb' : algebraMap ℚ K b ≠ 0 := by rw [map_ne_zero_iff _ (algebraMap ℚ K).injective]; exact hb.ne
  have h2 : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap ℚ K) 2]
    exact (map_ne_zero_iff _ (algebraMap ℚ K).injective).mpr two_ne_zero

  obtain ⟨φ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero K h2 (algebraMap ℚ K a) (algebraMap ℚ K b)
    ha' hb' y.re y.imI y.imJ y.imK hcomp h0

  obtain ⟨e, -, -, -, -⟩ := ValuationSubring.exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime r A hA v hv

  let ι₀ : ℍ[ℚ, a, b] →+* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A) :=
    (e.toRingHom.mapMatrix).comp ((φ.toRingEquiv.toRingHom).comp ((ψ.toRingEquiv.toRingHom).comp
      (Algebra.TensorProduct.includeLeft : ℍ[ℚ, a, b] →ₐ[ℚ] ℍ[ℚ, a, b] ⊗[ℚ] K).toRingHom))
  refine ⟨ι₀.toRatAlgHom, ?_⟩

  rw [injective_iff_map_eq_zero]
  intro z hz
  have hz' : ι₀.toRatAlgHom (z * star z) = 0 := by rw [map_mul, hz, zero_mul]
  rw [QuaternionAlgebra.mul_star_eq_coe_nrd, ← QuaternionAlgebra.coe_algebraMap] at hz'
  change ι₀.toRatAlgHom (algebraMap ℚ ℍ[ℚ, a, b] (QuaternionAlgebra.nrd z)) = 0 at hz'
  rw [AlgHom.commutes] at hz'
  have hn : QuaternionAlgebra.nrd z = 0 :=
    (algebraMap ℚ (Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A))).injective (by rw [hz', map_zero])
  exact eq_zero_of_nrd_eq_zero ha hb z hn

end QuaternionAlgebra.SplitRat

end

theorem solution
    {a b : ℚ} {q : ℕ} [Fact q.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A), Function.Injective ι :=
  QuaternionAlgebra.SplitRat.main hdef hrq A hA

end S_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_algHom_matrix_ratClosure_injective
end P2MW
export P2MW.S_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_algHom_matrix_ratClosure_injective (solution)
