-- Prove2me | solution 1 for QuaternionAlgebra.nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ae1e40d7-2ec6-54f1-afb7-175bbb50b8a6

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
import Theorems.Thm_Rat_hilbertReciprocity_even_card_not_ternary_isotropic
import Theorems.Thm_Rat_exists_ternary_isotropic_of_forall_adicCompletion_of_pos
import Theorems.Thm_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
import Theorems.Thm_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split
import Theorems.Thm_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_QuaternionAlgebra_nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace QuaternionAlgebra p2m_export "QuaternionAlgebra" "re Basis.lift finrank_eq_four lift imK imJ imI Basis IsDefiniteRamifiedExactlyAt forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv nonempty_algEquiv_matrix_of_normForm_eq_zero" end QuaternionAlgebra
p2m_open_scoped "QuaternionAlgebra" in
theorem QuaternionAlgebra.exists_ternary_isotropic_mul
    (K : Type) [Field K] (α β γ : K) (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (h₁ : ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - α * x ^ 2 - β * y ^ 2 = 0)
    (h₂ : ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - α * x ^ 2 - γ * y ^ 2 = 0) :
    ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - α * x ^ 2 - (β * γ) * y ^ 2 = 0 := by
  obtain ⟨z₁, x₁, y₁, hn₁, e₁⟩ := h₁
  obtain ⟨z₂, x₂, y₂, hn₂, e₂⟩ := h₂

  have hsq : ∀ {z x : K}, ¬ (z = 0 ∧ x = 0) → z ^ 2 - α * x ^ 2 = 0 →
      ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - α * x ^ 2 - (β * γ) * y ^ 2 = 0 := by
    intro z x hzx e
    exact ⟨z, x, 0, fun h => hzx ⟨h.1, h.2.1⟩, by rw [e]; ring⟩
  by_cases hy₁ : y₁ = 0
  · subst hy₁
    exact hsq (fun h => hn₁ ⟨h.1, h.2, rfl⟩) (by simpa using e₁)
  by_cases hy₂ : y₂ = 0
  · subst hy₂
    exact hsq (fun h => hn₂ ⟨h.1, h.2, rfl⟩) (by simpa using e₂)

  refine ⟨z₁ * z₂ + α * x₁ * x₂, z₁ * x₂ + x₁ * z₂, y₁ * y₂, fun h => (mul_ne_zero hy₁ hy₂) h.2.2, ?_⟩
  linear_combination (z₂ ^ 2 - α * x₂ ^ 2) * e₁ + (β * y₁ ^ 2) * e₂

theorem isotropic_of_not_forall_isUnit (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hnd : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (a : v.adicCompletion ℚ) * x ^ 2 - (b : v.adicCompletion ℚ) * y ^ 2 = 0 := by
  have hinj : Function.Injective (algebraMap ℚ (v.adicCompletion ℚ)) := (algebraMap ℚ (v.adicCompletion ℚ)).injective
  have ha' : (a : v.adicCompletion ℚ) ≠ 0 := fun h0 => ha (hinj (by simpa using h0))
  have hb' : (b : v.adicCompletion ℚ) ≠ 0 := fun h0 => hb (hinj (by simpa using h0))
  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero,
    QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero _ _ _ ha' hb'] at hnd
  simp only [not_forall, Classical.not_imp] at hnd
  obtain ⟨z, x, y, h0, hne⟩ := hnd
  exact ⟨z, x, y, hne, h0⟩

theorem heightOneSpectrum_eq_of_mem (q : ℕ) (hq : q.Prime) (v w : HeightOneSpectrum (𝓞 ℚ))
    (hv : (q : 𝓞 ℚ) ∈ v.asIdeal) (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by

  have hmax : (Ideal.span {((q : ℕ) : 𝓞 ℚ)}).IsMaximal := by
    haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
      IsPrincipalIdealRing.of_surjective (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) Rat.ringOfIntegersEquiv.symm.surjective
    have hirr : Irreducible ((q : ℕ) : 𝓞 ℚ) := by
      have hz : Irreducible ((q : ℕ) : ℤ) := (Nat.prime_iff_prime_int.mp hq).irreducible
      have h2 : Rat.ringOfIntegersEquiv.symm ((q : ℕ) : ℤ) = ((q : ℕ) : 𝓞 ℚ) := map_natCast _ q
      rw [← h2]
      exact (MulEquiv.irreducible_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr hz
    exact PrincipalIdealRing.isMaximal_of_irreducible hirr
  have h1 : Ideal.span {((q : ℕ) : 𝓞 ℚ)} = v.asIdeal :=
    hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  have h2 : Ideal.span {((q : ℕ) : 𝓞 ℚ)} = w.asIdeal :=
    hmax.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hw)
  exact HeightOneSpectrum.ext (h1.symm.trans h2)

p2m_open_scoped "QuaternionAlgebra" in
theorem QuaternionAlgebra.exists_mul_sq_sub_mul_sq_eq_of_isDefiniteRamifiedExactlyAt
    (a' c b' : ℚ) (q : ℕ) (hq : q.Prime)
    (h : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a' c q) (h' : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a' b' q) :
    ∃ y z : ℚ, c * (y ^ 2 - a' * z ^ 2) = b' := by
  obtain ⟨ha', hc, hloc⟩ := h
  obtain ⟨-, hb', hloc'⟩ := h'
  have ha'0 : a' ≠ 0 := ne_of_lt ha'
  have hc0 : c ≠ 0 := ne_of_lt hc
  have hb'0 : b' ≠ 0 := ne_of_lt hb'
  have hcb : 0 < c * b' := mul_pos_of_neg_of_neg hc hb'

  have hiso : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∉ v.asIdeal →
      ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a') * x ^ 2
          - (algebraMap ℚ (v.adicCompletion ℚ) (c * b')) * y ^ 2 = 0 := by
    intro v hv
    have h1 := isotropic_of_not_forall_isUnit a' c ha'0 hc0 v (fun hu => hv ((hloc v).mp hu))
    have h2 := isotropic_of_not_forall_isUnit a' b' ha'0 hb'0 v (fun hu => hv ((hloc' v).mp hu))
    have hinj : Function.Injective (algebraMap ℚ (v.adicCompletion ℚ)) := (algebraMap ℚ (v.adicCompletion ℚ)).injective
    have h3 := QuaternionAlgebra.exists_ternary_isotropic_mul (v.adicCompletion ℚ) (a' : v.adicCompletion ℚ) (c : v.adicCompletion ℚ) (b' : v.adicCompletion ℚ)
      (fun h0 => ha'0 (hinj (by simpa using h0))) (fun h0 => hc0 (hinj (by simpa using h0))) (fun h0 => hb'0 (hinj (by simpa using h0))) h1 h2
    simpa [map_mul] using h3

  obtain ⟨S, hS, heven⟩ := Rat.hilbertReciprocity_even_card_not_ternary_isotropic a' (c * b') ha'0 hcb.ne'
  have hnot : ¬ (a' < 0 ∧ c * b' < 0) := fun hh => absurd hh.2 (not_lt.mpr hcb.le)
  rw [if_neg hnot, add_zero] at heven
  have hsub : ∀ v ∈ S, (q : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v hvS
    by_contra hv
    exact ((hS v).mp hvS) (hiso v hv)
  have hcard : S.card ≤ 1 := Finset.card_le_one.mpr (fun v hv w hw => heightOneSpectrum_eq_of_mem q hq v w (hsub v hv) (hsub w hw))
  have hS0 : S = ∅ := by
    rcases Nat.even_iff.mp heven |> fun h => (show S.card = 0 by omega) with h0
    exact Finset.card_eq_zero.mp h0
  have hall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a') * x ^ 2
          - (algebraMap ℚ (v.adicCompletion ℚ) (c * b')) * y ^ 2 = 0 := by
    intro v
    by_contra hno
    have : v ∈ S := (hS v).mpr hno
    rw [hS0] at this
    exact absurd this (Finset.notMem_empty v)

  obtain ⟨z, x, y, hne, hzero⟩ :=
    Rat.exists_ternary_isotropic_of_forall_adicCompletion_of_pos a' (c * b') ha'0 hcb.ne' hall (Or.inr hcb)

  have hy : y ≠ 0 := by
    rintro rfl
    have h1 : z ^ 2 = a' * x ^ 2 := by linarith
    have hz : z = 0 := by nlinarith [sq_nonneg z, sq_nonneg x, mul_nonpos_of_nonpos_of_nonneg ha'.le (sq_nonneg x)]
    have hx : x = 0 := by
      subst hz
      have : a' * x ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h ha'0
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    exact hne ⟨hz, hx, rfl⟩

  refine ⟨z / (c * y), x / (c * y), ?_⟩
  have hcy : c * y ≠ 0 := mul_ne_zero hc0 hy
  have h1 : z ^ 2 - a' * x ^ 2 = c * b' * y ^ 2 := by linarith
  calc c * ((z / (c * y)) ^ 2 - a' * (x / (c * y)) ^ 2) = c * ((z ^ 2 - a' * x ^ 2) / (c * y) ^ 2) := by ring
    _ = c * ((c * b' * y ^ 2) / (c * y) ^ 2) := by rw [h1]
    _ = b' := by field_simp

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re Basis.lift finrank_eq_four lift imK imJ imI Basis IsDefiniteRamifiedExactlyAt forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv nonempty_algEquiv_matrix_of_normForm_eq_zero"
p2m_open "QuaternionAlgebra"

variable {F : Type} [Field F]

theorem nonempty_algEquiv_of_pure_pair (a b a' c : F) (ha' : a' ≠ 0) (hc : c ≠ 0)
    (u w : ℍ[F, a, b]) (hu0 : u.re = 0) (hw0 : w.re = 0) (huw0 : (u * w).re = 0)
    (huu : u * u = a' • (1 : ℍ[F, a, b])) (hww : w * w = c • (1 : ℍ[F, a, b])) (huw : w * u = -(u * w)) :
    Nonempty (ℍ[F, a, b] ≃ₐ[F] ℍ[F, a', c]) := by
  let B : QuaternionAlgebra.Basis ℍ[F, a, b] a' 0 c :=
    { i := u, j := w, k := u * w,
      i_mul_i := by rw [huu, zero_smul, add_zero]
      j_mul_j := hww
      i_mul_j := rfl
      j_mul_i := by rw [huw, zero_smul, zero_sub] }
  let f : ℍ[F, a', c] →ₐ[F] ℍ[F, a, b] := B.liftHom
  have hf : ∀ q : ℍ[F, a', c], f q = q.re • (1 : ℍ[F, a, b]) + q.imI • u + q.imJ • w + q.imK • (u * w) := fun q => by
    show B.lift q = _
    rw [Basis.lift, Algebra.algebraMap_eq_smul_one]

  have h_u_uw : u * (u * w) = a' • w := by rw [← mul_assoc, huu, smul_mul_assoc, one_mul]
  have h_w_uw : w * (u * w) = -(c • u) := by rw [← mul_assoc, huw, neg_mul, mul_assoc, hww, mul_smul_comm, mul_one]
  have h_uw_u : (u * w) * u = -(a' • w) := by rw [mul_assoc, huw, mul_neg, h_u_uw]
  have h_uw_w : (u * w) * w = c • u := by rw [mul_assoc, hww, mul_smul_comm, mul_one]
  have h_uw_uw : (u * w) * (u * w) = -((a' * c) • (1 : ℍ[F, a, b])) := by
    rw [mul_assoc, ← mul_assoc w u w, huw, neg_mul, mul_neg, mul_assoc, hww, ← mul_assoc, huu, smul_one_mul, smul_smul]

  have key : ∀ q : ℍ[F, a', c], f q = 0 → q = 0 := by
    intro q h
    have e0 : q.re • (1 : ℍ[F, a, b]) + q.imI • u + q.imJ • w + q.imK • (u * w) = 0 := by rw [← hf]; exact h
    have e1 : q.re • u + q.imI • (a' • (1 : ℍ[F, a, b])) + q.imJ • (u * w) + q.imK • (a' • w) = 0 := by
      have := congrArg (u * ·) e0
      simpa only [mul_add, mul_smul_comm, mul_one, huu, h_u_uw, mul_zero] using this
    have e2 : q.re • w + q.imI • (-(u * w)) + q.imJ • (c • (1 : ℍ[F, a, b])) + q.imK • (-(c • u)) = 0 := by
      have := congrArg (w * ·) e0
      simpa only [mul_add, mul_smul_comm, mul_one, huw, hww, h_w_uw, mul_zero] using this
    have e3 : q.re • (u * w) + q.imI • (-(a' • w)) + q.imJ • (c • u) + q.imK • (-((a' * c) • (1 : ℍ[F, a, b]))) = 0 := by
      have := congrArg ((u * w) * ·) e0
      simpa only [mul_add, mul_smul_comm, mul_one, h_uw_u, h_uw_w, h_uw_uw, mul_zero] using this
    have r0 := congrArg QuaternionAlgebra.re e0
    have r1 := congrArg QuaternionAlgebra.re e1
    have r2 := congrArg QuaternionAlgebra.re e2
    have r3 := congrArg QuaternionAlgebra.re e3
    simp [hu0, hw0, huw0] at r0 r1 r2 r3
    have hI : q.imI = 0 := r1.resolve_right ha'
    have hJ : q.imJ = 0 := r2.resolve_right hc
    have hK : q.imK = 0 := r3.resolve_right (by rintro (h | h); exacts [ha' h, hc h])
    ext
    · simpa using r0
    · simpa using hI
    · simpa using hJ
    · simpa using hK
  have hinj : Function.Injective f := by
    intro q₁ q₂ h
    have := key (q₁ - q₂) (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp this
  have hbij : Function.Bijective f := by
    refine ⟨hinj, ?_⟩
    have hfin : Module.finrank F ℍ[F, a', c] = Module.finrank F ℍ[F, a, b] := by
      rw [QuaternionAlgebra.finrank_eq_four, QuaternionAlgebra.finrank_eq_four]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := f.toLinearMap)).mp hinj
  exact ⟨(AlgEquiv.ofBijective f hbij).symm⟩

theorem exists_nonempty_algEquiv_of_sq_eq
    (F : Type) [Field F] (h2 : (2 : F) ≠ 0) (a b a' : F) (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0)
    (x y z : F) (hu : a * x ^ 2 + b * y ^ 2 - a * b * z ^ 2 = a') :
    ∃ c : F, c ≠ 0 ∧ Nonempty (ℍ[F, a, b] ≃ₐ[F] ℍ[F, a', c]) := by
  let u : ℍ[F, a, b] := ⟨0, x, y, z⟩
  have hu0 : u.re = 0 := rfl
  have huu : u * u = a' • (1 : ℍ[F, a, b]) := by
    ext <;> simp [u] <;> first | linear_combination hu | ring

  have finish : ∀ (w : ℍ[F, a, b]) (c : F), w.re = 0 → (u * w).re = 0 → w * w = c • (1 : ℍ[F, a, b]) →
      w * u = -(u * w) → c ≠ 0 → ∃ c : F, c ≠ 0 ∧ Nonempty (ℍ[F, a, b] ≃ₐ[F] ℍ[F, a', c]) :=
    fun w c hw0 huw0 hww huw hc => ⟨c, hc, nonempty_algEquiv_of_pure_pair a b a' c ha' hc u w hu0 hw0 huw0 huu hww huw⟩
  by_cases h₁ : a * x ^ 2 + b * y ^ 2 = 0
  · by_cases h₂ : b * z ^ 2 - x ^ 2 = 0
    · by_cases h₃ : a * z ^ 2 - y ^ 2 = 0
      ·
        exfalso
        have hz : 2 * a * b * z ^ 2 = 0 := by linear_combination a * h₂ + b * h₃ + h₁
        have hz2 : z ^ 2 = 0 := by
          rcases mul_eq_zero.mp hz with h | h
          · rcases mul_eq_zero.mp h with h' | h'
            · rcases mul_eq_zero.mp h' with h'' | h''
              · exact absurd h'' h2
              · exact absurd h'' ha
            · exact absurd h' hb
          · exact h
        exact ha' (by rw [← hu]; linear_combination h₁ - a * b * hz2)
      · exact finish ⟨0, 0, a * z, y⟩ (a * b * (a * z ^ 2 - y ^ 2)) rfl (by simp [u]; ring)
          (by ext <;> simp <;> ring) (by ext <;> simp [u] <;> ring) (mul_ne_zero (mul_ne_zero ha hb) h₃)
    · exact finish ⟨0, b * z, 0, x⟩ (a * b * (b * z ^ 2 - x ^ 2)) rfl (by simp [u]; ring)
        (by ext <;> simp <;> ring) (by ext <;> simp [u] <;> ring) (mul_ne_zero (mul_ne_zero ha hb) h₂)
  · exact finish ⟨0, b * y, -(a * x), 0⟩ (a * b * (a * x ^ 2 + b * y ^ 2)) rfl (by simp [u]; ring)
      (by ext <;> simp <;> ring) (by ext <;> simp [u] <;> ring) (mul_ne_zero (mul_ne_zero ha hb) h₁)

theorem nonempty_algEquiv_of_mul_sq_sub_mul_sq_eq
    (F : Type) [Field F] (a' c b' : F) (ha' : a' ≠ 0) (hc : c ≠ 0) (hb' : b' ≠ 0)
    (y z : F) (hw : c * (y ^ 2 - a' * z ^ 2) = b') :
    Nonempty (ℍ[F, a', c] ≃ₐ[F] ℍ[F, a', b']) := by
  let u : ℍ[F, a', c] := ⟨0, 1, 0, 0⟩
  let w : ℍ[F, a', c] := ⟨0, 0, y, z⟩
  exact nonempty_algEquiv_of_pure_pair a' c a' b' ha' hb' u w rfl rfl (by simp [u, w])
    (by ext <;> simp [u]) (by ext <;> simp [w] <;> first | linear_combination hw | ring) (by ext <;> simp [u, w] <;> ring)

end QuaternionAlgebra

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re Basis.lift finrank_eq_four lift imK imJ imI Basis IsDefiniteRamifiedExactlyAt forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv nonempty_algEquiv_matrix_of_normForm_eq_zero"
p2m_open "QuaternionAlgebra"

theorem neg_of_mul_self_eq_smul_one {a b : ℚ} (ha : a < 0) (hb : b < 0) (y : ℍ[ℚ, a, b]) (s : ℚ)
    (hy : y * y = s • (1 : ℍ[ℚ, a, b])) (hyc : ∀ r : ℚ, y ≠ r • (1 : ℍ[ℚ, a, b])) : s < 0 := by
  have hre := congrArg QuaternionAlgebra.re hy
  have hI := congrArg QuaternionAlgebra.imI hy
  have hJ := congrArg QuaternionAlgebra.imJ hy
  have hK := congrArg QuaternionAlgebra.imK hy
  simp at hre hI hJ hK

  have h0 : y.re = 0 := by
    by_contra h0
    have h1 : y.imI = 0 := by
      have : 2 * y.re * y.imI = 0 := by linear_combination hI
      simpa [h0] using this
    have h2 : y.imJ = 0 := by
      have : 2 * y.re * y.imJ = 0 := by linear_combination hJ
      simpa [h0] using this
    have h3 : y.imK = 0 := by
      have : 2 * y.re * y.imK = 0 := by linear_combination hK
      simpa [h0] using this
    exact hyc y.re (by ext <;> simp [h1, h2, h3])
  have hne : ¬ (y.imI = 0 ∧ y.imJ = 0 ∧ y.imK = 0) := by
    rintro ⟨h1, h2, h3⟩
    exact hyc 0 (by ext <;> simp [h0, h1, h2, h3])

  have hs : s = a * y.imI ^ 2 + b * y.imJ ^ 2 - a * b * y.imK ^ 2 := by
    rw [h0] at hre; linear_combination -hre
  have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  have hle : a * y.imI ^ 2 + b * y.imJ ^ 2 - a * b * y.imK ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg y.imI, sq_nonneg y.imJ, sq_nonneg y.imK, mul_nonneg hab.le (sq_nonneg y.imK),
      mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg y.imI), mul_nonpos_of_nonpos_of_nonneg hb.le (sq_nonneg y.imJ)]
  have hneq : a * y.imI ^ 2 + b * y.imJ ^ 2 - a * b * y.imK ^ 2 ≠ 0 := by
    intro hz
    have t1 : a * y.imI ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg _)
    have t2 : b * y.imJ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb.le (sq_nonneg _)
    have t3 : 0 ≤ a * b * y.imK ^ 2 := mul_nonneg hab.le (sq_nonneg _)
    have e1 : a * y.imI ^ 2 = 0 := by linarith
    have e2 : b * y.imJ ^ 2 = 0 := by linarith
    have e3 : a * b * y.imK ^ 2 = 0 := by linarith
    apply hne
    refine ⟨?_, ?_, ?_⟩
    · simpa [ha.ne] using e1
    · simpa [hb.ne] using e2
    · simpa [ha.ne, hb.ne] using e3
  rw [hs]
  exact lt_of_le_of_ne hle hneq

theorem forall_isUnit_iff_of_ringEquiv {A B : Type} [Ring A] [Ring B] (φ : A ≃+* B) :
    (∀ x : A, x ≠ 0 → IsUnit x) ↔ (∀ x : B, x ≠ 0 → IsUnit x) := by
  constructor
  · intro h x hx
    have := (h (φ.symm x) (by simpa using hx)).map φ
    simpa using this
  · intro h x hx
    have := (h (φ x) (by simpa using hx)).map φ.symm
    simpa using this

p2m_open_scoped "QuaternionAlgebra.IsDefiniteRamifiedExactlyAt" in

theorem IsDefiniteRamifiedExactlyAt.of_algEquiv
    (a b a' c : ℚ) (q : ℕ)
    (h : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q) (e : Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a', c]))
    (ha' : a' ≠ 0) (hc : c ≠ 0) :
    QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a' c q := by
  obtain ⟨ha, hb, hloc⟩ := h
  obtain ⟨e⟩ := e

  have hsq : ∀ (t : ℍ[ℚ, a', c]) (s : ℚ), t * t = s • (1 : ℍ[ℚ, a', c]) → (∀ r : ℚ, t ≠ r • 1) → s < 0 := by
    intro t s ht htc
    refine neg_of_mul_self_eq_smul_one ha hb (e.symm t) s ?_ ?_
    · rw [← map_mul, ht, map_smul, map_one]
    · intro r hr
      apply htc r
      have := congrArg e hr
      simpa using this
  have ha'neg : a' < 0 := hsq ⟨0, 1, 0, 0⟩ a' (by ext <;> simp) (fun r hr => by
    have := congrArg QuaternionAlgebra.imI hr; simp at this)
  have hcneg : c < 0 := hsq ⟨0, 0, 1, 0⟩ c (by ext <;> simp) (fun r hr => by
    have := congrArg QuaternionAlgebra.imJ hr; simp at this)
  refine ⟨ha'neg, hcneg, fun v => ?_⟩

  let φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃ₐ[ℚ] ℍ[ℚ, a', c] ⊗[ℚ] v.adicCompletion ℚ :=
    Algebra.TensorProduct.congr e AlgEquiv.refl
  rw [← forall_isUnit_iff_of_ringEquiv φ.toRingEquiv]
  exact hloc v

end QuaternionAlgebra

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re Basis.lift finrank_eq_four lift imK imJ imI Basis IsDefiniteRamifiedExactlyAt forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv nonempty_algEquiv_matrix_of_normForm_eq_zero"
p2m_open "QuaternionAlgebra"

theorem forall_isUnit_iff_of_ringEquiv' {A B : Type*} [Ring A] [Ring B] (φ : A ≃+* B) :
    (∀ x : A, x ≠ 0 → IsUnit x) ↔ (∀ x : B, x ≠ 0 → IsUnit x) := by
  constructor
  · intro h x hx
    have := (h (φ.symm x) (by simpa using hx)).map φ
    simpa using this
  · intro h x hx
    have := (h (φ x) (by simpa using hx)).map φ.symm
    simpa using this

theorem not_forall_isUnit_matrix (K : Type) [Field K] : ¬ ∀ x : Matrix (Fin 2) (Fin 2) K, x ≠ 0 → IsUnit x := by
  intro h
  have hne : (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : K)) ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 0) 0
    simp at this
  have hu := h _ hne
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  have : (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : K)).det = 0 := by
    rw [Matrix.det_fin_two]; simp
  rw [this] at hu
  exact not_isUnit_zero hu

variable (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ))

theorem not_nonempty_algEquiv_matrix_of_forall_isUnit
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ¬ Nonempty (QuaternionAlgebra (v.adicCompletion ℚ) (algebraMap ℚ (v.adicCompletion ℚ) a) 0 (algebraMap ℚ (v.adicCompletion ℚ) b)
        ≃ₐ[v.adicCompletion ℚ] Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  rintro ⟨ψ⟩
  obtain ⟨φ, -, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv (R := ℚ) (S := v.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b) rfl (map_zero _) rfl ψ
  exact not_forall_isUnit_matrix _ ((forall_isUnit_iff_of_ringEquiv' φ).mp hdiv)

theorem not_isSquare_of_forall_isUnit
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ¬ IsSquare (algebraMap ℚ (v.adicCompletion ℚ) a) := by
  rintro ⟨t, ht⟩
  obtain ⟨φ, -, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv (R := ℚ) (S := v.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (T := QuaternionAlgebra (v.adicCompletion ℚ) (algebraMap ℚ (v.adicCompletion ℚ) a) 0 (algebraMap ℚ (v.adicCompletion ℚ) b))
    rfl (map_zero _) rfl AlgEquiv.refl
  have hall := (forall_isUnit_iff_of_ringEquiv' φ).mp hdiv

  let i' : QuaternionAlgebra (v.adicCompletion ℚ) (algebraMap ℚ (v.adicCompletion ℚ) a) 0 (algebraMap ℚ (v.adicCompletion ℚ) b) := ⟨0, 1, 0, 0⟩
  let tt : QuaternionAlgebra (v.adicCompletion ℚ) (algebraMap ℚ (v.adicCompletion ℚ) a) 0 (algebraMap ℚ (v.adicCompletion ℚ) b) := ⟨t, 0, 0, 0⟩
  have hprod : (i' - tt) * (i' + tt) = 0 := by
    ext : 1 <;> simp [i', tt] at ht ⊢ <;> first | linear_combination ht | linear_combination -ht | ring
  have hne : i' - tt ≠ 0 := by
    intro h0; have := congrArg QuaternionAlgebra.imI h0; simp [i', tt] at this
  have hne' : i' + tt ≠ 0 := by
    intro h0; have := congrArg QuaternionAlgebra.imI h0; simp [i', tt] at this
  obtain ⟨u, hu⟩ := hall _ hne
  have : i' + tt = 0 := by
    have := congrArg (fun x => (↑u⁻¹ : QuaternionAlgebra (v.adicCompletion ℚ) (algebraMap ℚ (v.adicCompletion ℚ) a) 0 (algebraMap ℚ (v.adicCompletion ℚ) b)) * x) hprod
    simpa [← mul_assoc, ← hu] using this
  exact hne' this

theorem exists_pure_isotropic_of_algEquiv_matrix (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (α β : K)
    (ψ : ℍ[K, α, β] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) :
    ∃ x y z : K, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ -α * x ^ 2 - β * y ^ 2 + α * β * z ^ 2 = 0 := by
  let N : ℍ[K, α, β] := ψ.symm (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : K))
  have hN0 : N ≠ 0 := by
    intro h0
    have : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : K) = 0 := by simpa [N] using congrArg ψ h0
    have := congrFun (congrFun this 0) 1
    simp at this
  have hNN : N * N = 0 := by
    apply ψ.injective
    rw [map_mul, map_zero]
    simp [N, Matrix.single_mul_single_of_ne]
  have hre := congrArg QuaternionAlgebra.re hNN
  have hI := congrArg QuaternionAlgebra.imI hNN
  have hJ := congrArg QuaternionAlgebra.imJ hNN
  have hK := congrArg QuaternionAlgebra.imK hNN
  simp at hre hI hJ hK
  have h0 : N.re = 0 := by
    by_contra h0
    have h20 : 2 * N.re ≠ 0 := mul_ne_zero h2 h0
    have h1 : N.imI = 0 := by
      have : 2 * N.re * N.imI = 0 := by linear_combination hI
      exact (mul_eq_zero.mp this).resolve_left h20
    have h2' : N.imJ = 0 := by
      have : 2 * N.re * N.imJ = 0 := by linear_combination hJ
      exact (mul_eq_zero.mp this).resolve_left h20
    have h3 : N.imK = 0 := by
      have : 2 * N.re * N.imK = 0 := by linear_combination hK
      exact (mul_eq_zero.mp this).resolve_left h20
    rw [h1, h2', h3] at hre
    simp at hre
    exact h0 (by simpa using hre)
  refine ⟨N.imI, N.imJ, N.imK, ?_, ?_⟩
  · rintro ⟨h1, h2', h3⟩
    exact hN0 (by ext <;> simp [h0, h1, h2', h3])
  · rw [h0] at hre
    linear_combination -hre

theorem exists_ternary_eq_of_isDefiniteRamifiedExactlyAt
    (a b a' b' : ℚ) (q : ℕ)
    (h : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q) (h' : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a' b' q) :
    ∃ x y z : ℚ, a * x ^ 2 + b * y ^ 2 - a * b * z ^ 2 = a' := by
  obtain ⟨ha, hb, hloc⟩ := h
  obtain ⟨ha', hb', hloc'⟩ := h'
  have ha0 : a ≠ 0 := ne_of_lt ha
  have hb0 : b ≠ 0 := ne_of_lt hb
  have ha'0 : a' ≠ 0 := ne_of_lt ha'

  have hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ x y z : v.adicCompletion ℚ,
      -(algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (v.adicCompletion ℚ) a) * (algebraMap ℚ (v.adicCompletion ℚ) b) * z ^ 2
        = algebraMap ℚ (v.adicCompletion ℚ) (-a') := by
    intro v
    by_cases hq : ((q : 𝓞 ℚ) ∈ v.asIdeal)
    ·
      have hdiv := (hloc v).mpr hq
      have hdiv' := (hloc' v).mpr hq
      have hns := not_nonempty_algEquiv_matrix_of_forall_isUnit a b v hdiv
      have hnsq := not_isSquare_of_forall_isUnit a' b' v hdiv'
      exact QuadraticForm.exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split a b ha0 hb0 v hns _
        (by rwa [map_neg, neg_neg])
    ·
      have hnd : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x := fun hu => hq ((hloc v).mp hu)
      rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero] at hnd
      simp only [not_forall] at hnd
      obtain ⟨x₀, x₁, x₂, x₃, h0, hne⟩ := hnd
      have hinj : Function.Injective (algebraMap ℚ (v.adicCompletion ℚ)) := (algebraMap ℚ (v.adicCompletion ℚ)).injective
      have haK : (a : v.adicCompletion ℚ) ≠ 0 := fun e => ha0 (hinj (by simpa using e))
      have hbK : (b : v.adicCompletion ℚ) ≠ 0 := fun e => hb0 (hinj (by simpa using e))
      haveI : CharZero (v.adicCompletion ℚ) := charZero_of_injective_algebraMap hinj
      have h2K : (2 : v.adicCompletion ℚ) ≠ 0 := two_ne_zero
      obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero (v.adicCompletion ℚ) h2K (a : v.adicCompletion ℚ) (b : v.adicCompletion ℚ) haK hbK x₀ x₁ x₂ x₃ hne h0
      have hiso := exists_pure_isotropic_of_algEquiv_matrix (v.adicCompletion ℚ) h2K _ _ ψ
      have huniv := QuadraticForm.forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero (v.adicCompletion ℚ) (a : v.adicCompletion ℚ) (b : v.adicCompletion ℚ) haK hbK hiso
        (algebraMap ℚ (v.adicCompletion ℚ) (-a'))
      simpa using huniv

  have hR : ∃ x y z : ℝ, -(algebraMap ℚ ℝ a) * x ^ 2 - (algebraMap ℚ ℝ b) * y ^ 2
      + (algebraMap ℚ ℝ a) * (algebraMap ℚ ℝ b) * z ^ 2 = algebraMap ℚ ℝ (-a') := by
    refine ⟨Real.sqrt ((a' : ℝ) / a), 0, 0, ?_⟩
    have hpos : 0 ≤ (a' : ℝ) / a := div_nonneg_of_nonpos (by exact_mod_cast ha'.le) (by exact_mod_cast ha.le)
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
    simp only [eq_ratCast, Rat.cast_neg]
    rw [Real.sq_sqrt hpos]
    field_simp
    ring
  obtain ⟨x, y, z, hxyz⟩ := QuadraticForm.exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real a b ha0 hb0 (-a')
    (neg_ne_zero.mpr ha'0) hv hR
  exact ⟨x, y, z, by linarith⟩

end QuaternionAlgebra

theorem solution
    (a b a' b' : ℚ) (q : ℕ) (hq : q.Prime)
    (h : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q) (h' : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a' b' q) :
    Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a', b']) := by
  have ha : a < 0 := h.1
  have hb : b < 0 := h.2.1
  have ha' : a' < 0 := h'.1
  have hb' : b' < 0 := h'.2.1
  obtain ⟨x, y, z, hu⟩ := QuaternionAlgebra.exists_ternary_eq_of_isDefiniteRamifiedExactlyAt a b a' b' q h h'
  obtain ⟨c, hc, ⟨φ⟩⟩ := QuaternionAlgebra.exists_nonempty_algEquiv_of_sq_eq ℚ two_ne_zero a b a' (ne_of_lt ha) (ne_of_lt hb) (ne_of_lt ha') x y z hu
  have h'' : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a' c q :=
    QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.of_algEquiv a b a' c q h ⟨φ⟩ (ne_of_lt ha') hc
  obtain ⟨yy, zz, hw⟩ := QuaternionAlgebra.exists_mul_sq_sub_mul_sq_eq_of_isDefiniteRamifiedExactlyAt a' c b' q hq h'' h'
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_of_mul_sq_sub_mul_sq_eq ℚ a' c b' (ne_of_lt ha') hc (ne_of_lt hb') yy zz hw
  exact ⟨φ.trans ψ⟩

end S_QuaternionAlgebra_nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime
end P2MW
export P2MW.S_QuaternionAlgebra_nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime (solution)
