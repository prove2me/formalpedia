-- Prove2me | solution 1 for Transcendence.exists_irreducible_factor_cofactor_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-27T08:09:52.680089+00:00
-- url     : https://prove2.me/submissions/dad2ad0a-2cea-4344-a238-36d842ad8316

import Mathlib
import Theorems.Thm_Transcendence_norm_resultant_le_max_norm_eval

/-!
# The cofactor of the smallest irreducible factor is not small

This is the multiplicative step of Gel'fond's lemma. Let `P ∈ ℤ[X]` have positive degree and let
`θ ∈ ℂ`. Among the non-constant irreducible factors of `P`, let `Q` be one at which `|Q(θ)|` is
least, let `e` be its multiplicity, and write `P = Q^e R`. Every irreducible factor `T` of `R`
either is a constant, and then trivially satisfies the bound below, or is coprime to `Q` with
`|Q(θ)| ≤ |T(θ)|`; the Liouville inequality through the resultant then bounds `|T(θ)|` from below.
The bound is multiplicative in `T`, so it passes to `R`:
`1 ≤ 2^(deg Q · deg R) · M(Q)^(deg R) · M(R)^(deg Q) · |R(θ)|`, with `M` the Mahler measure.
-/

namespace S7W4_exists_irreducible_factor_cofactor_bound

open Polynomial

/-- An irreducible `Q ∈ ℤ[X]` of positive degree has a non-zero resultant with every polynomial it
does not divide: by Gauss's lemma the two are coprime in `ℚ[X]`. -/
lemma resultant_ne_zero_of_not_dvd {Q T : ℤ[X]} (hQ : Irreducible Q) (hQd : 0 < Q.natDegree)
    (h : ¬ Q ∣ T) : Q.resultant T ≠ 0 := by
  have hprim : Q.IsPrimitive := hQ.isPrimitive hQd.ne'
  have hQ' : Irreducible (Q.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hQ
  have hcop : IsCoprime (Q.map (Int.castRingHom ℚ)) (T.map (Int.castRingHom ℚ)) :=
    (hQ'.coprime_iff_not_dvd).mpr fun hd =>
      h ((IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast Q T hprim).mpr hd)
  intro h0
  apply resultant_ne_zero _ _ hcop
  rw [natDegree_map_eq_of_injective Int.cast_injective,
    natDegree_map_eq_of_injective Int.cast_injective, resultant_map_map, h0,
    map_zero (Int.castRingHom ℚ)]

lemma aeval_eq_eval_map (T : ℤ[X]) (θ : ℂ) :
    aeval θ T = (T.map (Int.castRingHom ℂ)).eval θ := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq]

/-- The lower bound that every factor of the cofactor satisfies. -/
def Good (Q : ℤ[X]) (θ : ℂ) (T : ℤ[X]) : Prop :=
  T ≠ 0 ∧ 1 ≤ 2 ^ (Q.natDegree * T.natDegree) *
    (Q.map (Int.castRingHom ℂ)).mahlerMeasure ^ T.natDegree *
    (T.map (Int.castRingHom ℂ)).mahlerMeasure ^ Q.natDegree * ‖aeval θ T‖

lemma good_mul (Q : ℤ[X]) (θ : ℂ) (T₁ T₂ : ℤ[X]) (h₁ : Good Q θ T₁) (h₂ : Good Q θ T₂) :
    Good Q θ (T₁ * T₂) := by
  obtain ⟨hT₁, hb₁⟩ := h₁
  obtain ⟨hT₂, hb₂⟩ := h₂
  refine ⟨mul_ne_zero hT₁ hT₂, ?_⟩
  rw [natDegree_mul hT₁ hT₂, Polynomial.map_mul, mahlerMeasure_mul, map_mul (aeval θ), norm_mul,
    mul_add, pow_add, pow_add, mul_pow]
  calc (1 : ℝ) ≤ _ * _ := one_le_mul_of_one_le_of_one_le hb₁ hb₂
    _ = _ := by ring

/-- A non-zero constant is `Good`, whatever its value. -/
lemma good_C (Q : ℤ[X]) (θ : ℂ) {c : ℤ} (hc : c ≠ 0) : Good Q θ (C c) := by
  refine ⟨C_ne_zero.2 hc, ?_⟩
  have h1 : (1 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast Int.one_le_abs hc
  have hM : ((C c).map (Int.castRingHom ℂ)).mahlerMeasure = |(c : ℝ)| := by
    rw [Polynomial.map_C, mahlerMeasure_const, eq_intCast (Int.castRingHom ℂ), Complex.norm_intCast]
  have hv : ‖aeval θ (C c)‖ = |(c : ℝ)| := by
    rw [aeval_C, algebraMap_int_eq, eq_intCast (Int.castRingHom ℂ), Complex.norm_intCast]
  rw [natDegree_C, mul_zero, pow_zero, pow_zero, one_mul, one_mul, hM, hv]
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) h1

/-- A factor `T` coprime to `Q` with `|Q(θ)| ≤ |T(θ)|` is `Good`, by the Liouville inequality. -/
lemma good_of_not_dvd (Q T : ℤ[X]) (θ : ℂ) (hQ : Irreducible Q) (hQd : 0 < Q.natDegree)
    (hT : T ≠ 0) (h : ¬ Q ∣ T) (hmin : ‖aeval θ Q‖ ≤ ‖aeval θ T‖) : Good Q θ T := by
  refine ⟨hT, ?_⟩
  have hres : 1 ≤ ‖(Q.map (Int.castRingHom ℂ)).resultant (T.map (Int.castRingHom ℂ))‖ := by
    rw [natDegree_map_eq_of_injective Int.cast_injective,
      natDegree_map_eq_of_injective Int.cast_injective, resultant_map_map,
      eq_intCast (Int.castRingHom ℂ), Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (resultant_ne_zero_of_not_dvd hQ hQd h)
  have hl := hres.trans (Transcendence.norm_resultant_le_max_norm_eval _ _
    (one_le_mahlerMeasure_of_ne_zero hQ.ne_zero) (one_le_mahlerMeasure_of_ne_zero hT) θ)
  rwa [natDegree_map_eq_of_injective Int.cast_injective,
    natDegree_map_eq_of_injective Int.cast_injective, ← aeval_eq_eval_map, ← aeval_eq_eval_map,
    max_eq_right hmin] at hl

end S7W4_exists_irreducible_factor_cofactor_bound

open Polynomial S7W4_exists_irreducible_factor_cofactor_bound in
theorem solution (P : Polynomial ℤ) (hP : 0 < P.natDegree)
    (θ : ℂ) :
    ∃ (Q R : Polynomial ℤ) (e : ℕ), Irreducible Q ∧ 0 < Q.natDegree ∧ 0 < e ∧ P = Q ^ e * R ∧
      1 ≤ 2 ^ (Q.natDegree * R.natDegree) *
        (Q.map (Int.castRingHom ℂ)).mahlerMeasure ^ R.natDegree *
        (R.map (Int.castRingHom ℂ)).mahlerMeasure ^ Q.natDegree * ‖Polynomial.aeval θ R‖ := by
  classical
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  set S := UniqueFactorizationMonoid.normalizedFactors P with hS
  have hirr : ∀ T ∈ S, Irreducible T := fun T hT =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor T hT
  -- `P = S.prod · C r` with `r` a unit
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hP0
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have hPS : P = S.prod * C r := by rw [hru]; exact hu.symm
  -- some irreducible factor is not constant; take one of least value at `θ`
  have hne : (S.filter fun T => 0 < T.natDegree).toFinset.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Multiset.toFinset_eq_empty,
      Multiset.filter_eq_nil] at hemp
    have h0 : (S.prod * C r).natDegree = 0 := by
      rw [natDegree_mul_C hr.ne_zero]
      refine Nat.eq_zero_of_le_zero ((natDegree_multiset_prod_le _).trans ?_)
      rw [Multiset.sum_eq_zero fun d hd => ?_]
      obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.1 hd
      exact Nat.eq_zero_of_not_pos (hemp T hT)
    rw [← hPS] at h0
    omega
  obtain ⟨Q, hQS', hmin⟩ := Finset.exists_min_image _ (fun T => ‖aeval θ T‖) hne
  obtain ⟨hQS, hQd⟩ := Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hQS')
  have hQirr := hirr Q hQS
  -- the cofactor
  set R₀ := (S.filter fun T => T ≠ Q).prod with hR₀
  have hprod : S.prod = Q ^ S.count Q * R₀ := by
    conv_lhs => rw [← Multiset.filter_add_not (fun T => T = Q) S]
    rw [Multiset.prod_add, Multiset.filter_eq', Multiset.prod_replicate]
  have hgood : Good Q θ R₀ := by
    refine Multiset.prod_induction (Good Q θ) _ (good_mul Q θ) ⟨one_ne_zero, by simp⟩
      fun T hT => ?_
    obtain ⟨hTS, hTQ⟩ := Multiset.mem_filter.1 hT
    have hT0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hTS
    rcases Nat.eq_zero_or_pos T.natDegree with hTd | hTd
    · rw [eq_C_of_natDegree_eq_zero hTd] at hT0 ⊢
      exact good_C Q θ fun h => hT0 (by rw [h, map_zero (C : ℤ →+* ℤ[X])])
    refine good_of_not_dvd Q T θ hQirr hQd hT0 (fun hd => hTQ ?_)
      (hmin T (Multiset.mem_toFinset.2 (Multiset.mem_filter.2 ⟨hTS, hTd⟩)))
    have hn := normalize_eq_normalize hd (hQirr.associated_of_dvd (hirr T hTS) hd).symm.dvd
    rwa [UniqueFactorizationMonoid.normalize_normalized_factor Q hQS,
      UniqueFactorizationMonoid.normalize_normalized_factor T hTS, eq_comm] at hn
  obtain ⟨-, hbound⟩ := good_mul Q θ R₀ (C r) hgood (good_C Q θ hr.ne_zero)
  exact ⟨Q, R₀ * C r, S.count Q, hQirr, hQd, Multiset.count_pos.2 hQS,
    by rw [hPS, hprod, mul_assoc], hbound⟩

#print axioms solution
