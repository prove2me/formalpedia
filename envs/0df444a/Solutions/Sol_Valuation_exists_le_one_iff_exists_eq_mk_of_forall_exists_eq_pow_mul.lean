-- Prove2me | solution 1 for Valuation.exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/17ef45b8-0121-5b0a-a9e3-eaf60f857d3f

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Valuation_exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul

set_option autoImplicit false

open WithZero

namespace LOCRING

variable {M : Type} [CommRing M] [IsDomain M] {K : Type} [Field K] (φ : M →+* K) (t : M)

theorem exp_unique (ht0 : t ≠ 0) (ht : φ t = 0) {n m : ℕ} {G G' : M} (hG : φ G ≠ 0) (hG' : φ G' ≠ 0)
    (h : t ^ n * G = t ^ m * G') : n = m := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  ·
    have h1 : t ^ n * G = t ^ n * (t ^ (m - n) * G') := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]; exact h
    have h2 : G = t ^ (m - n) * G' := mul_left_cancel₀ (pow_ne_zero n ht0) h1
    apply hG
    rw [h2, map_mul, map_pow, ht, zero_pow (Nat.sub_ne_zero_of_lt hlt), zero_mul]
  · have h1 : t ^ m * G' = t ^ m * (t ^ (n - m) * G) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]; exact h.symm
    have h2 : G' = t ^ (n - m) * G := mul_left_cancel₀ (pow_ne_zero m ht0) h1
    apply hG'
    rw [h2, map_mul, map_pow, ht, zero_pow (Nat.sub_ne_zero_of_lt hlt), zero_mul]

variable (hfac : ∀ F : M, F ≠ 0 → ∃ (n : ℕ) (G : M), F = t ^ n * G ∧ φ G ≠ 0)

noncomputable def ordT (F : M) : ℕ := by
  classical
  exact if hF : F = 0 then 0 else Classical.choose (hfac F hF)

theorem ordT_spec {F : M} (hF : F ≠ 0) : ∃ G : M, F = t ^ ordT φ t hfac F * G ∧ φ G ≠ 0 := by
  classical
  unfold ordT
  rw [dif_neg hF]
  exact Classical.choose_spec (hfac F hF)

theorem ordT_eq (ht0 : t ≠ 0) (ht : φ t = 0) {F : M} (hF : F ≠ 0) {n : ℕ} {G : M} (hG : φ G ≠ 0) (h : F = t ^ n * G) :
    ordT φ t hfac F = n := by
  obtain ⟨G', hF', hG'⟩ := ordT_spec φ t hfac hF
  exact exp_unique φ t ht0 ht hG' hG (hF'.symm.trans h)

theorem ordT_mul (ht0 : t ≠ 0) (ht : φ t = 0) {F F' : M} (hF : F ≠ 0) (hF' : F' ≠ 0) :
    ordT φ t hfac (F * F') = ordT φ t hfac F + ordT φ t hfac F' := by
  obtain ⟨G, h1, hG⟩ := ordT_spec φ t hfac hF
  obtain ⟨G', h2, hG'⟩ := ordT_spec φ t hfac hF'
  refine ordT_eq φ t hfac ht0 ht (mul_ne_zero hF hF') (G := G * G') ?_ ?_
  · rw [map_mul]; exact mul_ne_zero hG hG'
  · exact (congrArg₂ (· * ·) h1 h2).trans (by ring)

theorem min_le_ordT_add (ht0 : t ≠ 0) (ht : φ t = 0) {F F' : M} (hF : F ≠ 0) (hF' : F' ≠ 0) (hFF' : F + F' ≠ 0) :
    min (ordT φ t hfac F) (ordT φ t hfac F') ≤ ordT φ t hfac (F + F') := by
  obtain ⟨G, h1, hG⟩ := ordT_spec φ t hfac hF
  obtain ⟨G', h2, hG'⟩ := ordT_spec φ t hfac hF'
  obtain ⟨H, h3, hH⟩ := ordT_spec φ t hfac hFF'
  set n := ordT φ t hfac F
  set n' := ordT φ t hfac F'
  set k := ordT φ t hfac (F + F')
  set m := min n n'
  by_contra hlt
  push Not at hlt

  have hX : F + F' = t ^ m * (t ^ (n - m) * G + t ^ (n' - m) * G') := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, Nat.add_sub_cancel' (min_le_left n n'),
      Nat.add_sub_cancel' (min_le_right n n'), ← h1, ← h2]

  have h4 : t ^ k * H = t ^ k * (t ^ (m - k) * (t ^ (n - m) * G + t ^ (n' - m) * G')) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le, ← hX]; exact h3.symm
  have h5 : H = t ^ (m - k) * (t ^ (n - m) * G + t ^ (n' - m) * G') := mul_left_cancel₀ (pow_ne_zero k ht0) h4
  apply hH
  rw [h5, map_mul, map_pow, ht, zero_pow (Nat.sub_ne_zero_of_lt hlt), zero_mul]

noncomputable def val0 (ht0 : t ≠ 0) (ht : φ t = 0) : Valuation M ℤᵐ⁰ := by
  classical
  exact
  { toFun := fun F => if F = 0 then 0 else exp (-(ordT φ t hfac F : ℤ))
    map_zero' := by simp
    map_one' := by
      have h1 : (1 : M) ≠ 0 := one_ne_zero
      rw [if_neg h1, ordT_eq φ t hfac ht0 ht h1 (n := 0) (G := 1) (by rw [map_one]; exact one_ne_zero) (by ring)]
      simp
    map_mul' := fun F F' => by
      by_cases hF : F = 0
      · simp [hF]
      by_cases hF' : F' = 0
      · simp [hF']
      rw [if_neg (mul_ne_zero hF hF'), if_neg hF, if_neg hF', ordT_mul φ t hfac ht0 ht hF hF', ← exp_add]
      push_cast
      ring_nf
    map_add_le_max' := fun F F' => by
      by_cases hF : F = 0
      · simp [hF]
      by_cases hF' : F' = 0
      · simp [hF']
      by_cases hFF' : F + F' = 0
      · simp [hFF']
      rw [if_neg hFF', if_neg hF, if_neg hF']
      have := min_le_ordT_add φ t hfac ht0 ht hF hF' hFF'
      rw [le_max_iff, exp_le_exp, exp_le_exp]
      rcases min_le_iff.mp this with h | h
      · left; omega
      · right; omega }

theorem val0_apply (ht0 : t ≠ 0) (ht : φ t = 0) {F : M} (hF : F ≠ 0) :
    val0 φ t hfac ht0 ht F = exp (-(ordT φ t hfac F : ℤ)) := by
  classical
  show (if F = 0 then (0 : ℤᵐ⁰) else exp (-(ordT φ t hfac F : ℤ))) = _
  rw [if_neg hF]

theorem val0_ne_zero (ht0 : t ≠ 0) (ht : φ t = 0) {F : M} (hF : F ≠ 0) : val0 φ t hfac ht0 ht F ≠ 0 := by
  rw [val0_apply φ t hfac ht0 ht hF]; exact exp_ne_zero

theorem val0_eq_one_of (ht0 : t ≠ 0) (ht : φ t = 0) {F : M} (hF : φ F ≠ 0) : val0 φ t hfac ht0 ht F = 1 := by
  have hF0 : F ≠ 0 := fun h => hF (by rw [h, map_zero])
  rw [val0_apply φ t hfac ht0 ht hF0, ordT_eq φ t hfac ht0 ht hF0 (n := 0) hF (by ring)]
  simp

end LOCRING

namespace LOCRING

variable {M : Type} [CommRing M] [IsDomain M] {K : Type} [Field K] (φ : M →+* K) (t : M)
variable (hfac : ∀ F : M, F ≠ 0 → ∃ (n : ℕ) (G : M), F = t ^ n * G ∧ φ G ≠ 0) (ht0 : t ≠ 0) (ht : φ t = 0)

local notation "L" => FractionRing M

theorem alg_ne_zero {b : M} (hb : b ≠ 0) : algebraMap M L b ≠ 0 :=
  fun h => hb ((IsFractionRing.injective M L) (by rw [h, map_zero]))

theorem mk_eq_div (a b : M) (hb : b ∈ nonZeroDivisors M) :
    (Localization.mk a ⟨b, hb⟩ : L) = algebraMap M L a / algebraMap M L b := by
  rw [Localization.mk_eq_mk'_apply, IsFractionRing.mk'_eq_div]

theorem eq_of_div_eq {a b c d : M} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : algebraMap M L a / algebraMap M L b = algebraMap M L c / algebraMap M L d) : a * d = c * b := by
  rw [div_eq_div_iff (alg_ne_zero hb) (alg_ne_zero hd), ← map_mul, ← map_mul] at h
  exact IsFractionRing.injective M L h

theorem ne_zero_of_phi {b : M} (hb : φ b ≠ 0) : b ≠ 0 := fun h => hb (by rw [h, map_zero])

theorem hS : nonZeroDivisors M ≤ (val0 φ t hfac ht0 ht).supp.primeCompl := by
  intro s hs hmem
  exact val0_ne_zero φ t hfac ht0 ht (mem_nonZeroDivisors_iff_ne_zero.mp hs) ((Valuation.mem_supp_iff _ _).mp hmem)

noncomputable def val : Valuation L ℤᵐ⁰ :=
  (val0 φ t hfac ht0 ht).extendToLocalization (S := nonZeroDivisors M) (hS φ t hfac ht0 ht) L

theorem val_mk (a b : M) (hb : b ∈ nonZeroDivisors M) :
    val φ t hfac ht0 ht (Localization.mk a ⟨b, hb⟩) = val0 φ t hfac ht0 ht a * (val0 φ t hfac ht0 ht b)⁻¹ := by
  rw [Localization.mk_eq_mk'_apply]
  exact Valuation.extendToLocalization_mk' _ _ _ a ⟨b, hb⟩

theorem val_algebraMap (a : M) : val φ t hfac ht0 ht (algebraMap M L a) = val0 φ t hfac ht0 ht a :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ a

theorem val0_le_one (a : M) : val0 φ t hfac ht0 ht a ≤ 1 := by
  by_cases ha : a = 0
  · rw [ha, map_zero]; exact zero_le'
  · rw [val0_apply φ t hfac ht0 ht ha, ← exp_zero, exp_le_exp]; omega

theorem val_t : val φ t hfac ht0 ht (algebraMap M L t) = exp (-1) := by
  rw [val_algebraMap, val0_apply φ t hfac ht0 ht ht0,
    ordT_eq φ t hfac ht0 ht ht0 (n := 1) (G := 1) (by rw [map_one]; exact one_ne_zero) (by ring)]
  rfl

theorem val_le_one_iff (x : L) :
    val φ t hfac ht0 ht x ≤ 1 ↔ ∃ (a b : M) (hb : b ∈ nonZeroDivisors M), φ b ≠ 0 ∧ x = Localization.mk a ⟨b, hb⟩ := by
  constructor
  · intro hx
    obtain ⟨⟨a₀, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors M) x
    simp only at hx ⊢
    have hs0 : (s : M) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.2
    by_cases ha0 : a₀ = 0
    · refine ⟨0, 1, one_mem _, by rw [map_one]; exact one_ne_zero, ?_⟩
      rw [ha0, IsLocalization.mk'_zero, Localization.mk_zero]
    obtain ⟨G, hG1, hG⟩ := ordT_spec φ t hfac ha0
    obtain ⟨H, hH1, hH⟩ := ordT_spec φ t hfac hs0
    set n := ordT φ t hfac a₀ with hn
    set m := ordT φ t hfac (s : M) with hm

    have hx' : val φ t hfac ht0 ht (IsLocalization.mk' L a₀ s) = val0 φ t hfac ht0 ht a₀ * (val0 φ t hfac ht0 ht s)⁻¹ :=
      Valuation.extendToLocalization_mk' _ _ _ a₀ s
    rw [hx', val0_apply φ t hfac ht0 ht ha0, val0_apply φ t hfac ht0 ht hs0, ← exp_neg, neg_neg, ← exp_add, ← exp_zero,
      exp_le_exp] at hx
    have hmn : m ≤ n := by omega
    have hH0 : H ≠ 0 := ne_zero_of_phi φ hH
    refine ⟨t ^ (n - m) * G, H, mem_nonZeroDivisors_iff_ne_zero.mpr hH0, hH, ?_⟩
    rw [IsFractionRing.mk'_eq_div, mk_eq_div, div_eq_div_iff (alg_ne_zero hs0) (alg_ne_zero hH0), ← map_mul, ← map_mul]
    congr 1
    rw [hG1, hH1]
    conv_lhs => rw [← Nat.sub_add_cancel hmn]
    ring
  · rintro ⟨a, b, hb, hφb, rfl⟩
    rw [val_mk, val0_eq_one_of φ t hfac ht0 ht hφb, inv_one, mul_one]
    exact val0_le_one φ t hfac ht0 ht a

theorem val_mk_lt_one_iff (a b : M) (hb : b ∈ nonZeroDivisors M) (hφb : φ b ≠ 0) :
    val φ t hfac ht0 ht (Localization.mk a ⟨b, hb⟩) < 1 ↔ φ a = 0 := by
  rw [val_mk, val0_eq_one_of φ t hfac ht0 ht hφb, inv_one, mul_one]
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]; exact ⟨fun _ => rfl, fun _ => zero_lt_one⟩
  obtain ⟨G, hG1, hG⟩ := ordT_spec φ t hfac ha
  rw [val0_apply φ t hfac ht0 ht ha, ← exp_zero, exp_lt_exp]
  constructor
  · intro hlt
    rw [hG1, map_mul, map_pow, ht, zero_pow (by omega), zero_mul]
  · intro hφa
    by_contra hge
    have h0 : ordT φ t hfac a = 0 := by omega
    apply hG
    rw [hG1, h0, pow_zero, one_mul] at hφa
    exact hφa

theorem phi_div_eq {a b c d : M} (hφb : φ b ≠ 0) (hφd : φ d ≠ 0) (hb : b ∈ nonZeroDivisors M) (hd : d ∈ nonZeroDivisors M)
    (h : (Localization.mk a ⟨b, hb⟩ : L) = Localization.mk c ⟨d, hd⟩) : φ a / φ b = φ c / φ d := by
  rw [mk_eq_div, mk_eq_div] at h
  have h1 := eq_of_div_eq (ne_zero_of_phi φ hφb) (ne_zero_of_phi φ hφd) h
  rw [div_eq_div_iff hφb hφd, ← map_mul, ← map_mul, h1]

noncomputable def psiFun (x : ↥(val φ t hfac ht0 ht).valuationSubring) : K :=
  φ (Classical.choose ((val_le_one_iff φ t hfac ht0 ht x.1).mp x.2)) /
    φ (Classical.choose (Classical.choose_spec ((val_le_one_iff φ t hfac ht0 ht x.1).mp x.2)))

theorem psiFun_eq (x : ↥(val φ t hfac ht0 ht).valuationSubring) (a b : M) (hb : b ∈ nonZeroDivisors M) (hφb : φ b ≠ 0)
    (hx : (x : L) = Localization.mk a ⟨b, hb⟩) : psiFun φ t hfac ht0 ht x = φ a / φ b := by
  unfold psiFun
  set P := (val_le_one_iff φ t hfac ht0 ht x.1).mp x.2
  obtain ⟨hb', hφb', hx'⟩ := Classical.choose_spec (Classical.choose_spec P)
  exact phi_div_eq φ hφb' hφb _ hb (hx'.symm.trans hx)

theorem exists_rep (x : ↥(val φ t hfac ht0 ht).valuationSubring) :
    ∃ (a b : M) (hb : b ∈ nonZeroDivisors M), φ b ≠ 0 ∧ (x : L) = Localization.mk a ⟨b, hb⟩ :=
  (val_le_one_iff φ t hfac ht0 ht x.1).mp x.2

noncomputable def psi : ↥(val φ t hfac ht0 ht).valuationSubring →+* K where
  toFun := psiFun φ t hfac ht0 ht
  map_one' := by
    rw [psiFun_eq φ t hfac ht0 ht 1 1 1 (one_mem _) (by rw [map_one]; exact one_ne_zero)
      (by rw [OneMemClass.coe_one, ← Localization.mk_one]; rfl), div_self]
    rw [map_one]; exact one_ne_zero
  map_mul' := fun x y => by
    obtain ⟨a, b, hb, hφb, hx⟩ := exists_rep φ t hfac ht0 ht x
    obtain ⟨c, d, hd, hφd, hy⟩ := exists_rep φ t hfac ht0 ht y
    have hbd : φ (b * d) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hφb hφd
    rw [psiFun_eq φ t hfac ht0 ht x a b hb hφb hx, psiFun_eq φ t hfac ht0 ht y c d hd hφd hy,
      psiFun_eq φ t hfac ht0 ht (x * y) (a * c) (b * d) (Submonoid.mul_mem _ hb hd) hbd ?_]
    · rw [map_mul, map_mul, div_mul_div_comm]
    · rw [Subring.coe_mul, hx, hy, Localization.mk_mul]; rfl
  map_zero' := by
    rw [psiFun_eq φ t hfac ht0 ht 0 0 1 (one_mem _) (by rw [map_one]; exact one_ne_zero)
      (by rw [ZeroMemClass.coe_zero, Localization.mk_zero]), map_zero, zero_div]
  map_add' := fun x y => by
    obtain ⟨a, b, hb, hφb, hx⟩ := exists_rep φ t hfac ht0 ht x
    obtain ⟨c, d, hd, hφd, hy⟩ := exists_rep φ t hfac ht0 ht y
    have hbd : φ (b * d) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hφb hφd
    rw [psiFun_eq φ t hfac ht0 ht x a b hb hφb hx, psiFun_eq φ t hfac ht0 ht y c d hd hφd hy,
      psiFun_eq φ t hfac ht0 ht (x + y) (a * d + c * b) (b * d) (Submonoid.mul_mem _ hb hd) hbd ?_]
    · rw [map_add, map_mul, map_mul, map_mul, div_add_div _ _ hφb hφd]; ring
    · rw [Subring.coe_add, hx, hy, mk_eq_div, mk_eq_div, mk_eq_div,
        div_add_div _ _ (alg_ne_zero (ne_zero_of_phi φ hφb)) (alg_ne_zero (ne_zero_of_phi φ hφd))]
      simp only [map_add, map_mul]; ring

end LOCRING

theorem solution
    (M : Type) [CommRing M] [IsDomain M] (K : Type) [Field K] (φ : M →+* K) (t : M) (ht0 : t ≠ 0) (ht : φ t = 0)
    (hfac : ∀ F : M, F ≠ 0 → ∃ (n : ℕ) (G : M), F = t ^ n * G ∧ φ G ≠ 0) :
    ∃ v : Valuation (FractionRing M) ℤᵐ⁰,
      (∀ x : FractionRing M, v x ≤ 1 ↔
        ∃ (a b : M) (hb : b ∈ nonZeroDivisors M), φ b ≠ 0 ∧ x = Localization.mk a ⟨b, hb⟩) ∧
      (∀ (a b : M) (hb : b ∈ nonZeroDivisors M), φ b ≠ 0 →
        (v (Localization.mk a ⟨b, hb⟩ : FractionRing M) < 1 ↔ φ a = 0)) ∧
      v (algebraMap M (FractionRing M) t) = exp (-1) ∧
      ∃ ψ : ↥v.valuationSubring →+* K, ∀ (x : ↥v.valuationSubring) (a b : M) (hb : b ∈ nonZeroDivisors M), φ b ≠ 0 →
        (x : FractionRing M) = Localization.mk a ⟨b, hb⟩ → ψ x = φ a / φ b :=
  ⟨LOCRING.val φ t hfac ht0 ht, LOCRING.val_le_one_iff φ t hfac ht0 ht, LOCRING.val_mk_lt_one_iff φ t hfac ht0 ht,
    LOCRING.val_t φ t hfac ht0 ht, LOCRING.psi φ t hfac ht0 ht,
    fun x a b hb hφb hx => LOCRING.psiFun_eq φ t hfac ht0 ht x a b hb hφb hx⟩

end S_Valuation_exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul
end P2MW
export P2MW.S_Valuation_exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul (solution)
