-- Prove2me | solution 1 for ValuationSubring.exists_valuation_mul_eq_one_of_forall_sup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e169acd4-5cc1-51bb-a7de-42b4c8464812

import Mathlib
import Theorems.Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_valuation_mul_eq_one_of_forall_sup_eq_top

namespace ValuationSubring
p2m_export "ValuationSubring" "comap mem_comap ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff mem_or_inv_mem' mem_top one_mem mem_or_inv_mem valuation_lt_one_iff valuation_le_one_iff valuation valuation_eq_one_iff exists_forall_mem_and_sub_mem_nonunits"
namespace IndepMember
p2m_open "ValuationSubring"

open IsLocalRing

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F']

theorem mul_lt_one_aux {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a b : Γ₀}
    (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
  calc a * b ≤ 1 * b := mul_le_mul' ha le_rfl
    _ = b := one_mul b
    _ < 1 := hb

section Over

variable {O : ValuationSubring F} {V : ValuationSubring F'}
  (hV : V.comap (algebraMap F F') = O)
include hV

theorem mem_iff (x : F) : algebraMap F F' x ∈ V ↔ x ∈ O := by
  rw [← ValuationSubring.mem_comap (A := V) (f := algebraMap F F'), hV]

theorem lt_one_iff (x : F) : V.valuation (algebraMap F F' x) < 1 ↔ O.valuation x < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, map_eq_zero,
    ← map_inv₀, mem_iff hV]

theorem le_one {x : F} (hx : x ∈ O) : V.valuation (algebraMap F F' x) ≤ 1 :=
  (V.valuation_le_one_iff _).mpr ((mem_iff hV x).mpr hx)

theorem eq_one_iff (x : F) : V.valuation (algebraMap F F' x) = 1 ↔ O.valuation x = 1 := by
  constructor
  · intro h
    have hle : O.valuation x ≤ 1 :=
      (O.valuation_le_one_iff x).mpr ((mem_iff hV x).mp ((V.valuation_le_one_iff _).mp h.le))
    have hnlt : ¬ O.valuation x < 1 := fun hlt => (ne_of_lt ((lt_one_iff hV x).mpr hlt)) h
    exact le_antisymm hle (not_lt.mp hnlt)
  · intro h
    have hle : V.valuation (algebraMap F F' x) ≤ 1 :=
      (V.valuation_le_one_iff _).mpr ((mem_iff hV x).mpr ((O.valuation_le_one_iff x).mp h.le))
    have hnlt : ¬ V.valuation (algebraMap F F' x) < 1 := fun hlt =>
      (ne_of_lt ((lt_one_iff hV x).mp hlt)) h
    exact le_antisymm hle (not_lt.mp hnlt)

end Over

section Incomparable

variable {O : ValuationSubring F} {V W : ValuationSubring F'}

theorem valuation_eq_one_of_le (hVW : V ≤ W) {u : F'} (hu : V.valuation u = 1) :
    W.valuation u = 1 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu
    exact zero_ne_one hu
  have h1 : W.valuation u ≤ 1 :=
    (W.valuation_le_one_iff u).mpr (hVW ((V.valuation_le_one_iff u).mp hu.le))
  have h2 : W.valuation u⁻¹ ≤ 1 :=
    (W.valuation_le_one_iff u⁻¹).mpr (hVW ((V.valuation_le_one_iff u⁻¹).mp
      (by rw [map_inv₀, hu, inv_one])))
  rw [map_inv₀] at h2
  have hne : W.valuation u ≠ 0 := (Valuation.ne_zero_iff _).mpr hu0
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr hne)).mp h2)

theorem sum_ne_zero (hV : V.comap (algebraMap F F') = O) (hW : W.comap (algebraMap F F') = O)
    (hVW : V ≤ W) {y : F'} (hyV : V.valuation y < 1) (hyW : W.valuation y = 1)
    (c : ℕ → F) (hc : ∀ k, c k ∈ O) {j N : ℕ} (hjN : j < N) (hj : O.valuation (c j) = 1)
    (hlow : ∀ k < j, O.valuation (c k) < 1) :
    ∑ k ∈ Finset.range N, algebraMap F F' (c k) * y ^ k ≠ 0 := by
  intro hsum
  set t : ℕ → F' := fun k => algebraMap F F' (c k) * y ^ k with ht
  set H : F' := ∑ k ∈ Finset.Ico j N, algebraMap F F' (c k) * y ^ (k - j) with hH
  have hhigh : ∑ k ∈ Finset.Ico j N, t k = y ^ j * H := by
    rw [hH, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hjk : j ≤ k := (Finset.mem_Ico.mp hk).1
    have hyk : y ^ k = y ^ j * y ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hjk]
    simp only [ht, hyk]
    ring
  have hHV : V.valuation H = 1 := by
    rw [hH, Finset.sum_eq_sum_Ico_succ_bot hjN, Nat.sub_self, pow_zero, mul_one]
    have hrest : V.valuation
        (∑ k ∈ Finset.Ico (j + 1) N, algebraMap F F' (c k) * y ^ (k - j)) < 1 := by
      refine Valuation.map_sum_lt _ one_ne_zero fun k hk => ?_
      have hjk : j + 1 ≤ k := (Finset.mem_Ico.mp hk).1
      rw [map_mul, map_pow]
      refine mul_lt_one_aux (le_one hV (hc k)) ?_
      exact pow_lt_one₀ zero_le' hyV (by omega)
    have hcj : V.valuation (algebraMap F F' (c j)) = 1 := (eq_one_iff hV _).mpr hj
    rw [Valuation.map_add_eq_of_lt_left V.valuation (lt_of_lt_of_eq hrest hcj.symm), hcj]
  have hHW : W.valuation (y ^ j * H) = 1 := by
    rw [map_mul, map_pow, hyW, one_pow, one_mul]
    exact valuation_eq_one_of_le hVW hHV
  have hlowW : W.valuation (∑ k ∈ Finset.range j, t k) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun k hk => ?_
    have hkj : k < j := Finset.mem_range.mp hk
    simp only [ht]
    rw [map_mul, map_pow, hyW, one_pow, mul_one]
    exact (lt_one_iff hW _).mpr (hlow k hkj)
  have hsplit : ∑ k ∈ Finset.range N, t k =
      ∑ k ∈ Finset.range j, t k + ∑ k ∈ Finset.Ico j N, t k :=
    (Finset.sum_range_add_sum_Ico t hjN.le).symm
  have hsum' : ∑ k ∈ Finset.range N, t k = 0 := hsum
  rw [hsplit, hhigh] at hsum'
  have heq : y ^ j * H = -∑ k ∈ Finset.range j, t k := by linear_combination hsum'
  rw [heq, Valuation.map_neg] at hHW
  rw [hHW] at hlowW
  exact lt_irrefl 1 hlowW

theorem eq_of_le [Algebra.IsAlgebraic F F'] (hV : V.comap (algebraMap F F') = O)
    (hW : W.comap (algebraMap F F') = O) (hVW : V ≤ W) : V = W := by
  classical
  refine le_antisymm hVW fun x hxW => ?_
  by_contra hxV
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxV (zero_mem V)
  set y : F' := x⁻¹ with hy
  have hyV : y ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
  have hyV1 : V.valuation y < 1 := by
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
    right
    rw [hy, inv_inv]
    exact hxV
  have hyW1 : W.valuation y = 1 := by
    have h1 : W.valuation x ≤ 1 := (W.valuation_le_one_iff x).mpr hxW
    have h2 : W.valuation y ≤ 1 := (W.valuation_le_one_iff y).mpr (hVW hyV)
    rw [hy, map_inv₀] at h2 ⊢
    have hne : W.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    have h3 : 1 ≤ W.valuation x := (inv_le_one₀ (zero_lt_iff.mpr hne)).mp h2
    rw [le_antisymm h1 h3, inv_one]
  obtain ⟨p, hp0, hpy⟩ := Algebra.IsAlgebraic.isAlgebraic (R := F) y
  obtain ⟨k0, hk0, hmax⟩ := Finset.exists_max_image p.support
    (fun k => O.valuation (p.coeff k)) (Polynomial.support_nonempty.mpr hp0)
  have hc0 : p.coeff k0 ≠ 0 := Polynomial.mem_support_iff.mp hk0
  have hv0 : O.valuation (p.coeff k0) ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
  set c : ℕ → F := fun k => (p.coeff k0)⁻¹ * p.coeff k with hc
  have hcO : ∀ k, c k ∈ O := by
    intro k
    rw [← O.valuation_le_one_iff]
    simp only [hc, map_mul, map_inv₀]
    by_cases hk : k ∈ p.support
    · calc (O.valuation (p.coeff k0))⁻¹ * O.valuation (p.coeff k)
          ≤ (O.valuation (p.coeff k0))⁻¹ * O.valuation (p.coeff k0) :=
            mul_le_mul' le_rfl (hmax k hk)
        _ = 1 := inv_mul_cancel₀ hv0
    · rw [Polynomial.notMem_support_iff.mp hk, map_zero, mul_zero]
      exact zero_le'
  have hck0 : O.valuation (c k0) = 1 := by
    simp only [hc, map_mul, map_inv₀]
    exact inv_mul_cancel₀ hv0
  have hex : ∃ k, O.valuation (c k) = 1 := ⟨k0, hck0⟩
  set j := Nat.find hex with hjdef
  have hj : O.valuation (c j) = 1 := Nat.find_spec hex
  have hlow : ∀ k < j, O.valuation (c k) < 1 := fun k hk =>
    lt_of_le_of_ne ((O.valuation_le_one_iff _).mpr (hcO k)) (Nat.find_min hex hk)
  have hcj0 : c j ≠ 0 := by
    intro h
    rw [h, map_zero] at hj
    exact zero_ne_one hj
  have hpj : p.coeff j ≠ 0 := by
    intro h
    apply hcj0
    simp only [hc, h, mul_zero]
  have hjN : j < p.natDegree + 1 := Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hpj)
  have hrel : ∑ k ∈ Finset.range (p.natDegree + 1), algebraMap F F' (c k) * y ^ k = 0 := by
    have h := hpy
    rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_self _) y] at h
    have hfac : ∑ k ∈ Finset.range (p.natDegree + 1), algebraMap F F' (c k) * y ^ k =
        algebraMap F F' (p.coeff k0)⁻¹ *
          ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • y ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hc, map_mul, Algebra.smul_def, mul_assoc]
    rw [hfac, h, mul_zero]
  exact sum_ne_zero hV hW hVW hyV1 hyW1 c hcO hjN hj hlow hrel

end Incomparable

section Nagata

theorem pow_eq_self_of_orderOf_dvd {M : Type*} [Monoid M] (u : M) {D : ℕ}
    (hD : orderOf u ∣ D) (N : ℕ) : u ^ (1 + N * D) = u := by
  have h1 : u ^ D = 1 := orderOf_dvd_iff_pow_eq_one.mp hD
  rw [pow_add, pow_one, pow_mul', h1, one_pow, mul_one]

theorem eq_of_pow_eq_pow_of_not_isOfFinOrder {κ : Type*} [Field κ] {u : κ} (hu : u ≠ 0)
    (hfin : ¬ IsOfFinOrder u) {a b : ℕ} (h : u ^ a = u ^ b) : a = b := by
  wlog hab : a ≤ b generalizing a b
  · exact (this h.symm (le_of_not_ge hab)).symm
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add] at h
  have hc : u ^ c = 1 := by
    have h' : u ^ a * u ^ c = u ^ a * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel₀ (pow_ne_zero a hu) h'
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · omega
  · exact absurd (isOfFinOrder_iff_pow_eq_one.mpr ⟨c, hpos, hc⟩) hfin

theorem exists_exponent {ι : Type*} [Fintype ι] (κ : ι → Type*) [∀ j, Field (κ j)]
    (u : ∀ j, κ j) (hu : ∀ j, u j ≠ 0) :
    ∃ m : ℕ, 2 ≤ m ∧ ∀ j, 1 - u j + u j ^ m ≠ 0 := by
  classical
  let d : ι → ℕ := fun j => if IsOfFinOrder (u j) then orderOf (u j) else 1
  set D : ℕ := ∏ j, d j with hDdef
  have hDpos : 0 < D := Finset.prod_pos fun j _ => by
    simp only [d]
    split_ifs with h
    · exact h.orderOf_pos
    · exact one_pos
  have hdvd : ∀ j, IsOfFinOrder (u j) → orderOf (u j) ∣ D := fun j hj => by
    have h := Finset.dvd_prod_of_mem d (Finset.mem_univ j)
    simpa [d, hj] using h
  let m : ℕ → ℕ := fun N => 1 + (N + 1) * D
  have hm2 : ∀ N, 2 ≤ m N := fun N => by
    show 2 ≤ 1 + (N + 1) * D
    nlinarith
  have hminj : ∀ N N', m N = m N' → N = N' := fun N N' h => by
    have h' : (N + 1) * D = (N' + 1) * D := by
      change 1 + (N + 1) * D = 1 + (N' + 1) * D at h; omega
    have := Nat.eq_of_mul_eq_mul_right hDpos h'
    omega
  have htors : ∀ j, IsOfFinOrder (u j) → ∀ N, 1 - u j + u j ^ m N ≠ 0 := fun j hj N => by
    have h : u j ^ m N = u j := pow_eq_self_of_orderOf_dvd (u j) (hdvd j hj) (N + 1)
    rw [h, sub_add_cancel]
    exact one_ne_zero
  have hnt : ∀ j, ¬ IsOfFinOrder (u j) → ∀ N N',
      1 - u j + u j ^ m N = 0 → 1 - u j + u j ^ m N' = 0 → N = N' := by
    intro j hj N N' h1 h2
    apply hminj
    apply eq_of_pow_eq_pow_of_not_isOfFinOrder (hu j) hj
    have e1 : u j ^ m N = u j - 1 := by linear_combination h1
    have e2 : u j ^ m N' = u j - 1 := by linear_combination h2
    rw [e1, e2]
  by_contra hcon
  push Not at hcon
  have hex : ∀ N : Fin (Fintype.card ι + 1), ∃ j, 1 - u j + u j ^ m N = 0 :=
    fun N => hcon (m N) (hm2 N)
  choose f hf using hex
  obtain ⟨N, N', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  by_cases hj : IsOfFinOrder (u (f N))
  · exact htors _ hj N (hf N)
  · have h2 : 1 - u (f N) + u (f N) ^ m N' = 0 := by rw [heq]; exact hf N'
    exact hne (Fin.ext (hnt _ hj N N' (hf N) h2))

variable {K : Type*} [Field K] {ι : Type*}

theorem exists_mul_mem_forall [Fintype ι] (R : ι → ValuationSubring K) (x : K) :
    ∃ t : K, (∀ j, t ∈ R j) ∧ (∀ j, t * x ∈ R j) ∧
      (∀ j, x ∈ R j → (R j).valuation t = 1) := by
  classical

  let u : ∀ j, ResidueField (R j) := fun j =>
    if h : (R j).valuation x = 1 then
      IsLocalRing.residue (R j) ⟨x, ((R j).valuation_le_one_iff x).mp h.le⟩ else 1
  have hu : ∀ j, u j ≠ 0 := fun j => by
    by_cases h : (R j).valuation x = 1
    · simp only [u, dif_pos h]
      rw [ne_eq, residue_eq_zero_iff, valuation_lt_one_iff]
      exact fun hlt => hlt.ne h
    · simp only [u, dif_neg h]; exact one_ne_zero
  obtain ⟨m, hm2, hm⟩ := exists_exponent (fun j => ResidueField (R j)) u hu
  set P : K := 1 - x + x ^ m with hP

  have hA : ∀ j, x ∈ R j → (R j).valuation P = 1 := by
    intro j hxj
    rcases lt_or_eq_of_le (((R j).valuation_le_one_iff x).mpr hxj) with hlt | heq
    · have h1 : (R j).valuation (x ^ m - x) < 1 := by
        apply Valuation.map_sub_lt
        · rw [map_pow]; exact pow_lt_one₀ zero_le' hlt (by omega)
        · exact hlt
      have : P = 1 + (x ^ m - x) := by rw [hP]; ring
      rw [this]
      exact Valuation.map_one_add_of_lt _ h1
    · set xj : R j := ⟨x, hxj⟩ with hxjdef
      have hPj : P = ((1 - xj + xj ^ m : R j) : K) := by rw [hP]; push_cast; rfl
      rw [hPj]
      apply ((R j).valuation_eq_one_iff _).mp
      rw [← residue_ne_zero_iff_isUnit]
      have hres : IsLocalRing.residue (R j) xj = u j := by
        simp only [u, dif_pos heq]
        rfl
      rw [map_add, map_sub, map_one, map_pow, hres]
      exact hm j

  have hB : ∀ j, x ∉ R j → (R j).valuation P⁻¹ < 1 ∧ (R j).valuation (P⁻¹ * x) < 1 := by
    intro j hxj
    have hx0 : x ≠ 0 := by rintro rfl; exact hxj (zero_mem _)
    have hy : x⁻¹ ∈ R j := ((R j).mem_or_inv_mem x).resolve_left hxj
    have hylt : (R j).valuation x⁻¹ < 1 := by
      rcases lt_or_eq_of_le (((R j).valuation_le_one_iff _).mpr hy) with h | h
      · exact h
      · exfalso; apply hxj
        rw [← (R j).valuation_le_one_iff]
        rw [map_inv₀, inv_eq_one] at h
        exact h.le
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    set Q : K := 1 + (x⁻¹ ^ (n + 2) - x⁻¹ ^ (n + 1)) with hQ
    have hQv : (R j).valuation Q = 1 := by
      apply Valuation.map_one_add_of_lt
      apply Valuation.map_sub_lt
      · rw [map_pow]; exact pow_lt_one₀ zero_le' hylt (by omega)
      · rw [map_pow]; exact pow_lt_one₀ zero_le' hylt (by omega)
    have h1 : x ^ (n + 2) * x⁻¹ ^ (n + 2) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hx0, one_pow]
    have h2 : x ^ (n + 2) * x⁻¹ ^ (n + 1) = x := by
      rw [pow_succ, mul_comm (x ^ (n + 1)) x, mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0, one_pow,
        mul_one]
    have h3 : x⁻¹ ^ (n + 2) * x = x⁻¹ ^ (n + 1) := by
      rw [pow_succ, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
    have hPQ : P = x ^ (n + 2) * Q := by
      rw [hP, hQ]
      linear_combination (-1 : K) * h1 + h2
    have ht : P⁻¹ = x⁻¹ ^ (n + 2) * Q⁻¹ := by
      rw [hPQ, mul_inv, ← inv_pow]
    have htx : P⁻¹ * x = x⁻¹ ^ (n + 1) * Q⁻¹ := by
      rw [ht, mul_right_comm, h3]
    refine ⟨?_, ?_⟩
    · rw [ht, map_mul, map_inv₀, hQv, inv_one, mul_one, map_pow]
      exact pow_lt_one₀ zero_le' hylt (by omega)
    · rw [htx, map_mul, map_inv₀, hQv, inv_one, mul_one, map_pow]
      exact pow_lt_one₀ zero_le' hylt (by omega)
  refine ⟨P⁻¹, fun j => ?_, fun j => ?_, fun j hxj => ?_⟩
  · by_cases hxj : x ∈ R j
    · rw [← (R j).valuation_le_one_iff, map_inv₀, hA j hxj, inv_one]
    · rw [← (R j).valuation_le_one_iff]; exact (hB j hxj).1.le
  · by_cases hxj : x ∈ R j
    · rw [← (R j).valuation_le_one_iff, map_mul, map_inv₀, hA j hxj, inv_one, one_mul]
      exact ((R j).valuation_le_one_iff x).mpr hxj
    · rw [← (R j).valuation_le_one_iff]; exact (hB j hxj).2.le
  · rw [map_inv₀, hA j hxj, inv_one]

end Nagata

section Indep

variable {K : Type*} [Field K]

def locAt (A : ValuationSubring K) (D : Set K) : ValuationSubring K where
  carrier := {x | ∀ d ∈ D, A.valuation d < 1 → ∀ n : ℕ, A.valuation (d * x ^ n) < 1}
  mul_mem' := by
    intro x y hx hy d hdD hd n
    have key : ∀ x y : K, A.valuation x ≤ A.valuation y →
        (∀ n : ℕ, A.valuation (d * y ^ n) < 1) → A.valuation (d * (x * y) ^ n) < 1 := by
      intro x y h hy'
      calc A.valuation (d * (x * y) ^ n)
          = A.valuation d * (A.valuation x ^ n * A.valuation y ^ n) := by
            rw [map_mul, mul_pow, map_mul, map_pow, map_pow]
        _ ≤ A.valuation d * (A.valuation y ^ n * A.valuation y ^ n) := by
            gcongr
        _ = A.valuation (d * y ^ (2 * n)) := by
            rw [map_mul, map_pow, two_mul, pow_add]
        _ < 1 := hy' (2 * n)
    rcases le_total (A.valuation x) (A.valuation y) with h | h
    · exact key x y h (hy d hdD hd)
    · rw [mul_comm x y]; exact key y x h (hx d hdD hd)
  one_mem' := by
    intro d _ hd n
    simpa using hd
  add_mem' := by
    intro x y hx hy d hdD hd n
    have key : ∀ x y : K, A.valuation x ≤ A.valuation y →
        (∀ n : ℕ, A.valuation (d * y ^ n) < 1) → A.valuation (d * (x + y) ^ n) < 1 := by
      intro x y h hy'
      have hxy : A.valuation (x + y) ≤ A.valuation y :=
        (Valuation.map_add _ _ _).trans (max_le h le_rfl)
      calc A.valuation (d * (x + y) ^ n)
          = A.valuation d * A.valuation (x + y) ^ n := by rw [map_mul, map_pow]
        _ ≤ A.valuation d * A.valuation y ^ n := by gcongr
        _ = A.valuation (d * y ^ n) := by rw [map_mul, map_pow]
        _ < 1 := hy' n
    rcases le_total (A.valuation x) (A.valuation y) with h | h
    · exact key x y h (hy d hdD hd)
    · rw [add_comm x y]; exact key y x h (hx d hdD hd)
  zero_mem' := by
    intro d _ hd n
    cases n with
    | zero => simpa using hd
    | succ n => simp
  neg_mem' := by
    intro x hx d hdD hd n
    have h := hx d hdD hd n
    have e : A.valuation (d * (-x) ^ n) = A.valuation (d * x ^ n) := by
      rw [map_mul, map_mul, map_pow, map_pow, Valuation.map_neg]
    rwa [e]
  mem_or_inv_mem' := by
    intro x
    by_contra h
    rw [not_or] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Set.mem_setOf_eq, not_forall, not_lt, exists_prop] at h1 h2
    obtain ⟨d, -, hd, n, hn⟩ := h1
    obtain ⟨d', -, hd', n', hn'⟩ := h2
    have one_lt : ∀ (d z : K) (n : ℕ), A.valuation d < 1 → 1 ≤ A.valuation (d * z ^ n) →
        1 < A.valuation z := by
      intro d z n hd hn
      by_contra hz
      rw [not_lt] at hz
      have : A.valuation (d * z ^ n) < 1 := by
        rw [map_mul, map_pow]
        calc A.valuation d * A.valuation z ^ n ≤ A.valuation d * 1 := by
              gcongr; exact pow_le_one₀ zero_le' hz
          _ < 1 := by rw [mul_one]; exact hd
      exact (lt_irrefl _) (lt_of_le_of_lt hn this)
    have hx1 := one_lt d x n hd hn
    have hx2 := one_lt d' x⁻¹ n' hd' hn'
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx1
      exact not_lt_zero hx1
    rw [map_inv₀] at hx2
    have : A.valuation x < 1 := by
      have h := one_lt_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)) |>.mp hx2
      exact h
    exact lt_irrefl _ (hx1.trans this)

theorem mem_locAt_iff (A : ValuationSubring K) (D : Set K) (x : K) :
    x ∈ locAt A D ↔ ∀ d ∈ D, A.valuation d < 1 → ∀ n : ℕ, A.valuation (d * x ^ n) < 1 :=
  Iff.rfl

theorem le_locAt (A : ValuationSubring K) (D : Set K) : A ≤ locAt A D := by
  intro x hx d _ hd n
  rw [map_mul, map_pow]
  calc A.valuation d * A.valuation x ^ n ≤ A.valuation d * 1 := by
        gcongr
        exact pow_le_one₀ zero_le' ((A.valuation_le_one_iff x).mpr hx)
    _ < 1 := by rw [mul_one]; exact hd

theorem inv_not_mem_locAt (A : ValuationSubring K) {D : Set K} {d : K} (hdD : d ∈ D)
    (hd : A.valuation d < 1) (hd0 : d ≠ 0) : d⁻¹ ∉ locAt A D := by
  intro h
  have := h d hdD hd 1
  rw [pow_one, mul_inv_cancel₀ hd0, map_one] at this
  exact lt_irrefl 1 this

theorem exists_le_and_one_le (P₀ P : ValuationSubring K) (hsup : P₀ ⊔ P = ⊤) {d : K}
    (hd0 : d ≠ 0) (hd : P₀.valuation d < 1) :
    ∃ y : K, y ≠ 0 ∧ P₀.valuation y ≤ P₀.valuation d ∧ 1 ≤ P.valuation y := by
  set R := locAt P₀ {d} with hR
  have hPR : ¬ P ≤ R := by
    intro h
    have htop : (⊤ : ValuationSubring K) ≤ R := hsup ▸ sup_le (le_locAt P₀ {d}) h
    exact inv_not_mem_locAt P₀ (Set.mem_singleton d) hd hd0 (htop (mem_top _))
  obtain ⟨w, hwP, hwR⟩ := Set.not_subset.mp hPR
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hwR (zero_mem R)
  rw [SetLike.mem_coe, mem_locAt_iff] at hwR
  simp only [Set.mem_singleton_iff, forall_eq, hd, forall_true_left, not_forall, not_lt] at hwR
  obtain ⟨n, hn⟩ := hwR
  refine ⟨(w ^ n)⁻¹, inv_ne_zero (pow_ne_zero n hw0), ?_, ?_⟩
  · have hwn : P₀.valuation (w ^ n) ≠ 0 := (Valuation.ne_zero_iff _).mpr (pow_ne_zero n hw0)
    rw [map_inv₀]
    calc (P₀.valuation (w ^ n))⁻¹ = (P₀.valuation (w ^ n))⁻¹ * 1 := (mul_one _).symm
      _ ≤ (P₀.valuation (w ^ n))⁻¹ * P₀.valuation (d * w ^ n) := by gcongr
      _ = P₀.valuation d := by
          rw [map_mul, mul_comm, mul_assoc, mul_inv_cancel₀ hwn, mul_one]
  · rw [map_inv₀, map_pow]
    have h1 : P.valuation w ^ n ≤ 1 := pow_le_one₀ zero_le' ((P.valuation_le_one_iff w).mpr hwP)
    have h0 : P.valuation w ^ n ≠ 0 := pow_ne_zero n ((Valuation.ne_zero_iff _).mpr hw0)
    exact (one_le_inv₀ (zero_lt_iff.mpr h0)).mpr h1

theorem exists_deep {ι : Type*} [Fintype ι] (R : ι → ValuationSubring K) (i₀ i : ι)
    (hsup : R i₀ ⊔ R i = ⊤) {d : K} (hd0 : d ≠ 0) (hd : (R i₀).valuation d < 1) :
    ∃ t : K, (∀ j, t ∈ R j) ∧ (R i).valuation t = 1 ∧
      (R i₀).valuation t ≤ (R i₀).valuation d := by
  obtain ⟨y, hy0, hy₀, hyi⟩ := exists_le_and_one_le (R i₀) (R i) hsup hd0 hd

  have hnorm : ∃ y' : K, y' ≠ 0 ∧ (R i).valuation y' = 1 ∧
      (R i₀).valuation y' ≤ (R i₀).valuation d := by
    rcases hyi.eq_or_lt with h | h
    · exact ⟨y, hy0, h.symm, hy₀⟩
    · have h1y : (R i).valuation (y + 1) = (R i).valuation y :=
        Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact h)
      have hy1 : y + 1 ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h1y
        exact hy0 ((Valuation.zero_iff _).mp h1y.symm)
      have h1y₀ : (R i₀).valuation (y + 1) = 1 := by
        rw [add_comm]
        exact Valuation.map_one_add_of_lt _ (lt_of_le_of_lt hy₀ hd)
      refine ⟨y * (y + 1)⁻¹, mul_ne_zero hy0 (inv_ne_zero hy1), ?_, ?_⟩
      · rw [map_mul, map_inv₀, h1y, mul_inv_cancel₀]
        exact (Valuation.ne_zero_iff _).mpr hy0
      · rw [map_mul, map_inv₀, h1y₀, inv_one, mul_one]
        exact hy₀
  obtain ⟨y', hy'0, hy'i, hy'₀⟩ := hnorm
  have hy'mem₀ : y' ∈ R i₀ := ((R i₀).valuation_le_one_iff _).mp (hy'₀.trans hd.le)
  have hy'memi : y' ∈ R i := ((R i).valuation_le_one_iff _).mp hy'i.le
  obtain ⟨t, ht, hty, htu⟩ := exists_mul_mem_forall R y'
  refine ⟨t * y', hty, ?_, ?_⟩
  · rw [map_mul, htu i hy'memi, hy'i, one_mul]
  · rw [map_mul, htu i₀ hy'mem₀, one_mul]
    exact hy'₀

end Indep

section Counting

theorem valuation_sum_eq_one_of_sub {O : ValuationSubring F} {V : ValuationSubring F'}
    (hV : V.comap (algebraMap F F') = O) {σ : Type*} (s : Finset σ) (a : σ → F)
    (ha : ∀ i, a i ∈ O) (ω ω' : σ → F') (hωω' : ∀ i ∈ s, a i ≠ 0 → V.valuation (ω' i - ω i) < 1)
    (h : V.valuation (∑ i ∈ s, algebraMap F F' (a i) * ω i) = 1) :
    V.valuation (∑ i ∈ s, algebraMap F F' (a i) * ω' i) = 1 := by
  have e : ∑ i ∈ s, algebraMap F F' (a i) * ω' i =
      ∑ i ∈ s, algebraMap F F' (a i) * ω i + ∑ i ∈ s, algebraMap F F' (a i) * (ω' i - ω i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, Valuation.map_add_eq_of_lt_left, h]
  rw [h]
  refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
  by_cases hai : a i = 0
  · rw [hai, map_zero, zero_mul, map_zero]; exact zero_lt_one
  · rw [map_mul]
    exact mul_lt_one_aux (le_one hV (ha i)) (hωω' i hi hai)

variable [FiniteDimensional F F']

theorem exists_valuation_mul_eq_one_of_forall_sup_eq_top
    (Q : ValuationSubring F) (S : Finset (ValuationSubring F'))
    (hS : ∀ P ∈ S, P.comap (algebraMap F F') = Q)
    {σ : Type*} [Fintype σ] (cls : σ → ValuationSubring F') (hcls : ∀ s, cls s ∈ S)
    (ω : σ → F') (hω : ∀ s, ω s ∈ cls s)
    (hind : ∀ P ∈ S, ∀ a : σ → F, (∀ s, a s ∈ Q) → (∀ s, cls s ≠ P → a s = 0) →
      (∃ s, Q.valuation (a s) = 1) → P.valuation (∑ s, algebraMap F F' (a s) * ω s) = 1)
    (hcard : Module.finrank F F' ≤ Fintype.card σ)
    (P₀ : ValuationSubring F') (hP₀ : P₀ ∈ S) (hindep : ∀ P ∈ S, P ≠ P₀ → P₀ ⊔ P = ⊤)
    (g : F') (hg : g ≠ 0) :
    ∃ h : F, P₀.valuation (algebraMap F F' h * g) = 1 := by
  classical

  suffices key : ∀ g : F', g ≠ 0 → P₀.valuation g < 1 →
      ∃ h : F, P₀.valuation (algebraMap F F' h * g) = 1 by
    rcases lt_trichotomy (P₀.valuation g) 1 with h | h | h
    · exact key g hg h
    · exact ⟨1, by rw [map_one, one_mul]; exact h⟩
    · have hg' : P₀.valuation g⁻¹ < 1 := by
        rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h
      obtain ⟨h', hh'⟩ := key g⁻¹ (inv_ne_zero hg) hg'
      refine ⟨h'⁻¹, ?_⟩
      rw [map_inv₀, show (algebraMap F F' h')⁻¹ * g = (algebraMap F F' h' * g⁻¹)⁻¹ by
        rw [mul_inv, inv_inv], map_inv₀, hh', inv_one]
  intro g hg hg1
  by_contra hne
  push Not at hne

  haveI : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.of_finite F F'
  let R : ↥S → ValuationSubring F' := fun j => (j : ValuationSubring F')
  have hR : ∀ i j : ↥S, R i ≤ R j → i = j := fun i j hij =>
    Subtype.ext (eq_of_le (hS _ i.2) (hS _ j.2) hij)
  let j₀ : ↥S := ⟨P₀, hP₀⟩
  have hg₀ : g ∈ P₀ := (P₀.valuation_le_one_iff g).mp hg1.le

  obtain ⟨z₀, hz₀⟩ := ValuationSubring.exists_forall_mem_and_sub_mem_nonunits R hR
    (fun j => if j = j₀ then 1 else 0) (fun j => by
      split_ifs
      · exact one_mem _
      · exact zero_mem _)
  have hz₀mem : ∀ P ∈ S, z₀ ∈ P := fun P hP => (hz₀ ⟨P, hP⟩).1
  have hz₀one : P₀.valuation z₀ = 1 := by
    have h := (hz₀ j₀).2
    rw [if_pos rfl, mem_nonunits_iff] at h
    have : z₀ = 1 + (z₀ - 1) := by ring
    rw [this]
    exact Valuation.map_one_add_of_lt _ h
  have hz₀lt : ∀ P ∈ S, P ≠ P₀ → P.valuation z₀ < 1 := by
    intro P hP hne'
    have h := (hz₀ ⟨P, hP⟩).2
    have hj : (⟨P, hP⟩ : ↥S) ≠ j₀ := fun e => hne' (congrArg Subtype.val e)
    rw [if_neg hj, sub_zero, mem_nonunits_iff] at h
    exact h

  have hc : ∀ s, ∃ c : F', (∀ P ∈ S, c ∈ P) ∧ (cls s).valuation (c - ω s) < 1 ∧
      ∀ P ∈ S, P ≠ cls s → P.valuation c < 1 := by
    intro s
    obtain ⟨c, hc⟩ := ValuationSubring.exists_forall_mem_and_sub_mem_nonunits R hR
      (fun j => if (j : ValuationSubring F') = cls s then ω s else 0) (fun j => by
        split_ifs with h
        · show ω s ∈ (j : ValuationSubring F'); rw [h]; exact hω s
        · exact zero_mem _)
    refine ⟨c, fun P hP => (hc ⟨P, hP⟩).1, ?_, ?_⟩
    · have h := (hc ⟨cls s, hcls s⟩).2
      rw [if_pos rfl, mem_nonunits_iff] at h
      exact h
    · intro P hP hne'
      have h := (hc ⟨P, hP⟩).2
      rw [if_neg (show ((⟨P, hP⟩ : ↥S) : ValuationSubring F') ≠ cls s from hne'), sub_zero,
        mem_nonunits_iff] at h
      exact h
  choose c hcmem hcω hclt using hc

  obtain ⟨t₀, ht₀, ht₀g, ht₀u⟩ := exists_mul_mem_forall R g
  have ht₀one : P₀.valuation t₀ = 1 := ht₀u j₀ hg₀

  have hT : ∀ j : ↥S, ∃ T : F', (∀ P ∈ S, T ∈ P) ∧ (j : ValuationSubring F').valuation T = 1 ∧
      ((j : ValuationSubring F') ≠ P₀ → P₀.valuation T ≤ P₀.valuation g) := by
    intro j
    by_cases hj : (j : ValuationSubring F') = P₀
    · exact ⟨1, fun P _ => one_mem _, by rw [map_one], fun h => absurd hj h⟩
    · obtain ⟨t, ht, htj, ht₀'⟩ := exists_deep R j₀ j (hindep _ j.2 hj) hg hg1
      exact ⟨t, fun P hP => ht ⟨P, hP⟩, htj, fun _ => ht₀'⟩
  choose T hTmem hTone hTle using hT

  set π : F' := t₀ * g * z₀ with hπdef
  set ω' : σ → F' := fun s => c s * T ⟨cls s, hcls s⟩ with hω'def
  have hω'app : ∀ s, ω' s = c s * T ⟨cls s, hcls s⟩ := fun s => rfl
  have hπlt : ∀ P ∈ S, P ≠ P₀ → P.valuation π < 1 := by
    intro P hP hne'
    rw [hπdef, map_mul]
    exact mul_lt_one_aux ((P.valuation_le_one_iff _).mpr (ht₀g ⟨P, hP⟩)) (hz₀lt P hP hne')
  have hπ₀ : P₀.valuation π = P₀.valuation g := by
    rw [hπdef, map_mul, map_mul, ht₀one, hz₀one, one_mul, mul_one]
  have hω'lt : ∀ s, ∀ P ∈ S, P ≠ cls s → P.valuation (ω' s) < 1 := by
    intro s P hP hne'
    rw [hω'app, mul_comm, map_mul]
    exact mul_lt_one_aux ((P.valuation_le_one_iff _).mpr (hTmem _ P hP)) (hclt s P hP hne')
  have hω'₀ : ∀ s, cls s ≠ P₀ → P₀.valuation (ω' s) ≤ P₀.valuation g := by
    intro s hs
    rw [hω'app, map_mul]
    calc P₀.valuation (c s) * P₀.valuation (T ⟨cls s, hcls s⟩)
        ≤ 1 * P₀.valuation g :=
          mul_le_mul' ((P₀.valuation_le_one_iff _).mpr (hcmem s P₀ hP₀)) (hTle _ hs)
      _ = P₀.valuation g := one_mul _

  have htrans : ∀ P ∈ S, ∀ a : σ → F, (∀ s, a s ∈ Q) → (∀ s, cls s ≠ P → a s = 0) →
      (∃ s, Q.valuation (a s) = 1) →
      P.valuation (∑ s, algebraMap F F' (a s) * ω' s) = 1 := by
    intro P hP a haQ hsupp hunit
    let j : ↥S := ⟨P, hP⟩
    have e : ∑ s, algebraMap F F' (a s) * ω' s =
        (∑ s, algebraMap F F' (a s) * c s) * T j := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hs : cls s = P
      · have hj : (⟨cls s, hcls s⟩ : ↥S) = j := Subtype.ext hs
        rw [hω'app, hj, mul_assoc]
      · rw [hsupp s hs, map_zero, zero_mul, zero_mul, zero_mul]
    rw [e, map_mul, hTone j, mul_one]
    refine valuation_sum_eq_one_of_sub (hS P hP) Finset.univ a haQ ω c ?_ (hind P hP a haQ hsupp hunit)
    intro s _ has
    have hs : cls s = P := by
      by_contra hs
      exact has (hsupp s hs)
    rw [← hs]
    exact hcω s

  let vec : Option σ → F' := fun o => o.elim π ω'
  have hdep : ¬ LinearIndependent F vec := by
    intro hli
    have h := hli.fintype_card_le_finrank
    rw [Fintype.card_option] at h
    omega
  obtain ⟨e, he, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.mp hdep

  obtain ⟨iM, -, hiM⟩ :=
    Finset.exists_max_image Finset.univ (fun i => Q.valuation (e i)) Finset.univ_nonempty
  have heM : e iM ≠ 0 := by
    intro h0
    have h := hiM i₁ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff] at h
    exact hi₁ ((Valuation.zero_iff _).mp h)
  set f : Option σ → F := fun i => e i / e iM with hfdef
  have hfQ : ∀ i, f i ∈ Q := by
    intro i
    rw [← Q.valuation_le_one_iff, hfdef]
    dsimp only
    rw [map_div₀]
    exact div_le_one_of_le₀ (hiM i (Finset.mem_univ _)) zero_le'
  have hfM : f iM = 1 := div_self heM
  have hfle : ∀ i, Q.valuation (f i) ≤ 1 := fun i => (Q.valuation_le_one_iff _).mpr (hfQ i)
  have hfrel : ∑ i, f i • vec i = 0 := by
    have : ∑ i, f i • vec i = (e iM)⁻¹ • ∑ i, e i • vec i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hfdef]
      dsimp only
      rw [div_eq_inv_mul, mul_smul]
    rw [this, he, smul_zero]
  set b : F := f none with hbdef
  set a : σ → F := fun s => f (some s) with hadef
  have hrel : algebraMap F F' b * π + ∑ s, algebraMap F F' (a s) * ω' s = 0 := by
    have h := hfrel
    rw [Fintype.sum_option] at h
    simpa only [vec, Option.elim, Algebra.smul_def] using h
  have haQ : ∀ s, a s ∈ Q := fun s => hfQ (some s)
  have hbQ : b ∈ Q := hfQ none

  have hsplit : ∀ P : ValuationSubring F',
      ∑ s, algebraMap F F' (a s) * ω' s =
        ∑ s, algebraMap F F' (if cls s = P then a s else 0) * ω' s +
        ∑ s, algebraMap F F' (if cls s = P then 0 else a s) * ω' s := by
    intro P
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  have hγ0 : P₀.valuation g ≠ 0 := (Valuation.ne_zero_iff _).mpr hg
  have hcoefQ : ∀ (P : ValuationSubring F') (s : σ), (if cls s = P then a s else 0) ∈ Q := by
    intro P s
    split_ifs
    exacts [haQ s, zero_mem _]
  by_cases hcase : ∃ s₁, cls s₁ ≠ P₀ ∧ Q.valuation (a s₁) = 1
  ·
    obtain ⟨s₁, hs₁, hu⟩ := hcase
    have hP₁ : cls s₁ ∈ S := hcls s₁
    have hmain : (cls s₁).valuation
        (∑ s, algebraMap F F' (if cls s = cls s₁ then a s else 0) * ω' s) = 1 :=
      htrans (cls s₁) hP₁ _ (hcoefQ _) (fun s hs => if_neg hs) ⟨s₁, by rw [if_pos rfl]; exact hu⟩
    have hrest : (cls s₁).valuation (algebraMap F F' b * π +
        ∑ s, algebraMap F F' (if cls s = cls s₁ then 0 else a s) * ω' s) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]; exact mul_lt_one_aux (le_one (hS _ hP₁) hbQ) (hπlt _ hP₁ hs₁)
      · refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
        split_ifs with hs
        · rw [map_zero, zero_mul, map_zero]; exact zero_lt_one
        · rw [map_mul]
          exact mul_lt_one_aux (le_one (hS _ hP₁) (haQ s)) (hω'lt s _ hP₁ (Ne.symm hs))
    have h1 : (cls s₁).valuation
        (algebraMap F F' b * π + ∑ s, algebraMap F F' (a s) * ω' s) = 1 := by
      rw [hsplit (cls s₁), show ∀ x y z : F', x + (y + z) = y + (x + z) from fun x y z => by ring,
        Valuation.map_add_eq_of_lt_left _ (lt_of_lt_of_eq hrest hmain.symm), hmain]
    rw [hrel, map_zero] at h1
    exact zero_ne_one h1
  ·
    push Not at hcase
    have hlt : ∀ s, cls s ≠ P₀ → Q.valuation (a s) < 1 := fun s hs =>
      lt_of_le_of_ne (hfle (some s)) (hcase s hs)
    set γ := P₀.valuation g with hγdef
    have hZ : P₀.valuation (∑ s, algebraMap F F' (if cls s = P₀ then 0 else a s) * ω' s) < γ := by
      refine Valuation.map_sum_lt _ hγ0 fun s _ => ?_
      split_ifs with hs
      · rw [map_zero, zero_mul, map_zero]; exact zero_lt_iff.mpr hγ0
      · rw [map_mul]
        calc P₀.valuation (algebraMap F F' (a s)) * P₀.valuation (ω' s)
            ≤ P₀.valuation (algebraMap F F' (a s)) * γ := mul_le_mul' le_rfl (hω'₀ s hs)
          _ < 1 * γ := mul_lt_mul_of_pos_right ((lt_one_iff (hS P₀ hP₀) _).mpr (hlt s hs))
              (zero_lt_iff.mpr hγ0)
          _ = γ := one_mul γ
    have hY : P₀.valuation (algebraMap F F' b * π) ≤ γ := by
      rw [map_mul, hπ₀]
      calc P₀.valuation (algebraMap F F' b) * P₀.valuation g ≤ 1 * γ :=
            mul_le_mul' (le_one (hS P₀ hP₀) hbQ) le_rfl
        _ = γ := one_mul γ
    by_cases hcase2 : ∃ s, cls s = P₀ ∧ Q.valuation (a s) = 1
    ·
      have hX : P₀.valuation (∑ s, algebraMap F F' (if cls s = P₀ then a s else 0) * ω' s) = 1 := by
        obtain ⟨s₁, hs₁, hu⟩ := hcase2
        exact htrans P₀ hP₀ _ (hcoefQ _) (fun s hs => if_neg hs)
          ⟨s₁, by rw [if_pos hs₁]; exact hu⟩
      have hYZ : P₀.valuation (algebraMap F F' b * π +
          ∑ s, algebraMap F F' (if cls s = P₀ then 0 else a s) * ω' s) < 1 :=
        lt_of_le_of_lt (Valuation.map_add _ _ _)
          (max_lt (lt_of_le_of_lt hY hg1) (hZ.trans hg1))
      have h1 : P₀.valuation (algebraMap F F' b * π + ∑ s, algebraMap F F' (a s) * ω' s) = 1 := by
        rw [hsplit P₀, show ∀ x y z : F', x + (y + z) = y + (x + z) from fun x y z => by ring,
          Valuation.map_add_eq_of_lt_left _ (lt_of_lt_of_eq hYZ hX.symm), hX]
      rw [hrel, map_zero] at h1
      exact zero_ne_one h1
    ·
      push Not at hcase2
      have hlt' : ∀ s, Q.valuation (a s) < 1 := by
        intro s
        by_cases hs : cls s = P₀
        · exact lt_of_le_of_ne (hfle (some s)) (hcase2 s hs)
        · exact hlt s hs
      have hb1 : b = 1 := by
        rcases hiMcase : iM with _ | s
        · show f none = 1
          rw [← hiMcase]; exact hfM
        · exfalso
          have h := hlt' s
          have : a s = 1 := by
            show f (some s) = 1
            rw [← hiMcase]; exact hfM
          rw [this, map_one] at h
          exact lt_irrefl _ h
      have hYeq : P₀.valuation (algebraMap F F' b * π) = γ := by
        rw [hb1, map_one, one_mul, hπ₀]
      by_cases hcase3 : ∀ s, cls s = P₀ → a s = 0
      ·
        have hX0 : ∑ s, algebraMap F F' (if cls s = P₀ then a s else 0) * ω' s = 0 := by
          refine Finset.sum_eq_zero fun s _ => ?_
          split_ifs with hs
          · rw [hcase3 s hs, map_zero, zero_mul]
          · rw [map_zero, zero_mul]
        have h1 : P₀.valuation (algebraMap F F' b * π + ∑ s, algebraMap F F' (a s) * ω' s) = γ := by
          rw [hsplit P₀, hX0, zero_add,
            Valuation.map_add_eq_of_lt_left _ (lt_of_lt_of_eq hZ hYeq.symm), hYeq]
        rw [hrel, map_zero] at h1
        exact hγ0 h1.symm
      · push Not at hcase3
        obtain ⟨s₀, hs₀, has₀⟩ := hcase3

        obtain ⟨sM, hsMU, hsM⟩ := Finset.exists_max_image
          (Finset.univ.filter fun s => cls s = P₀) (fun s => Q.valuation (a s)) ⟨s₀, by simp [hs₀]⟩
        have hsM₀ : cls sM = P₀ := by simpa using hsMU
        have haM : a sM ≠ 0 := by
          intro h0
          have h := hsM s₀ (by simp [hs₀])
          rw [h0, map_zero, le_zero_iff] at h
          exact has₀ ((Valuation.zero_iff _).mp h)
        let a'' : σ → F := fun s => if cls s = P₀ then a s / a sM else 0
        have ha''app : ∀ s, a'' s = if cls s = P₀ then a s / a sM else 0 := fun s => rfl
        have ha''Q : ∀ s, a'' s ∈ Q := by
          intro s
          rw [ha''app]
          split_ifs with hs
          · rw [← Q.valuation_le_one_iff, map_div₀]
            exact div_le_one_of_le₀ (hsM s (by simp [hs])) zero_le'
          · exact zero_mem _
        have hX1 : P₀.valuation (∑ s, algebraMap F F' (a'' s) * ω' s) = 1 := by
          refine htrans P₀ hP₀ a'' ha''Q (fun s hs => by rw [ha''app, if_neg hs]) ⟨sM, ?_⟩
          rw [ha''app, if_pos hsM₀, div_self haM, map_one]
        have hXeq : ∑ s, algebraMap F F' (if cls s = P₀ then a s else 0) * ω' s =
            algebraMap F F' (a sM) * ∑ s, algebraMap F F' (a'' s) * ω' s := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [ha''app]
          split_ifs with hs
          · conv_rhs => rw [← mul_assoc, ← RingHom.map_mul, mul_div_cancel₀ _ haM]
          · rw [map_zero, zero_mul, mul_zero]
        set α := P₀.valuation (algebraMap F F' (a sM)) with hαdef
        have hXval : P₀.valuation
            (∑ s, algebraMap F F' (if cls s = P₀ then a s else 0) * ω' s) = α := by
          rw [hXeq, map_mul, hX1, mul_one]
        by_cases hαγ : α = γ
        ·
          refine hne (a sM)⁻¹ ?_
          rw [map_mul, map_inv₀, map_inv₀, ← hαdef, hαγ, hγdef, inv_mul_cancel₀ hγ0]
        · have hXY : γ ≤ P₀.valuation
              (∑ s, algebraMap F F' (if cls s = P₀ then a s else 0) * ω' s +
                algebraMap F F' b * π) := by
            rcases lt_or_gt_of_ne hαγ with h | h
            · rw [Valuation.map_add_eq_of_lt_right _ (by rw [hXval, hYeq]; exact h), hYeq]
            · rw [Valuation.map_add_eq_of_lt_left _ (by rw [hXval, hYeq]; exact h), hXval]
              exact h.le
          have h1 : P₀.valuation (algebraMap F F' b * π + ∑ s, algebraMap F F' (a s) * ω' s) =
              P₀.valuation (∑ s, algebraMap F F' (if cls s = P₀ then a s else 0) * ω' s +
                algebraMap F F' b * π) := by
            rw [hsplit P₀, show ∀ x y z : F', y + (x + z) = (x + y) + z from fun x y z => by ring,
              Valuation.map_add_eq_of_lt_left _ (lt_of_lt_of_le hZ hXY)]
          rw [hrel, map_zero] at h1
          rw [← h1] at hXY
          exact hγ0 (le_zero_iff.mp hXY)

end Counting

end ValuationSubring.IndepMember

theorem solution
    {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    (Q : ValuationSubring F) (S : Finset (ValuationSubring F'))
    (hS : ∀ P ∈ S, P.comap (algebraMap F F') = Q)
    {σ : Type*} [Fintype σ] (cls : σ → ValuationSubring F') (hcls : ∀ s, cls s ∈ S)
    (ω : σ → F') (hω : ∀ s, ω s ∈ cls s)
    (hind : ∀ P ∈ S, ∀ a : σ → F, (∀ s, a s ∈ Q) → (∀ s, cls s ≠ P → a s = 0) →
      (∃ s, Q.valuation (a s) = 1) → P.valuation (∑ s, algebraMap F F' (a s) * ω s) = 1)
    (hcard : Module.finrank F F' ≤ Fintype.card σ)
    (P₀ : ValuationSubring F') (hP₀ : P₀ ∈ S) (hindep : ∀ P ∈ S, P ≠ P₀ → P₀ ⊔ P = ⊤)
    (g : F') (hg : g ≠ 0) :
    ∃ h : F, P₀.valuation (algebraMap F F' h * g) = 1 :=
  ValuationSubring.IndepMember.exists_valuation_mul_eq_one_of_forall_sup_eq_top Q S hS cls hcls ω hω
    hind hcard P₀ hP₀ hindep g hg

end S_ValuationSubring_exists_valuation_mul_eq_one_of_forall_sup_eq_top
end P2MW
export P2MW.S_ValuationSubring_exists_valuation_mul_eq_one_of_forall_sup_eq_top (solution)
