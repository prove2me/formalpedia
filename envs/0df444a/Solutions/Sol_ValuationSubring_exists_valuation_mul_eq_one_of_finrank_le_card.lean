-- Prove2me | solution 1 for ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c918f106-4dfa-50ca-b230-9475b354bb5c

import Mathlib
import Theorems.Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits
import Theorems.Thm_ValuationSubring_exists_valuation_mul_eq_one_of_forall_sup_eq_top
import Theorems.Thm_ValuationSubring_exists_le_forall_mem_iff_apply_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card

namespace ValuationSubring
p2m_export "ValuationSubring" "comap coe_mem_nonunits_iff mem_comap neg_mem nonunits_le_nonunits ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff mem_or_inv_mem' mem_top mul_mem one_mem mem_or_inv_mem linearOrderOverring nonunits_subset add_mem coe_subtype valuation_le_one_iff algebra valuation valuation_eq_one_iff exists_forall_mem_and_sub_mem_nonunits exists_valuation_mul_eq_one_of_forall_sup_eq_top exists_le_forall_mem_iff_apply_mem"
namespace CompleteSplittingE
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

section Loc

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

end Loc

section Transfer

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

end Transfer

section Normalize

variable [Algebra.IsAlgebraic F F']

theorem exists_normalized (Q : ValuationSubring F) (S : Finset (ValuationSubring F'))
    (hS : ∀ P ∈ S, P.comap (algebraMap F F') = Q)
    {σ : Type*} (cls : σ → ValuationSubring F') (hcls : ∀ s, cls s ∈ S)
    (ω : σ → F') (hω : ∀ s, ω s ∈ cls s) :
    ∃ ω' : σ → F', (∀ s, ∀ P ∈ S, ω' s ∈ P) ∧
      (∀ s, (cls s).valuation (ω' s - ω s) < 1) ∧
      (∀ s, ∀ P ∈ S, P ≠ cls s → P.valuation (ω' s) < 1) := by
  classical
  have hR : ∀ i j : ↥S, (i : ValuationSubring F') ≤ j → i = j := fun i j hij =>
    Subtype.ext (eq_of_le (hS _ i.2) (hS _ j.2) hij)
  have hc : ∀ s, ∃ c : F', (∀ P ∈ S, c ∈ P) ∧ (cls s).valuation (c - ω s) < 1 ∧
      ∀ P ∈ S, P ≠ cls s → P.valuation c < 1 := by
    intro s
    obtain ⟨c, hc⟩ := ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
      (fun j : ↥S => (j : ValuationSubring F')) hR
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
  choose c h1 h2 h3 using hc
  exact ⟨c, h1, h2, h3⟩

omit [Algebra.IsAlgebraic F F'] in

theorem hind_congr (Q : ValuationSubring F) (S : Finset (ValuationSubring F'))
    (hS : ∀ P ∈ S, P.comap (algebraMap F F') = Q)
    {σ : Type*} [Fintype σ] (cls : σ → ValuationSubring F')
    (ω ω' : σ → F') (hωω' : ∀ s, (cls s).valuation (ω' s - ω s) < 1)
    (hind : ∀ P ∈ S, ∀ a : σ → F, (∀ s, a s ∈ Q) → (∀ s, cls s ≠ P → a s = 0) →
      (∃ s, Q.valuation (a s) = 1) → P.valuation (∑ s, algebraMap F F' (a s) * ω s) = 1) :
    ∀ P ∈ S, ∀ a : σ → F, (∀ s, a s ∈ Q) → (∀ s, cls s ≠ P → a s = 0) →
      (∃ s, Q.valuation (a s) = 1) → P.valuation (∑ s, algebraMap F F' (a s) * ω' s) = 1 := by
  intro P hP a haQ hsupp hunit
  refine valuation_sum_eq_one_of_sub (hS P hP) Finset.univ a haQ ω ω' ?_
    (hind P hP a haQ hsupp hunit)
  intro s _ hs
  have : cls s = P := by
    by_contra h
    exact hs (hsupp s h)
  rw [← this]
  exact hωω' s

end Normalize

section Coarsen

def coarsen (Q' : ValuationSubring F) (P : ValuationSubring F') : ValuationSubring F' :=
  locAt P ((algebraMap F F') '' (Q'.nonunits : Set F))

theorem le_coarsen (Q' : ValuationSubring F) (P : ValuationSubring F') : P ≤ coarsen Q' P :=
  le_locAt _ _

theorem coarsen_comap {Q Q' : ValuationSubring F} (hQQ' : Q ≤ Q') {P : ValuationSubring F'}
    (hP : P.comap (algebraMap F F') = Q) : (coarsen Q' P).comap (algebraMap F F') = Q' := by
  ext x
  rw [ValuationSubring.mem_comap]
  show algebraMap F F' x ∈ locAt P _ ↔ _
  rw [mem_locAt_iff]
  constructor
  · intro h
    by_contra hx
    have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
    have hinv : x⁻¹ ∈ Q'.nonunits := by
      rw [mem_nonunits_iff, map_inv₀]
      have : 1 < Q'.valuation x := by
        rw [← not_le]; exact fun h' => hx ((Q'.valuation_le_one_iff x).mp h')
      exact inv_lt_one_of_one_lt₀ this
    have hlt : P.valuation (algebraMap F F' x⁻¹) < 1 := by
      rw [lt_one_iff hP]
      rw [← mem_nonunits_iff]
      exact nonunits_le_nonunits.mpr hQQ' hinv
    have := h _ ⟨x⁻¹, hinv, rfl⟩ hlt 1
    rw [pow_one, ← map_mul, inv_mul_cancel₀ hx0, map_one, map_one] at this
    exact lt_irrefl _ this
  · rintro hx _ ⟨d, hd, rfl⟩ - n
    rw [← map_pow, ← map_mul, lt_one_iff hP, ← mem_nonunits_iff]
    apply nonunits_le_nonunits.mpr hQQ'
    rw [mem_nonunits_iff, map_mul, map_pow]
    rw [mul_comm]
    exact mul_lt_one_aux (pow_le_one₀ zero_le' ((Q'.valuation_le_one_iff x).mpr hx))
      ((mem_nonunits_iff _).mp hd)

theorem hind_coarsen [Algebra.IsAlgebraic F F'] {Q Q' : ValuationSubring F} (hQQ' : Q ≤ Q')
    (S : Finset (ValuationSubring F')) (hS : ∀ P ∈ S, P.comap (algebraMap F F') = Q)
    {σ : Type*} [Fintype σ] (cls : σ → ValuationSubring F') (hcls : ∀ s, cls s ∈ S)
    (ω : σ → F')
    (hωlt : ∀ s, ∀ P ∈ S, P ≠ cls s → P.valuation (ω s) < 1)
    (hind : ∀ P ∈ S, ∀ a : σ → F, (∀ s, a s ∈ Q) → (∀ s, cls s ≠ P → a s = 0) →
      (∃ s, Q.valuation (a s) = 1) → P.valuation (∑ s, algebraMap F F' (a s) * ω s) = 1)
    (P' : ValuationSubring F') (a : σ → F) (haQ' : ∀ s, a s ∈ Q')
    (hsupp : ∀ s, coarsen Q' (cls s) ≠ P' → a s = 0) (hunit : ∃ s, Q'.valuation (a s) = 1) :
    P'.valuation (∑ s, algebraMap F F' (a s) * ω s) = 1 := by
  classical
  obtain ⟨s₀, hs₀⟩ := hunit
  have ha0 : a s₀ ≠ 0 := by
    intro h; rw [h, map_zero] at hs₀; exact zero_ne_one hs₀

  obtain ⟨sM, -, hsM⟩ := Finset.exists_max_image Finset.univ (fun s => Q.valuation (a s))
    ⟨s₀, Finset.mem_univ _⟩
  have hM0 : a sM ≠ 0 := by
    intro h
    have := hsM s₀ (Finset.mem_univ _)
    rw [h, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact ha0 this
  set P₁ := cls sM with hP₁def
  have hP₁S : P₁ ∈ S := hcls sM
  have hcoP₁ : coarsen Q' P₁ = P' := by
    by_contra h; exact hM0 (hsupp sM h)
  have hdivQ : ∀ s, a s / a sM ∈ Q := by
    intro s
    rw [← Q.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hsM s (Finset.mem_univ _)) zero_le'

  set a' : σ → F := fun s => if cls s = P₁ then a s / a sM else 0 with ha'def
  have ha'app : ∀ s, a' s = if cls s = P₁ then a s / a sM else 0 := fun s => rfl
  have ha'Q : ∀ s, a' s ∈ Q := by
    intro s; rw [ha'app]; split_ifs
    · exact hdivQ s
    · exact zero_mem _
  have ha'supp : ∀ s, cls s ≠ P₁ → a' s = 0 := by
    intro s hs; rw [ha'app, if_neg hs]
  have ha'unit : ∃ s, Q.valuation (a' s) = 1 :=
    ⟨sM, by rw [ha'app, if_pos rfl, div_self hM0, map_one]⟩
  have hX : P₁.valuation (∑ s, algebraMap F F' (a' s) * ω s) = 1 :=
    hind P₁ hP₁S a' ha'Q ha'supp ha'unit

  have hY : P₁.valuation
      (∑ s, algebraMap F F' (if cls s = P₁ then 0 else a s / a sM) * ω s) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro s _
    split_ifs with h
    · rw [map_zero, zero_mul, map_zero]; exact zero_lt_one
    · rw [map_mul]
      exact mul_lt_one_aux (le_one (hS P₁ hP₁S) (hdivQ s)) (hωlt s P₁ hP₁S (Ne.symm h))
  have hsum : ∑ s, algebraMap F F' (a s / a sM) * ω s =
      (∑ s, algebraMap F F' (a' s) * ω s) +
        ∑ s, algebraMap F F' (if cls s = P₁ then 0 else a s / a sM) * ω s := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ha'app]
    split_ifs <;> simp
  have hXY : P₁.valuation (∑ s, algebraMap F F' (a s / a sM) * ω s) = 1 := by
    rw [hsum, Valuation.map_add_eq_of_lt_left]
    · exact hX
    · rw [hX]; exact hY

  have hXY' : P'.valuation (∑ s, algebraMap F F' (a s / a sM) * ω s) = 1 := by
    rw [← hcoP₁]
    exact valuation_eq_one_of_le (le_coarsen Q' P₁) hXY
  have hsM1 : Q'.valuation (a sM) = 1 := by
    apply le_antisymm ((Q'.valuation_le_one_iff _).mpr (haQ' sM))
    have h1 : Q'.valuation (a s₀ / a sM) ≤ 1 :=
      (Q'.valuation_le_one_iff _).mpr (hQQ' (hdivQ s₀))
    rw [map_div₀, hs₀] at h1
    exact (div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hM0))).mp h1
  have hcoP' : P'.comap (algebraMap F F') = Q' := hcoP₁ ▸ coarsen_comap hQQ' (hS P₁ hP₁S)
  have hfinal : ∑ s, algebraMap F F' (a s) * ω s =
      algebraMap F F' (a sM) * ∑ s, algebraMap F F' (a s / a sM) * ω s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    conv_rhs => rw [← mul_assoc, ← RingHom.map_mul, mul_div_cancel₀ _ hM0]
  rw [hfinal, map_mul, hXY', mul_one, eq_one_iff hcoP']
  exact hsM1

end Coarsen

section Bar

variable {K : Type*} [Field K]

theorem valuation_eq_one_iff_mem_and_inv_mem (A : ValuationSubring K) {x : K} (hx : x ≠ 0) :
    A.valuation x = 1 ↔ x ∈ A ∧ x⁻¹ ∈ A := by
  constructor
  · intro h
    refine ⟨(A.valuation_le_one_iff x).mp h.le, (A.valuation_le_one_iff _).mp ?_⟩
    rw [map_inv₀, h, inv_one]
  · rintro ⟨h1, h2⟩
    apply le_antisymm ((A.valuation_le_one_iff x).mpr h1)
    have := (A.valuation_le_one_iff _).mpr h2
    rw [map_inv₀] at this
    exact (inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))).mp this

def bar (R P : ValuationSubring K) : ValuationSubring (ResidueField R) where
  carrier := {y | ∃ x : R, (x : K) ∈ P ∧ residue R x = y}
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, P.mul_mem _ _ hx hy, map_mul _ _ _⟩
  one_mem' := ⟨1, P.one_mem, map_one _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, P.add_mem _ _ hx hy, map_add _ _ _⟩
  zero_mem' := ⟨0, P.zero_mem, map_zero _⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, P.neg_mem _ hx, map_neg _ _⟩
  mem_or_inv_mem' := by
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    by_cases hx0 : residue R x = 0
    · exact Or.inl ⟨0, P.zero_mem, by rw [map_zero, hx0]⟩
    rcases P.mem_or_inv_mem (x : K) with h | h
    · exact Or.inl ⟨x, h, rfl⟩
    · right
      obtain ⟨u, rfl⟩ := (residue_ne_zero_iff_isUnit x).mp hx0
      refine ⟨↑u⁻¹, ?_, ?_⟩
      · have hmul : (((u⁻¹ : Rˣ) : R) : K) * ((u : R) : K) = 1 := by
          rw [← R.coe_mul, Units.inv_mul]; rfl
        rw [eq_inv_of_mul_eq_one_left hmul]; exact h
      · rw [map_units_inv]

variable {R P : ValuationSubring K}

theorem mem_bar {y : ResidueField R} : y ∈ bar R P ↔ ∃ x : R, (x : K) ∈ P ∧ residue R x = y :=
  Iff.rfl

theorem mem_nonunits_of_mem_maximalIdeal (hPR : P ≤ R) {x : R} (hx : x ∈ maximalIdeal R) :
    (x : K) ∈ P.nonunits :=
  nonunits_le_nonunits.mpr hPR (coe_mem_nonunits_iff.mpr hx)

theorem mem_bar_iff (hPR : P ≤ R) (x : R) : residue R x ∈ bar R P ↔ (x : K) ∈ P := by
  constructor
  · rintro ⟨x', hx', he⟩
    have hm : x - x' ∈ maximalIdeal R := by
      rw [← residue_eq_zero_iff, map_sub, he, sub_self]
    have hmem : ((x - x' : R) : K) ∈ P := nonunits_subset (mem_nonunits_of_mem_maximalIdeal hPR hm)
    have e : (x : K) = ((x - x' : R) : K) + (x' : K) := by push_cast; ring
    rw [e]; exact P.add_mem _ _ hmem hx'
  · intro hx; exact ⟨x, hx, rfl⟩

theorem bar_valuation_eq_one_iff (hPR : P ≤ R) (x : R) :
    (bar R P).valuation (residue R x) = 1 ↔ P.valuation (x : K) = 1 := by
  by_cases hx0 : residue R x = 0
  · rw [hx0, map_zero]
    have hlt : P.valuation (x : K) < 1 :=
      (mem_nonunits_iff _).mp (mem_nonunits_of_mem_maximalIdeal hPR ((residue_eq_zero_iff x).mp hx0))
    constructor
    · intro h; exact absurd h zero_ne_one
    · intro h; exact absurd h hlt.ne
  obtain ⟨u, hu⟩ := (residue_ne_zero_iff_isUnit x).mp hx0
  have hxK : (x : K) ≠ 0 := by
    rintro h
    apply hx0
    have : x = 0 := Subtype.ext h
    rw [this, map_zero]
  have hinvK : (((u⁻¹ : Rˣ) : R) : K) = (x : K)⁻¹ := by
    have hmul : (((u⁻¹ : Rˣ) : R) : K) * ((u : R) : K) = 1 := by
      rw [← R.coe_mul, Units.inv_mul]; rfl
    rw [eq_inv_of_mul_eq_one_left hmul, hu]
  rw [valuation_eq_one_iff_mem_and_inv_mem _ hx0, valuation_eq_one_iff_mem_and_inv_mem _ hxK,
    mem_bar_iff hPR]
  have hres : (residue R x)⁻¹ = residue R ↑u⁻¹ := by
    rw [map_units_inv, hu]
  rw [hres, mem_bar_iff hPR, hinvK]

theorem eq_of_bar_eq {P' : ValuationSubring K} (hPR : P ≤ R) (hP'R : P' ≤ R)
    (h : bar R P = bar R P') : P = P' := by
  have key : ∀ {A B : ValuationSubring K}, A ≤ R → B ≤ R → bar R A = bar R B → A ≤ B := by
    intro A B hA hB hAB x hx
    have := (mem_bar_iff hA ⟨x, hA hx⟩).mpr hx
    rw [hAB] at this
    exact (mem_bar_iff hB ⟨x, hA hx⟩).mp this
  exact le_antisymm (key hPR hP'R h) (key hP'R hPR h.symm)

theorem bar_sup_bar_eq_top {P₀ : ValuationSubring K} (hP₀R : P₀ ≤ R) (hPR : P ≤ R)
    (hsup : R ≤ P₀ ⊔ P) : bar R P₀ ⊔ bar R P = ⊤ := by
  set W := bar R P₀ ⊔ bar R P
  obtain ⟨O', hO'R, hO'mem, -⟩ := ValuationSubring.exists_le_forall_mem_iff_apply_mem R
    (residue R) (fun x hx => (RingHom.mem_ker).mpr ((residue_eq_zero_iff x).mpr hx)) W
  have hP₀O' : P₀ ≤ O' := fun x hx =>
    (hO'mem ⟨x, hP₀R hx⟩).mpr (le_sup_left (b := bar R P) ((mem_bar_iff hP₀R ⟨x, hP₀R hx⟩).mpr hx))
  have hPO' : P ≤ O' := fun x hx =>
    (hO'mem ⟨x, hPR hx⟩).mpr (le_sup_right (a := bar R P₀) ((mem_bar_iff hPR ⟨x, hPR hx⟩).mpr hx))
  have hRO' : R ≤ O' := hsup.trans (sup_le hP₀O' hPO')
  ext y
  refine ⟨fun _ => mem_top _, fun _ => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective y
  exact (hO'mem x).mp (hRO' x.2)

end Bar

section Residue

variable (R : ValuationSubring F')

def resHom : ↥(R.comap (algebraMap F F')) →+* ↥R :=
  (algebraMap F F').restrict (R.comap (algebraMap F F')) R (fun _ hx => hx)

@[scoped simp] theorem coe_resHom_apply (x : ↥(R.comap (algebraMap F F'))) :
    ((resHom R x : ↥R) : F') = algebraMap F F' x := rfl

scoped instance isLocalHom_resHom : IsLocalHom (resHom (F := F) R) where
  map_nonunit := by
    intro x hx
    rw [valuation_eq_one_iff] at hx ⊢
    exact (eq_one_iff (V := R) (O := R.comap (algebraMap F F')) rfl (x : F)).mp hx

@[reducible] noncomputable def residueAlgebra : Algebra (ResidueField ↥(R.comap (algebraMap F F'))) (ResidueField ↥R) :=
  (ResidueField.map (resHom R)).toAlgebra

attribute [local instance] residueAlgebra

theorem algebraMap_residue (x : ↥(R.comap (algebraMap F F'))) :
    algebraMap (ResidueField ↥(R.comap (algebraMap F F'))) (ResidueField ↥R) (residue _ x) =
      residue _ (resHom R x) :=
  ResidueField.map_residue _ _

variable {R}

theorem le_comap_of_le {P : ValuationSubring F'} (hPR : P ≤ R) {Q : ValuationSubring F}
    (hP : P.comap (algebraMap F F') = Q) : Q ≤ R.comap (algebraMap F F') :=
  fun x hx => show algebraMap F F' x ∈ R from hPR ((mem_iff hP x).mpr hx)

theorem bar_comap {P : ValuationSubring F'} (hPR : P ≤ R) {Q : ValuationSubring F}
    (hP : P.comap (algebraMap F F') = Q) :
    (bar R P).comap (algebraMap (ResidueField ↥(R.comap (algebraMap F F'))) (ResidueField ↥R)) =
      bar (R.comap (algebraMap F F')) Q := by
  ext y
  obtain ⟨x, rfl⟩ := residue_surjective y
  rw [ValuationSubring.mem_comap, algebraMap_residue, mem_bar_iff hPR,
    mem_bar_iff (le_comap_of_le hPR hP), coe_resHom_apply]
  exact mem_iff hP _

theorem card_add_card_le_finrank [FiniteDimensional F F']
    (S' : Finset (ValuationSubring F'))
    (hS' : ∀ P ∈ S', P.comap (algebraMap F F') = R.comap (algebraMap F F')) (hRS' : R ∈ S')
    {τ : Type*} [Fintype τ] (clsR : τ → ValuationSubring F') (hclsR : ∀ t, clsR t ∈ S')
    (hne : ∀ t, clsR t ≠ R) (ω : τ → F')
    (hωlt : ∀ t, ∀ P ∈ S', P ≠ clsR t → P.valuation (ω t) < 1)
    (hind : ∀ P ∈ S', ∀ a : τ → F, (∀ t, a t ∈ R.comap (algebraMap F F')) →
      (∀ t, clsR t ≠ P → a t = 0) → (∃ t, (R.comap (algebraMap F F')).valuation (a t) = 1) →
      P.valuation (∑ t, algebraMap F F' (a t) * ω t) = 1)
    (s : Finset (ResidueField ↥R))
    (hs : LinearIndependent (ResidueField ↥(R.comap (algebraMap F F')))
      (fun i : ↥s => (i : ResidueField ↥R))) :
    s.card + Fintype.card τ ≤ Module.finrank F F' := by
  classical
  set QR := R.comap (algebraMap F F') with hQRdef
  haveI : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.of_finite F F'

  choose lift hlift using fun i : ↥s => residue_surjective (R := ↥R) (i : ResidueField ↥R)

  obtain ⟨x', hx'mem, hx'sub, hx'lt⟩ := exists_normalized QR S' hS' (fun _ : ↥s => R)
    (fun _ => hRS') (fun i => (lift i : F')) (fun i => (lift i).2)
  have hx'R : ∀ i, x' i ∈ R := fun i => hx'mem i R hRS'
  have hres : ∀ i, residue (↥R) ⟨x' i, hx'R i⟩ = (i : ResidueField ↥R) := by
    intro i
    rw [← hlift i, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← coe_mem_nonunits_iff,
      mem_nonunits_iff]
    exact hx'sub i

  set vec : ↥s ⊕ τ → F' := fun o => Sum.elim x' ω o with hvecdef
  suffices hli : LinearIndependent F vec by
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_sum, Fintype.card_coe] at this
  by_contra hdep
  obtain ⟨g, hrel, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.mp hdep
  obtain ⟨iM, -, hiM⟩ := Finset.exists_max_image Finset.univ (fun o => QR.valuation (g o))
    ⟨i₁, Finset.mem_univ _⟩
  have hM0 : g iM ≠ 0 := by
    intro h
    have := hiM i₁ (Finset.mem_univ _)
    rw [h, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hi₁ this
  set f : ↥s ⊕ τ → F := fun o => g o / g iM with hfdef
  have hfQ : ∀ o, f o ∈ QR := by
    intro o
    rw [← QR.valuation_le_one_iff, hfdef, map_div₀]
    exact div_le_one_of_le₀ (hiM o (Finset.mem_univ _)) zero_le'
  have hfM : f iM = 1 := div_self hM0
  have hfrel : (∑ i, algebraMap F F' (f (Sum.inl i)) * x' i) +
      ∑ t, algebraMap F F' (f (Sum.inr t)) * ω t = 0 := by
    have : ∑ o, f o • vec o = 0 := by
      simp only [hfdef, div_eq_mul_inv, mul_comm _ (g iM)⁻¹, ← smul_smul, ← Finset.smul_sum, hrel,
        smul_zero]
    rw [Fintype.sum_sum_type] at this
    simpa only [hvecdef, Sum.elim_inl, Sum.elim_inr, Algebra.smul_def] using this
  have hle : ∀ P ∈ S', ∀ o, P.valuation (algebraMap F F' (f o)) ≤ 1 :=
    fun P hP o => le_one (hS' P hP) (hfQ o)
  rcases hiMcase : iM with i₀ | t₀
  ·
    rw [hiMcase] at hfM
    have hB : R.valuation (∑ t, algebraMap F F' (f (Sum.inr t)) * ω t) < 1 := by
      apply Valuation.map_sum_lt _ one_ne_zero
      intro t _
      rw [map_mul]
      exact mul_lt_one_aux (hle R hRS' _) (hωlt t R hRS' (hne t).symm)
    have hA : R.valuation (∑ i, algebraMap F F' (f (Sum.inl i)) * x' i) < 1 := by
      rw [eq_neg_of_add_eq_zero_left hfrel, Valuation.map_neg]
      exact hB

    set fR : ↥s → ↥QR := fun i => ⟨f (Sum.inl i), hfQ _⟩ with hfRdef
    set AR : ↥R := ∑ i, resHom R (fR i) * ⟨x' i, hx'R i⟩ with hARdef
    have hAcoe : (AR : F') = ∑ i, algebraMap F F' (f (Sum.inl i)) * x' i := by
      rw [hARdef, ← R.coe_subtype, map_sum]
      rfl
    have hAres : residue (↥R) AR = 0 := by
      rw [residue_eq_zero_iff, ← coe_mem_nonunits_iff, mem_nonunits_iff, hAcoe]
      exact hA
    have hsum : ∑ i, (residue (↥QR) (fR i)) • (i : ResidueField ↥R) = 0 := by
      rw [← hAres, hARdef, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hres, Algebra.smul_def, algebraMap_residue]
    have h1 : residue (↥QR) (fR i₀) = 1 := by
      have : fR i₀ = 1 := Subtype.ext hfM
      rw [this, map_one]
    have := Fintype.linearIndependent_iff.mp hs (fun i => residue (↥QR) (fR i)) hsum i₀
    rw [h1] at this
    exact one_ne_zero this
  ·
    rw [hiMcase] at hfM
    set P' := clsR t₀ with hP'def
    have hP'S : P' ∈ S' := hclsR t₀
    have hA : P'.valuation (∑ i, algebraMap F F' (f (Sum.inl i)) * x' i) < 1 := by
      apply Valuation.map_sum_lt _ one_ne_zero
      intro i _
      rw [map_mul]
      exact mul_lt_one_aux (hle P' hP'S _) (hx'lt i P' hP'S (hne t₀))
    have hB₁ : P'.valuation
        (∑ t, algebraMap F F' (if clsR t = P' then f (Sum.inr t) else 0) * ω t) = 1 := by
      refine hind P' hP'S _ (fun t => ?_) (fun t ht => if_neg ht) ⟨t₀, ?_⟩
      · split_ifs
        · exact hfQ _
        · exact zero_mem _
      · rw [if_pos rfl, hfM, map_one]
    have hB₂ : P'.valuation
        (∑ t, algebraMap F F' (if clsR t = P' then 0 else f (Sum.inr t)) * ω t) < 1 := by
      apply Valuation.map_sum_lt _ one_ne_zero
      intro t _
      split_ifs with h
      · rw [map_zero, zero_mul, map_zero]; exact zero_lt_one
      · rw [map_mul]
        exact mul_lt_one_aux (hle P' hP'S _) (hωlt t P' hP'S (Ne.symm h))
    have hBsplit : ∑ t, algebraMap F F' (f (Sum.inr t)) * ω t =
        (∑ t, algebraMap F F' (if clsR t = P' then f (Sum.inr t) else 0) * ω t) +
          ∑ t, algebraMap F F' (if clsR t = P' then 0 else f (Sum.inr t)) * ω t := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs <;> simp
    have hB : P'.valuation (∑ t, algebraMap F F' (f (Sum.inr t)) * ω t) = 1 := by
      rw [hBsplit, Valuation.map_add_eq_of_lt_left]
      · exact hB₁
      · rw [hB₁]; exact hB₂
    have hAB : P'.valuation ((∑ i, algebraMap F F' (f (Sum.inl i)) * x' i) +
        ∑ t, algebraMap F F' (f (Sum.inr t)) * ω t) = 1 := by
      rw [Valuation.map_add_eq_of_lt_right]
      · exact hB
      · rw [hB]; exact hA
    rw [hfrel, map_zero] at hAB
    exact zero_ne_one hAB

end Residue

section Main

variable [FiniteDimensional F F'] {σ : Type*} [Fintype σ]

attribute [local instance] residueAlgebra

theorem main (n : ℕ) : ∀ (Q : ValuationSubring F) (S : Finset (ValuationSubring F')),
    S.card = n → (∀ P ∈ S, P.comap (algebraMap F F') = Q) →
    ∀ (cls : σ → ValuationSubring F'), (∀ s, cls s ∈ S) →
    ∀ (ω : σ → F'), (∀ s, ω s ∈ cls s) →
    (∀ P ∈ S, ∀ a : σ → F, (∀ s, a s ∈ Q) → (∀ s, cls s ≠ P → a s = 0) →
      (∃ s, Q.valuation (a s) = 1) → P.valuation (∑ s, algebraMap F F' (a s) * ω s) = 1) →
    Module.finrank F F' ≤ Fintype.card σ →
    ∀ P₀ ∈ S, ∀ g : F', g ≠ 0 → ∃ h : F, P₀.valuation (algebraMap F F' h * g) = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  intro Q S hcardS hS cls hcls ω hω hind hcard P₀ hP₀ g hg
  classical
  haveI : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.of_finite F F'
  by_cases hA : ∀ P ∈ S, P ≠ P₀ → P₀ ⊔ P = ⊤
  · exact ValuationSubring.exists_valuation_mul_eq_one_of_forall_sup_eq_top Q S hS cls hcls ω hω
      hind hcard P₀ hP₀ hA g hg
  push Not at hA
  obtain ⟨P₁', hP₁'S, hP₁'ne, hP₁'top⟩ := hA

  set T := S.filter (fun P => P ≠ P₀ ∧ P₀ ⊔ P ≠ ⊤) with hTdef
  have hTne : T.Nonempty := ⟨P₁', Finset.mem_filter.mpr ⟨hP₁'S, hP₁'ne, hP₁'top⟩⟩
  obtain ⟨P₁, hP₁T, hP₁min⟩ := by
    letI := P₀.linearOrderOverring
    exact Finset.exists_min_image T (fun P => (⟨P₀ ⊔ P, le_sup_left⟩ : {S // P₀ ≤ S})) hTne
  obtain ⟨hP₁S, hP₁ne, hP₁top⟩ := Finset.mem_filter.mp hP₁T
  set R := P₀ ⊔ P₁ with hRdef
  have hP₀R : P₀ ≤ R := le_sup_left
  have hP₁R : P₁ ≤ R := le_sup_right
  have hRtop : R ≠ ⊤ := hP₁top
  have hRmin : ∀ P ∈ S, P ≠ P₀ → P₀ ⊔ P ≠ ⊤ → R ≤ P₀ ⊔ P := fun P hP hne htop =>
    hP₁min P (Finset.mem_filter.mpr ⟨hP, hne, htop⟩)
  set QR := R.comap (algebraMap F F') with hQRdef
  have hQQR : Q ≤ QR := le_comap_of_le hP₀R (hS P₀ hP₀)

  set co : ValuationSubring F' → ValuationSubring F' := coarsen QR with hcodef
  have hco1 : ∀ P, P ≤ co P := fun P => le_coarsen QR P
  have hco2 : ∀ P ∈ S, (co P).comap (algebraMap F F') = QR := fun P hP =>
    coarsen_comap hQQR (hS P hP)
  have hcoR : ∀ P ∈ S, P ≤ R → co P = R := by
    intro P hP hPR
    letI := P.linearOrderOverring
    rcases le_total (⟨co P, hco1 P⟩ : {S // P ≤ S}) ⟨R, hPR⟩ with h | h
    · exact eq_of_le (hco2 P hP) rfl h
    · exact (eq_of_le rfl (hco2 P hP) h).symm
  set SR := S.image co with hSRdef
  have hSR : ∀ P' ∈ SR, P'.comap (algebraMap F F') = QR := by
    intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hP'
    exact hco2 P hP
  have hRSR : R ∈ SR := Finset.mem_image.mpr ⟨P₀, hP₀, hcoR P₀ hP₀ hP₀R⟩
  have hcardSR : SR.card < n := by
    rw [← hcardS]
    refine lt_of_le_of_ne Finset.card_image_le fun h => ?_
    have hinj := Finset.card_image_iff.mp h
    have : P₀ = P₁ :=
      hinj hP₀ hP₁S ((hcoR P₀ hP₀ hP₀R).trans (hcoR P₁ hP₁S hP₁R).symm)
    exact hP₁ne this.symm
  have hclsR : ∀ s, (co ∘ cls) s ∈ SR := fun s => Finset.mem_image_of_mem _ (hcls s)

  obtain ⟨ω₁, hω₁mem, hω₁sub, hω₁lt⟩ := exists_normalized Q S hS cls hcls ω hω
  have hind₁ := hind_congr Q S hS cls ω ω₁ hω₁sub hind
  have hω₁R : ∀ s, ω₁ s ∈ (co ∘ cls) s := fun s => hco1 _ (hω₁mem s _ (hcls s))

  have hindR₁ : ∀ P' ∈ SR, ∀ a : σ → F, (∀ s, a s ∈ QR) → (∀ s, (co ∘ cls) s ≠ P' → a s = 0) →
      (∃ s, QR.valuation (a s) = 1) →
      P'.valuation (∑ s, algebraMap F F' (a s) * ω₁ s) = 1 :=
    fun P' _ a haQ hsupp hunit =>
      hind_coarsen hQQR S hS cls hcls ω₁ hω₁lt hind₁ P' a haQ hsupp hunit

  obtain ⟨h₁, hh₁⟩ :=
    ih SR.card hcardSR QR SR rfl hSR (co ∘ cls) hclsR ω₁ hω₁R hindR₁ hcard R hRSR g hg
  set g₁ := algebraMap F F' h₁ * g with hg₁def
  have hg₁R : g₁ ∈ R := (R.valuation_le_one_iff _).mp hh₁.le

  obtain ⟨ω₂, hω₂mem, hω₂sub, hω₂lt⟩ := exists_normalized QR SR hSR (co ∘ cls) hclsR ω₁ hω₁R
  have hindR₂ := hind_congr QR SR hSR (co ∘ cls) ω₁ ω₂ hω₂sub hindR₁
  have hω₂sub' : ∀ s, (cls s).valuation (ω₂ s - ω₁ s) < 1 := fun s =>
    (mem_nonunits_iff _).mp (nonunits_le_nonunits.mpr (hco1 (cls s))
      ((mem_nonunits_iff _).mpr (hω₂sub s)))
  have hind₂ := hind_congr Q S hS cls ω₁ ω₂ hω₂sub' hind₁
  have hω₂R : ∀ s, ω₂ s ∈ R := fun s => hω₂mem s R hRSR
  have hω₂cls : ∀ s, ω₂ s ∈ cls s := by
    intro s
    have e : ω₂ s = ω₁ s + (ω₂ s - ω₁ s) := by ring
    rw [e]
    exact (cls s).add_mem _ _ (hω₁mem s _ (hcls s))
      (nonunits_subset ((mem_nonunits_iff _).mpr (hω₂sub' s)))

  have hτne : ∀ t : {s : σ // ¬ cls s ≤ R}, (co ∘ cls) t.1 ≠ R := fun t h =>
    t.2 (le_of_le_of_eq (hco1 (cls t.1)) h)
  have hindτ : ∀ P ∈ SR, ∀ a : {s : σ // ¬ cls s ≤ R} → F, (∀ t, a t ∈ QR) →
      (∀ t, (co ∘ cls) t.1 ≠ P → a t = 0) → (∃ t, QR.valuation (a t) = 1) →
      P.valuation (∑ t, algebraMap F F' (a t) * ω₂ t.1) = 1 := by
    intro P hP a haQ hsupp hunit
    set a' : σ → F := fun s => if h : cls s ≤ R then 0 else a ⟨s, h⟩ with ha'def
    have h := hindR₂ P hP a' (fun s => ?_) (fun s hs => ?_) ?_
    · rw [← Fintype.sum_subtype_add_sum_subtype (fun s => cls s ≤ R)
        (fun s => algebraMap F F' (a' s) * ω₂ s)] at h
      rw [Finset.sum_eq_zero (fun (s : {s : σ // cls s ≤ R}) _ => by
        rw [ha'def]; dsimp only; rw [dif_pos s.2, map_zero, zero_mul]), zero_add] at h
      convert h using 3 with t
      rw [ha'def]; dsimp only; rw [dif_neg t.2]
    · rw [ha'def]; dsimp only
      split_ifs with h
      · exact zero_mem _
      · exact haQ _
    · rw [ha'def]; dsimp only
      split_ifs with h
      · rfl
      · exact hsupp ⟨s, h⟩ hs
    · obtain ⟨t, ht⟩ := hunit
      refine ⟨t.1, ?_⟩
      rw [ha'def]; dsimp only; rw [dif_neg t.2]
      exact ht
  have hcount : ∀ t : Finset (ResidueField ↥R),
      LinearIndependent (ResidueField ↥QR) (fun i : ↥t => (i : ResidueField ↥R)) →
      t.card ≤ Fintype.card {s : σ // cls s ≤ R} := by
    intro t ht
    have h := card_add_card_le_finrank SR hSR hRSR (fun t : {s : σ // ¬ cls s ≤ R} =>
      (co ∘ cls) t.1) (fun t => hclsR t.1) hτne (fun t => ω₂ t.1)
      (fun t P hP hne => hω₂lt t.1 P hP hne) hindτ t ht
    have h1 := Fintype.card_subtype_compl (fun s : σ => cls s ≤ R)
    have h2 := Fintype.card_subtype_le (fun s : σ => cls s ≤ R)
    omega
  have hrank : Module.rank (ResidueField ↥QR) (ResidueField ↥R) ≤
      (Fintype.card {s : σ // cls s ≤ R} : ℕ) := rank_le hcount
  haveI : FiniteDimensional (ResidueField ↥QR) (ResidueField ↥R) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0))
  have hcard' : Module.finrank (ResidueField ↥QR) (ResidueField ↥R) ≤
      Fintype.card {s : σ // cls s ≤ R} := Module.finrank_le_of_rank_le hrank

  set Sbar : Finset (ValuationSubring (ResidueField ↥R)) :=
    (S.filter (· ≤ R)).image (bar R) with hSbardef
  have hmemSbar : ∀ {Pb}, Pb ∈ Sbar ↔ ∃ P, (P ∈ S ∧ P ≤ R) ∧ bar R P = Pb := by
    intro Pb
    simp only [hSbardef, Finset.mem_image, Finset.mem_filter]
  have hSbar : ∀ Pb ∈ Sbar, Pb.comap (algebraMap (ResidueField ↥QR) (ResidueField ↥R)) =
      bar QR Q := by
    intro Pb hPb
    obtain ⟨P, hP, rfl⟩ := hmemSbar.mp hPb
    exact bar_comap hP.2 (hS P hP.1)
  set cls' : {s : σ // cls s ≤ R} → ValuationSubring (ResidueField ↥R) :=
    fun s => bar R (cls s.1) with hcls'def
  have hcls' : ∀ s, cls' s ∈ Sbar := fun s => hmemSbar.mpr ⟨cls s.1, ⟨hcls s.1, s.2⟩, rfl⟩
  set ω' : {s : σ // cls s ≤ R} → ResidueField ↥R :=
    fun s => residue (↥R) ⟨ω₂ s.1, hω₂R s.1⟩ with hω'def
  have hω' : ∀ s, ω' s ∈ cls' s := fun s => (mem_bar_iff s.2 _).mpr (hω₂cls s.1)
  have hind' : ∀ Pb ∈ Sbar, ∀ ab : {s : σ // cls s ≤ R} → ResidueField ↥QR,
      (∀ s, ab s ∈ bar QR Q) → (∀ s, cls' s ≠ Pb → ab s = 0) →
      (∃ s, (bar QR Q).valuation (ab s) = 1) →
      Pb.valuation (∑ s, algebraMap (ResidueField ↥QR) (ResidueField ↥R) (ab s) * ω' s) = 1 := by
    intro Pb hPb ab habQ hsupp hunit
    obtain ⟨P, hP, rfl⟩ := hmemSbar.mp hPb
    choose x hxQ hxres using fun s => mem_bar.mp (habQ s)

    set a : σ → F := fun s =>
      if h : cls s ≤ R then (if ab ⟨s, h⟩ = 0 then 0 else (x ⟨s, h⟩ : F)) else 0 with hadef
    have ha' : ∀ s : {s : σ // cls s ≤ R},
        a s.1 = if ab s = 0 then 0 else (x s : F) := by
      intro s
      rw [hadef]; dsimp only; rw [dif_pos s.2]
    have haQ : ∀ s, a s ∈ Q := by
      intro s
      rw [hadef]; dsimp only
      split_ifs
      · exact zero_mem _
      · exact hxQ _
      · exact zero_mem _
    have hsupp' : ∀ s, cls s ≠ P → a s = 0 := by
      intro s hs
      rw [hadef]; dsimp only
      split_ifs with h1 h2
      · rfl
      · exact (h2 (hsupp ⟨s, h1⟩ fun he => hs (eq_of_bar_eq h1 hP.2 he))).elim
      · rfl
    have hunit' : ∃ s, Q.valuation (a s) = 1 := by
      obtain ⟨s, hs1⟩ := hunit
      have hne0 : ab s ≠ 0 := fun h => by
        rw [h, map_zero] at hs1
        exact zero_ne_one hs1
      refine ⟨s.1, ?_⟩
      rw [ha' s, if_neg hne0]
      rw [← hxres s] at hs1
      exact (bar_valuation_eq_one_iff hQQR _).mp hs1
    have hres_a : ∀ s : {s : σ // cls s ≤ R},
        residue (↥QR) ⟨a s.1, hQQR (haQ s.1)⟩ = ab s := by
      intro s
      by_cases h0 : ab s = 0
      · have : (⟨a s.1, hQQR (haQ s.1)⟩ : ↥QR) = 0 :=
          Subtype.ext (show a s.1 = ((0 : ↥QR) : F) by rw [ha' s, if_pos h0]; rfl)
        rw [this, map_zero, h0]
      · have : (⟨a s.1, hQQR (haQ s.1)⟩ : ↥QR) = x s :=
          Subtype.ext (show a s.1 = (x s : F) by rw [ha' s, if_neg h0])
        rw [this, hxres]
    have hv := hind₂ P hP.1 a haQ hsupp' hunit'
    set AR : ↥R := ∑ s : {s : σ // cls s ≤ R},
      resHom R ⟨a s.1, hQQR (haQ s.1)⟩ * ⟨ω₂ s.1, hω₂R s.1⟩ with hARdef
    have hAcoe : (AR : F') = ∑ s, algebraMap F F' (a s) * ω₂ s := by
      rw [hARdef, ← R.coe_subtype, map_sum,
        ← Fintype.sum_subtype_add_sum_subtype (fun s => cls s ≤ R)
          (fun s => algebraMap F F' (a s) * ω₂ s)]
      rw [Finset.sum_eq_zero (fun (s : {s : σ // ¬ cls s ≤ R}) _ => by
        rw [hadef]; dsimp only; rw [dif_neg s.2, map_zero, zero_mul]), add_zero]
      rfl
    have hvR : (bar R P).valuation (residue (↥R) AR) = 1 :=
      (bar_valuation_eq_one_iff hP.2 AR).mpr (by rw [hAcoe]; exact hv)
    have hresA : residue (↥R) AR =
        ∑ s, algebraMap (ResidueField ↥QR) (ResidueField ↥R) (ab s) * ω' s := by
      rw [hARdef, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_mul, ← algebraMap_residue, hres_a]
    rw [hresA] at hvR
    exact hvR

  have hg₁res : residue (↥R) ⟨g₁, hg₁R⟩ ≠ 0 := by
    rw [Ne, residue_eq_zero_iff, ← coe_mem_nonunits_iff, mem_nonunits_iff, not_lt]
    exact hh₁.ge
  have hP₀bar : bar R P₀ ∈ Sbar := hmemSbar.mpr ⟨P₀, ⟨hP₀, hP₀R⟩, rfl⟩
  have hindep : ∀ Pb ∈ Sbar, Pb ≠ bar R P₀ → bar R P₀ ⊔ Pb = ⊤ := by
    intro Pb hPb hne
    obtain ⟨P, hP, rfl⟩ := hmemSbar.mp hPb
    have hPne : P ≠ P₀ := fun h => hne (by rw [h])
    refine bar_sup_bar_eq_top hP₀R hP.2 (hRmin P hP.1 hPne fun htop => hRtop ?_)
    exact top_le_iff.mp (htop ▸ sup_le hP₀R hP.2)
  obtain ⟨hb, hhb⟩ := ValuationSubring.exists_valuation_mul_eq_one_of_forall_sup_eq_top
    (bar QR Q) Sbar hSbar cls' hcls' ω' hω' hind' hcard' (bar R P₀) hP₀bar hindep
    (residue (↥R) ⟨g₁, hg₁R⟩) hg₁res
  obtain ⟨h₂, rfl⟩ := residue_surjective hb
  refine ⟨(h₂ : F) * h₁, ?_⟩
  have e : algebraMap F F' ((h₂ : F) * h₁) * g = ((resHom R h₂ * ⟨g₁, hg₁R⟩ : ↥R) : F') := by
    rw [map_mul, mul_assoc]
    rfl
  rw [e, ← bar_valuation_eq_one_iff hP₀R, map_mul, ← algebraMap_residue]
  exact hhb

end Main

section Target

variable [FiniteDimensional F F']

theorem exists_valuation_mul_eq_one_of_finrank_le_card
    (O : ValuationSubring F) {ι : Type*} [Fintype ι] (O' : ι → ValuationSubring F')
    (hinj : Function.Injective O') (hO' : ∀ i, (O' i).comap (algebraMap F F') = O)
    (hcard : Module.finrank F F' ≤ Fintype.card ι) (i : ι) (g : F') (hg : g ≠ 0) :
    ∃ h : F, (O' i).valuation (algebraMap F F' h * g) = 1 := by
  classical
  set S := Finset.univ.image O' with hSdef
  have hS : ∀ P ∈ S, P.comap (algebraMap F F') = O := by
    intro P hP
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hP
    exact hO' j
  have hcls : ∀ j, O' j ∈ S := fun j => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  refine main S.card O S rfl hS O' hcls (fun _ => 1) (fun j => one_mem _) ?_ hcard (O' i)
    (hcls i) g hg
  intro P hP a haO hsupp hunit
  obtain ⟨j, hj⟩ := hunit
  have hjP : O' j = P := by
    by_contra h
    rw [hsupp j h, map_zero] at hj
    exact zero_ne_one hj
  have hsum : ∑ s, algebraMap F F' (a s) * 1 = algebraMap F F' (a j) := by
    rw [Finset.sum_eq_single j]
    · rw [mul_one]
    · intro s _ hs
      rw [hsupp s (fun h => hs (hinj (h.trans hjP.symm))), map_zero, zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  rw [hsum, ← hjP]
  exact (eq_one_iff (hO' j) (a j)).mpr hj

end Target

end ValuationSubring.CompleteSplittingE
p2m_reactivate "P2MW.S_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card.ValuationSubring P2MW.S_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card.ValuationSubring.CompleteSplittingE"
p2m_reactivate "P2MW.S_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card.ValuationSubring"

theorem solution
    {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    (O : ValuationSubring F) {ι : Type*} [Fintype ι] (O' : ι → ValuationSubring F')
    (hinj : Function.Injective O') (hO' : ∀ i, (O' i).comap (algebraMap F F') = O)
    (hcard : Module.finrank F F' ≤ Fintype.card ι) (i : ι) (g : F') (hg : g ≠ 0) :
    ∃ h : F, (O' i).valuation (algebraMap F F' h * g) = 1 :=
  ValuationSubring.CompleteSplittingE.exists_valuation_mul_eq_one_of_finrank_le_card O O' hinj hO'
    hcard i g hg

end S_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card
end P2MW
export P2MW.S_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card (solution)
