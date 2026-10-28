-- Prove2me | solution 1 for ZhengFedergruenSS.Algorithm.theorem_1a
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T06:23:52.636242+00:00
-- url     : https://prove2.me/submissions/48be04b5-58e9-49b8-8eac-87dddd12cecc

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model
import Definitions.Def_ZhengFedergruenSS_Algorithm_Run

set_option autoImplicit false

namespace ZFSOne

open ZhengFedergruenSS.Algorithm

/-! ## The renewal density `m` -/

theorem m_zero (p : ℕ → ℝ) : m p 0 = (1 - p 0)⁻¹ := by
  rw [m]

theorem m_succ (p : ℕ → ℝ) (j : ℕ) :
    m p (j + 1) = (1 - p 0)⁻¹ * ∑ i ∈ Finset.range (j + 1), p (j + 1 - i) * m p i := by
  rw [m, Fin.sum_univ_eq_sum_range (fun i => p (j + 1 - i) * m p i)]

theorem m_nonneg (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) (j : ℕ) : 0 ≤ m p j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => rw [m_zero]; exact inv_nonneg.mpr (by linarith)
    | succ j =>
      rw [m_succ]
      apply mul_nonneg (inv_nonneg.mpr (by linarith))
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hp _) (ih i (by simp at hi; omega))

theorem one_le_m_zero (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) : 1 ≤ m p 0 := by
  rw [m_zero]
  have h1 : 0 < 1 - p 0 := by linarith
  have h2 : 1 - p 0 ≤ 1 := by linarith [hp 0]
  rw [le_inv_comm₀ one_pos h1]; simpa using h2

theorem M_pos (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) {n : ℕ} (hn : 0 < n) :
    0 < M p n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [M, Finset.sum_range_succ']
  have h1 : 1 ≤ m p 0 := one_le_m_zero p hp hp0
  have h2 : 0 ≤ ∑ i ∈ Finset.range k, m p (i + 1) :=
    Finset.sum_nonneg (fun i _ => m_nonneg p hp hp0 _)
  linarith

/-! ## The normalized cost `F x s S = k(s,S) - x M(S-s)` -/

noncomputable def F (p : ℕ → ℝ) (K : ℝ) (G : ℤ → ℝ) (x : ℝ) (s S : ℤ) : ℝ :=
  K + ∑ j ∈ Finset.range (S - s).toNat, m p j * (G (S - (j : ℤ)) - x)

noncomputable def g (p : ℕ → ℝ) (h : ℤ → ℝ) (s T : ℤ) : ℝ :=
  ∑ j ∈ Finset.range (T - s).toNat, m p j * h (T - (j : ℤ))

theorem F_eq_g (p : ℕ → ℝ) (K : ℝ) (G : ℤ → ℝ) (x : ℝ) (s S : ℤ) :
    F p K G x s S = K + g p (fun y => G y - x) s S := rfl

theorem F_of_le (p : ℕ → ℝ) (K : ℝ) (G : ℤ → ℝ) (x : ℝ) {s S : ℤ} (h : S ≤ s) :
    F p K G x s S = K := by
  have : (S - s).toNat = 0 := by omega
  simp [F, this]

theorem F_pred (p : ℕ → ℝ) (K : ℝ) (G : ℤ → ℝ) (x : ℝ) {s S : ℤ} (h : s ≤ S) :
    F p K G x (s - 1) S = F p K G x s S + m p (S - s).toNat * (G s - x) := by
  have h1 : (S - (s - 1)).toNat = (S - s).toNat + 1 := by omega
  have h2 : S - ((S - s).toNat : ℤ) = s := by omega
  simp only [F, h1, Finset.sum_range_succ, h2]
  ring

theorem F_eq (p : ℕ → ℝ) (K : ℝ) (G : ℤ → ℝ) (x : ℝ) (s S : ℤ) :
    F p K G x s S = (K + ∑ j ∈ Finset.range (S - s).toNat, m p j * G (S - (j : ℤ)))
      - x * M p (S - s).toNat := by
  unfold F M
  rw [add_sub_assoc, Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

section cF
variable (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) (K : ℝ) (G : ℤ → ℝ)

include hp hp0

theorem c_le_iff {s S : ℤ} (h : s < S) (x : ℝ) : c p K G s S ≤ x ↔ F p K G x s S ≤ 0 := by
  have hM := M_pos p hp hp0 (n := (S - s).toNat) (by omega)
  rw [F_eq, c, div_le_iff₀ hM]
  constructor <;> intro h' <;> linarith

theorem c_lt_iff {s S : ℤ} (h : s < S) (x : ℝ) : c p K G s S < x ↔ F p K G x s S < 0 := by
  have hM := M_pos p hp hp0 (n := (S - s).toNat) (by omega)
  rw [F_eq, c, div_lt_iff₀ hM]
  constructor <;> intro h' <;> linarith

theorem le_c_iff {s S : ℤ} (h : s < S) (x : ℝ) : x ≤ c p K G s S ↔ 0 ≤ F p K G x s S := by
  have hM := M_pos p hp hp0 (n := (S - s).toNat) (by omega)
  rw [F_eq, c, le_div_iff₀ hM]
  constructor <;> intro h' <;> linarith

theorem lt_c_iff {s S : ℤ} (h : s < S) (x : ℝ) : x < c p K G s S ↔ 0 < F p K G x s S := by
  have hM := M_pos p hp hp0 (n := (S - s).toNat) (by omega)
  rw [F_eq, c, lt_div_iff₀ hM]
  constructor <;> intro h' <;> linarith

theorem F_c_self {s S : ℤ} (h : s < S) : F p K G (c p K G s S) s S = 0 :=
  le_antisymm ((c_le_iff p hp hp0 K G h _).1 le_rfl) ((le_c_iff p hp hp0 K G h _).1 le_rfl)

theorem F_anti {x x' : ℝ} (hx : x ≤ x') (s S : ℤ) : F p K G x' s S ≤ F p K G x s S := by
  unfold F
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (m_nonneg p hp hp0 j)
  linarith

theorem F_step_ge {x : ℝ} {t S : ℤ} (ht : x ≤ G t) : F p K G x t S ≤ F p K G x (t - 1) S := by
  rcases le_or_gt t S with h | h
  · rw [F_pred p K G x h]
    have := mul_nonneg (m_nonneg p hp hp0 (S - t).toNat) (sub_nonneg.mpr ht)
    linarith
  · rw [F_of_le p K G x h.le, F_of_le p K G x (by omega)]

theorem F_step_le {x : ℝ} {t S : ℤ} (ht : G t ≤ x) : F p K G x (t - 1) S ≤ F p K G x t S := by
  rcases le_or_gt t S with h | h
  · rw [F_pred p K G x h]
    have := mul_nonneg (m_nonneg p hp hp0 (S - t).toNat) (sub_nonneg.mpr ht)
    nlinarith
  · rw [F_of_le p K G x h.le, F_of_le p K G x (by omega)]

theorem F_chain_ge_nat {x : ℝ} {S t₁ : ℤ} (k : ℕ) :
    (∀ t, t₁ < t → t ≤ t₁ + k → x ≤ G t) → F p K G x (t₁ + k) S ≤ F p K G x t₁ S := by
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hx
    have h1 := F_step_ge p hp hp0 K G (S := S) (x := x) (t := t₁ + ((k + 1 : ℕ) : ℤ))
      (hx _ (by push_cast; omega) le_rfl)
    have e : t₁ + ((k + 1 : ℕ) : ℤ) - 1 = t₁ + (k : ℤ) := by push_cast; ring
    rw [e] at h1
    exact h1.trans (ih (fun t ht1 ht2 => hx t ht1 (by push_cast; omega)))

theorem F_chain_le_nat {x : ℝ} {S t₁ : ℤ} (k : ℕ) :
    (∀ t, t₁ < t → t ≤ t₁ + k → G t ≤ x) → F p K G x t₁ S ≤ F p K G x (t₁ + k) S := by
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hx
    have h1 := F_step_le p hp hp0 K G (S := S) (x := x) (t := t₁ + ((k + 1 : ℕ) : ℤ))
      (hx _ (by push_cast; omega) le_rfl)
    have e : t₁ + ((k + 1 : ℕ) : ℤ) - 1 = t₁ + (k : ℤ) := by push_cast; ring
    rw [e] at h1
    exact (ih (fun t ht1 ht2 => hx t ht1 (by push_cast; omega))).trans h1

theorem F_chain_ge {x : ℝ} {S t₁ t₂ : ℤ} (h12 : t₁ ≤ t₂)
    (hx : ∀ t, t₁ < t → t ≤ t₂ → x ≤ G t) : F p K G x t₂ S ≤ F p K G x t₁ S := by
  have e : t₂ = t₁ + ((t₂ - t₁).toNat : ℤ) := by omega
  rw [e]
  exact F_chain_ge_nat p hp hp0 K G _ (fun t h1 h2 => hx t h1 (by omega))

theorem F_chain_le {x : ℝ} {S t₁ t₂ : ℤ} (h12 : t₁ ≤ t₂)
    (hx : ∀ t, t₁ < t → t ≤ t₂ → G t ≤ x) : F p K G x t₁ S ≤ F p K G x t₂ S := by
  have e : t₂ = t₁ + ((t₂ - t₁).toNat : ℤ) := by omega
  rw [e]
  exact F_chain_le_nat p hp hp0 K G _ (fun t h1 h2 => hx t h1 (by omega))

/-- Reduction in the reorder level `s`: a "crossing point" `a` (everything at or below `a` costs
at least `x`, and above `a` the set where `G > x` is an up-set) is optimal up to `K`. -/
theorem lemB {x : ℝ} {a S : ℤ} (hA : ∀ y, y ≤ a → x ≤ G y)
    (hQ : ∀ y z, a < y → y ≤ z → x < G y → x < G z) (s' : ℤ) :
    min K (F p K G x a S) ≤ F p K G x s' S := by
  rcases le_or_gt s' a with h | h
  · exact (min_le_right _ _).trans (F_chain_ge p hp hp0 K G h (fun t _ ht => hA t ht))
  · by_cases hall : ∀ y, a < y → y ≤ s' → G y ≤ x
    · exact (min_le_right _ _).trans (F_chain_le p hp hp0 K G h.le hall)
    · push Not at hall
      obtain ⟨y, hy1, hy2, hy3⟩ := hall
      refine (min_le_left _ _).trans ?_
      rcases le_or_gt S s' with hS | hS
      · rw [F_of_le p K G x hS]
      · have := F_chain_ge p hp hp0 K G (S := S) (x := x) hS.le
          (fun t ht1 _ => (hQ y t hy1 (by omega) hy3).le)
        rwa [F_of_le p K G x le_rfl] at this

theorem F_shift {x : ℝ} {s S d : ℤ}
    (hG : ∀ j : ℕ, G (S + d - (j : ℤ)) ≤ G (S - (j : ℤ))) :
    F p K G x (s + d) (S + d) ≤ F p K G x s S := by
  have e : (S + d - (s + d)) = S - s := by ring
  unfold F
  rw [e]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (m_nonneg p hp hp0 j)
  have := hG j
  linarith

end cF

/-! ## The renewal equation in the order-up-to level -/

theorem renewal_nat (p : ℕ → ℝ) (hp0 : p 0 < 1) (u : ℕ → ℝ) (n : ℕ) :
    (1 - p 0) * ∑ j ∈ Finset.range (n + 1), m p j * u j =
      u 0 + ∑ l ∈ Finset.range n, p (l + 1) * ∑ i ∈ Finset.range (n - l), m p i * u (l + 1 + i) := by
  have hne : (1 - p 0) ≠ 0 := by linarith
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, add_zero,
      m_zero]
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  | succ n ih =>
    have hm : (1 - p 0) * m p (n + 1) = ∑ l ∈ Finset.range (n + 1), p (l + 1) * m p (n - l) := by
      rw [m_succ, ← mul_assoc, mul_inv_cancel₀ hne, one_mul,
        ← Finset.sum_range_reflect (fun i => p (n + 1 - i) * m p i) (n + 1)]
      apply Finset.sum_congr rfl
      intro l hl
      have := Finset.mem_range.mp hl
      have e1 : n + 1 - (n + 1 - 1 - l) = l + 1 := by omega
      have e2 : n + 1 - 1 - l = n - l := by omega
      rw [e1, e2]
    have hm' : (1 - p 0) * m p (n + 1) =
        ∑ l ∈ Finset.range n, p (l + 1) * m p (n - l) + p (n + 1) * m p 0 := by
      rw [hm, Finset.sum_range_succ, Nat.sub_self]
    have h1 : ∀ l ∈ Finset.range n,
        p (l + 1) * ∑ i ∈ Finset.range (n + 1 - l), m p i * u (l + 1 + i)
          = p (l + 1) * ∑ i ∈ Finset.range (n - l), m p i * u (l + 1 + i)
            + p (l + 1) * m p (n - l) * u (n + 1) := by
      intro l hl
      have hl' : l < n := Finset.mem_range.mp hl
      rw [show n + 1 - l = (n - l) + 1 by omega, Finset.sum_range_succ,
        show l + 1 + (n - l) = n + 1 by omega]
      ring
    have hlast : ∑ i ∈ Finset.range (n + 1 - n), m p i * u (n + 1 + i) = m p 0 * u (n + 1) := by
      rw [show n + 1 - n = 1 by omega, Finset.sum_range_one, add_zero]
    have hsplit : ∑ l ∈ Finset.range (n + 1),
          p (l + 1) * ∑ i ∈ Finset.range (n + 1 - l), m p i * u (l + 1 + i)
        = ∑ l ∈ Finset.range n, p (l + 1) * ∑ i ∈ Finset.range (n - l), m p i * u (l + 1 + i)
          + (∑ l ∈ Finset.range n, p (l + 1) * m p (n - l)) * u (n + 1)
          + p (n + 1) * (m p 0 * u (n + 1)) := by
      rw [Finset.sum_range_succ, Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_mul,
        hlast]
    rw [Finset.sum_range_succ (fun j => m p j * u j) (n + 1), mul_add, ih, hsplit]
    linear_combination u (n + 1) * hm'

theorem renewal_int (p : ℕ → ℝ) (hp0 : p 0 < 1) (h : ℤ → ℝ) (s T : ℤ) (n : ℕ)
    (hn : (T - s).toNat = n + 1) :
    (1 - p 0) * g p h s T = h T + ∑ l ∈ Finset.range n, p (l + 1) * g p h s (T - (l + 1 : ℕ)) := by
  have key := renewal_nat p hp0 (fun j => h (T - (j : ℤ))) n
  unfold g
  rw [hn, key]
  simp only [Nat.cast_zero, sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := Finset.mem_range.mp hl
  have e : (T - ((l + 1 : ℕ) : ℤ) - s).toNat = n - l := by omega
  rw [e]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  push_cast
  ring

theorem lemR (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∀ n, ∑ l ∈ Finset.range n, p l ≤ 1)
    (hp0 : p 0 < 1) (h : ℤ → ℝ) (s B : ℤ) (μ : ℝ) (hμ : μ ≤ 0)
    (hbelow : ∀ T, T < B → μ ≤ g p h s T) (habove : ∀ T, B ≤ T → 0 < h T) :
    ∀ T, μ ≤ g p h s T := by
  have main : ∀ N : ℕ, ∀ T, (T - s).toNat = N → μ ≤ g p h s T := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro T hT
      rcases lt_or_ge T B with hTB | hTB
      · exact hbelow T hTB
      · cases N with
        | zero =>
          have : g p h s T = 0 := by simp [g, hT]
          rw [this]; exact hμ
        | succ n =>
          have hr := renewal_int p hp0 h s T n hT
          have hIH : ∀ l ∈ Finset.range n, p (l + 1) * μ ≤ p (l + 1) * g p h s (T - (l + 1 : ℕ)) := by
            intro l hl
            have hl' := Finset.mem_range.mp hl
            exact mul_le_mul_of_nonneg_left (ih (n - l) (by omega) _ (by omega)) (hp _)
          have hs1 := Finset.sum_le_sum hIH
          rw [← Finset.sum_mul] at hs1
          have hps : ∑ l ∈ Finset.range n, p (l + 1) ≤ 1 - p 0 := by
            have := hsum (n + 1)
            rw [Finset.sum_range_succ'] at this
            linarith
          have hpos := habove T hTB
          have h1p : 0 < 1 - p 0 := by linarith
          have : (∑ l ∈ Finset.range n, p (l + 1)) * μ ≥ (1 - p 0) * μ := by nlinarith
          by_contra hcon
          push Not at hcon
          nlinarith
  intro T
  exact main _ T rfl

/-! ## Shape of `G` -/

section Gshape
variable {G : ℤ → ℝ}

theorem monoLeft (hG : NegUnimodal G) {ys : ℤ} (hys : ∀ x, G ys ≤ G x) {x x' : ℤ}
    (h1 : x ≤ x') (h2 : x' ≤ ys) : G x' ≤ G x := by
  obtain ⟨mo, hA, hM⟩ := hG
  rcases le_or_gt x' mo with h | h
  · exact hA (Set.mem_Iic.mpr (h1.trans h)) (Set.mem_Iic.mpr h) h1
  · have : G x' ≤ G ys := hM (Set.mem_Ici.mpr h.le) (Set.mem_Ici.mpr (h.le.trans h2)) h2
    exact this.trans (hys x)

theorem monoRight (hG : NegUnimodal G) {ys : ℤ} (hys : ∀ x, G ys ≤ G x) {x x' : ℤ}
    (h1 : ys ≤ x) (h2 : x ≤ x') : G x ≤ G x' := by
  obtain ⟨mo, hA, hM⟩ := hG
  rcases le_or_gt mo x with h | h
  · exact hM (Set.mem_Ici.mpr h) (Set.mem_Ici.mpr (h.trans h2)) h2
  · have : G x ≤ G ys := hA (Set.mem_Iic.mpr (h1.trans h.le)) (Set.mem_Iic.mpr h.le) h1
    exact this.trans (hys x')

theorem antiBelow (hG : NegUnimodal G) {a : ℤ} (ha : G (a + 1) < G a) {y : ℤ} (hy : y ≤ a) :
    G a ≤ G y := by
  obtain ⟨mo, hA, hM⟩ := hG
  rcases lt_or_ge a mo with h | h
  · exact hA (Set.mem_Iic.mpr (hy.trans h.le)) (Set.mem_Iic.mpr h.le) hy
  · have := hM (Set.mem_Ici.mpr h) (Set.mem_Ici.mpr (by omega : mo ≤ a + 1)) (by omega : a ≤ a + 1)
    linarith

theorem quasi (hG : NegUnimodal G) {x : ℝ} {x0 y z : ℤ} (h0 : G x0 < x) (h1 : x0 ≤ y)
    (h2 : y ≤ z) (hy : x < G y) : x < G z := by
  obtain ⟨mo, hA, hM⟩ := hG
  rcases le_or_gt y mo with h | h
  · have := hA (Set.mem_Iic.mpr (h1.trans h)) (Set.mem_Iic.mpr h) h1
    linarith
  · have := hM (Set.mem_Ici.mpr h.le) (Set.mem_Ici.mpr (h.le.trans h2)) h2
    linarith

end Gshape

/-- The crossing lemma used at every invariant step. -/
theorem cross (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) (K : ℝ) {G : ℤ → ℝ}
    (hG : NegUnimodal G) {x : ℝ} {a : ℤ} (h1 : G (a + 1) < x) (h2 : x ≤ G a) (S s' : ℤ) :
    min K (F p K G x a S) ≤ F p K G x s' S := by
  have hlt : G (a + 1) < G a := lt_of_lt_of_le h1 h2
  apply lemB p hp hp0 K G
  · intro y hy
    exact h2.trans (antiBelow hG hlt hy)
  · intro y z hy hyz hxy
    exact quasi hG h1 (by omega) hyz hxy


/-! ## Mediant step and simple bounds -/

theorem mediant_up (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) (K : ℝ) (G : ℤ → ℝ)
    {s S : ℤ} (h : s + 1 < S) (hc : c p K G s S ≤ G (s + 1)) :
    c p K G (s + 1) S ≤ c p K G s S := by
  have h0 := F_c_self p hp hp0 K G (show s < S by omega)
  have hpred := F_pred p K G (c p K G s S) (show s + 1 ≤ S by omega)
  rw [add_sub_cancel_right, h0] at hpred
  have := mul_nonneg (m_nonneg p hp hp0 ((S - (s + 1)).toNat)) (sub_nonneg.mpr hc)
  rw [c_le_iff p hp hp0 K G h]
  linarith

theorem c0_bound (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) (K : ℝ) (hK : 0 < K)
    (G : ℤ → ℝ) (ystar : ℤ) {x : ℝ} {S : ℤ} (hyS : ystar < S)
    (hI3 : ∀ S' s', S' < S → 0 ≤ F p K G x s' S') : x ≤ G ystar + K := by
  have h := hI3 ystar (ystar - 1) hyS
  rw [F_pred p K G x le_rfl, F_of_le p K G x le_rfl, sub_self, Int.toNat_zero] at h
  have hm := one_le_m_zero p hp hp0
  by_contra hcon
  push Not at hcon
  nlinarith

theorem growth_bounds {K : ℝ} {G : ℤ → ℝ} (hgrowth : GrowthCond K G) {ys : ℤ}
    (hys : ∀ x, G ys ≤ G x) :
    ∃ B L : ℤ, (∀ y, B ≤ y → G ys + K < G y) ∧ (∀ y, y ≤ L → G ys + K < G y) := by
  obtain ⟨y0, hy0, hev⟩ := hgrowth
  have heq : G y0 = G ys := le_antisymm (hy0 ys) (hys y0)
  rw [Int.cofinite_eq, Filter.eventually_sup, Filter.eventually_atBot,
    Filter.eventually_atTop] at hev
  obtain ⟨⟨L, hL⟩, ⟨B, hB⟩⟩ := hev
  refine ⟨B, L, fun y hy => ?_, fun y hy => ?_⟩
  · rw [← heq]; exact hB y hy
  · rw [← heq]; exact hL y hy

theorem far_left (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) (K : ℝ) (hK : 0 < K)
    (G : ℤ → ℝ) (hG : NegUnimodal G) (ystar : ℤ) (hys : ∀ x, G ystar ≤ G x) {Lf : ℤ}
    (hLf : Lf < ystar) (hbig : G ystar + K < G Lf) : F p K G (G Lf) Lf ystar < 0 := by
  obtain ⟨n, hn⟩ : ∃ n, (ystar - Lf).toNat = n + 1 := ⟨(ystar - Lf).toNat - 1, by omega⟩
  unfold F
  rw [hn, Finset.sum_range_succ']
  have hrest : ∑ i ∈ Finset.range n,
      m p (i + 1) * (G (ystar - ((i + 1 : ℕ) : ℤ)) - G Lf) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hi' := Finset.mem_range.mp hi
    apply mul_nonpos_of_nonneg_of_nonpos (m_nonneg p hp hp0 _)
    have := monoLeft hG hys (x := Lf) (x' := ystar - ((i + 1 : ℕ) : ℤ))
      (by push_cast; omega) (by push_cast; omega)
    linarith
  have hm := one_le_m_zero p hp hp0
  simp only [Nat.cast_zero, sub_zero]
  nlinarith

/-! ## The invariant of the algorithm -/

section Alg
variable (p : ℕ → ℝ) (K : ℝ) (G : ℤ → ℝ) (ystar : ℤ)

def InvO (σ : AlgState) : Prop :=
  σ.c0 = c p K G σ.s σ.S0 ∧ σ.s < σ.S0 ∧ σ.S0 < σ.S ∧ G (σ.s + 1) < σ.c0 ∧ σ.c0 ≤ G σ.s ∧
    ystar < σ.S ∧ ∀ S' s', S' < σ.S → 0 ≤ F p K G σ.c0 s' S'

def InvP : Phase → AlgState → Prop
  | .step0, σ => σ.s ≤ ystar ∧ ∀ t, σ.s ≤ t → t ≤ ystar → 0 < F p K G (G t) t ystar
  | .outer, σ => InvO p K G ystar σ
  | .inner, σ => σ.s < σ.S0 ∧ σ.S0 = σ.S ∧ ystar < σ.S ∧ c p K G σ.s σ.S0 ≤ G σ.s ∧
      c p K G σ.s σ.S0 < σ.c0 ∧ G σ.S ≤ σ.c0 ∧ ∀ S' s', S' < σ.S → 0 ≤ F p K G σ.c0 s' S'
  | .done, σ => InvO p K G ystar σ ∧ σ.c0 < G σ.S

def Inv (σ : AlgState) : Prop := InvP p K G ystar σ.phase σ

end Alg

def bonus : Phase → ℤ
  | .outer => 1
  | _ => 0

theorem inv_step (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) (K : ℝ) (hK : 0 < K)
    (G : ℤ → ℝ) (hG : NegUnimodal G) (ystar : ℤ) (hys : ∀ x, G ystar ≤ G x)
    (σ : AlgState) (hσ : Inv p K G ystar σ) : Inv p K G ystar (step p K G ystar σ) := by
  obtain ⟨s, S, S0, c0, ph⟩ := σ
  cases ph with
  | step0 =>
    simp only [Inv, InvP] at hσ
    obtain ⟨hsy, ht⟩ := hσ
    simp only [step]
    split_ifs with hc
    · simp only [Inv, InvP, InvO]
      have hs1 : s - 1 < ystar := by omega
      have hGs : G (s - 1 + 1) < c p K G (s - 1) ystar := by
        rw [sub_add_cancel]
        have h0 := ht s le_rfl hsy
        have hpr := F_pred p K G (G s) hsy
        rw [sub_self, mul_zero, add_zero] at hpr
        rw [lt_c_iff p hp hp0 K G hs1, hpr]
        exact h0
      refine ⟨trivial, hs1, by omega, hGs, hc, by omega, ?_⟩
      intro S' s' hS'
      have hF0 : F p K G (c p K G (s - 1) ystar) (s - 1) ystar = 0 := F_c_self p hp hp0 K G hs1
      have hy : ∀ s'', 0 ≤ F p K G (c p K G (s - 1) ystar) s'' ystar := by
        intro s''
        have := cross p hp hp0 K hG hGs hc ystar s''
        rw [hF0] at this
        exact le_trans (le_min hK.le le_rfl) this
      rcases eq_or_lt_of_le (show S' ≤ ystar by omega) with h | h
      · rw [h]; exact hy s'
      · have hsh := F_shift p hp hp0 K G (x := c p K G (s - 1) ystar) (s := s') (S := S')
          (d := ystar - S') (fun j => monoLeft hG hys (by omega) (by omega))
        rw [show S' + (ystar - S') = ystar by ring] at hsh
        exact (hy _).trans hsh
    · simp only [Inv, InvP]
      refine ⟨by omega, ?_⟩
      intro t ht1 ht2
      rcases eq_or_lt_of_le ht1 with h | h
      · rw [← h]
        have hs1 : s - 1 < ystar := by omega
        push Not at hc
        exact (lt_c_iff p hp hp0 K G hs1 _).1 hc
      · exact ht t (by omega) ht2
  | outer =>
    simp only [Inv, InvP, InvO] at hσ
    obtain ⟨hc0, hsS0, hS0S, h1, h2, hyS, hI3⟩ := hσ
    simp only [step]
    split_ifs with hGS hc
    · simp only [Inv, InvP]
      exact ⟨by omega, trivial, hyS, by linarith, hc, hGS, hI3⟩
    · push Not at hc
      simp only [Inv, InvP, InvO]
      refine ⟨hc0, hsS0, by omega, h1, h2, by omega, ?_⟩
      intro S' s' hS'
      rcases lt_or_ge S' S with h | h
      · exact hI3 S' s' h
      · have hS'eq : S' = S := by omega
        rw [hS'eq]
        have hcr := cross p hp hp0 K hG h1 h2 S s'
        have hF : 0 ≤ F p K G c0 s S := (le_c_iff p hp hp0 K G (by omega) c0).1 hc
        exact le_trans (le_min hK.le hF) hcr
    · push Not at hGS
      simp only [Inv, InvP, InvO]
      exact ⟨⟨hc0, hsS0, hS0S, h1, h2, hyS, hI3⟩, hGS⟩
  | inner =>
    simp only [Inv, InvP] at hσ
    obtain ⟨hsS0, hS0S, hyS, hcG, hcc0, hGS, hI3⟩ := hσ
    simp only [step]
    split_ifs with hc
    · simp only [Inv, InvP]
      have hlt : s + 1 < S0 := by
        rcases lt_or_ge (s + 1) S0 with h | h
        · exact h
        · exfalso
          have he : s = S0 - 1 := by omega
          have hF := F_pred p K G (G S0) (le_refl S0)
          rw [F_of_le p K G _ le_rfl] at hF; simp only [sub_self, mul_zero, add_zero] at hF
          have : G S0 < c p K G (S0 - 1) S0 :=
            (lt_c_iff p hp hp0 K G (by omega) _).2 (by rw [hF]; exact hK)
          rw [he, show S0 - 1 + 1 = S0 by ring] at hc
          linarith
      have hmed := mediant_up p hp hp0 K G hlt hc
      exact ⟨hlt, hS0S, hyS, hmed.trans hc, hmed.trans_lt hcc0, hGS, hI3⟩
    · push Not at hc
      simp only [Inv, InvP, InvO]
      refine ⟨trivial, hsS0, by omega, hc, hcG, by omega, ?_⟩
      intro S' s' hS'
      rcases lt_or_ge S' S with h | h
      · exact (hI3 S' s' h).trans (F_anti p hp hp0 K G hcc0.le s' S')
      · have hS'eq : S' = S0 := by omega
        rw [hS'eq]
        have hcr := cross p hp hp0 K hG hc hcG S0 s'
        rw [F_c_self p hp hp0 K G hsS0] at hcr
        exact le_trans (le_min hK.le le_rfl) hcr
  | done =>
    simp only [step]
    exact hσ

theorem inv_iter (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) (K : ℝ) (hK : 0 < K)
    (G : ℤ → ℝ) (hG : NegUnimodal G) (ystar : ℤ) (hys : ∀ x, G ystar ≤ G x)
    (σ : AlgState) (hσ : Inv p K G ystar σ) :
    ∀ n : ℕ, Inv p K G ystar ((step p K G ystar)^[n] σ) := by
  intro n
  induction n with
  | zero => exact hσ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact inv_step p hp hp0 K hK G hG ystar hys _ ih

theorem opt_of_done (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∀ n, ∑ l ∈ Finset.range n, p l ≤ 1)
    (hp0 : p 0 < 1) (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (ystar : ℤ)
    (hys : ∀ x, G ystar ≤ G x) (σ : AlgState) (h : InvO p K G ystar σ) (hlt : σ.c0 < G σ.S) :
    IsOptimalPolicy p K G σ.s σ.S0 ∧ σ.c0 = c p K G σ.s σ.S0 := by
  obtain ⟨hc0, hsS0, hS0S, h1, h2, hyS, hI3⟩ := h
  refine ⟨⟨hsS0, ?_⟩, hc0⟩
  intro s' S' hs'S'
  rw [← hc0, le_c_iff p hp hp0 K G hs'S']
  rcases lt_or_ge S' σ.S with h | h
  · exact hI3 S' s' h
  · have hR := lemR p hp hsum hp0 (fun y => G y - σ.c0) s' σ.S (-K) (by linarith)
      (fun T hT => by
        have := hI3 T s' hT
        rw [F_eq_g] at this
        linarith)
      (fun T hT => by
        have := monoRight hG hys (le_of_lt hyS) hT
        show 0 < G T - σ.c0
        linarith) S'
    rw [F_eq_g]
    linarith

/-! ## Termination -/

theorem T1 (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) (K : ℝ) (hK : 0 < K)
    (G : ℤ → ℝ) (hG : NegUnimodal G) (ystar : ℤ) (hys : ∀ x, G ystar ≤ G x)
    (B : ℤ) (hB : ∀ y, B ≤ y → G ystar + K < G y) :
    ∀ N : ℕ, ∀ (s S S0 : ℤ) (c0 : ℝ) (ph : Phase), Inv p K G ystar ⟨s, S, S0, c0, ph⟩ →
      (ph = .outer ∨ ph = .inner) →
      (4 * (B + 1 - S) + 2 * (S - s) + bonus ph).toNat = N →
      ∃ n, ((step p K G ystar)^[n] ⟨s, S, S0, c0, ph⟩).phase = .done := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro s S S0 c0 ph hσ hph hN
  have hinv' := inv_step p hp hp0 K hK G hG ystar hys _ hσ
  have next : ∀ σ' : AlgState, step p K G ystar ⟨s, S, S0, c0, ph⟩ = σ' →
      (∃ n, ((step p K G ystar)^[n] σ').phase = .done) →
      ∃ n, ((step p K G ystar)^[n] ⟨s, S, S0, c0, ph⟩).phase = .done := by
    rintro σ' hσ' ⟨n, hn⟩
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, hσ']; exact hn⟩
  cases ph with
  | step0 => simp at hph
  | done => simp at hph
  | outer =>
    have hσ2 := hσ
    simp only [Inv, InvP, InvO] at hσ2
    obtain ⟨hc0, hsS0, hS0S, h1, h2, hyS, hI3⟩ := hσ2
    have hbd := c0_bound p hp hp0 K hK G ystar hyS hI3
    simp only [bonus] at hN
    by_cases hGS : G S ≤ c0
    · have hSB : S < B := by
        by_contra hh
        push Not at hh
        have := hB S hh
        linarith
      by_cases hc : c p K G s S < c0
      · have hst : step p K G ystar ⟨s, S, S0, c0, .outer⟩ = ⟨s, S, S, c0, .inner⟩ := by
          simp only [step, if_pos hGS, if_pos hc]
        rw [hst] at hinv'
        refine next _ hst (ih _ ?_ s S S c0 .inner hinv' (Or.inr rfl) rfl)
        simp only [bonus]
        omega
      · have hst : step p K G ystar ⟨s, S, S0, c0, .outer⟩ = ⟨s, S + 1, S0, c0, .outer⟩ := by
          simp only [step, if_pos hGS, if_neg hc]
        rw [hst] at hinv'
        refine next _ hst (ih _ ?_ s (S + 1) S0 c0 .outer hinv' (Or.inl rfl) rfl)
        simp only [bonus]
        omega
    · have hst : step p K G ystar ⟨s, S, S0, c0, .outer⟩ = ⟨s, S, S0, c0, .done⟩ := by
        simp only [step, if_neg hGS]
      exact ⟨1, by rw [Function.iterate_one, hst]⟩
  | inner =>
    have hσ2 := hσ
    simp only [Inv, InvP] at hσ2
    obtain ⟨hsS0, hS0S, hyS, hcG, hcc0, hGS, hI3⟩ := hσ2
    have hbd := c0_bound p hp hp0 K hK G ystar hyS hI3
    simp only [bonus] at hN
    have hSB : S < B := by
      by_contra hh
      push Not at hh
      have := hB S hh
      linarith
    by_cases hc : c p K G s S0 ≤ G (s + 1)
    · have hst : step p K G ystar ⟨s, S, S0, c0, .inner⟩ = ⟨s + 1, S, S0, c0, .inner⟩ := by
        simp only [step, if_pos hc]
      rw [hst] at hinv'
      refine next _ hst (ih _ ?_ (s + 1) S S0 c0 .inner hinv' (Or.inr rfl) rfl)
      simp only [bonus]
      omega
    · have hst : step p K G ystar ⟨s, S, S0, c0, .inner⟩ =
          ⟨s, S + 1, S0, c p K G s S0, .outer⟩ := by
        simp only [step, if_neg hc]
      rw [hst] at hinv'
      refine next _ hst (ih _ ?_ s (S + 1) S0 _ .outer hinv' (Or.inl rfl) rfl)
      simp only [bonus]
      omega

theorem T2 (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) (K : ℝ) (hK : 0 < K)
    (G : ℤ → ℝ) (hG : NegUnimodal G) (ystar : ℤ) (hys : ∀ x, G ystar ≤ G x)
    (B : ℤ) (hB : ∀ y, B ≤ y → G ystar + K < G y) (Lf : ℤ)
    (hLf : F p K G (G Lf) Lf ystar < 0) (hLfy : Lf ≤ ystar) :
    ∀ N : ℕ, ∀ (s S S0 : ℤ) (c0 : ℝ), Inv p K G ystar ⟨s, S, S0, c0, .step0⟩ →
      (s - Lf).toNat = N →
      ∃ n, ((step p K G ystar)^[n] ⟨s, S, S0, c0, .step0⟩).phase = .done := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro s S S0 c0 hσ hN
  have hinv' := inv_step p hp hp0 K hK G hG ystar hys _ hσ
  have next : ∀ σ' : AlgState, step p K G ystar ⟨s, S, S0, c0, .step0⟩ = σ' →
      (∃ n, ((step p K G ystar)^[n] σ').phase = .done) →
      ∃ n, ((step p K G ystar)^[n] ⟨s, S, S0, c0, .step0⟩).phase = .done := by
    rintro σ' hσ' ⟨n, hn⟩
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, hσ']; exact hn⟩
  have hσ2 := hσ
  simp only [Inv, InvP] at hσ2
  obtain ⟨hsy, ht⟩ := hσ2
  have hLs : Lf < s := by
    by_contra hh
    push Not at hh
    have := ht Lf hh hLfy
    linarith
  by_cases hc : c p K G (s - 1) ystar ≤ G (s - 1)
  · have hst : step p K G ystar ⟨s, S, S0, c0, .step0⟩ =
        ⟨s - 1, ystar + 1, ystar, c p K G (s - 1) ystar, .outer⟩ := by
      simp only [step, if_pos hc]
    rw [hst] at hinv'
    exact next _ hst (T1 p hp hp0 K hK G hG ystar hys B hB _ _ _ _ _ _ hinv' (Or.inl rfl) rfl)
  · have hst : step p K G ystar ⟨s, S, S0, c0, .step0⟩ = ⟨s - 1, S, S0, c0, .step0⟩ := by
      simp only [step, if_neg hc]
    rw [hst] at hinv'
    exact next _ hst (ih _ (by omega) (s - 1) S S0 c0 hinv' rfl)

end ZFSOne

open ZhengFedergruenSS.Algorithm in
theorem solution (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (ystar : ℤ) (hystar : ∀ x : ℤ, G ystar ≤ G x) :
    (∃ (n : ℕ) (out : ℤ × ℤ × ℝ), run D.φ K G ystar n = some out) ∧
      ∀ (n : ℕ) (s S₀ : ℤ) (c₀ : ℝ), run D.φ K G ystar n = some (s, S₀, c₀) →
        IsOptimalPolicy D.φ K G s S₀ ∧ c₀ = c D.φ K G s S₀ := by
  have hp := D.nonneg
  have hsum : ∀ n, ∑ l ∈ Finset.range n, D.φ l ≤ 1 :=
    fun n => sum_le_hasSum _ (fun i _ => D.nonneg i) D.hasSum
  obtain ⟨B, L, hB, hL⟩ := ZFSOne.growth_bounds hgrowth hystar
  have hinit : ZFSOne.Inv D.φ K G ystar (init ystar) := by
    simp only [ZFSOne.Inv, init, ZFSOne.InvP]
    refine ⟨le_rfl, ?_⟩
    intro t h1 h2
    have : t = ystar := le_antisymm h2 h1
    rw [this, ZFSOne.F_of_le _ _ _ _ le_rfl]
    exact hK
  constructor
  · have hLf := ZFSOne.far_left D.φ hp hp0 K hK G hG ystar hystar
      (Lf := min L (ystar - 1)) (by omega) (hL _ (min_le_left _ _))
    obtain ⟨n, hn⟩ := ZFSOne.T2 D.φ hp hp0 K hK G hG ystar hystar B hB _ hLf (by omega) _
      ystar ystar ystar 0 hinit rfl
    refine ⟨n, (((step D.φ K G ystar)^[n] (init ystar)).s,
      ((step D.φ K G ystar)^[n] (init ystar)).S0, ((step D.φ K G ystar)^[n] (init ystar)).c0), ?_⟩
    have hn' : ((step D.φ K G ystar)^[n] (init ystar)).phase = Phase.done := hn
    simp only [run, hn', if_true]
  · intro n s S₀ c₀ h
    simp only [run] at h
    split_ifs at h with hd
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hI := ZFSOne.inv_iter D.φ hp hp0 K hK G hG ystar hystar _ hinit n
    unfold ZFSOne.Inv at hI
    rw [hd] at hI
    simp only [ZFSOne.InvP] at hI
    exact ZFSOne.opt_of_done D.φ hp hsum hp0 K hK G hG ystar hystar _ hI.1 hI.2
