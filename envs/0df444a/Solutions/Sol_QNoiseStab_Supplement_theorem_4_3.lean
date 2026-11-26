-- Prove2me | solution 1 for QNoiseStab.Supplement.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @blake-holman
-- created : 2026-11-26T04:04:17.432451+00:00
-- url     : https://prove2.me/submissions/27fa987a-552d-434e-88db-ea465087ebd6

import Mathlib
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_FitsInSpace
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_successProb
import Definitions.Def_QNoiseStab_Supplement_IsStronglyUniversal
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_QNoiseStab_Supplement_CommitsCorrect
import Definitions.Def_QNoiseStab_phaseQuery

-- Solutions.SpaceAccounting
section
/-! Physical memory and the address register in the public instrument model. -/

namespace QNoiseStab.Supplement

/-- The trace-one start state requires at least one physical memory basis state. -/
theorem SpaceBoundedAlg.memory_nonempty {n d T : ℕ} [NeZero d] {W K V κ : Type}
    [Fintype W] [DecidableEq W] [Fintype K] [Fintype V] [Fintype κ]
    (A : SpaceBoundedAlg n d W K V κ T) : Nonempty ((Fin n × ZMod d) × W) := by
  by_contra h
  have : IsEmpty ((Fin n × ZMod d) × W) := ⟨fun w => h ⟨w⟩⟩
  simpa [Matrix.trace] using A.start_trace

/-- The address register must fit along with the phase register and the workspace. -/
theorem SpaceBoundedAlg.address_fits {n d T S : ℕ} [NeZero d] {W K V κ : Type}
    [Fintype W] [DecidableEq W] [Fintype K] [Fintype V] [Fintype κ]
    (A : SpaceBoundedAlg n d W K V κ T) (hA : A.FitsInSpace S) : n ≤ 2^S := by
  obtain ⟨⟨⟨_, _⟩, w⟩⟩ := A.memory_nonempty
  have : Nonempty W := ⟨w⟩
  have h₁ : n ≤ n*d := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne d))
  exact (h₁.trans (Nat.le_mul_of_pos_right _ Fintype.card_pos)).trans hA

theorem SpaceBoundedAlg.card_memory_le {n d T S : ℕ} [NeZero d] {W K V κ : Type}
    [Fintype W] [DecidableEq W] [Fintype K] [Fintype V] [Fintype κ]
    (A : SpaceBoundedAlg n d W K V κ T) (hA : A.FitsInSpace S) :
    Fintype.card ((Fin n × ZMod d) × W) ≤ 2^S := by
  simpa only [SpaceBoundedAlg.FitsInSpace, Fintype.card_prod, Fintype.card_fin, ZMod.card] using hA

end QNoiseStab.Supplement
end

-- Solutions.HashingCore.Fourier
section
/-!
# Fourier analysis on the Boolean cube

This module sets up the characters `χ_U(x) = (-1)^{∑_{i ∈ U} x_i}` on `{0,1}^n`,
their orthogonality, normalized Fourier coefficients, the low-degree predicate for
complex-valued functions, and the quadratic-form bound

`∑_x g(x) |f(x)|² ≤ ‖M‖_F ∑_x |f(x)|²`

for `f` of degree at most `t`, where `M_{UV} = ĝ(U △ V)` ranges over sets of size at
most `t`. The proof uses character orthogonality and finite sums.
-/


namespace QuantumNoiseStability.Hashing

open Finset

/-- Bit strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

variable {n : ℕ}

theorem card_bits (n : ℕ) : Fintype.card (Bits n) = 2 ^ n := by
  simp [Bits]

/-! ## Characters -/

/-- The sign contributed by coordinate `i` to the character of `U`. -/
def chiFactor (U : Finset (Fin n)) (x : Bits n) (i : Fin n) : ℝ :=
  if i ∈ U ∧ x i then -1 else 1

/-- The character `χ_U(x) = (-1)^{∑_{i ∈ U} x_i}`. -/
def chi (U : Finset (Fin n)) (x : Bits n) : ℝ := ∏ i, chiFactor U x i

theorem chiFactor_mul (U V : Finset (Fin n)) (x : Bits n) (i : Fin n) :
    chiFactor U x i * chiFactor V x i = chiFactor (symmDiff U V) x i := by
  unfold chiFactor
  by_cases hU : i ∈ U <;> by_cases hV : i ∈ V <;> by_cases hx : x i <;>
    simp [hU, hV, hx, Finset.mem_symmDiff]

theorem chi_mul (U V : Finset (Fin n)) (x : Bits n) :
    chi U x * chi V x = chi (symmDiff U V) x := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => chiFactor_mul U V x i)

@[simp] theorem chi_empty (x : Bits n) : chi ∅ x = 1 := by
  simp [chi, chiFactor]

theorem chi_mul_self (U : Finset (Fin n)) (x : Bits n) : chi U x * chi U x = 1 := by
  rw [chi_mul, symmDiff_self]
  exact chi_empty x

theorem chi_sq (U : Finset (Fin n)) (x : Bits n) : chi U x ^ 2 = 1 := by
  rw [sq]; exact chi_mul_self U x

theorem chi_eq_one_or_neg_one (U : Finset (Fin n)) (x : Bits n) :
    chi U x = 1 ∨ chi U x = -1 := by
  have h := chi_mul_self U x
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

theorem abs_chi (U : Finset (Fin n)) (x : Bits n) : |chi U x| = 1 := by
  rcases chi_eq_one_or_neg_one U x with h | h <;> simp [h]

/-- The single-coordinate sign `(-1)^{x_j}` is a character of degree one. -/
theorem chi_singleton (j : Fin n) (x : Bits n) :
    chi {j} x = if x j then -1 else 1 := by
  unfold chi chiFactor
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Summing a character over the cube. -/
theorem sum_chi (U : Finset (Fin n)) :
    ∑ x : Bits n, chi U x = if U = ∅ then (2 : ℝ) ^ n else 0 := by
  unfold chi
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
    (fun i b => chiFactor U (fun _ => b) i)
  rw [Fintype.piFinset_univ] at h
  have hfac : ∀ (x : Bits n) (i : Fin n), chiFactor U (fun _ => x i) i = chiFactor U x i := by
    intro x i; rfl
  simp_rw [hfac] at h
  rw [← h]
  have hinner : ∀ i : Fin n, ∑ b : Bool, chiFactor U (fun _ => b) i =
      if i ∈ U then 0 else 2 := by
    intro i
    unfold chiFactor
    by_cases hi : i ∈ U <;> simp [hi]
  simp_rw [hinner]
  by_cases hU : U = ∅
  · subst hU
    simp
  · rw [if_neg hU]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hU
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem sum_chi_mul_chi (U V : Finset (Fin n)) :
    ∑ x : Bits n, chi U x * chi V x = if U = V then (2 : ℝ) ^ n else 0 := by
  simp_rw [chi_mul]
  rw [sum_chi]
  congr 1
  simp

/-! ## Low-degree sets and Fourier coefficients -/

/-- Subsets of `[n]` of size at most `t`. -/
def lowSets (n t : ℕ) : Finset (Finset (Fin n)) := univ.filter (fun U => U.card ≤ t)

theorem mem_lowSets {t : ℕ} {U : Finset (Fin n)} : U ∈ lowSets n t ↔ U.card ≤ t := by
  simp [lowSets]

/-- `d_t = ∑_{j ≤ t} binom(n, j)`, the number of sets of size at most `t`. -/
def lowDim (n t : ℕ) : ℕ := (lowSets n t).card

/-- The normalized Fourier coefficient `ĝ(U) = 2^{-n} ∑_x g(x) χ_U(x)` of a real function. -/
noncomputable def fourierCoeff (g : Bits n → ℝ) (U : Finset (Fin n)) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x, g x * chi U x

/-- A complex-valued function on the cube has Fourier degree at most `t`: it is a
linear combination of characters indexed by sets of size at most `t`. -/
def LowDegree (t : ℕ) (f : Bits n → ℂ) : Prop :=
  ∃ a : Finset (Fin n) → ℂ, (∀ U, t < U.card → a U = 0) ∧
    ∀ x, f x = ∑ U, a U * (chi U x : ℂ)

namespace LowDegree

theorem mono {s t : ℕ} (hst : s ≤ t) {f : Bits n → ℂ} (hf : LowDegree s f) :
    LowDegree t f := by
  obtain ⟨a, ha, hfa⟩ := hf
  exact ⟨a, fun U hU => ha U (lt_of_le_of_lt hst hU), hfa⟩

theorem const (t : ℕ) (c : ℂ) : LowDegree t (fun _ : Bits n => c) := by
  refine ⟨fun U => if U = ∅ then c else 0, ?_, ?_⟩
  · intro U hU
    have : U ≠ ∅ := by
      rintro rfl
      simp at hU
    simp [this]
  · intro x
    simp [Finset.sum_ite_eq']

theorem zero (t : ℕ) : LowDegree t (fun _ : Bits n => (0 : ℂ)) := const t 0

theorem add {t : ℕ} {f g : Bits n → ℂ} (hf : LowDegree t f) (hg : LowDegree t g) :
    LowDegree t (fun x => f x + g x) := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  refine ⟨fun U => a U + b U, fun U hU => by simp [ha U hU, hb U hU], ?_⟩
  intro x
  simp only [hfa x, hgb x, add_mul, Finset.sum_add_distrib]

theorem smul {t : ℕ} (c : ℂ) {f : Bits n → ℂ} (hf : LowDegree t f) :
    LowDegree t (fun x => c * f x) := by
  obtain ⟨a, ha, hfa⟩ := hf
  refine ⟨fun U => c * a U, fun U hU => by simp [ha U hU], ?_⟩
  intro x
  simp only [hfa x, Finset.mul_sum, mul_assoc]

theorem sum {t : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Bits n → ℂ}
    (hf : ∀ i ∈ s, LowDegree t (f i)) :
    LowDegree t (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero t
  | insert i s hi ih =>
    have h1 := hf i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hi]
    exact h1.add h2

/-- Multiplying by a character of degree `|V|` raises the degree by at most `|V|`. -/
theorem mul_chi {t : ℕ} (V : Finset (Fin n)) {f : Bits n → ℂ} (hf : LowDegree t f) :
    LowDegree (t + V.card) (fun x => (chi V x : ℂ) * f x) := by
  obtain ⟨a, ha, hfa⟩ := hf
  refine ⟨fun U => a (symmDiff U V), ?_, ?_⟩
  · intro U hU
    apply ha
    have hsub : U ⊆ symmDiff U V ∪ V := by
      intro i hi
      by_cases hiV : i ∈ V
      · exact Finset.mem_union_right _ hiV
      · exact Finset.mem_union_left _ (Finset.mem_symmDiff.mpr (Or.inl ⟨hi, hiV⟩))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (symmDiff U V) V
    omega
  · intro x
    show (chi V x : ℂ) * f x = _
    rw [hfa x, Finset.mul_sum]
    have hinv : ∀ U : Finset (Fin n), symmDiff (symmDiff U V) V = U := by
      intro U
      rw [symmDiff_symmDiff_cancel_right]
    calc (∑ U, (chi V x : ℂ) * (a U * (chi U x : ℂ)))
        = ∑ U, a U * (chi (symmDiff U V) x : ℂ) := by
          apply Finset.sum_congr rfl
          intro U _
          rw [← chi_mul]
          push_cast
          ring
      _ = ∑ U, a (symmDiff U V) * (chi (symmDiff (symmDiff U V) V) x : ℂ) := by
          exact (Equiv.sum_comp ⟨fun U => symmDiff U V, fun U => symmDiff U V, hinv, hinv⟩
            (fun U => a U * (chi (symmDiff U V) x : ℂ))).symm
      _ = ∑ U, a (symmDiff U V) * (chi U x : ℂ) := by
          simp_rw [hinv]

/-- Multiplying by the single-bit sign `(-1)^{b ∧ x_j}` raises the degree by at most one. -/
theorem mul_sign {t : ℕ} (b : Bool) (j : Fin n) {f : Bits n → ℂ} (hf : LowDegree t f) :
    LowDegree (t + 1) (fun x => (if b ∧ x j then -1 else 1) * f x) := by
  cases b with
  | false =>
    convert hf.mono (Nat.le_succ t) using 2 with x
    simp
  | true =>
    have h := hf.mul_chi {j}
    simp only [Finset.card_singleton] at h
    convert h using 2 with x
    rw [chi_singleton]
    by_cases hx : x j <;> simp [hx]

end LowDegree

/-! ## Quadratic forms and the Frobenius bound -/

section Frobenius

variable {ι : Type*}

/-- A vector's image under a matrix is bounded in norm by the Frobenius norm of the
matrix times the norm of the vector. Stated with squared sums to avoid square roots. -/
theorem sum_normSq_mulVec_le [Fintype ι] (M : ι → ι → ℂ) (v : ι → ℂ) :
    ∑ i, ‖∑ j, M i j * v j‖ ^ 2 ≤ (∑ i, ∑ j, ‖M i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  calc ‖∑ j, M i j * v j‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖v j‖) ^ 2 := by
        gcongr
        calc ‖∑ j, M i j * v j‖ ≤ ∑ j, ‖M i j * v j‖ := norm_sum_le _ _
          _ = ∑ j, ‖M i j‖ * ‖v j‖ := by simp
    _ ≤ (∑ j, ‖M i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The quadratic form of a real matrix on a complex vector is bounded by the Frobenius
norm times the squared vector norm; here in squared form over a finite index set. -/
theorem normSq_quadratic_form_le (s : Finset ι) (M : ι → ι → ℝ) (a : ι → ℂ) :
    ‖∑ U ∈ s, ∑ V ∈ s, a U * (starRingEnd ℂ) (a V) * (M U V : ℂ)‖ ^ 2 ≤
      (∑ U ∈ s, ∑ V ∈ s, M U V ^ 2) * (∑ U ∈ s, ‖a U‖ ^ 2) ^ 2 := by
  set c : ι → ℂ := fun U => ∑ V ∈ s, (starRingEnd ℂ) (a V) * (M U V : ℂ) with hc
  have hrow : ∀ U ∈ s, ‖c U‖ ^ 2 ≤ (∑ V ∈ s, M U V ^ 2) * ∑ V ∈ s, ‖a V‖ ^ 2 := by
    intro U _
    calc ‖c U‖ ^ 2 ≤ (∑ V ∈ s, ‖a V‖ * |M U V|) ^ 2 := by
          gcongr
          calc ‖c U‖ ≤ ∑ V ∈ s, ‖(starRingEnd ℂ) (a V) * (M U V : ℂ)‖ := norm_sum_le _ _
            _ = ∑ V ∈ s, ‖a V‖ * |M U V| := by
              apply Finset.sum_congr rfl
              intro V _
              rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      _ = (∑ V ∈ s, |M U V| * ‖a V‖) ^ 2 := by simp_rw [mul_comm]
      _ ≤ (∑ V ∈ s, |M U V| ^ 2) * ∑ V ∈ s, ‖a V‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ V ∈ s, M U V ^ 2) * ∑ V ∈ s, ‖a V‖ ^ 2 := by simp [sq_abs]
  have hsum : ∑ U ∈ s, ∑ V ∈ s, a U * (starRingEnd ℂ) (a V) * (M U V : ℂ) =
      ∑ U ∈ s, a U * c U := by
    apply Finset.sum_congr rfl
    intro U _
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro V _
    ring
  rw [hsum]
  calc ‖∑ U ∈ s, a U * c U‖ ^ 2 ≤ (∑ U ∈ s, ‖a U‖ * ‖c U‖) ^ 2 := by
        gcongr
        calc ‖∑ U ∈ s, a U * c U‖ ≤ ∑ U ∈ s, ‖a U * c U‖ := norm_sum_le _ _
          _ = ∑ U ∈ s, ‖a U‖ * ‖c U‖ := by simp
    _ ≤ (∑ U ∈ s, ‖a U‖ ^ 2) * ∑ U ∈ s, ‖c U‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ U ∈ s, ‖a U‖ ^ 2) * ∑ U ∈ s, ((∑ V ∈ s, M U V ^ 2) * ∑ V ∈ s, ‖a V‖ ^ 2) := by
        gcongr with U hU
        exact hrow U hU
    _ = (∑ U ∈ s, ∑ V ∈ s, M U V ^ 2) * (∑ U ∈ s, ‖a U‖ ^ 2) ^ 2 := by
        rw [← Finset.sum_mul]
        ring

end Frobenius

/-! ## Parseval and the weighted second moment for low-degree functions -/

theorem sum_comm_innermost {α β γ M : Type*} [AddCommMonoid M] [Fintype α] [Fintype β]
    [Fintype γ] (F : α → β → γ → M) :
    ∑ x, ∑ U, ∑ V, F x U V = ∑ U, ∑ V, ∑ x, F x U V := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U _
  rw [Finset.sum_comm]

/-- Restrict a double sum to the low sets when the coefficients are supported there. -/
theorem double_sum_restrict_lowSets {t : ℕ} (a : Finset (Fin n) → ℂ)
    (ha : ∀ U, t < U.card → a U = 0) (G : Finset (Fin n) → Finset (Fin n) → ℂ) :
    ∑ U, ∑ V, a U * (starRingEnd ℂ) (a V) * G U V =
      ∑ U ∈ lowSets n t, ∑ V ∈ lowSets n t, a U * (starRingEnd ℂ) (a V) * G U V := by
  rw [← Finset.sum_subset (Finset.subset_univ (lowSets n t))]
  · apply Finset.sum_congr rfl
    intro U _
    rw [← Finset.sum_subset (Finset.subset_univ (lowSets n t))]
    intro V _ hV
    rw [mem_lowSets] at hV
    push Not at hV
    simp [ha V hV]
  · intro U _ hU
    rw [mem_lowSets] at hU
    push Not at hU
    simp [ha U hU]

theorem normSq_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem re_mul_conj_mul_ofReal (z : ℂ) (c : ℝ) :
    (z * (starRingEnd ℂ) z * (c : ℂ)).re = ‖z‖ ^ 2 * c := by
  rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem sum_normSq_of_lowDegree {t : ℕ} {f : Bits n → ℂ} (a : Finset (Fin n) → ℂ)
    (ha : ∀ U, t < U.card → a U = 0) (hfa : ∀ x, f x = ∑ U, a U * (chi U x : ℂ)) :
    ∑ x, ‖f x‖ ^ 2 = (2 : ℝ) ^ n * ∑ U ∈ lowSets n t, ‖a U‖ ^ 2 := by
  have hcomplex : ∀ x, (‖f x‖ ^ 2 : ℝ) =
      (∑ U, ∑ V, a U * (starRingEnd ℂ) (a V) * ((chi U x * chi V x : ℝ) : ℂ)).re := by
    intro x
    rw [normSq_eq_re_mul_conj]
    congr 1
    rw [hfa x, map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro U _
    apply Finset.sum_congr rfl
    intro V _
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [hcomplex]
  rw [← Complex.re_sum, sum_comm_innermost]
  have hortho : ∀ U V : Finset (Fin n),
      ∑ x : Bits n, a U * (starRingEnd ℂ) (a V) * ((chi U x * chi V x : ℝ) : ℂ) =
        a U * (starRingEnd ℂ) (a V) * ((if U = V then (2 : ℝ) ^ n else 0 : ℝ) : ℂ) := by
    intro U V
    rw [← Finset.mul_sum, ← sum_chi_mul_chi U V]
    push_cast
    rfl
  simp_rw [hortho]
  rw [double_sum_restrict_lowSets a ha, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  rw [Complex.re_sum]
  have hterm : ∀ V ∈ lowSets n t,
      (a U * (starRingEnd ℂ) (a V) * ((if U = V then (2 : ℝ) ^ n else 0 : ℝ) : ℂ)).re =
        if U = V then ‖a U‖ ^ 2 * (2 : ℝ) ^ n else 0 := by
    intro V _
    by_cases hUV : U = V
    · subst hUV
      simp only [ite_true]
      exact re_mul_conj_mul_ofReal (a U) _
    · simp [hUV]
  rw [Finset.sum_congr rfl hterm]
  have hU : U ∈ lowSets n t := by assumption
  rw [Finset.sum_ite_eq]
  simp [hU, mul_comm]

/-- The weighted second moment of a low-degree function is a Fourier quadratic form. -/
theorem sum_weight_normSq_of_lowDegree {t : ℕ} (g : Bits n → ℝ) {f : Bits n → ℂ}
    (a : Finset (Fin n) → ℂ) (ha : ∀ U, t < U.card → a U = 0)
    (hfa : ∀ x, f x = ∑ U, a U * (chi U x : ℂ)) :
    ∑ x, g x * ‖f x‖ ^ 2 = (2 : ℝ) ^ n *
      (∑ U ∈ lowSets n t, ∑ V ∈ lowSets n t,
        a U * (starRingEnd ℂ) (a V) * (fourierCoeff g (symmDiff U V) : ℂ)).re := by
  have hcomplex : ∀ x, (g x * ‖f x‖ ^ 2 : ℝ) =
      (∑ U, ∑ V, a U * (starRingEnd ℂ) (a V) * ((g x * chi (symmDiff U V) x : ℝ) : ℂ)).re := by
    intro x
    rw [normSq_eq_re_mul_conj, ← Complex.re_ofReal_mul]
    congr 1
    rw [hfa x, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro V _
    rw [map_mul, Complex.conj_ofReal, ← chi_mul]
    push_cast
    ring
  simp_rw [hcomplex]
  rw [← Complex.re_sum, sum_comm_innermost]
  have hcoef : ∀ U V : Finset (Fin n),
      ∑ x : Bits n, a U * (starRingEnd ℂ) (a V) * ((g x * chi (symmDiff U V) x : ℝ) : ℂ) =
        a U * (starRingEnd ℂ) (a V) *
          (((2 : ℝ) ^ n * fourierCoeff g (symmDiff U V) : ℝ) : ℂ) := by
    intro U V
    rw [← Finset.mul_sum]
    congr 1
    unfold fourierCoeff
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    push_cast
    rfl
  simp_rw [hcoef]
  rw [double_sum_restrict_lowSets a ha, ← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro U _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro V _
  push_cast
  ring

/-- The Frobenius quantity `‖W_t diag(g) W_t‖_F²` in the Fourier basis. -/
noncomputable def frobSq (t : ℕ) (g : Bits n → ℝ) : ℝ :=
  ∑ U ∈ lowSets n t, ∑ V ∈ lowSets n t, fourierCoeff g (symmDiff U V) ^ 2

theorem frobSq_nonneg (t : ℕ) (g : Bits n → ℝ) : 0 ≤ frobSq t g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Quadratic-form bound.** If the compressed centered matrix of `g` has Frobenius norm
at most `δ`, then the `g`-weighted second moment of every degree-`t` function is at most
`δ` times its plain second moment. -/
theorem sum_weight_normSq_le_of_lowDegree {t : ℕ} (g : Bits n → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : frobSq t g ≤ δ ^ 2) {f : Bits n → ℂ} (hf : LowDegree t f) :
    ∑ x, g x * ‖f x‖ ^ 2 ≤ δ * ∑ x, ‖f x‖ ^ 2 := by
  obtain ⟨a, ha, hfa⟩ := hf
  rw [sum_weight_normSq_of_lowDegree g a ha hfa, sum_normSq_of_lowDegree a ha hfa]
  set Q := ∑ U ∈ lowSets n t, ∑ V ∈ lowSets n t,
    a U * (starRingEnd ℂ) (a V) * (fourierCoeff g (symmDiff U V) : ℂ) with hQ
  set A := ∑ U ∈ lowSets n t, ‖a U‖ ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQbound : ‖Q‖ ≤ δ * A := by
    have h := normSq_quadratic_form_le (lowSets n t)
      (fun U V => fourierCoeff g (symmDiff U V)) a
    have h2 : ‖Q‖ ^ 2 ≤ (δ * A) ^ 2 := by
      calc ‖Q‖ ^ 2 ≤ frobSq t g * A ^ 2 := h
        _ ≤ δ ^ 2 * A ^ 2 := by gcongr
        _ = (δ * A) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  calc (2 : ℝ) ^ n * Q.re ≤ (2 : ℝ) ^ n * ‖Q‖ := by
        gcongr
        exact Complex.re_le_norm Q
    _ ≤ (2 : ℝ) ^ n * (δ * A) := by gcongr
    _ = δ * ((2 : ℝ) ^ n * A) := by ring

end QuantumNoiseStability.Hashing
end

-- Solutions.HashingCore.Hash
section
/-!
# Strongly universal hash families and the centered covariance

A uniform seed of any finite type selects a function between two Boolean cubes. Strong universality is stated in counting
form. Output labels are partial assignments `τ : Fin m → Option Bool`; the label `(K, z)`
of the proof draft is `τ` with support `K` and values `z`.

This module proves step 1 of the proof chain (the exact centered covariance) and step 2
(the Fourier-entry and Frobenius second moments).
-/


namespace QuantumNoiseStability.Hashing

open Finset

variable {n m : ℕ} {K : Type*} [Fintype K]

/-- Hashes of binary strings indexed by a finite seed type. -/
abbrev Family (K : Type*) (n m : ℕ) := K → Bits n → Bits m

/-- A family for which the algorithm may additionally query a binary seed. -/
abbrev HashFamily (L n m : ℕ) := Family (Bits L) n m

/-- Strong universality of the uniform description distribution, in counting form:
for `x ≠ y` and all outputs `a, b`, the number of descriptions with `h(x) = a` and
`h(y) = b` is exactly `Fintype.card K / 2^(2m)`. -/
def StronglyUniversal (H : Family K n m) : Prop :=
  ∀ x y : Bits n, x ≠ y → ∀ a b : Bits m,
    (univ.filter fun d => H d x = a ∧ H d y = b).card * 2 ^ (2 * m) = Fintype.card K

/-! ## Partial assignments as output labels -/

/-- A partial assignment of output bits. -/
abbrev Label (m : ℕ) := Fin m → Option Bool

namespace Label

/-- The set of assigned coordinates. -/
def support (τ : Label m) : Finset (Fin m) := univ.filter fun c => (τ c).isSome

/-- The number of assigned coordinates. -/
def size (τ : Label m) : ℕ := τ.support.card

theorem mem_support {τ : Label m} {c : Fin m} : c ∈ τ.support ↔ (τ c).isSome := by
  simp [support]

theorem size_le (τ : Label m) : τ.size ≤ m := by
  unfold size support
  exact (Finset.card_filter_le _ _).trans (by simp)

end Label

/-- The output `a` agrees with the partial assignment `τ`. -/
def Agree (a : Bits m) (τ : Label m) : Prop := ∀ c b, τ c = some b → a c = b

instance (a : Bits m) (τ : Label m) : Decidable (Agree a τ) :=
  inferInstanceAs (Decidable (∀ c b, τ c = some b → a c = b))

/-- The allowed values at coordinate `c` under `τ`. -/
def allowed (τ : Label m) (c : Fin m) : Finset Bool :=
  match τ c with
  | none => univ
  | some b => {b}

theorem mem_allowed {τ : Label m} {c : Fin m} {b : Bool} :
    b ∈ allowed τ c ↔ ∀ b', τ c = some b' → b = b' := by
  unfold allowed
  cases h : τ c with
  | none => simp
  | some b' => simp

theorem card_allowed (τ : Label m) (c : Fin m) :
    (allowed τ c).card = if (τ c).isSome then 1 else 2 := by
  unfold allowed
  cases h : τ c <;> simp

theorem agree_iff_mem_piFinset (a : Bits m) (τ : Label m) :
    Agree a τ ↔ a ∈ Fintype.piFinset (allowed τ) := by
  rw [Fintype.mem_piFinset]
  constructor
  · intro h c
    rw [mem_allowed]
    intro b' hb'
    exact h c b' hb'
  · intro h c b hb
    have := h c
    rw [mem_allowed] at this
    exact this b hb

/-- The number of outputs agreeing with a label of size `k` is `2^(m-k)`. -/
theorem card_agree (τ : Label m) :
    (univ.filter fun a : Bits m => Agree a τ).card = 2 ^ (m - τ.size) := by
  have hset : (univ.filter fun a : Bits m => Agree a τ) = Fintype.piFinset (allowed τ) := by
    ext a
    simp [agree_iff_mem_piFinset]
  rw [hset, Fintype.card_piFinset]
  simp_rw [card_allowed]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin m))) (fun c => (τ c).isSome)
  unfold Label.size Label.support
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem card_agree_mul (τ : Label m) :
    (univ.filter fun a : Bits m => Agree a τ).card * 2 ^ τ.size = 2 ^ m := by
  rw [card_agree, ← pow_add, Nat.sub_add_cancel (Label.size_le τ)]

/-! ## Projected marginal and joint distributions -/

section Counting

variable {H : Family K n m} (hH : StronglyUniversal H)
include hH

/-- Joint agreement at two distinct arguments has probability `2^(-2k)`. -/
theorem card_agree_pair (τ : Label m) {x y : Bits n} (hxy : x ≠ y) :
    (univ.filter fun d => Agree (H d x) τ ∧ Agree (H d y) τ).card * 2 ^ (2 * τ.size) = Fintype.card K := by
  set s := univ.filter fun d => Agree (H d x) τ ∧ Agree (H d y) τ with hs
  have hfib := Finset.card_eq_sum_card_fiberwise (s := s) (t := (univ : Finset (Bits m × Bits m)))
    (f := fun d => (H d x, H d y)) (fun _ _ => Finset.mem_univ _)
  have hterm : ∀ p : Bits m × Bits m,
      (s.filter fun d => (H d x, H d y) = p).card * 2 ^ (2 * m) =
        if Agree p.1 τ ∧ Agree p.2 τ then Fintype.card K else 0 := by
    rintro ⟨a, b⟩
    by_cases hp : Agree a τ ∧ Agree b τ
    · rw [if_pos hp, ← hH x y hxy a b]
      congr 2
      ext d
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1 ▸ hp.1, h2 ▸ hp.2⟩, h1, h2⟩
    · rw [if_neg hp]
      have : (s.filter fun d => (H d x, H d y) = (a, b)) = ∅ := by
        ext d
        simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
          Finset.notMem_empty, iff_false]
        rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact hp ⟨h3 ▸ h1, h4 ▸ h2⟩
      rw [this, Finset.card_empty, zero_mul]
  have hcount : (univ.filter fun p : Bits m × Bits m => Agree p.1 τ ∧ Agree p.2 τ).card =
      2 ^ (m - τ.size) * 2 ^ (m - τ.size) := by
    have := Finset.card_product (univ.filter fun a : Bits m => Agree a τ)
      (univ.filter fun a : Bits m => Agree a τ)
    rw [card_agree] at this
    rw [← this]
    congr 1
    ext p
    simp [Finset.mem_product]
  have hmain : s.card * 2 ^ (2 * m) = Fintype.card K * (2 ^ (m - τ.size) * 2 ^ (m - τ.size)) := by
    rw [hfib, Finset.sum_mul]
    simp_rw [hterm]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, hcount,
      mul_comm]
  have hk := Label.size_le τ
  have hpow : 2 ^ (2 * m) = 2 ^ (2 * τ.size) * (2 ^ (m - τ.size) * 2 ^ (m - τ.size)) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hpow, ← mul_assoc] at hmain
  have hpos : 0 < 2 ^ (m - τ.size) * 2 ^ (m - τ.size) := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos hmain

/-- Agreement at one argument has probability `2^(-k)`; the domain must have at least
two points so that a second distinct argument exists. -/
theorem card_agree_single (hn : 1 ≤ n) (τ : Label m) (x : Bits n) :
    (univ.filter fun d => Agree (H d x) τ).card * 2 ^ τ.size = Fintype.card K := by
  obtain ⟨y, hxy⟩ : ∃ y : Bits n, x ≠ y := by
    refine ⟨fun i => !x i, ?_⟩
    intro h
    have := congrFun h ⟨0, hn⟩
    simp at this
  set s := univ.filter fun d => Agree (H d x) τ with hs
  have hfib := Finset.card_eq_sum_card_fiberwise (s := s) (t := (univ : Finset (Bits m × Bits m)))
    (f := fun d => (H d x, H d y)) (fun _ _ => Finset.mem_univ _)
  have hterm : ∀ p : Bits m × Bits m,
      (s.filter fun d => (H d x, H d y) = p).card * 2 ^ (2 * m) =
        if Agree p.1 τ then Fintype.card K else 0 := by
    rintro ⟨a, b⟩
    by_cases hp : Agree a τ
    · rw [if_pos hp, ← hH x y hxy a b]
      congr 2
      ext d
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1 ▸ hp, h1, h2⟩
    · rw [if_neg hp]
      have : (s.filter fun d => (H d x, H d y) = (a, b)) = ∅ := by
        ext d
        simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
          Finset.notMem_empty, iff_false]
        rintro ⟨h1, h3, _⟩
        exact hp (h3 ▸ h1)
      rw [this, Finset.card_empty, zero_mul]
  have hcount : (univ.filter fun p : Bits m × Bits m => Agree p.1 τ).card =
      2 ^ (m - τ.size) * 2 ^ m := by
    have := Finset.card_product (univ.filter fun a : Bits m => Agree a τ) (univ : Finset (Bits m))
    rw [card_agree, Finset.card_univ, card_bits] at this
    rw [← this]
    congr 1
    ext p
    simp [Finset.mem_product]
  have hmain : s.card * 2 ^ (2 * m) = Fintype.card K * (2 ^ (m - τ.size) * 2 ^ m) := by
    rw [hfib, Finset.sum_mul]
    simp_rw [hterm]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, hcount,
      mul_comm]
  have hk := Label.size_le τ
  have hpow : 2 ^ (2 * m) = 2 ^ τ.size * (2 ^ (m - τ.size) * 2 ^ m) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hpow, ← mul_assoc] at hmain
  have hpos : 0 < 2 ^ (m - τ.size) * 2 ^ m := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos hmain

end Counting

/-! ## The centered correctness indicator and its covariance -/

/-- The indicator of the event `h_d(x)` agrees with `τ`, as a real number. -/
def indicator (H : Family K n m) (τ : Label m) (d : K) (x : Bits n) : ℝ :=
  if Agree (H d x) τ then 1 else 0

/-- The centered correctness function `f_{h,K,z}(x) = 1[h(x)_K = z] - 2^{-k}`. -/
noncomputable def centered (H : Family K n m) (τ : Label m) (d : K) (x : Bits n) : ℝ :=
  indicator H τ d x - ((2 : ℝ) ^ τ.size)⁻¹

omit [Fintype K] in
theorem indicator_mul_self (H : Family K n m) (τ : Label m) (d : K) (x : Bits n) :
    indicator H τ d x * indicator H τ d x = indicator H τ d x := by
  unfold indicator
  split_ifs <;> simp

section Moments

variable {H : Family K n m} (hH : StronglyUniversal H) (hn : 1 ≤ n)
include hH hn

theorem sum_indicator (τ : Label m) (x : Bits n) :
    ∑ d, indicator H τ d x = (Fintype.card K : ℝ) * ((2 : ℝ) ^ τ.size)⁻¹ := by
  unfold indicator
  rw [Finset.sum_boole]
  have h := card_agree_single hH hn τ x
  have h' : ((univ.filter fun d => Agree (H d x) τ).card : ℝ) * (2 : ℝ) ^ τ.size = (Fintype.card K : ℝ) := by
    exact_mod_cast h
  rw [← eq_div_iff (by positivity)] at h'
  rw [h', div_eq_mul_inv]

omit hn in
theorem sum_indicator_mul (τ : Label m) {x y : Bits n} (hxy : x ≠ y) :
    ∑ d, indicator H τ d x * indicator H τ d y =
      (Fintype.card K : ℝ) * (((2 : ℝ) ^ τ.size)⁻¹) ^ 2 := by
  unfold indicator
  simp_rw [ite_mul, one_mul, zero_mul, ← ite_and]
  rw [Finset.sum_boole]
  have h := card_agree_pair hH τ hxy
  have h' : ((univ.filter fun d => Agree (H d x) τ ∧ Agree (H d y) τ).card : ℝ) *
      (2 : ℝ) ^ (2 * τ.size) = (Fintype.card K : ℝ) := by
    exact_mod_cast h
  rw [← eq_div_iff (by positivity)] at h'
  rw [h', div_eq_mul_inv, inv_pow, ← pow_mul, mul_comm τ.size 2]

/-- **Step 1: centered covariance.**
`E_h[f_{h,K,z}(x) f_{h,K,z}(y)] = 2^{-k}(1 - 2^{-k}) 1[x = y]`, in unnormalized form. -/
theorem sum_centered_mul (τ : Label m) (x y : Bits n) :
    ∑ d, centered H τ d x * centered H τ d y =
      (Fintype.card K : ℝ) * (((2 : ℝ) ^ τ.size)⁻¹ * (1 - ((2 : ℝ) ^ τ.size)⁻¹)) *
        (if x = y then 1 else 0) := by
  set p : ℝ := ((2 : ℝ) ^ τ.size)⁻¹ with hp
  have hexpand : ∀ d, centered H τ d x * centered H τ d y =
      indicator H τ d x * indicator H τ d y - p * indicator H τ d x - p * indicator H τ d y
        + p * p := by
    intro d
    unfold centered
    ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    sum_indicator hH hn τ x, sum_indicator hH hn τ y]
  by_cases hxy : x = y
  · subst hxy
    simp_rw [indicator_mul_self]
    rw [sum_indicator hH hn τ x, ite_true]
    ring
  · rw [sum_indicator_mul hH τ hxy, if_neg hxy]
    ring

/-- **Step 2: Fourier-entry second moment.**
`E_h[ f̂_{h,K,z}(U)² ] = 2^{-n-k}(1-2^{-k})` for every `U`, in unnormalized form. -/
theorem sum_fourierCoeff_sq (τ : Label m) (U : Finset (Fin n)) :
    ∑ d, fourierCoeff (centered H τ d) U ^ 2 =
      (Fintype.card K : ℝ) * ((2 : ℝ) ^ n)⁻¹ * (((2 : ℝ) ^ τ.size)⁻¹ * (1 - ((2 : ℝ) ^ τ.size)⁻¹)) := by
  unfold fourierCoeff
  have hsq : ∀ d, (((2 : ℝ) ^ n)⁻¹ * ∑ x, centered H τ d x * chi U x) ^ 2 =
      (((2 : ℝ) ^ n)⁻¹) ^ 2 *
        ∑ x, ∑ y, (chi U x * chi U y) * (centered H τ d x * centered H τ d y) := by
    intro d
    rw [mul_pow, sq (∑ x, _), Finset.sum_mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp_rw [hsq]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (univ : Finset K)) (t := (univ : Finset (Bits n)))]
  simp_rw [← Finset.mul_sum, sum_centered_mul hH hn τ]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [chi_mul_self, one_mul]
  rw [Finset.sum_const, Finset.card_univ, card_bits, nsmul_eq_mul]
  push_cast
  field_simp

/-- **Lemma 1 (Frobenius second moment).**
`E_h ‖W_t (Π_{h,K,z} - 2^{-k} I) W_t‖_F² = d_t² 2^{-n-k}(1-2^{-k})`, in unnormalized form. -/
theorem sum_frobSq (t : ℕ) (τ : Label m) :
    ∑ d, frobSq t (centered H τ d) =
      (Fintype.card K : ℝ) * ((lowDim n t : ℝ) ^ 2 * ((2 : ℝ) ^ n)⁻¹ *
        (((2 : ℝ) ^ τ.size)⁻¹ * (1 - ((2 : ℝ) ^ τ.size)⁻¹))) := by
  unfold frobSq
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (univ : Finset K)) (t := lowSets n t)]
  simp_rw [sum_fourierCoeff_sq hH hn τ]
  rw [Finset.sum_const, Finset.sum_const, smul_smul, nsmul_eq_mul]
  unfold lowDim
  push_cast
  ring

end Moments

end QuantumNoiseStability.Hashing
end

-- Solutions.HashCounting
section
/-! Counting strongly universal functions under the uniform distribution on a finite seed set. -/

namespace QNoiseStab.Supplement

open QuantumNoiseStability.Hashing

theorem IsStronglyUniversal.binary_counts {ι : Type} [Fintype ι] {n m : ℕ}
    {H : Family ι n m} (hH : IsStronglyUniversal H) : StronglyUniversal H := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    intro x x' _ a b
    simp
  | inr h =>
    intro x x' hx a b
    have hcount := (div_eq_div_iff (by positivity : (Fintype.card ι : ℝ) ≠ 0)
      (by positivity : (Fintype.card (Bits m) : ℝ)^2 ≠ 0)).mp (hH x x' hx a b)
    rw [one_mul, card_bits, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Nat.mul_comm m 2] at hcount
    exact_mod_cast hcount

end QNoiseStab.Supplement
end

-- Solutions.HashingCore.GoodSet
section
/-!
# The common good set of hash descriptions

Step 3 of the proof chain. With `t₀ = ⌊n/32⌋`, `g = min{m, ⌊n/64⌋}`, `δ = 2^{-n/8}`, a
seed is *good* when every centered compressed correctness matrix for a label of
size between `1` and `g` has squared Frobenius norm at most `δ²`.

The main results are the exact label-sum identity (`sum_labels_frobSq`), the binomial
bounds `d_{t₀}⁴ ≤ 2^n` and `(∑_{j ≤ ⌊n/64⌋} binom(n,j))⁸ ≤ 2^n`, and the Markov bound
`Pr[not good] ≤ δ` (`card_not_good_le`). Finally, `indicator_sum_le_of_good` is Lemma 3
in quadratic-form language.
-/


namespace QuantumNoiseStability.Hashing

open Finset

variable {n m : ℕ} {K : Type*} [Fintype K]

/-! ## Parameters -/

/-- `t₀ = ⌊n/32⌋`. -/
def t0 (n : ℕ) : ℕ := n / 32

/-- `g = min{m, ⌊n/64⌋}`. -/
def gBound (n m : ℕ) : ℕ := min m (n / 64)

/-- `δ = 2^{-n/8}` with real division in the exponent. -/
noncomputable def delta (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℝ) / 8)

theorem delta_pos (n : ℕ) : 0 < delta n := by
  unfold delta
  positivity

theorem delta_pow_eight (n : ℕ) : delta n ^ 8 = ((2 : ℝ) ^ n)⁻¹ := by
  unfold delta
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have : -(n : ℝ) / 8 * ((8 : ℕ) : ℝ) = -(n : ℝ) := by push_cast; ring
  rw [this, Real.rpow_neg (by norm_num), Real.rpow_natCast]

theorem delta_le_one (n : ℕ) : delta n ≤ 1 := by
  unfold delta
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- `δ ≤ 2^{-k}` whenever `8k ≤ n`. -/
theorem delta_le_inv_pow {k : ℕ} (hk : 8 * k ≤ n) : delta n ≤ ((2 : ℝ) ^ k)⁻¹ := by
  unfold delta
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (8 : ℝ) * k ≤ n := by exact_mod_cast hk
  linarith

/-! ## Binomial-sum bounds -/

theorem lowDim_eq_sum_choose (n t : ℕ) :
    lowDim n t = ∑ j ∈ range (t + 1), n.choose j := by
  unfold lowDim
  rw [Finset.card_eq_sum_card_fiberwise (f := fun U : Finset (Fin n) => U.card)
    (t := range (t + 1))]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hset : (lowSets n t).filter (fun U => U.card = j) = powersetCard j univ := by
      ext U
      simp only [Finset.mem_filter, mem_lowSets, Finset.mem_powersetCard, Finset.subset_univ,
        true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨h ▸ Nat.lt_succ_iff.mp hj, h⟩
    rw [hset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro U hU
    rw [Finset.mem_coe, mem_lowSets] at hU
    simp only [Finset.mem_coe, Finset.mem_range]
    omega

/-- `∑_{j ≤ q} binom(n,j) · b^n ≤ b^q (b+1)^n` for `q ≤ n` and `b ≥ 1`. -/
theorem sum_choose_mul_pow_le (n q b : ℕ) (hq : q ≤ n) (hb : 1 ≤ b) :
    (∑ j ∈ range (q + 1), n.choose j) * b ^ n ≤ b ^ q * (b + 1) ^ n := by
  have hbin : (b + 1) ^ n = ∑ j ∈ range (n + 1), n.choose j * b ^ (n - j) := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    rw [one_pow, one_mul, mul_comm, Nat.cast_id]
  rw [hbin, Finset.mul_sum, Finset.sum_mul]
  calc ∑ j ∈ range (q + 1), n.choose j * b ^ n
      ≤ ∑ j ∈ range (q + 1), b ^ q * (n.choose j * b ^ (n - j)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_range] at hj
        have hjq : j ≤ q := Nat.lt_succ_iff.mp hj
        have : b ^ n = b ^ j * b ^ (n - j) := by
          rw [← pow_add, Nat.add_sub_cancel' (hjq.trans hq)]
        rw [this]
        have hpow : b ^ j ≤ b ^ q := Nat.pow_le_pow_right hb hjq
        calc n.choose j * (b ^ j * b ^ (n - j)) = b ^ j * (n.choose j * b ^ (n - j)) := by ring
          _ ≤ b ^ q * (n.choose j * b ^ (n - j)) := Nat.mul_le_mul_right _ hpow
    _ ≤ ∑ j ∈ range (n + 1), b ^ q * (n.choose j * b ^ (n - j)) := by
        have hsub : range (q + 1) ⊆ range (n + 1) := Finset.range_subset_range.mpr (by omega)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

theorem thirtythree_pow : 33 ^ 32 ≤ 8 * 32 ^ 32 := by norm_num

theorem sixtyfive_pow : 65 ^ 32 ≤ 2 * 64 ^ 32 := by norm_num

/-- `d_{t₀}⁴ ≤ 2^n`. -/
theorem lowDim_t0_pow_four_le (n : ℕ) : lowDim n (t0 n) ^ 4 ≤ 2 ^ n := by
  rw [lowDim_eq_sum_choose]
  set d := ∑ j ∈ range (t0 n + 1), n.choose j with hd
  have h1 : d * 32 ^ n ≤ 32 ^ (t0 n) * 33 ^ n :=
    sum_choose_mul_pow_le n (t0 n) 32 (Nat.div_le_self n 32) (by norm_num)
  -- raise to the 32nd power
  have h2 : (d * 32 ^ n) ^ 32 ≤ (32 ^ (t0 n) * 33 ^ n) ^ 32 := Nat.pow_le_pow_left h1 32
  have h3 : (32 ^ (t0 n)) ^ 32 ≤ 32 ^ n := by
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    unfold t0
    omega
  have h4 : (33 ^ n) ^ 32 ≤ 8 ^ n * (32 ^ n) ^ 32 := by
    calc (33 ^ n) ^ 32 = (33 ^ 32) ^ n := by rw [← pow_mul, mul_comm, pow_mul]
      _ ≤ (8 * 32 ^ 32) ^ n := Nat.pow_le_pow_left thirtythree_pow n
      _ = 8 ^ n * (32 ^ n) ^ 32 := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 32 n]
  have h5 : d ^ 32 * (32 ^ n) ^ 32 ≤ 32 ^ n * (8 ^ n * (32 ^ n) ^ 32) := by
    calc d ^ 32 * (32 ^ n) ^ 32 = (d * 32 ^ n) ^ 32 := by rw [mul_pow]
      _ ≤ (32 ^ (t0 n) * 33 ^ n) ^ 32 := h2
      _ = (32 ^ (t0 n)) ^ 32 * (33 ^ n) ^ 32 := by rw [mul_pow]
      _ ≤ 32 ^ n * (8 ^ n * (32 ^ n) ^ 32) := Nat.mul_le_mul h3 h4
  have h6 : d ^ 32 ≤ 32 ^ n * 8 ^ n := by
    have hpos : 0 < (32 ^ n) ^ 32 := by positivity
    have : d ^ 32 * (32 ^ n) ^ 32 ≤ (32 ^ n * 8 ^ n) * (32 ^ n) ^ 32 := by
      calc d ^ 32 * (32 ^ n) ^ 32 ≤ 32 ^ n * (8 ^ n * (32 ^ n) ^ 32) := h5
        _ = (32 ^ n * 8 ^ n) * (32 ^ n) ^ 32 := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have h7 : 32 ^ n * 8 ^ n = (2 ^ n) ^ 8 := by
    rw [← mul_pow, ← pow_mul, mul_comm n 8, pow_mul]
    norm_num
  have h8 : (d ^ 4) ^ 8 ≤ (2 ^ n) ^ 8 := by
    rw [← pow_mul]
    rw [h7] at h6
    exact h6
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h8

/-- `(∑_{j ≤ ⌊n/64⌋} binom(n,j))⁸ ≤ 2^n`. -/
theorem sum_choose_div64_pow_eight_le (n : ℕ) :
    (∑ j ∈ range (n / 64 + 1), n.choose j) ^ 8 ≤ 2 ^ n := by
  set B := ∑ j ∈ range (n / 64 + 1), n.choose j with hB
  have h1 : B * 64 ^ n ≤ 64 ^ (n / 64) * 65 ^ n :=
    sum_choose_mul_pow_le n (n / 64) 64 (Nat.div_le_self n 64) (by norm_num)
  have h2 : (B * 64 ^ n) ^ 32 ≤ (64 ^ (n / 64) * 65 ^ n) ^ 32 := Nat.pow_le_pow_left h1 32
  have h3 : (64 ^ (n / 64)) ^ 32 ≤ 64 ^ (n / 2) := by
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  have h4 : (65 ^ n) ^ 32 ≤ 2 ^ n * (64 ^ n) ^ 32 := by
    calc (65 ^ n) ^ 32 = (65 ^ 32) ^ n := by rw [← pow_mul, mul_comm, pow_mul]
      _ ≤ (2 * 64 ^ 32) ^ n := Nat.pow_le_pow_left sixtyfive_pow n
      _ = 2 ^ n * (64 ^ n) ^ 32 := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 32 n]
  have h5 : B ^ 32 * (64 ^ n) ^ 32 ≤ 64 ^ (n / 2) * (2 ^ n * (64 ^ n) ^ 32) := by
    calc B ^ 32 * (64 ^ n) ^ 32 = (B * 64 ^ n) ^ 32 := by rw [mul_pow]
      _ ≤ (64 ^ (n / 64) * 65 ^ n) ^ 32 := h2
      _ = (64 ^ (n / 64)) ^ 32 * (65 ^ n) ^ 32 := by rw [mul_pow]
      _ ≤ 64 ^ (n / 2) * (2 ^ n * (64 ^ n) ^ 32) := Nat.mul_le_mul h3 h4
  have h6 : B ^ 32 ≤ 64 ^ (n / 2) * 2 ^ n := by
    have hpos : 0 < (64 ^ n) ^ 32 := by positivity
    have : B ^ 32 * (64 ^ n) ^ 32 ≤ (64 ^ (n / 2) * 2 ^ n) * (64 ^ n) ^ 32 := by
      calc B ^ 32 * (64 ^ n) ^ 32 ≤ 64 ^ (n / 2) * (2 ^ n * (64 ^ n) ^ 32) := h5
        _ = (64 ^ (n / 2) * 2 ^ n) * (64 ^ n) ^ 32 := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have h7 : 64 ^ (n / 2) * 2 ^ n ≤ (2 ^ n) ^ 4 := by
    have : (64 : ℕ) ^ (n / 2) = 2 ^ (6 * (n / 2)) := by
      rw [pow_mul]; norm_num
    rw [this, ← pow_add, ← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  have h8 : (B ^ 8) ^ 4 ≤ (2 ^ n) ^ 4 := by
    rw [← pow_mul]
    exact h6.trans h7
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h8

/-- The number of labels of size at most `g` is at most `∑_{j ≤ ⌊n/64⌋} binom(n,j)`
when `m ≤ n` and `g ≤ ⌊n/64⌋`. -/
theorem sum_choose_le (hmn : m ≤ n) (g : ℕ) (hg : g ≤ n / 64) :
    ∑ k ∈ Icc 1 g, m.choose k ≤ ∑ j ∈ range (n / 64 + 1), n.choose j := by
  calc ∑ k ∈ Icc 1 g, m.choose k ≤ ∑ k ∈ Icc 1 g, n.choose k :=
        Finset.sum_le_sum fun k _ => Nat.choose_le_choose k hmn
    _ ≤ ∑ j ∈ range (n / 64 + 1), n.choose j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_Icc] at hk
          rw [Finset.mem_range]
          omega
        · intros; positivity

/-! ## Counting labels -/

/-- Labels whose support is exactly `K`. -/
theorem card_support_eq (K : Finset (Fin m)) :
    (univ.filter fun τ : Label m => τ.support = K).card = 2 ^ K.card := by
  have hset : (univ.filter fun τ : Label m => τ.support = K) =
      Fintype.piFinset (fun c => if c ∈ K then ({some true, some false} : Finset (Option Bool))
        else {none}) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h c
      have hc : (τ c).isSome ↔ c ∈ K := by
        rw [← h, Label.mem_support]
      by_cases hcK : c ∈ K
      · rw [if_pos hcK]
        have := hc.mpr hcK
        cases hτ : τ c with
        | none => simp [hτ] at this
        | some b => cases b <;> simp
      · rw [if_neg hcK]
        cases hτ : τ c with
        | none => simp
        | some b => exact absurd (hc.mp (by simp [hτ])) hcK
    · intro h
      ext c
      rw [Label.mem_support]
      have := h c
      by_cases hcK : c ∈ K
      · rw [if_pos hcK] at this
        simp only [hcK, iff_true]
        cases hτ : τ c with
        | none => simp [hτ] at this
        | some b => simp
      · rw [if_neg hcK] at this
        simp only [hcK, iff_false]
        simp only [Finset.mem_singleton] at this
        simp [this]
  rw [hset, Fintype.card_piFinset]
  have hcard : ∀ c : Fin m, (if c ∈ K then ({some true, some false} : Finset (Option Bool))
      else {none}).card = if c ∈ K then 2 else 1 := by
    intro c
    split_ifs <;> simp
  simp_rw [hcard]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- The number of labels of size `k` is `binom(m,k) 2^k`. -/
theorem card_size_eq (k : ℕ) :
    (univ.filter fun τ : Label m => τ.size = k).card = m.choose k * 2 ^ k := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun τ : Label m => τ.support)
    (t := powersetCard k univ)]
  · have hterm : ∀ K ∈ powersetCard k univ,
        ((univ.filter fun τ : Label m => τ.size = k).filter fun τ => τ.support = K).card =
          2 ^ k := by
      intro K hK
      rw [Finset.mem_powersetCard] at hK
      rw [← hK.2, ← card_support_eq K]
      congr 1
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h
        refine ⟨?_, h⟩
        unfold Label.size
        rw [h, hK.2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  · intro τ hτ
    rw [Finset.mem_coe, Finset.mem_filter] at hτ
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hτ.2⟩

/-- The labels of size between `1` and `g`. -/
def labels (m g : ℕ) : Finset (Label m) := univ.filter fun τ => 1 ≤ τ.size ∧ τ.size ≤ g

theorem mem_labels {g : ℕ} {τ : Label m} : τ ∈ labels m g ↔ 1 ≤ τ.size ∧ τ.size ≤ g := by
  simp [labels]

/-- Summing a function of the size over labels of size between `1` and `g`. -/
theorem sum_labels_eq (g : ℕ) (F : ℕ → ℝ) :
    ∑ τ ∈ labels m g, F τ.size = ∑ k ∈ Icc 1 g, (m.choose k * 2 ^ k : ℝ) * F k := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := labels m g) (t := Icc 1 g)
    (g := fun τ => τ.size)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hfilter : (labels m g).filter (fun τ => τ.size = k) =
        univ.filter fun τ : Label m => τ.size = k := by
      ext τ
      simp only [Finset.mem_filter, mem_labels, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨⟨h ▸ hk.1, h ▸ hk.2⟩, h⟩
    rw [Finset.sum_congr rfl (fun τ hτ => by rw [(Finset.mem_filter.mp hτ).2]), hfilter,
      Finset.sum_const, card_size_eq, nsmul_eq_mul]
    push_cast
    ring
  · intro τ hτ
    rw [mem_labels] at hτ
    rw [Finset.mem_Icc]
    exact hτ

/-! ## The label sum of Frobenius norms -/

section LabelSum

variable {H : Family K n m} (hH : StronglyUniversal H) (hn : 1 ≤ n)
include hH hn

/-- **Step 3 (exact label sum).**
`E_h ∑_{1 ≤ |K| ≤ g} ∑_z ‖W_t(Π_{h,K,z} - 2^{-k} I) W_t‖_F² = d_t² 2^{-n} ∑_{k=1}^g binom(m,k)(1-2^{-k})`,
in unnormalized form. -/
theorem sum_labels_frobSq (t g : ℕ) :
    ∑ d, ∑ τ ∈ labels m g, frobSq t (centered H τ d) =
      (Fintype.card K : ℝ) * ((lowDim n t : ℝ) ^ 2 * ((2 : ℝ) ^ n)⁻¹ *
        ∑ k ∈ Icc 1 g, (m.choose k : ℝ) * (1 - ((2 : ℝ) ^ k)⁻¹)) := by
  rw [Finset.sum_comm]
  simp_rw [sum_frobSq hH hn t]
  have h := sum_labels_eq (m := m) g (fun k => (Fintype.card K : ℝ) * ((lowDim n t : ℝ) ^ 2 *
    ((2 : ℝ) ^ n)⁻¹ * (((2 : ℝ) ^ k)⁻¹ * (1 - ((2 : ℝ) ^ k)⁻¹))))
  rw [h, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  field_simp

/-- The label sum is at most `#K d_t² 2^{-n} ∑_{k=1}^g binom(m,k)`. -/
theorem sum_labels_frobSq_le (t g : ℕ) :
    ∑ d, ∑ τ ∈ labels m g, frobSq t (centered H τ d) ≤
      (Fintype.card K : ℝ) * ((lowDim n t : ℝ) ^ 2 * ((2 : ℝ) ^ n)⁻¹ *
        ∑ k ∈ Icc 1 g, (m.choose k : ℝ)) := by
  rw [sum_labels_frobSq hH hn t g]
  gcongr with k _
  have : 0 ≤ ((2 : ℝ) ^ k)⁻¹ := by positivity
  exact mul_le_of_le_one_right (by positivity) (by linarith)

end LabelSum

/-! ## The good set -/

/-- A description is good when every centered compressed correctness matrix of a label of
size between `1` and `g` has squared Frobenius norm at most `δ²`. -/
def Good (H : Family K n m) (d : K) : Prop :=
  ∀ τ : Label m, 1 ≤ τ.size → τ.size ≤ gBound n m →
    frobSq (t0 n) (centered H τ d) ≤ delta n ^ 2

noncomputable instance (H : Family K n m) (d : K) : Decidable (Good H d) :=
  Classical.dec _

omit [Fintype K] in
theorem lt_sum_of_not_good {H : Family K n m} {d : K} (hd : ¬ Good H d) :
    delta n ^ 2 < ∑ τ ∈ labels m (gBound n m), frobSq (t0 n) (centered H τ d) := by
  unfold Good at hd
  push Not at hd
  obtain ⟨τ, h1, h2, h3⟩ := hd
  calc delta n ^ 2 < frobSq (t0 n) (centered H τ d) := h3
    _ ≤ ∑ τ ∈ labels m (gBound n m), frobSq (t0 n) (centered H τ d) :=
        Finset.single_le_sum (f := fun τ => frobSq (t0 n) (centered H τ d))
          (fun τ _ => frobSq_nonneg _ _) (mem_labels.mpr ⟨h1, h2⟩)

/-- The number of descriptions that are not good, times `δ²`, is at most the label sum. -/
theorem card_not_good_mul_le (H : Family K n m) :
    ((univ.filter fun d => ¬ Good H d).card : ℝ) * delta n ^ 2 ≤
      ∑ d, ∑ τ ∈ labels m (gBound n m), frobSq (t0 n) (centered H τ d) := by
  calc ((univ.filter fun d => ¬ Good H d).card : ℝ) * delta n ^ 2
      = ∑ d ∈ univ.filter (fun d => ¬ Good H d), delta n ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ d ∈ univ.filter (fun d => ¬ Good H d),
          ∑ τ ∈ labels m (gBound n m), frobSq (t0 n) (centered H τ d) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [Finset.mem_filter] at hd
        exact (lt_sum_of_not_good hd.2).le
    _ ≤ ∑ d, ∑ τ ∈ labels m (gBound n m), frobSq (t0 n) (centered H τ d) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intros
        exact Finset.sum_nonneg fun _ _ => frobSq_nonneg _ _

/-- The numerical core of Lemma 2: `d_{t₀}² 2^{-n} B ≤ δ³` where `B = ∑_{j ≤ ⌊n/64⌋} binom(n,j)`. -/
theorem numeric_core (n : ℕ) :
    (lowDim n (t0 n) : ℝ) ^ 2 * ((2 : ℝ) ^ n)⁻¹ *
      (∑ j ∈ range (n / 64 + 1), n.choose j : ℝ) ≤ delta n ^ 3 := by
  set d : ℝ := (lowDim n (t0 n) : ℝ) with hd
  set B : ℝ := ∑ j ∈ range (n / 64 + 1), n.choose j with hB
  set δ := delta n with hδ
  have hδpos : 0 < δ := delta_pos n
  have hd0 : 0 ≤ d := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hδ8 : δ ^ 8 = ((2 : ℝ) ^ n)⁻¹ := delta_pow_eight n
  have hd4 : d ^ 4 ≤ (2 : ℝ) ^ n := by
    rw [hd]
    exact_mod_cast lowDim_t0_pow_four_le n
  have hB8 : B ^ 8 ≤ (2 : ℝ) ^ n := by
    rw [hB]
    exact_mod_cast sum_choose_div64_pow_eight_le n
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  -- (d δ²)⁴ ≤ 1 and (B δ)⁸ ≤ 1
  have hdδ : d * δ ^ 2 ≤ 1 := by
    have : (d * δ ^ 2) ^ 4 ≤ 1 := by
      calc (d * δ ^ 2) ^ 4 = d ^ 4 * δ ^ 8 := by ring
        _ ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ n)⁻¹ := by rw [hδ8]; gcongr
        _ = 1 := mul_inv_cancel₀ h2n.ne'
    exact (pow_le_one_iff_of_nonneg (by positivity) (by norm_num)).mp this
  have hBδ : B * δ ≤ 1 := by
    have : (B * δ) ^ 8 ≤ 1 := by
      calc (B * δ) ^ 8 = B ^ 8 * δ ^ 8 := by ring
        _ ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ n)⁻¹ := by rw [hδ8]; gcongr
        _ = 1 := mul_inv_cancel₀ h2n.ne'
    exact (pow_le_one_iff_of_nonneg (by positivity) (by norm_num)).mp this
  calc d ^ 2 * ((2 : ℝ) ^ n)⁻¹ * B = (d * δ ^ 2) ^ 2 * (B * δ) * δ ^ 3 := by
        rw [← hδ8]; ring
    _ ≤ 1 ^ 2 * 1 * δ ^ 3 := by gcongr
    _ = δ ^ 3 := by ring

/-- **Lemma 2.** The number of descriptions that are not good is at most `δ * Fintype.card K`, so a
random description fails to be good with probability at most `δ = 2^{-n/8}`. -/
theorem card_not_good_le {H : Family K n m} (hH : StronglyUniversal H) (hn : 1 ≤ n)
    (hmn : m ≤ n) :
    ((univ.filter fun d => ¬ Good H d).card : ℝ) ≤ delta n * (Fintype.card K : ℝ) := by
  have hδ := delta_pos n
  have h1 := card_not_good_mul_le H
  have h2 := sum_labels_frobSq_le hH hn (t0 n) (gBound n m)
  have h3 : (∑ k ∈ Icc 1 (gBound n m), (m.choose k : ℝ)) ≤
      (∑ j ∈ range (n / 64 + 1), n.choose j : ℝ) := by
    exact_mod_cast sum_choose_le hmn (gBound n m) (min_le_right _ _)
  have h4 := numeric_core n
  have hmain : ((univ.filter fun d => ¬ Good H d).card : ℝ) * delta n ^ 2 ≤
      (Fintype.card K : ℝ) * delta n ^ 3 := by
    calc ((univ.filter fun d => ¬ Good H d).card : ℝ) * delta n ^ 2
        ≤ ∑ d, ∑ τ ∈ labels m (gBound n m), frobSq (t0 n) (centered H τ d) := h1
      _ ≤ (Fintype.card K : ℝ) * ((lowDim n (t0 n) : ℝ) ^ 2 * ((2 : ℝ) ^ n)⁻¹ *
            ∑ k ∈ Icc 1 (gBound n m), (m.choose k : ℝ)) := h2
      _ ≤ (Fintype.card K : ℝ) * ((lowDim n (t0 n) : ℝ) ^ 2 * ((2 : ℝ) ^ n)⁻¹ *
            ∑ j ∈ range (n / 64 + 1), (n.choose j : ℝ)) := by gcongr
      _ ≤ (Fintype.card K : ℝ) * delta n ^ 3 := by gcongr
  have hδ2 : 0 < delta n ^ 2 := by positivity
  have : ((univ.filter fun d => ¬ Good H d).card : ℝ) * delta n ^ 2 ≤
      (delta n * (Fintype.card K : ℝ)) * delta n ^ 2 := by
    calc ((univ.filter fun d => ¬ Good H d).card : ℝ) * delta n ^ 2
        ≤ (Fintype.card K : ℝ) * delta n ^ 3 := hmain
      _ = (delta n * (Fintype.card K : ℝ)) * delta n ^ 2 := by ring
  exact le_of_mul_le_mul_right this hδ2

/-! ## Lemma 3: the quadratic-form consequence of goodness -/

omit [Fintype K] in
/-- **Lemma 3 (quadratic form).** For a good description, a label `τ` with
`1 ≤ |τ| ≤ g`, and a function `f` of Fourier degree at most `t₀`,
`∑_x 1[h(x) ∥ τ] |f(x)|² ≤ (2^{-|τ|} + δ) ∑_x |f(x)|²`. -/
theorem indicator_sum_le_of_good {H : Family K n m} {d : K} (hd : Good H d)
    (τ : Label m) (h1 : 1 ≤ τ.size) (h2 : τ.size ≤ gBound n m)
    {f : Bits n → ℂ} (hf : LowDegree (t0 n) f) :
    ∑ x, indicator H τ d x * ‖f x‖ ^ 2 ≤
      (((2 : ℝ) ^ τ.size)⁻¹ + delta n) * ∑ x, ‖f x‖ ^ 2 := by
  have hc := sum_weight_normSq_le_of_lowDegree (centered H τ d) (delta_pos n).le
    (hd τ h1 h2) hf
  have hsplit : ∀ x, indicator H τ d x * ‖f x‖ ^ 2 =
      centered H τ d x * ‖f x‖ ^ 2 + ((2 : ℝ) ^ τ.size)⁻¹ * ‖f x‖ ^ 2 := by
    intro x
    unfold centered
    ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

end QuantumNoiseStability.Hashing
end

-- Solutions.HashingCore.Model
section
/-!
# The finite quantum bit-query model

An algorithm is a finite list of steps acting on a finite workspace basis `W`.

* An `Operation` is an arbitrary input-independent quantum operation between queries: a
  finite family of Kraus operators `op j`, each carrying an output record
  `out j : List (Fin m × Bool)` (claims "coordinate `c` has value `b`", usually at most
  one). The family is subnormalized: `∑_j ‖op j v‖² ≤ ‖v‖²`. Unitaries, standard-basis
  measurements, resets, and output emissions are all instances. Adaptive behaviour is
  realized inside the workspace: a later operation may act differently on the different
  basis states, so measured values that remain in `W` steer the computation, and nothing
  outside `W` is remembered. Emitted claims are attached to the branch index only; they
  are not accessible to later steps except through what the algorithm keeps in `W`. This
  is the manuscript's convention that the whole state is stored in qubits, so every
  classical record available to later steps counts in the dimension of `W`.
* A `Query` addresses, for each basis state `w`, a bit position `idx w` of the input
  (a description bit or an argument bit) with phase `phase w`; on input `u` it applies
  the diagonal unitary `(-1)^{phase(w) · u[idx w]}`. This is the standard phase oracle
  `|i, p, w⟩ ↦ (-1)^{p · u_i} |i, p, w⟩` with the index and phase registers read from the
  workspace basis state; a query in superposition over description and argument positions
  is one such step. A phase of `false` is a no-op query. An algorithm that halts
  adaptively after at most `T` queries on every execution is represented with exactly
  `T` query steps, the surplus steps having phase `false` on the halted basis states, so
  the worst-case query count is the number of query steps.

The classical history of an execution is the sequence of branch indices of the
operations. `run l u v h` is the unnormalized state at the end of history `h` on input
`u` from the initial state `v`; `‖run l u v h‖²` is the probability of that history.
`claims l h` is the ordered output record of the history.

This module proves that the model is subnormalized (`sum_mass_run_le`), that runs
decompose along list concatenation (`run_append`), and the low-degree bridge
(`lowDegree_run`): with the description fixed, every workspace component of the state
after `q` query steps has Fourier degree at most `q` in the argument.
-/


namespace QuantumNoiseStability.Hashing

open Finset

set_option linter.unusedSectionVars false

variable {L n m : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- Query positions: description bits or argument bits. -/
abbrev Pos (L n : ℕ) := Fin L ⊕ Fin n

/-- The joint input: a description and an argument. -/
abbrev Input (L n : ℕ) := Bits L × Bits n

/-- The bit of the input at a query position. -/
def Input.bit (u : Input L n) : Pos L n → Bool
  | Sum.inl i => u.1 i
  | Sum.inr j => u.2 j

/-- Workspace states: complex amplitude vectors over the basis `W`. -/
abbrev State (W : Type) := W → ℂ

/-- Squared norm of a workspace state. -/
noncomputable def mass (v : State W) : ℝ := ∑ w, ‖v w‖ ^ 2

theorem mass_nonneg (v : State W) : 0 ≤ mass v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The standard basis state `e w`. -/
def basis (w : W) : State W := Pi.single w 1

theorem mass_basis (w : W) : mass (basis w) = 1 := by
  unfold mass basis
  rw [Finset.sum_eq_single w]
  · simp
  · intro w' _ hw'
    simp [hw']
  · intro h
    exact absurd (Finset.mem_univ w) h

/-- An input-independent operation between queries: Kraus operators with output records. -/
structure Operation (W : Type) [Fintype W] (m : ℕ) where
  /-- Number of branches. -/
  N : ℕ
  /-- Kraus operators. -/
  op : Fin N → Matrix W W ℂ
  /-- The output record emitted on each branch. -/
  out : Fin N → List (Fin m × Bool)
  /-- Subnormalization: total branch mass does not exceed the input mass. -/
  sub : ∀ v : State W, ∑ j, mass ((op j).mulVec v) ≤ mass v

/-- A bit query. -/
structure Query (W : Type) (L n : ℕ) where
  /-- The queried position, per basis state. -/
  idx : W → Pos L n
  /-- The phase bit, per basis state. -/
  phase : W → Bool

/-- The sign `(-1)^{phase(w) · u[idx w]}`. -/
def Query.sign (q : Query W L n) (u : Input L n) (w : W) : ℂ :=
  if q.phase w ∧ u.bit (q.idx w) then -1 else 1

/-- The oracle unitary of a query on input `u`. -/
def Query.matrix (q : Query W L n) (u : Input L n) : Matrix W W ℂ :=
  Matrix.diagonal (q.sign u)

theorem Query.matrix_mulVec (q : Query W L n) (u : Input L n) (v : State W) (w : W) :
    (q.matrix u).mulVec v w = q.sign u w * v w := by
  unfold Query.matrix
  rw [Matrix.mulVec_diagonal]

theorem Query.norm_sign (q : Query W L n) (u : Input L n) (w : W) : ‖q.sign u w‖ = 1 := by
  unfold Query.sign
  split_ifs <;> simp

theorem Query.mass_mulVec (q : Query W L n) (u : Input L n) (v : State W) :
    mass ((q.matrix u).mulVec v) = mass v := by
  unfold mass
  apply Finset.sum_congr rfl
  intro w _
  rw [Query.matrix_mulVec, norm_mul, Query.norm_sign, one_mul]

/-- A step of an algorithm. -/
inductive Step (W : Type) [Fintype W] (L n m : ℕ)
  | op : Operation W m → Step W L n m
  | query : Query W L n → Step W L n m

/-- The classical history type of a list of steps. -/
def Hist : List (Step W L n m) → Type
  | [] => Unit
  | Step.op K :: rest => Fin K.N × Hist rest
  | Step.query _ :: rest => Hist rest

instance instFintypeHist : (l : List (Step W L n m)) → Fintype (Hist l)
  | [] => inferInstanceAs (Fintype Unit)
  | Step.op K :: rest =>
      haveI := instFintypeHist rest
      inferInstanceAs (Fintype (Fin K.N × Hist rest))
  | Step.query _ :: rest => instFintypeHist rest

/-- The unnormalized state at the end of history `h` on input `u` from initial state `v`. -/
def run : (l : List (Step W L n m)) → Input L n → State W → Hist l → State W
  | [], _, v, _ => v
  | Step.op K :: rest, u, v, h => run rest u ((K.op h.1).mulVec v) h.2
  | Step.query q :: rest, u, v, h => run rest u ((q.matrix u).mulVec v) h

/-- The ordered output record along a history. -/
def claims : (l : List (Step W L n m)) → Hist l → List (Fin m × Bool)
  | [], _ => []
  | Step.op K :: rest, h => K.out h.1 ++ claims rest h.2
  | Step.query _ :: rest, h => claims rest h

/-- The number of query steps. -/
def queries : List (Step W L n m) → ℕ
  | [] => 0
  | Step.op _ :: rest => queries rest
  | Step.query _ :: rest => queries rest + 1

@[simp] theorem run_nil (u : Input L n) (v : State W) (h : Hist ([] : List (Step W L n m))) :
    run [] u v h = v := rfl

@[simp] theorem run_op (K : Operation W m) (rest : List (Step W L n m)) (u : Input L n)
    (v : State W) (h : Hist (Step.op K :: rest)) :
    run (Step.op K :: rest) u v h = run rest u ((K.op h.1).mulVec v) h.2 := rfl

@[simp] theorem run_query (q : Query W L n) (rest : List (Step W L n m)) (u : Input L n)
    (v : State W) (h : Hist (Step.query q :: rest)) :
    run (Step.query q :: rest) u v h = run rest u ((q.matrix u).mulVec v) h := rfl

@[simp] theorem claims_nil (h : Hist ([] : List (Step W L n m))) : claims [] h = [] := rfl

@[simp] theorem claims_op (K : Operation W m) (rest : List (Step W L n m))
    (h : Hist (Step.op K :: rest)) :
    claims (Step.op K :: rest) h = K.out h.1 ++ claims rest h.2 := rfl

@[simp] theorem claims_query (q : Query W L n) (rest : List (Step W L n m))
    (h : Hist (Step.query q :: rest)) :
    claims (Step.query q :: rest) h = claims rest h := rfl

@[simp] theorem queries_nil : queries ([] : List (Step W L n m)) = 0 := rfl
@[simp] theorem queries_op (K : Operation W m) (rest : List (Step W L n m)) :
    queries (Step.op K :: rest) = queries rest := rfl
@[simp] theorem queries_query (q : Query W L n) (rest : List (Step W L n m)) :
    queries (Step.query q :: rest) = queries rest + 1 := rfl

theorem queries_append (a b : List (Step W L n m)) :
    queries (a ++ b) = queries a + queries b := by
  induction a with
  | nil => simp
  | cons s rest ih =>
    cases s with
    | op K => simp [ih]
    | query q => simp [ih]; omega

/-! ## Sums over histories -/

theorem sum_hist_op {M : Type*} [AddCommMonoid M] (K : Operation W m)
    (rest : List (Step W L n m)) (f : Hist (Step.op K :: rest) → M) :
    ∑ h, f h = ∑ j : Fin K.N, ∑ h' : Hist rest, f (j, h') := by
  exact Fintype.sum_prod_type f

/-- **Subnormalization of the run.** The total mass over histories is at most the initial
mass. -/
theorem sum_mass_run_le (l : List (Step W L n m)) (u : Input L n) (v : State W) :
    ∑ h, mass (run l u v h) ≤ mass v := by
  induction l generalizing v with
  | nil =>
    show ∑ _ : Unit, mass v ≤ mass v
    simp
  | cons s rest ih =>
    cases s with
    | op K =>
      rw [sum_hist_op]
      calc ∑ j : Fin K.N, ∑ h' : Hist rest, mass (run (Step.op K :: rest) u v (j, h'))
          = ∑ j : Fin K.N, ∑ h' : Hist rest, mass (run rest u ((K.op j).mulVec v) h') := rfl
        _ ≤ ∑ j : Fin K.N, mass ((K.op j).mulVec v) := Finset.sum_le_sum fun j _ => ih _
        _ ≤ mass v := K.sub v
    | query q =>
      calc ∑ h : Hist (Step.query q :: rest), mass (run (Step.query q :: rest) u v h)
          = ∑ h : Hist rest, mass (run rest u ((q.matrix u).mulVec v) h) := rfl
        _ ≤ mass ((q.matrix u).mulVec v) := ih _
        _ = mass v := q.mass_mulVec u v

/-! ## The branch operator -/

/-- The operator applied along a history. -/
def branchMatrix : (l : List (Step W L n m)) → Input L n → Hist l → Matrix W W ℂ
  | [], _, _ => 1
  | Step.op K :: rest, u, h => branchMatrix rest u h.2 * K.op h.1
  | Step.query q :: rest, u, h => branchMatrix rest u h * q.matrix u

theorem run_eq_mulVec (l : List (Step W L n m)) (u : Input L n) (v : State W) (h : Hist l) :
    run l u v h = (branchMatrix l u h).mulVec v := by
  induction l generalizing v with
  | nil => simp [branchMatrix]
  | cons s rest ih =>
    cases s with
    | op K =>
      rw [run_op, ih, branchMatrix, Matrix.mulVec_mulVec]
    | query q =>
      change run rest u ((q.matrix u).mulVec v) (show Hist rest from h) =
        (branchMatrix rest u (show Hist rest from h) * q.matrix u).mulVec v
      rw [ih, Matrix.mulVec_mulVec]

/-! ## Concatenation -/

/-- Histories of a concatenation split into histories of the two parts. -/
def histAppend : (a b : List (Step W L n m)) → Hist (a ++ b) ≃ Hist a × Hist b
  | [], b => (Equiv.punitProd (Hist b)).symm
  | Step.op K :: a', b =>
      ((Equiv.refl (Fin K.N)).prodCongr (histAppend a' b)).trans
        (Equiv.prodAssoc (Fin K.N) (Hist a') (Hist b)).symm
  | Step.query _ :: a', b => histAppend a' b

theorem run_append (a b : List (Step W L n m)) (u : Input L n) (v : State W)
    (h : Hist (a ++ b)) :
    run (a ++ b) u v h = run b u (run a u v (histAppend a b h).1) (histAppend a b h).2 := by
  induction a generalizing v with
  | nil => rfl
  | cons s a' ih =>
    cases s with
    | op K => exact ih _ _
    | query q => exact ih _ _

theorem claims_append (a b : List (Step W L n m)) (h : Hist (a ++ b)) :
    claims (a ++ b) h = claims a (histAppend a b h).1 ++ claims b (histAppend a b h).2 := by
  induction a with
  | nil => rfl
  | cons s a' ih =>
    cases s with
    | op K =>
      show K.out _ ++ claims (a' ++ b) _ = (K.out _ ++ claims a' _) ++ _
      rw [ih, List.append_assoc]
      rfl
    | query q => exact ih _

/-- Summing over histories of a concatenation. -/
theorem sum_hist_append {M : Type*} [AddCommMonoid M] (a b : List (Step W L n m))
    (f : Hist (a ++ b) → M) :
    ∑ h, f h = ∑ h₁ : Hist a, ∑ h₂ : Hist b, f ((histAppend a b).symm (h₁, h₂)) := by
  calc ∑ h, f h = ∑ p : Hist a × Hist b, f ((histAppend a b).symm p) :=
        Fintype.sum_equiv (histAppend a b) _ _ (fun h => by simp)
    _ = ∑ h₁ : Hist a, ∑ h₂ : Hist b, f ((histAppend a b).symm (h₁, h₂)) :=
        Fintype.sum_prod_type _

/-! ## The low-degree bridge -/

/-- Applying a matrix to a family of low-degree states preserves the degree. -/
theorem lowDegree_mulVec {D : ℕ} (A : Matrix W W ℂ) (v : Bits n → State W)
    (hv : ∀ w, LowDegree D (fun x => v x w)) (w : W) :
    LowDegree D (fun x => A.mulVec (v x) w) := by
  have : (fun x => A.mulVec (v x) w) = fun x => ∑ w' ∈ univ, A w w' * v x w' := by
    funext x
    rfl
  rw [this]
  exact LowDegree.sum univ fun w' _ => (hv w').smul (A w w')

/-- One query raises the argument degree by at most one, with the description fixed. -/
theorem lowDegree_query {D : ℕ} (q : Query W L n) (d : Bits L) (v : Bits n → State W)
    (hv : ∀ w, LowDegree D (fun x => v x w)) (w : W) :
    LowDegree (D + 1) (fun x => (q.matrix (d, x)).mulVec (v x) w) := by
  simp_rw [Query.matrix_mulVec]
  unfold Query.sign
  cases hidx : q.idx w with
  | inl i =>
    -- a description bit: the sign is constant in the argument
    have : (fun x => (if q.phase w ∧ Input.bit (d, x) (Sum.inl i) then -1 else 1) * v x w) =
        fun x => (if q.phase w ∧ d i then -1 else 1) * v x w := by
      funext x
      rfl
    rw [this]
    exact ((hv w).smul _).mono (Nat.le_succ D)
  | inr j =>
    have : (fun x => (if q.phase w ∧ Input.bit (d, x) (Sum.inr j) then -1 else 1) * v x w) =
        fun x => (if q.phase w ∧ x j then -1 else 1) * v x w := by
      funext x
      rfl
    rw [this]
    exact (hv w).mul_sign (q.phase w) j

/-- **Low-degree bridge.** With the description `d` fixed, if every workspace component of
the initial state has degree at most `D` in the argument, then after running `l` every
component of the final state on every history has degree at most `D + queries l`. -/
theorem lowDegree_run (l : List (Step W L n m)) (d : Bits L) (D : ℕ) (v : Bits n → State W)
    (hv : ∀ w, LowDegree D (fun x => v x w)) (h : Hist l) (w : W) :
    LowDegree (D + queries l) (fun x => run l (d, x) (v x) h w) := by
  induction l generalizing D v with
  | nil =>
    simpa using hv w
  | cons s rest ih =>
    cases s with
    | op K =>
      simp only [run_op, queries_op]
      exact ih D (fun x => (K.op h.1).mulVec (v x)) (lowDegree_mulVec (K.op h.1) v hv) h.2
    | query q =>
      simp only [run_query, queries_query]
      have := ih (D + 1) (fun x => (q.matrix (d, x)).mulVec (v x))
        (lowDegree_query q d v hv) h
      rw [← Nat.add_right_comm] at this
      exact this

/-- An input-independent initial state has degree zero in the argument. -/
theorem lowDegree_const_state (v : State W) (w : W) :
    LowDegree 0 (fun _ : Bits n => v w) :=
  LowDegree.const 0 (v w)

end QuantumNoiseStability.Hashing
end

-- Solutions.MatrixMass
section
namespace QNoiseStab.Supplement.MatrixMass

open Matrix
open scoped ComplexOrder MatrixOrder

variable {I J : Type*} [Fintype I] [Fintype J]

theorem trace_mmstar_re (M : Matrix I J ℂ) :
    (M * Mᴴ).trace.re = ∑ j, ∑ i, ‖M i j‖ ^ 2 := by
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, Complex.star_def,
    Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  exact Finset.sum_comm

theorem posSemidef_factor {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef) :
    ∃ L : Matrix I I ℂ, ρ = L * Lᴴ := by
  classical
  exact CStarAlgebra.nonneg_iff_eq_mul_star_self.mp hρ.nonneg

theorem kraus_mass [DecidableEq I] (A : J → Matrix I I ℂ)
    (hA : ∑ j, (A j)ᴴ * A j = 1) (v : I → ℂ) :
    ∑ j, ∑ i, ‖(A j).mulVec v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have h : ∑ j, star ((A j) *ᵥ v) ⬝ᵥ ((A j) *ᵥ v) = star v ⬝ᵥ v := calc
    _ = ∑ j, star v ⬝ᵥ (((A j)ᴴ * A j) *ᵥ v) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← mulVec_mulVec, dotProduct_mulVec (star v), star_mulVec]
    _ = star v ⬝ᵥ v := by rw [← dotProduct_sum, ← sum_mulVec, hA, one_mulVec]
  have re_star_mul (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  simpa only [dotProduct, Complex.re_sum, Pi.star_apply, re_star_mul] using congrArg Complex.re h

theorem trace_of_kraus_product (A : Matrix I I ℂ) {ρ : Matrix I I ℂ}
    (L : Matrix I J ℂ) (hρ : ρ = L * Lᴴ) :
    (A * ρ * Aᴴ).trace.re = ∑ j, ∑ i, ‖A.mulVec (fun k => L k j) i‖ ^ 2 := by
  have h : A * ρ * Aᴴ = (A * L) * (A * L)ᴴ := by
    simp only [hρ, conjTranspose_mul, Matrix.mul_assoc]
  rw [h, trace_mmstar_re]
  rfl

end QNoiseStab.Supplement.MatrixMass
end

-- Solutions.HashingCore.Claims
section
/-!
# Output records, labels, and success events

A claim is a pair `(c, b)`: coordinate `c` is asserted to have value `b`. The record of an
execution is a list of claims. `firstClaims l` keeps the first claim at each coordinate, in
order of first appearance. The short-query event for `k` keeps the first `k` distinct
coordinates: `ShortSuccess k a l` means at least `k` distinct coordinates were claimed and
the first claim at each of the first `k` of them is correct for the output `a`. Its label
`shortLabel k l` is the partial assignment formed by those `k` claims; it is a fixed
function of the record and never inspects the input.

`FullSuccess a l` means every coordinate is claimed and every claim is correct.
`exists_shortSuccess_of_cover` is the pigeonhole step of the slicing argument.
-/


namespace QuantumNoiseStability.Hashing

open Finset

variable {m : ℕ}

/-- A claim: a coordinate and a value. -/
abbrev Claim (m : ℕ) := Fin m × Bool

/-- The coordinates of a list of claims. -/
def coords (l : List (Claim m)) : Finset (Fin m) := (l.map Prod.fst).toFinset

theorem mem_coords {l : List (Claim m)} {c : Fin m} : c ∈ coords l ↔ ∃ b, (c, b) ∈ l := by
  unfold coords
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨c', b⟩, h, rfl⟩
    exact ⟨b, h⟩
  · rintro ⟨b, h⟩
    exact ⟨(c, b), h, rfl⟩

theorem coords_append (l l' : List (Claim m)) : coords (l ++ l') = coords l ∪ coords l' := by
  unfold coords
  rw [List.map_append, List.toFinset_append]

/-! ## First claims -/

/-- First claims at distinct coordinates, in order of first appearance. -/
def firstClaims : List (Claim m) → List (Claim m)
  | [] => []
  | p :: l => p :: (firstClaims l).filter (fun q => q.1 ≠ p.1)

theorem firstClaims_subset : ∀ (l : List (Claim m)), ∀ p ∈ firstClaims l, p ∈ l
  | [], p, h => by simp [firstClaims] at h
  | q :: l, p, h => by
    simp only [firstClaims, List.mem_cons, List.mem_filter] at h
    rcases h with rfl | ⟨h, _⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (firstClaims_subset l p h)

theorem map_fst_filter_ne (l : List (Claim m)) (c : Fin m) :
    ((l.filter fun q => q.1 ≠ c).map Prod.fst) = (l.map Prod.fst).filter (fun k => k ≠ c) := by
  rw [List.filter_map]
  rfl

theorem firstClaims_nodup_keys : ∀ (l : List (Claim m)), ((firstClaims l).map Prod.fst).Nodup
  | [] => by simp [firstClaims]
  | p :: l => by
    simp only [firstClaims, List.map_cons, List.nodup_cons, map_fst_filter_ne]
    refine ⟨?_, (firstClaims_nodup_keys l).filter _⟩
    simp

theorem mem_keys_firstClaims : ∀ (l : List (Claim m)) (c : Fin m),
    c ∈ (firstClaims l).map Prod.fst ↔ c ∈ l.map Prod.fst
  | [], c => by simp [firstClaims]
  | p :: l, c => by
    simp only [firstClaims, List.map_cons, List.mem_cons, map_fst_filter_ne, List.mem_filter,
      mem_keys_firstClaims l c]
    by_cases h : c = p.1
    · subst h; simp
    · simp [h]

theorem coords_firstClaims (l : List (Claim m)) : coords (firstClaims l) = coords l := by
  unfold coords
  ext c
  simp only [List.mem_toFinset]
  exact mem_keys_firstClaims l c

theorem length_firstClaims (l : List (Claim m)) : (firstClaims l).length = (coords l).card := by
  rw [← coords_firstClaims]
  unfold coords
  rw [List.toFinset_card_of_nodup (firstClaims_nodup_keys l), List.length_map]

/-! ## Lookup and labels -/

/-- The value of the first claim at coordinate `c`. -/
def lookupClaim (c : Fin m) : List (Claim m) → Option Bool
  | [] => none
  | p :: l => if p.1 = c then some p.2 else lookupClaim c l

/-- The partial assignment determined by a list of claims. -/
def labelOfList (l : List (Claim m)) : Label m := fun c => lookupClaim c l

theorem mem_of_lookupClaim_eq_some {c : Fin m} {b : Bool} :
    ∀ {l : List (Claim m)}, lookupClaim c l = some b → (c, b) ∈ l
  | [], h => by simp [lookupClaim] at h
  | p :: l, h => by
    simp only [lookupClaim] at h
    split_ifs at h with hp
    · obtain ⟨rfl⟩ := Option.some.inj h
      rw [← hp]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookupClaim_eq_some h)

theorem lookupClaim_isSome_iff (c : Fin m) :
    ∀ (l : List (Claim m)), (lookupClaim c l).isSome ↔ c ∈ l.map Prod.fst
  | [] => by simp [lookupClaim]
  | p :: l => by
    simp only [lookupClaim, List.map_cons, List.mem_cons]
    split_ifs with hp
    · simp [hp]
    · rw [lookupClaim_isSome_iff c l]
      constructor
      · intro h; exact Or.inr h
      · rintro (h | h)
        · exact absurd h.symm hp
        · exact h

theorem lookupClaim_eq_some_of_mem {c : Fin m} {b : Bool} :
    ∀ {l : List (Claim m)}, (l.map Prod.fst).Nodup → (c, b) ∈ l → lookupClaim c l = some b
  | [], _, h => by simp at h
  | p :: l, hnd, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [lookupClaim]
    rcases List.mem_cons.mp h with rfl | h'
    · simp
    · have hne : p.1 ≠ c := by
        intro hpc
        apply hnd.1
        rw [hpc]
        exact List.mem_map.mpr ⟨(c, b), h', rfl⟩
      rw [if_neg hne]
      exact lookupClaim_eq_some_of_mem hnd.2 h'

theorem support_labelOfList (l : List (Claim m)) : (labelOfList l).support = coords l := by
  ext c
  rw [Label.mem_support, mem_coords]
  unfold labelOfList
  rw [lookupClaim_isSome_iff, List.mem_map]
  constructor
  · rintro ⟨⟨c', b⟩, h, rfl⟩; exact ⟨b, h⟩
  · rintro ⟨b, h⟩; exact ⟨(c, b), h, rfl⟩

theorem size_labelOfList {l : List (Claim m)} (hnd : (l.map Prod.fst).Nodup) :
    (labelOfList l).size = l.length := by
  unfold Label.size
  rw [support_labelOfList]
  unfold coords
  rw [List.toFinset_card_of_nodup hnd, List.length_map]

theorem agree_labelOfList_iff {l : List (Claim m)} (hnd : (l.map Prod.fst).Nodup) (a : Bits m) :
    Agree a (labelOfList l) ↔ ∀ p ∈ l, a p.1 = p.2 := by
  constructor
  · intro h p hp
    exact h p.1 p.2 (lookupClaim_eq_some_of_mem hnd hp)
  · intro h c b hcb
    exact h (c, b) (mem_of_lookupClaim_eq_some hcb)

/-! ## Success events -/

/-- The short-query success event for `k` distinct coordinates. -/
def ShortSuccess (k : ℕ) (a : Bits m) (l : List (Claim m)) : Prop :=
  k ≤ (firstClaims l).length ∧ ∀ p ∈ (firstClaims l).take k, a p.1 = p.2

/-- The label of the first `k` distinct claims. -/
def shortLabel (k : ℕ) (l : List (Claim m)) : Label m := labelOfList ((firstClaims l).take k)

theorem take_firstClaims_nodup_keys (k : ℕ) (l : List (Claim m)) :
    (((firstClaims l).take k).map Prod.fst).Nodup := by
  rw [List.map_take]
  exact (firstClaims_nodup_keys l).sublist (List.take_sublist _ _)

theorem shortLabel_size {k : ℕ} {l : List (Claim m)} (h : k ≤ (firstClaims l).length) :
    (shortLabel k l).size = k := by
  unfold shortLabel
  rw [size_labelOfList (take_firstClaims_nodup_keys k l), List.length_take, min_eq_left h]

theorem shortSuccess_iff_agree {k : ℕ} {l : List (Claim m)} (h : k ≤ (firstClaims l).length)
    (a : Bits m) : ShortSuccess k a l ↔ Agree a (shortLabel k l) := by
  unfold ShortSuccess shortLabel
  rw [agree_labelOfList_iff (take_firstClaims_nodup_keys k l)]
  exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩

/-- Full success: every coordinate is claimed and every claim is correct. -/
def FullSuccess (a : Bits m) (l : List (Claim m)) : Prop :=
  (∀ c, ∃ b, (c, b) ∈ l) ∧ ∀ p ∈ l, a p.1 = p.2

theorem shortSuccess_of_correct {k : ℕ} {a : Bits m} {l : List (Claim m)}
    (hk : k ≤ (coords l).card) (hc : ∀ p ∈ l, a p.1 = p.2) : ShortSuccess k a l := by
  refine ⟨by rw [length_firstClaims]; exact hk, ?_⟩
  intro p hp
  exact hc p (firstClaims_subset l p (List.mem_of_mem_take hp))

theorem coords_eq_univ_of_fullSuccess {a : Bits m} {l : List (Claim m)} (h : FullSuccess a l) :
    coords l = univ := by
  ext c
  simp only [Finset.mem_univ, iff_true]
  rw [mem_coords]
  exact h.1 c

/-- Full success implies the short event with one coordinate, for `m ≥ 1`. -/
theorem shortSuccess_one_of_fullSuccess (hm : 1 ≤ m) {a : Bits m} {l : List (Claim m)}
    (h : FullSuccess a l) : ShortSuccess 1 a l := by
  apply shortSuccess_of_correct _ h.2
  rw [coords_eq_univ_of_fullSuccess h, Finset.card_univ, Fintype.card_fin]
  exact hm

/-- **Pigeonhole over slices.** If the records of `ls` together claim every coordinate of
`C` correctly and `|C| > |ls| (k - 1)`, then some record in `ls` has at least `k` distinct
correct claims, hence satisfies the short event. -/
theorem exists_shortSuccess_of_cover (k : ℕ) (a : Bits m) :
    ∀ (ls : List (List (Claim m))) (C : Finset (Fin m)),
      (∀ c ∈ C, ∃ b, (c, b) ∈ ls.flatten) → (∀ p ∈ ls.flatten, a p.1 = p.2) →
      ls.length * (k - 1) < C.card → ∃ l ∈ ls, ShortSuccess k a l
  | [], C, hcover, _, hcard => by
    exfalso
    have : C = ∅ := by
      ext c
      simp only [Finset.notMem_empty, iff_false]
      intro hc
      obtain ⟨b, hb⟩ := hcover c hc
      simp at hb
    rw [this] at hcard
    simp at hcard
  | l :: ls, C, hcover, hcorrect, hcard => by
    simp only [List.flatten_cons, List.mem_append] at hcover hcorrect
    by_cases hk : k ≤ (coords l).card
    · exact ⟨l, List.mem_cons_self, shortSuccess_of_correct hk fun p hp => hcorrect p (Or.inl hp)⟩
    · push Not at hk
      have hrest := exists_shortSuccess_of_cover k a ls (C \ coords l) ?_ ?_ ?_
      · obtain ⟨l', hl', hs⟩ := hrest
        exact ⟨l', List.mem_cons_of_mem _ hl', hs⟩
      · intro c hc
        rw [Finset.mem_sdiff] at hc
        obtain ⟨b, hb⟩ := hcover c hc.1
        rcases hb with hb | hb
        · exact absurd (mem_coords.mpr ⟨b, hb⟩) hc.2
        · exact ⟨b, hb⟩
      · intro p hp
        exact hcorrect p (Or.inr hp)
      · have h1 := Finset.card_sdiff_add_card_inter C (coords l)
        have h2 : (C ∩ coords l).card ≤ (coords l).card :=
          Finset.card_le_card Finset.inter_subset_right
        simp only [List.length_cons] at hcard
        have : (ls.length + 1) * (k - 1) = ls.length * (k - 1) + (k - 1) := by ring
        omega

end QuantumNoiseStability.Hashing
end

-- Solutions.HashProgramOperations
section
/-! Finite operations on the original memory and their emitted bit records. -/

noncomputable section

namespace QNoiseStab.Supplement.HashProgram

open QuantumNoiseStability.Hashing Matrix
open scoped Classical

variable {M B V κ : Type} [Fintype M] [DecidableEq M] [Fintype B] {m : ℕ}

/-- Number a finite family of branch matrices and their records as a bit-program operation. -/
def operation (K : B → Matrix M M ℂ) (out : B → List (Fin m × Bool))
    (sub : ∀ v, ∑ b, mass ((K b).mulVec v) ≤ mass v) : Operation M m where
  N := Fintype.card B
  op i := K ((Fintype.equivFin B).symm i)
  out i := out ((Fintype.equivFin B).symm i)
  sub v := (Equiv.sum_comp (Fintype.equivFin B).symm _).le.trans (sub v)

/-- The operation sum can be evaluated using the original branch labels. -/
theorem sum_operation {n : ℕ} (K : B → Matrix M M ℂ) (out : B → List (Fin m × Bool)) (sub)
    (l : List (Step M 0 n m)) (u : Input 0 n) (v : State M)
    (g : List (Fin m × Bool) → State M → ℝ) :
    (∑ h, g (claims (.op (operation K out sub) :: l) h)
      (run (.op (operation K out sub) :: l) u v h)) =
    ∑ b, ∑ h, g (out b ++ claims l h) (run l u ((K b).mulVec v) h) := by
  rw [sum_hist_op]
  exact Equiv.sum_comp (Fintype.equivFin B).symm
    (fun b => ∑ h, g (out b ++ claims l h) (run l u ((K b).mulVec v) h))

/-- A single commit emits one bit claim, and a silent outcome emits the empty list. -/
def record (q : V → Bool) (o : Option (Fin m × V)) : List (Fin m × Bool) :=
  (o.map (fun p => (p.1, q p.2))).toList

/-- The ordered bit record of a sequence of instrument outcomes. -/
def transcript {k : ℕ} (q : V → Bool) (o : Fin k → Option (Fin m × V)) :=
  (List.ofFn o).flatMap (record q)

private theorem mem_record (q : V → Bool) (j : Fin m) (b : Bool) (o : Option (Fin m × V)) :
    (j,b) ∈ record q o ↔ ∃ v, o = some (j,v) ∧ b = q v := by
  cases o with
  | none => simp [record]
  | some p => rcases p with ⟨k,v⟩; simp [record, eq_comm (a := k), @eq_comm V v]

private theorem mem_transcript {k : ℕ} (q : V → Bool) (o : Fin k → Option (Fin m × V))
    (j : Fin m) (b : Bool) :
    (j,b) ∈ transcript q o ↔ ∃ t v, o t = some (j,v) ∧ b = q v := by
  simp [transcript, List.mem_flatMap, List.mem_ofFn, mem_record]

/-- Correctness of all public commits, including coverage, is full success of the bit record. -/
theorem fullSuccess_transcript {T : ℕ} (q : V → Bool) (z : Fin m → Bool)
    (o : Fin (T+1) → Option (Fin m × V)) :
    FullSuccess z (transcript q o) ↔ CommitsCorrect q z o := by
  constructor
  · rintro ⟨cover, agree⟩
    refine ⟨fun t j v h => (agree (j, q v) ((mem_transcript ..).2 ⟨t,v,h,rfl⟩)).symm, ?_⟩
    intro j
    obtain ⟨b,h⟩ := cover j
    obtain ⟨t,v,h,_⟩ := (mem_transcript ..).1 h
    exact ⟨t,v,h⟩
  · rintro ⟨agree, cover⟩
    constructor
    · intro j
      obtain ⟨t,v,h⟩ := cover j
      exact ⟨q v, (mem_transcript ..).2 ⟨t,v,h,rfl⟩⟩
    · rintro ⟨j,b⟩ h
      obtain ⟨t,v,ho,hb⟩ := (mem_transcript ..).1 h
      exact (agree t j v ho).symm.trans hb.symm

/-- The preparation branch for column `j` maps basis vector `w` to that column. -/
def prepareMatrix (L : Matrix M M ℂ) (w j : M) : Matrix M M ℂ :=
  Matrix.of fun i k => if k = w then L i j else 0

private theorem prepare_apply (L : Matrix M M ℂ) (w j : M) (v : State M) (i : M) :
    (prepareMatrix L w j).mulVec v i = L i j * v w := by
  simp [prepareMatrix, mulVec, dotProduct, ite_mul]

/-- The preparation matrices reproduce the factor columns on their designated basis state. -/
theorem prepare_basis (L : Matrix M M ℂ) (w j : M) :
    (prepareMatrix L w j).mulVec (basis w) = fun i => L i j := by
  funext i
  simp [prepare_apply, basis]

/-- Columns with total squared norm one form a subnormalized operation on the memory. -/
theorem prepare_sub (L : Matrix M M ℂ) (w : M) (h : ∑ j, ∑ i, ‖L i j‖ ^ 2 = 1)
    (v : State M) : ∑ j, mass ((prepareMatrix L w j).mulVec v) ≤ mass v := by
  simp only [mass, prepare_apply, norm_mul, mul_pow, ← Finset.sum_mul, h, one_mul]
  exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ w)

variable [Fintype V] [Fintype κ]

/-- Completeness of an instrument gives the mass bound for paired outcome and Kraus labels,
including an input-independent mass-preserving matrix immediately before the instrument. -/
theorem instrument_sub (I : KAQROM.Instrument (Option (Fin m × V)) M M κ)
    (D : Matrix M M ℂ) (hD : ∀ v, mass (D.mulVec v) = mass v) (v : State M) :
    ∑ b : Option (Fin m × V) × κ, mass ((I.kraus b.1 b.2 * D).mulVec v) ≤ mass v := by
  have hc : ∑ b : Option (Fin m × V) × κ, (I.kraus b.1 b.2)ᴴ * I.kraus b.1 b.2 = 1 := by
    rw [Fintype.sum_prod_type]
    exact I.complete
  rw [← hD v]
  simp only [← Matrix.mulVec_mulVec]
  exact (MatrixMass.kraus_mass _ hc _).le

end QNoiseStab.Supplement.HashProgram
end
end

-- Solutions.BranchExecution
section
namespace QNoiseStab.Supplement.BranchExecution

open Matrix

variable {J : Type*} [Fintype J] {T : ℕ}

/-- The final vector for one sequence of Kraus matrices, with an oracle between steps. -/
noncomputable def pathState (K : Fin (T + 1) → Matrix J J ℂ) (O : Matrix J J ℂ)
    (v : J → ℂ) : J → ℂ :=
  Fin.induction (motive := fun _ => J → ℂ) (K 0 *ᵥ v)
    (fun t w => K t.succ *ᵥ (O *ᵥ w)) (Fin.last T)

@[simp] theorem pathState_zero (K : Fin 1 → Matrix J J ℂ) (O : Matrix J J ℂ) (v : J → ℂ) :
    pathState K O v = K 0 *ᵥ v := rfl

private theorem induction_castSucc {S : Type*} (a : S) (step : Fin (T + 1) → S → S)
    (i : Fin (T + 1)) :
    Fin.induction (motive := fun _ => S) a step i.castSucc =
      Fin.induction (motive := fun _ => S) a (fun t => step t.castSucc) i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact congrArg (step i.castSucc) ih

private theorem induction_last_succ {S : Type*} (a : S) (step : Fin (T + 1) → S → S) :
    Fin.induction (motive := fun _ => S) a step (Fin.last (T + 1)) =
      step (Fin.last T)
        (Fin.induction (motive := fun _ => S) a (fun t => step t.castSucc) (Fin.last T)) :=
  congrArg (step (Fin.last T)) (induction_castSucc a step (Fin.last T))

theorem pathState_succ (K : Fin (T + 2) → Matrix J J ℂ) (O : Matrix J J ℂ) (v : J → ℂ) :
    pathState K O v =
      K (Fin.last (T + 1)) *ᵥ (O *ᵥ pathState (fun t => K t.castSucc) O v) :=
  induction_last_succ (K 0 *ᵥ v) (fun t w => K t.succ *ᵥ (O *ᵥ w))

variable {κ : Type*} [Fintype κ]

/-- Column `j` is the path starting from column `j` of the initial factor. -/
private noncomputable def pathMatrix (K : Fin (T + 1) → Matrix J J ℂ) (O L : Matrix J J ℂ) :
    Matrix J J ℂ :=
  of fun i j => pathState K O (fun k => L k j) i

private theorem pathMatrix_succ (K : Fin (T + 2) → Matrix J J ℂ) (O L : Matrix J J ℂ) :
    pathMatrix K O L =
      K (Fin.last (T + 1)) * (O * pathMatrix (fun t => K t.castSucc) O L) := by
  ext i j
  exact congrFun (pathState_succ K O (fun k => L k j)) i

private noncomputable def applyKraus (K : κ → Matrix J J ℂ) (ρ : Matrix J J ℂ) :
    Matrix J J ℂ := ∑ r, K r * ρ * (K r)ᴴ

private noncomputable def density (K : Fin (T + 1) → κ → Matrix J J ℂ) (O ρ : Matrix J J ℂ) :
    Matrix J J ℂ :=
  Fin.induction (motive := fun _ => Matrix J J ℂ) (applyKraus (K 0) ρ)
    (fun t σ => applyKraus (K t.succ) (O * σ * Oᴴ)) (Fin.last T)

private theorem density_eq_sum (K : Fin (T + 1) → κ → Matrix J J ℂ) (O L : Matrix J J ℂ) :
    density K O (L * Lᴴ) = ∑ r : Fin (T + 1) → κ,
      let M := pathMatrix (fun t => K t (r t)) O L
      M * Mᴴ := by
  classical
  induction T with
  | zero =>
    change (∑ r, K 0 r * (L * Lᴴ) * (K 0 r)ᴴ) = _
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) κ).symm
    intro r
    change K 0 r * (L * Lᴴ) * (K 0 r)ᴴ = (K 0 r * L) * (K 0 r * L)ᴴ
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  | succ T ih =>
    unfold density
    rw [induction_last_succ]
    change applyKraus (K (Fin.last (T + 1)))
      (O * density (fun t => K t.castSucc) O (L * Lᴴ) * Oᴴ) = _
    rw [ih]
    simp only [applyKraus, Matrix.mul_sum, Matrix.sum_mul]
    rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (T + 2) => κ))
    intro ⟨s, r⟩
    simp only [Fin.snocEquiv_apply, pathMatrix_succ, Fin.snoc_last, Fin.snoc_castSucc,
      conjTranspose_mul, Matrix.mul_assoc]

variable {n d : ℕ} {W : Type} [DecidableEq W]

/-- The published phase query on the full memory. -/
noncomputable abbrev oracle (ω : ℂ) (y : Fin n → ZMod d) :=
  Matrix.kronecker (QNoiseStab.phaseQuery ω y) (1 : Matrix W W ℂ)

local notation "Mem" => (Fin n × ZMod d) × W

variable [NeZero d] [Fintype W] {K V ι : Type} [Fintype K] [Fintype V] [Fintype ι]

/-- Every initial density matrix has a factor whose columns have total squared norm one. -/
theorem exists_start_factor (A : SpaceBoundedAlg n d W K V ι T) :
    ∃ L : Matrix Mem Mem ℂ, A.start = L * Lᴴ ∧ ∑ j, ∑ i, ‖L i j‖ ^ 2 = 1 := by
  obtain ⟨L, hL⟩ := MatrixMass.posSemidef_factor A.start_psd
  refine ⟨L, hL, ?_⟩
  rw [← MatrixMass.trace_mmstar_re, ← hL, A.start_trace, Complex.one_re]

/-- Sum the squared final amplitudes over Kraus paths and columns of the initial factor. -/
theorem commitProb_eq_sum (A : SpaceBoundedAlg n d W K V ι T) (ω : ℂ) (y : Fin n → ZMod d)
    (o : Fin (T + 1) → Option (K × V)) (L : Matrix Mem Mem ℂ)
    (hL : A.start = L * Lᴴ) :
    A.commitProb ω y o = ∑ r : Fin (T + 1) → ι, ∑ j : Mem, ∑ i : Mem,
      ‖pathState (fun t => (A.step t).kraus (o t) (r t)) (oracle ω y) (fun k => L k j) i‖ ^ 2 := by
  change (density (fun t => (A.step t).kraus (o t)) (oracle ω y) A.start).trace.re = _
  rw [hL, density_eq_sum, trace_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun r _ => MatrixMass.trace_mmstar_re _

open Classical in
/-- Average the path expansion over inputs and sum over correct commit sequences. -/
theorem successProb_eq_sum {X Y : Type} [Fintype X] (A : SpaceBoundedAlg n d W K V ι T)
    (enc : X ≃ ZMod d) (ω : ℂ) (q : V → Y) (f : (Fin n → X) → K → Y)
    (L : Matrix Mem Mem ℂ) (hL : A.start = L * Lᴴ) :
    A.successProb enc ω q f = ((Fintype.card X : ℝ) ^ n)⁻¹ *
      ∑ x : Fin n → X, ∑ o : Fin (T + 1) → Option (K × V),
        if CommitsCorrect q (f x) o then
          ∑ r : Fin (T + 1) → ι, ∑ j : Mem, ∑ i : Mem,
            ‖pathState (fun t => (A.step t).kraus (o t) (r t))
              (oracle ω (fun k => enc (x k))) (fun k => L k j) i‖ ^ 2
        else 0 := by
  simp only [SpaceBoundedAlg.successProb, commitProb_eq_sum A ω _ _ L hL]

end QNoiseStab.Supplement.BranchExecution
end

-- Solutions.HashProgramExecution
section
/-! Execution of the compiled instruments, with one bit query between consecutive instruments. -/

noncomputable section

namespace QNoiseStab.Supplement.HashProgram

open Matrix QuantumNoiseStability.Hashing BranchExecution
open scoped Classical

variable {M V κ : Type} [Fintype M] [DecidableEq M] [Fintype V] [Fintype κ] {n m T : ℕ}

local notation "Outcome" => Option (Fin m × V)
local notation "Branch" => Outcome × κ
local notation "Inst" => KAQROM.Instrument Outcome M M κ

private def measure (q : V → Bool) (I : Inst) (D : Matrix M M ℂ)
    (hD : ∀ v, mass (D.mulVec v) = mass v) : Operation M m :=
  operation (fun b : Branch => I.kraus b.1 b.2 * D) (fun b => record q b.1)
    (instrument_sub I D hD)

private theorem sum_measure (q : V → Bool) (I : Inst) (D : Matrix M M ℂ)
    (hD : ∀ v, mass (D.mulVec v) = mass v) (u : Input 0 n) (v : State M)
    (g : List (Fin m × Bool) → State M → ℝ) :
    (∑ h, g (claims [.op (measure q I D hD)] h) (run [.op (measure q I D hD)] u v h)) =
    ∑ b : Branch, g (record q b.1) ((I.kraus b.1 b.2 * D).mulVec v) := by
  unfold measure
  rw [sum_operation]
  apply Finset.sum_congr rfl
  intro b _
  change (∑ _ : Unit, g (record q b.1 ++ []) _) = _
  simp
  rfl

variable (q : V → Bool) (Q : Query M 0 n) (D : Matrix M M ℂ)
  (hD : ∀ v, mass (D.mulVec v) = mass v)

/-- Compile step zero and then append one query and one instrument for each later step.
The matrix `D` supplies the input-independent part of the public oracle. -/
def compiledSteps : {T : ℕ} → (Fin (T+1) → Inst) → List (Step M 0 n m)
  | 0, I => [.op (measure q (I 0) 1 (by simp))]
  | T+1, I => compiledSteps (fun i => I i.castSucc) ++
      [.query Q, .op (measure q (I (Fin.last (T+1))) D hD)]

/-- Compiling `T+1` instruments uses exactly `T` queries. -/
theorem queries_compiledSteps (I : Fin (T+1) → Inst) :
    queries (compiledSteps q Q D hD I) = T := by
  induction T with
  | zero => rfl
  | succ T ih => simp [compiledSteps, queries_append, ih]

private theorem sum_append (a b : List (Step M 0 n m)) (u : Input 0 n) (v : State M)
    (g : List (Fin m × Bool) → State M → ℝ) :
    (∑ h, g (claims (a ++ b) h) (run (a ++ b) u v h)) =
    ∑ h, ∑ k, g (claims a h ++ claims b k) (run b u (run a u v h) k) := by
  rw [sum_hist_append]
  simp only [claims_append, run_append, Equiv.apply_symm_apply]

private theorem sum_last (a : List (Step M 0 n m)) (I : Inst) (u : Input 0 n) (v : State M)
    (g : List (Fin m × Bool) → State M → ℝ) :
    (∑ h, g (claims (a ++ [.query Q, .op (measure q I D hD)]) h)
      (run (a ++ [.query Q, .op (measure q I D hD)]) u v h)) =
    ∑ b : Branch, ∑ h, g (claims a h ++ record q b.1)
      ((I.kraus b.1 b.2).mulVec ((D * Q.matrix u).mulVec (run a u v h))) := by
  rw [sum_append]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  simp only [← Matrix.mulVec_mulVec, claims_query, run_query]
  have hs := sum_measure q I D hD u ((Q.matrix u).mulVec (run a u v h))
      (fun l w => g (claims a h ++ l) w)
  simp only [← Matrix.mulVec_mulVec] at hs
  convert hs using 1
  rfl

/-- Sum any function of the final record and vector using the public instrument branches.
In particular this preserves the mass of every event defined by the emitted claims. -/
theorem sum_compiledSteps (I : Fin (T+1) → Inst) (u : Input 0 n) (v : State M)
    (g : List (Fin m × Bool) → State M → ℝ) :
    (∑ h, g (claims (compiledSteps q Q D hD I) h) (run (compiledSteps q Q D hD I) u v h)) =
    ∑ p : Fin (T+1) → Branch, g (transcript q (fun t => (p t).1))
      (pathState (fun t => (I t).kraus (p t).1 (p t).2) (D * Q.matrix u) v) := by
  induction T generalizing g with
  | zero =>
    rw [compiledSteps, sum_measure]
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) Branch).symm
    intro b
    simp [transcript, Equiv.funUnique, Equiv.piUnique]
  | succ T ih =>
    rw [compiledSteps, sum_last]
    have hpre (b : Branch) := ih (fun i => I i.castSucc)
      (fun l w => g (l ++ record q b.1)
        ((I (Fin.last (T+1))).kraus b.1 b.2 *ᵥ ((D * Q.matrix u) *ᵥ w)))
    simp_rw [hpre]
    rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (T+2) => Branch))
    rintro ⟨b,p⟩
    rw [pathState_succ]
    simp only [Fin.snocEquiv_apply, Fin.snoc_last, Fin.snoc_castSucc]
    congr 1
    simp only [transcript, List.ofFn_succ' (n := T+1), Fin.snoc_castSucc, Fin.snoc_last,
      List.concat_eq_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

end QNoiseStab.Supplement.HashProgram
end
end

-- Solutions.HashBitOracle
section
/-! The binary phase oracle with either encoding of the public input bits. -/

noncomputable section

namespace QNoiseStab.Supplement.HashBitOracle

open Matrix
open QuantumNoiseStability.Hashing
open scoped Classical

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

private def factor (enc : Bool ≃ ZMod 2) (ω : ℂ) (p : ZMod 2) (b : Bool) : ℂ :=
  ω ^ (p * enc b).val

private theorem sign_cases {ω : ℂ} (hω : ω^2 = 1) (r : ℕ) : ω^r = 1 ∨ ω^r = -1 := by
  apply sq_eq_one_iff.mp
  rw [← pow_mul, Nat.mul_comm, pow_mul, hω, one_pow]

/-- Query register `i` supplies the address. The sign changes precisely when the two
values of the public cyclic phase differ on that workspace basis vector. -/
def query (enc : Bool ≃ ZMod 2) (ω : ℂ) : Query ((Fin n × ZMod 2) × W) 0 n where
  idx w := .inr w.1.1
  phase w := decide (factor enc ω w.1.2 false ≠ factor enc ω w.1.2 true)

/-- Phase of the published oracle on the all-false input. -/
def offset (enc : Bool ≃ ZMod 2) (ω : ℂ) :
    Matrix ((Fin n × ZMod 2) × W) ((Fin n × ZMod 2) × W) ℂ :=
  diagonal fun w => factor enc ω w.1.2 false

theorem mass_offset (enc : Bool ≃ ZMod 2) (ω : ℂ) (hω : ω^2 = 1)
    (v : State ((Fin n × ZMod 2) × W)) : mass ((offset enc ω).mulVec v) = mass v := by
  unfold mass
  apply Finset.sum_congr rfl
  intro w _
  rcases sign_cases hω (w.1.2 * enc false).val with h | h <;>
    simp [offset, mulVec_diagonal, factor, h]

omit [Fintype W] [DecidableEq W] in
private theorem sign_factor (enc : Bool ≃ ZMod 2) (ω : ℂ) (hω : ω^2 = 1)
    (x : Bits n) (d₀ : Bits 0) (w : (Fin n × ZMod 2) × W) :
    factor enc ω w.1.2 (x w.1.1) =
      factor enc ω w.1.2 false * (query enc ω).sign (d₀,x) w := by
  cases hb : x w.1.1 with
  | false => simp [Query.sign, query, Input.bit, hb]
  | true =>
    rcases sign_cases hω (w.1.2 * enc false).val with hf | hf <;>
      rcases sign_cases hω (w.1.2 * enc true).val with ht | ht <;>
      norm_num [Query.sign, query, Input.bit, factor, hb, hf, ht]

/-- For each input the public query is one usual sign query followed by an
input-independent diagonal unitary. Both operators act on the original memory. -/
theorem oracle_eq (enc : Bool ≃ ZMod 2) (ω : ℂ) (hω : ω^2 = 1) (x : Bits n) (d₀ : Bits 0) :
    Matrix.kronecker (QNoiseStab.phaseQuery ω (enc ∘ x)) (1 : Matrix W W ℂ) =
      (offset enc ω) * (query enc ω).matrix (d₀,x) := by
  rw [offset, Query.matrix, diagonal_mul_diagonal]
  ext ⟨a,w⟩ ⟨b,z⟩
  by_cases hab : a = b <;> by_cases hwz : w = z
  · subst b
    subst z
    simpa [phaseQuery, kronecker_apply, factor] using sign_factor enc ω hω x d₀ (a,w)
  · subst b
    simp [hwz]
  · subst z
    simp [phaseQuery, hab]
  · simp [phaseQuery, hab]

end QNoiseStab.Supplement.HashBitOracle
end
end

-- Solutions.HashingCore.ShortQuery
section
/-!
# The short-query bound

For a fixed good description, every algorithm in the model
with at most `t₀` query steps and an argument-independent initial state has short-event
success at most `2^{-k} + δ`, averaged over uniform arguments. The algorithm's steps and
initial state may depend on the fixed description.

Theorem 5: averaging over uniform descriptions, with the excluded descriptions charged
once with probability at most `δ`, gives `2^{-k} + 2δ`.
-/


namespace QuantumNoiseStability.Hashing

open Finset
open scoped Classical

noncomputable section

variable {L n m : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- The mass of the histories whose record satisfies `P`: the probability of the event
`P` when the steps are run on input `u` from the initial state `v`. -/
def eventMass (l : List (Step W L n m)) (u : Input L n) (v : State W)
    (P : List (Claim m) → Prop) : ℝ :=
  ∑ h, if P (claims l h) then mass (run l u v h) else 0

theorem eventMass_nonneg (l : List (Step W L n m)) (u : Input L n) (v : State W)
    (P : List (Claim m) → Prop) : 0 ≤ eventMass l u v P := by
  unfold eventMass
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact mass_nonneg _
  · exact le_rfl

theorem eventMass_le_mass (l : List (Step W L n m)) (u : Input L n) (v : State W)
    (P : List (Claim m) → Prop) : eventMass l u v P ≤ mass v := by
  unfold eventMass
  calc ∑ h, (if P (claims l h) then mass (run l u v h) else 0)
      ≤ ∑ h, mass (run l u v h) := by
        apply Finset.sum_le_sum
        intro h _
        split_ifs
        · exact le_rfl
        · exact mass_nonneg _
    _ ≤ mass v := sum_mass_run_le l u v

theorem eventMass_mono (l : List (Step W L n m)) (u : Input L n) (v : State W)
    {P Q : List (Claim m) → Prop} (hPQ : ∀ c, P c → Q c) :
    eventMass l u v P ≤ eventMass l u v Q := by
  unfold eventMass
  apply Finset.sum_le_sum
  intro h _
  by_cases hP : P (claims l h)
  · rw [if_pos hP, if_pos (hPQ _ hP)]
  · rw [if_neg hP]
    split_ifs
    · exact mass_nonneg _
    · exact le_rfl

/-- The short-event success probability with description `d` fixed and the argument
uniform. -/
def shortProb (H : HashFamily L n m) (k : ℕ) (l : List (Step W L n m)) (d : Bits L)
    (v : State W) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x, eventMass l (d, x) v (ShortSuccess k (H d x))

theorem shortProb_le_one (H : HashFamily L n m) (k : ℕ) (l : List (Step W L n m))
    (d : Bits L) {v : State W} (hv : mass v ≤ 1) : shortProb H k l d v ≤ 1 := by
  unfold shortProb
  calc ((2 : ℝ) ^ n)⁻¹ * ∑ x, eventMass l (d, x) v (ShortSuccess k (H d x))
      ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ x : Bits n, (1 : ℝ) := by
        gcongr with x _
        exact (eventMass_le_mass _ _ _ _).trans hv
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, card_bits, nsmul_eq_mul, mul_one]
        push_cast
        exact inv_mul_cancel₀ (by positivity)

theorem shortProb_nonneg (H : HashFamily L n m) (k : ℕ) (l : List (Step W L n m))
    (d : Bits L) (v : State W) : 0 ≤ shortProb H k l d v := by
  unfold shortProb
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => eventMass_nonneg _ _ _ _)

/-- One history's contribution to the short event, summed over arguments, is at most
`(2^{-k} + δ)` times its total mass, for a good description. -/
theorem sum_short_hist_le {H : HashFamily L n m} {d : Bits L} (hd : Good H d)
    (l : List (Step W L n m)) (hl : queries l ≤ t0 n) (v : State W) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k ≤ gBound n m) (h : Hist l) :
    ∑ x, (if ShortSuccess k (H d x) (claims l h) then mass (run l (d, x) v h) else 0) ≤
      (((2 : ℝ) ^ k)⁻¹ + delta n) * ∑ x, mass (run l (d, x) v h) := by
  by_cases hlen : k ≤ (firstClaims (claims l h)).length
  · set τ := shortLabel k (claims l h) with hτ
    have hsize : τ.size = k := shortLabel_size hlen
    have hind : ∀ x, (if ShortSuccess k (H d x) (claims l h) then mass (run l (d, x) v h) else 0)
        = indicator H τ d x * mass (run l (d, x) v h) := by
      intro x
      unfold indicator
      rw [shortSuccess_iff_agree hlen]
      split_ifs <;> simp
    simp_rw [hind]
    unfold mass
    calc ∑ x, indicator H τ d x * ∑ w, ‖run l (d, x) v h w‖ ^ 2
        = ∑ w, ∑ x, indicator H τ d x * ‖run l (d, x) v h w‖ ^ 2 := by
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ w, (((2 : ℝ) ^ k)⁻¹ + delta n) * ∑ x, ‖run l (d, x) v h w‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro w _
          have hdeg : LowDegree (t0 n) (fun x => run l (d, x) v h w) := by
            have := lowDegree_run l d 0 (fun _ => v) (fun w => lowDegree_const_state v w) h w
            rw [zero_add] at this
            exact this.mono hl
          have := indicator_sum_le_of_good hd τ (hsize ▸ hk1) (hsize ▸ hk2) hdeg
          rw [hsize] at this
          exact this
      _ = (((2 : ℝ) ^ k)⁻¹ + delta n) * ∑ x, ∑ w, ‖run l (d, x) v h w‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
  · have hzero : ∀ x, (if ShortSuccess k (H d x) (claims l h) then mass (run l (d, x) v h) else 0)
        = 0 := by
      intro x
      rw [if_neg]
      intro hs
      exact hlen hs.1
    simp_rw [hzero]
    rw [Finset.sum_const_zero]
    apply mul_nonneg
    · have := delta_pos n
      positivity
    · exact Finset.sum_nonneg fun _ _ => mass_nonneg _

/-- **Lemma 4 (short-query bound for a fixed good description).** Any algorithm with at
most `t₀` query steps whose initial state (of mass at most one) does not depend on the
argument has short-event success at most `2^{-k} + δ` for `1 ≤ k ≤ g`. The steps and the
initial state may depend on the fixed description. -/
theorem shortProb_le_of_good {H : HashFamily L n m} {d : Bits L} (hd : Good H d)
    (l : List (Step W L n m)) (hl : queries l ≤ t0 n) {v : State W} (hv : mass v ≤ 1)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ gBound n m) :
    shortProb H k l d v ≤ ((2 : ℝ) ^ k)⁻¹ + delta n := by
  unfold shortProb eventMass
  have hbound : ∑ x, ∑ h, (if ShortSuccess k (H d x) (claims l h) then mass (run l (d, x) v h)
      else 0) ≤ (((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n := by
    rw [Finset.sum_comm]
    calc ∑ h, ∑ x, (if ShortSuccess k (H d x) (claims l h) then mass (run l (d, x) v h) else 0)
        ≤ ∑ h, (((2 : ℝ) ^ k)⁻¹ + delta n) * ∑ x, mass (run l (d, x) v h) :=
          Finset.sum_le_sum fun h _ => sum_short_hist_le hd l hl v hk1 hk2 h
      _ = (((2 : ℝ) ^ k)⁻¹ + delta n) * ∑ x, ∑ h, mass (run l (d, x) v h) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (((2 : ℝ) ^ k)⁻¹ + delta n) * ∑ _x : Bits n, (1 : ℝ) := by
          gcongr with x _
          · have := delta_pos n; positivity
          · exact (sum_mass_run_le l (d, x) v).trans hv
      _ = (((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n := by
          rw [Finset.sum_const, Finset.card_univ, card_bits, nsmul_eq_mul, mul_one]
          push_cast
          ring
  calc ((2 : ℝ) ^ n)⁻¹ * ∑ x, ∑ h, (if ShortSuccess k (H d x) (claims l h)
        then mass (run l (d, x) v h) else 0)
      ≤ ((2 : ℝ) ^ n)⁻¹ * ((((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n) := by gcongr
    _ = ((2 : ℝ) ^ k)⁻¹ + delta n := by
        field_simp

/-- A program: a list of steps and an initial state of mass at most one. -/
structure Program (W : Type) [Fintype W] (L n m : ℕ) where
  /-- The steps. -/
  steps : List (Step W L n m)
  /-- The initial workspace state. -/
  init : State W
  /-- The initial state is subnormalized. -/
  init_mass : mass init ≤ 1

/-- The short-event success probability of a description-dependent family of programs,
averaged over uniform descriptions and arguments. -/
def shortProbAvg (H : HashFamily L n m) (k : ℕ) (P : Bits L → Program W L n m) : ℝ :=
  ((2 : ℝ) ^ L)⁻¹ * ∑ d, shortProb H k (P d).steps d (P d).init

/-- **Theorem 5 (the short-query theorem).** For a strongly universal family with
`1 ≤ m ≤ n`, any family of programs, indexed by the description, each with at most `t₀`
query steps and an argument-independent initial state, has short-event success at most
`2^{-k} + 2δ` for `1 ≤ k ≤ g`, averaged over independent uniform descriptions and
arguments. -/
theorem short_query_theorem {H : HashFamily L n m} (hH : StronglyUniversal H) (hn : 1 ≤ n)
    (hmn : m ≤ n) (P : Bits L → Program W L n m) (hP : ∀ d, queries (P d).steps ≤ t0 n)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ gBound n m) :
    shortProbAvg H k P ≤ ((2 : ℝ) ^ k)⁻¹ + 2 * delta n := by
  unfold shortProbAvg
  have hbad := card_not_good_le hH hn hmn
  rw [card_bits, Nat.cast_pow, Nat.cast_ofNat] at hbad
  have hsplit : ∑ d, shortProb H k (P d).steps d (P d).init ≤
      (2 : ℝ) ^ L * (((2 : ℝ) ^ k)⁻¹ + delta n) +
        ((univ.filter fun d => ¬ Good H d).card : ℝ) := by
    calc ∑ d, shortProb H k (P d).steps d (P d).init
        ≤ ∑ d, ((((2 : ℝ) ^ k)⁻¹ + delta n) + if Good H d then 0 else 1) := by
          apply Finset.sum_le_sum
          intro d _
          by_cases hd : Good H d
          · rw [if_pos hd, add_zero]
            exact shortProb_le_of_good hd (P d).steps (hP d) (P d).init_mass hk1 hk2
          · rw [if_neg hd]
            have h1 := shortProb_le_one H k (P d).steps d (P d).init_mass
            have h2 : 0 ≤ ((2 : ℝ) ^ k)⁻¹ + delta n := by
              have := delta_pos n; positivity
            linarith
      _ = (2 : ℝ) ^ L * (((2 : ℝ) ^ k)⁻¹ + delta n) +
            ((univ.filter fun d => ¬ Good H d).card : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_bits,
            nsmul_eq_mul, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
            nsmul_eq_mul, mul_one]
          push_cast
          ring
  calc ((2 : ℝ) ^ L)⁻¹ * ∑ d, shortProb H k (P d).steps d (P d).init
      ≤ ((2 : ℝ) ^ L)⁻¹ * ((2 : ℝ) ^ L * (((2 : ℝ) ^ k)⁻¹ + delta n) + delta n * (2 : ℝ) ^ L) := by
        gcongr
        linarith
    _ = ((2 : ℝ) ^ k)⁻¹ + 2 * delta n := by
        field_simp
        ring

end

end QuantumNoiseStability.Hashing
end

-- Solutions.HashingCore.Slicing
section
/-!
# State replacement and slicing

Step 6 of the proof chain.

* **State replacement.** For any matrix `A` and any subnormalized family of states
  `ψ_j` (that is, `∑_j ‖ψ_j‖² ≤ 1`, the pure-branch representation of a density matrix
  `ρ ⪯ I`), `∑_j ‖A ψ_j‖² ≤ ∑_w ‖A e_w‖²`. This is `ρ ⪯ I = |W| · (I/|W|)`: any event
  after the replacement by the maximally mixed state loses at most the factor `|W|`.
  The proof here uses the Frobenius bound from `Fourier.lean`.
* **Chunking.** Every step list splits into at most `max 1 ⌈T/t₀⌉` contiguous slices with
  at most `t₀` query steps each (`exists_chunks`). Output processing before the first
  query and after the last query belongs to the adjacent slice.
* **Slice event.** `SliceEvent k a cs h` says that some slice's own record satisfies the
  short event. It depends only on the records of the slices, which are fixed functions of
  the history; earlier records are not accessible to later slices except through the
  workspace, whose dimension is charged by the state replacement.
* **Slice bound.** `sliceEvent_sum_le` runs the union bound over slices. Each slice is
  a valid short computation once its starting family is replaced by the standard basis,
  so Lemma 4 applies to it with the same fixed good description.
-/


namespace QuantumNoiseStability.Hashing

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

variable {L n m : ℕ} {W : Type} [Fintype W] [DecidableEq W]

theorem sum_comm_rotate {α β γ M : Type*} [AddCommMonoid M] [Fintype α] [Fintype β]
    [Fintype γ] (F : α → β → γ → M) :
    ∑ x, ∑ y, ∑ z, F x y z = ∑ z, ∑ x, ∑ y, F x y z := by
  calc ∑ x, ∑ y, ∑ z, F x y z = ∑ x, ∑ z, ∑ y, F x y z := by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, F x y z := Finset.sum_comm

/-! ## State replacement -/

theorem mass_mulVec_basis (A : Matrix W W ℂ) (w : W) :
    mass (A.mulVec (basis w)) = ∑ w', ‖A w' w‖ ^ 2 := by
  unfold mass basis
  apply Finset.sum_congr rfl
  intro w' _
  congr 1
  rw [Matrix.mulVec_single_one]
  rfl

/-- **Frobenius bound.** `‖A v‖² ≤ (∑_w ‖A e_w‖²) ‖v‖²`. -/
theorem mass_mulVec_le (A : Matrix W W ℂ) (v : State W) :
    mass (A.mulVec v) ≤ (∑ w, mass (A.mulVec (basis w))) * mass v := by
  simp_rw [mass_mulVec_basis]
  unfold mass
  have h := sum_normSq_mulVec_le (fun i j => A i j) v
  rw [Finset.sum_comm]
  exact h

/-- **State replacement.** A subnormalized family of states, mapped by `A`, has total
mass at most the mass obtained from the uniform basis mixture times the dimension:
`∑_j ‖A ψ_j‖² ≤ ∑_w ‖A e_w‖²`. -/
theorem sum_mass_mulVec_le {J : Type*} [Fintype J] (A : Matrix W W ℂ) (ψ : J → State W)
    (hψ : ∑ j, mass (ψ j) ≤ 1) :
    ∑ j, mass (A.mulVec (ψ j)) ≤ ∑ w, mass (A.mulVec (basis w)) := by
  calc ∑ j, mass (A.mulVec (ψ j))
      ≤ ∑ j, (∑ w, mass (A.mulVec (basis w))) * mass (ψ j) :=
        Finset.sum_le_sum fun j _ => mass_mulVec_le A (ψ j)
    _ = (∑ w, mass (A.mulVec (basis w))) * ∑ j, mass (ψ j) := by rw [Finset.mul_sum]
    _ ≤ (∑ w, mass (A.mulVec (basis w))) * 1 := by
        gcongr
        exact Finset.sum_nonneg fun _ _ => mass_nonneg _
    _ = ∑ w, mass (A.mulVec (basis w)) := mul_one _

/-! ## Chunking a step list into slices -/

/-- A step list with at least `t` query steps splits as `a ++ b` with exactly `t` query
steps in `a`. -/
theorem exists_split_queries :
    ∀ (l : List (Step W L n m)) (t : ℕ), t ≤ queries l →
      ∃ a b, l = a ++ b ∧ queries a = t
  | [], t, ht => by
    refine ⟨[], [], rfl, ?_⟩
    simp at ht
    simp [ht]
  | s :: l, t, ht => by
    cases t with
    | zero => exact ⟨[], s :: l, rfl, rfl⟩
    | succ t' =>
      cases s with
      | op K =>
        simp only [queries_op] at ht
        obtain ⟨a, b, hab, ha⟩ := exists_split_queries l (t' + 1) ht
        exact ⟨Step.op K :: a, b, by rw [hab]; rfl, by simp [ha]⟩
      | query q =>
        simp only [queries_query] at ht
        obtain ⟨a, b, hab, ha⟩ := exists_split_queries l t' (by omega)
        exact ⟨Step.query q :: a, b, by rw [hab]; rfl, by simp [ha]⟩

/-- The number of slices of at most `t` queries each: `max 1 ⌈T / t⌉`. -/
def sliceCount (T t : ℕ) : ℕ := max 1 ((T + t - 1) / t)

theorem queries_flatten (cs : List (List (Step W L n m))) :
    queries cs.flatten = (cs.map queries).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatten_cons, queries_append, ih, List.map_cons, List.sum_cons]

/-- **Chunking.** Every step list splits into contiguous slices with at most `t` query
steps each, using at most `max 1 ⌈T/t⌉` slices, where `T` is the number of query steps. -/
theorem exists_chunks (t : ℕ) (ht : 1 ≤ t) (l : List (Step W L n m)) :
    ∃ cs : List (List (Step W L n m)), cs.flatten = l ∧ (∀ c ∈ cs, queries c ≤ t) ∧
      cs.length ≤ sliceCount (queries l) t := by
  induction hN : queries l using Nat.strong_induction_on generalizing l with
  | _ N ih =>
    by_cases hle : queries l ≤ t
    · refine ⟨[l], by simp, ?_, ?_⟩
      · intro c hc
        rw [List.mem_singleton] at hc
        rw [hc]; exact hle
      · simp [sliceCount]
    · push Not at hle
      obtain ⟨a, b, hab, ha⟩ := exists_split_queries l t hle.le
      have hqb : queries b = queries l - t := by
        rw [hab, queries_append, ha] at *
        omega
      have hlt : queries b < N := by omega
      obtain ⟨cs, hflat, hcs, hlen⟩ := ih (queries b) hlt b rfl
      refine ⟨a :: cs, ?_, ?_, ?_⟩
      · rw [List.flatten_cons, hflat, hab]
      · intro c hc
        rw [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact ha.le
        · exact hcs c hc
      · rw [List.length_cons]
        unfold sliceCount at hlen ⊢
        rw [hqb] at hlen
        have h1 : 1 ≤ (queries l - t + t - 1) / t := by
          apply Nat.le_div_iff_mul_le (by omega) |>.mpr
          omega
        rw [max_eq_right h1] at hlen
        have h2 : (queries l - t + t - 1) / t + 1 = (queries l + t - 1) / t := by
          have : queries l + t - 1 = (queries l - t + t - 1) + 1 * t := by omega
          rw [this, Nat.add_mul_div_right _ _ (by omega)]
        have h3 : (queries l + t - 1) / t ≤ max 1 ((queries l + t - 1) / t) := le_max_right _ _
        rw [← hN]
        omega

/-! ## The slice event -/

/-- The event that some slice's own record satisfies the short event for `k`. -/
def SliceEvent (k : ℕ) (a : Bits m) :
    (cs : List (List (Step W L n m))) → Hist cs.flatten → Prop
  | [], _ => False
  | c :: cs, h =>
      ShortSuccess k a (claims c (histAppend c cs.flatten h).1) ∨
        SliceEvent k a cs (histAppend c cs.flatten h).2

/-- The records of the slices along a history. -/
def records : (cs : List (List (Step W L n m))) → Hist cs.flatten → List (List (Claim m))
  | [], _ => []
  | c :: cs, h =>
      claims c (histAppend c cs.flatten h).1 :: records cs (histAppend c cs.flatten h).2

theorem flatten_records : ∀ (cs : List (List (Step W L n m))) (h : Hist cs.flatten),
    (records cs h).flatten = claims cs.flatten h
  | [], h => by
    show [] = claims [] h
    rfl
  | c :: cs, h => by
    show claims c _ ++ (records cs _).flatten = claims (c ++ cs.flatten) h
    rw [flatten_records cs, claims_append]

theorem length_records : ∀ (cs : List (List (Step W L n m))) (h : Hist cs.flatten),
    (records cs h).length = cs.length
  | [], _ => rfl
  | c :: cs, h => by
    show (records cs _).length + 1 = cs.length + 1
    rw [length_records cs]

theorem sliceEvent_of_mem_records (k : ℕ) (a : Bits m) :
    ∀ (cs : List (List (Step W L n m))) (h : Hist cs.flatten),
      (∃ l ∈ records cs h, ShortSuccess k a l) → SliceEvent k a cs h
  | [], _, ⟨l, hl, _⟩ => by simp [records] at hl
  | c :: cs, h, ⟨l, hl, hs⟩ => by
    simp only [records, List.mem_cons] at hl
    show ShortSuccess k a (claims c _) ∨ SliceEvent k a cs _
    rcases hl with rfl | hl
    · exact Or.inl hs
    · exact Or.inr (sliceEvent_of_mem_records k a cs _ ⟨l, hl, hs⟩)

/-- **Pigeonhole.** A fully successful history with `m > |cs| (k - 1)` has a slice whose
own record has at least `k` distinct correct claims, hence satisfies the short event. -/
theorem sliceEvent_of_fullSuccess {k : ℕ} {a : Bits m} (cs : List (List (Step W L n m)))
    (h : Hist cs.flatten) (hfull : FullSuccess a (claims cs.flatten h))
    (hm : cs.length * (k - 1) < m) : SliceEvent k a cs h := by
  apply sliceEvent_of_mem_records
  apply exists_shortSuccess_of_cover k a (records cs h) univ
  · intro c _
    rw [flatten_records]
    exact hfull.1 c
  · rw [flatten_records]
    exact hfull.2
  · rw [length_records, Finset.card_univ, Fintype.card_fin]
    exact hm

/-! ## The slice bound -/

/-- Basis-state runs of a slice with at most `t₀` queries: the short event has total mass
at most `|W| (2^{-k} + δ) 2^n` over all arguments and basis states. -/
theorem sum_basis_short_le {H : HashFamily L n m} {d : Bits L} (hd : Good H d)
    (c : List (Step W L n m)) (hc : queries c ≤ t0 n) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k ≤ gBound n m) :
    ∑ w : W, ∑ x, eventMass c (d, x) (basis w) (ShortSuccess k (H d x)) ≤
      (Fintype.card W : ℝ) * ((((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n) := by
  calc ∑ w : W, ∑ x, eventMass c (d, x) (basis w) (ShortSuccess k (H d x))
      = ∑ w : W, (2 : ℝ) ^ n * shortProb H k c d (basis w) := by
        apply Finset.sum_congr rfl
        intro w _
        unfold shortProb
        rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    _ ≤ ∑ _w : W, (2 : ℝ) ^ n * (((2 : ℝ) ^ k)⁻¹ + delta n) := by
        apply Finset.sum_le_sum
        intro w _
        gcongr
        exact shortProb_le_of_good hd c hc (le_of_eq (mass_basis w)) hk1 hk2
    _ = (Fintype.card W : ℝ) * ((((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- **Slice bound with union over slices.** For a fixed good description, slices with at
most `t₀` queries each, and any argument-dependent subnormalized starting family, the
total mass of the slice event over arguments is at most
`|cs| · |W| (2^{-k} + δ) 2^n`. -/
theorem sliceEvent_sum_le {H : HashFamily L n m} {d : Bits L} (hd : Good H d) {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ gBound n m) :
    ∀ (cs : List (List (Step W L n m))), (∀ c ∈ cs, queries c ≤ t0 n) →
      ∀ {J : Type} [Fintype J] (ψ : J → Bits n → State W), (∀ x, ∑ j, mass (ψ j x) ≤ 1) →
      ∑ x, ∑ j, ∑ h : Hist cs.flatten,
        (if SliceEvent k (H d x) cs h then mass (run cs.flatten (d, x) (ψ j x) h) else 0) ≤
        (cs.length : ℝ) * ((Fintype.card W : ℝ) * ((((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n))
  | [], _, J, _, ψ, _ => by
    simp [SliceEvent]
  | c :: cs, hcs, J, _, ψ, hψ => by
    have hc : queries c ≤ t0 n := hcs c List.mem_cons_self
    have hcs' : ∀ c' ∈ cs, queries c' ≤ t0 n := fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')
    set F := cs.flatten with hF
    show ∑ x, ∑ j, ∑ h : Hist (c ++ F),
        (if SliceEvent k (H d x) (c :: cs) h then mass (run (c ++ F) (d, x) (ψ j x) h)
          else 0) ≤ _
    -- split every history of `c ++ F` into its `c` part and its `F` part
    have hsplit : ∀ x j, ∑ h : Hist (c ++ F),
        (if SliceEvent k (H d x) (c :: cs) h then mass (run (c ++ F) (d, x) (ψ j x) h)
          else 0) =
        ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          (if ShortSuccess k (H d x) (claims c h₁) ∨ SliceEvent k (H d x) cs h₂ then
            mass (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂) else 0) := by
      intro x j
      rw [sum_hist_append c F]
      apply Finset.sum_congr rfl
      intro h₁ _
      apply Finset.sum_congr rfl
      intro h₂ _
      have e1 : histAppend c F ((histAppend c F).symm (h₁, h₂)) = (h₁, h₂) :=
        (histAppend c F).apply_symm_apply _
      have hev : SliceEvent k (H d x) (c :: cs) ((histAppend c F).symm (h₁, h₂)) ↔
          ShortSuccess k (H d x) (claims c h₁) ∨ SliceEvent k (H d x) cs h₂ := by
        show ShortSuccess k (H d x) (claims c (histAppend c F _).1) ∨
          SliceEvent k (H d x) cs (histAppend c F _).2 ↔ _
        rw [e1]
      rw [run_append c F, e1]
      simp only [hev]
    simp_rw [hsplit]
    -- union bound
    have hunion : ∀ x j h₁ h₂,
        (if ShortSuccess k (H d x) (claims c h₁) ∨ SliceEvent k (H d x) cs h₂ then
          mass (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂) else 0) ≤
        (if ShortSuccess k (H d x) (claims c h₁) then
          mass (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂) else 0) +
        (if SliceEvent k (H d x) cs h₂ then
          mass (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂) else 0) := by
      intro x j h₁ h₂
      have h0 := mass_nonneg (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂)
      split_ifs <;> first | linarith | (exfalso; tauto)
    -- the first-slice term
    have hA : ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
        (if ShortSuccess k (H d x) (claims c h₁) then
          mass (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂) else 0) ≤
        (Fintype.card W : ℝ) * ((((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n) := by
      calc ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
            (if ShortSuccess k (H d x) (claims c h₁) then
              mass (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂) else 0)
          ≤ ∑ x, ∑ j, ∑ h₁ : Hist c,
            (if ShortSuccess k (H d x) (claims c h₁) then
              mass (run c (d, x) (ψ j x) h₁) else 0) := by
            gcongr with x _ j _ h₁ _
            split_ifs
            · exact sum_mass_run_le F (d, x) _
            · simp
        _ = ∑ x, ∑ h₁ : Hist c,
            (if ShortSuccess k (H d x) (claims c h₁) then
              ∑ j, mass ((branchMatrix c (d, x) h₁).mulVec (ψ j x)) else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro h₁ _
            split_ifs
            · apply Finset.sum_congr rfl
              intro j _
              rw [run_eq_mulVec]
            · simp
        _ ≤ ∑ x, ∑ h₁ : Hist c,
            (if ShortSuccess k (H d x) (claims c h₁) then
              ∑ w, mass ((branchMatrix c (d, x) h₁).mulVec (basis w)) else 0) := by
            gcongr with x _ h₁ _
            split_ifs
            · exact sum_mass_mulVec_le _ _ (hψ x)
            · exact le_rfl
        _ = ∑ w, ∑ x, eventMass c (d, x) (basis w) (ShortSuccess k (H d x)) := by
            unfold eventMass
            have hpush : ∀ x h₁, (if ShortSuccess k (H d x) (claims c h₁) then
                ∑ w, mass ((branchMatrix c (d, x) h₁).mulVec (basis w)) else 0) =
                ∑ w, (if ShortSuccess k (H d x) (claims c h₁) then
                  mass (run c (d, x) (basis w) h₁) else 0) := by
              intro x h₁
              split_ifs
              · apply Finset.sum_congr rfl
                intro w _
                rw [run_eq_mulVec]
              · simp
            simp_rw [hpush]
            exact sum_comm_rotate _
        _ ≤ (Fintype.card W : ℝ) * ((((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n) :=
            sum_basis_short_le hd c hc hk1 hk2
    -- the remaining slices, by the induction hypothesis with the new starting family
    have hB : ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
        (if SliceEvent k (H d x) cs h₂ then
          mass (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂) else 0) ≤
        (cs.length : ℝ) * ((Fintype.card W : ℝ) * ((((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n)) := by
      have hψ' : ∀ x, ∑ p : J × Hist c, mass (run c (d, x) (ψ p.1 x) p.2) ≤ 1 := by
        intro x
        rw [Fintype.sum_prod_type]
        calc ∑ j, ∑ h₁ : Hist c, mass (run c (d, x) (ψ j x) h₁)
            ≤ ∑ j, mass (ψ j x) := Finset.sum_le_sum fun j _ => sum_mass_run_le c (d, x) _
          _ ≤ 1 := hψ x
      have := sliceEvent_sum_le hd hk1 hk2 cs hcs' (fun p : J × Hist c => fun x =>
        run c (d, x) (ψ p.1 x) p.2) hψ'
      simp_rw [Fintype.sum_prod_type] at this
      exact this
    calc ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          (if ShortSuccess k (H d x) (claims c h₁) ∨ SliceEvent k (H d x) cs h₂ then
            mass (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂) else 0)
        ≤ ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          ((if ShortSuccess k (H d x) (claims c h₁) then
            mass (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂) else 0) +
          (if SliceEvent k (H d x) cs h₂ then
            mass (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂) else 0)) := by
          gcongr with x _ j _ h₁ _ h₂ _
          exact hunion x j h₁ h₂
      _ = (∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          (if ShortSuccess k (H d x) (claims c h₁) then
            mass (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂) else 0)) +
          (∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          (if SliceEvent k (H d x) cs h₂ then
            mass (run F (d, x) (run c (d, x) (ψ j x) h₁) h₂) else 0)) := by
          simp_rw [Finset.sum_add_distrib]
      _ ≤ (Fintype.card W : ℝ) * ((((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n) +
          (cs.length : ℝ) * ((Fintype.card W : ℝ) * ((((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n)) :=
          add_le_add hA hB
      _ = ((c :: cs).length : ℝ) *
          ((Fintype.card W : ℝ) * ((((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n)) := by
          rw [List.length_cons]
          push_cast
          ring

/-! ## Full success of a sliced program -/

/-- The full-success probability with description `d` fixed and the argument uniform. -/
def fullProb (H : HashFamily L n m) (P : Program W L n m) (d : Bits L) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x, eventMass P.steps (d, x) P.init (FullSuccess (H d x))

theorem fullProb_le_one (H : HashFamily L n m) (P : Program W L n m) (d : Bits L) :
    fullProb H P d ≤ 1 := by
  unfold fullProb
  calc ((2 : ℝ) ^ n)⁻¹ * ∑ x, eventMass P.steps (d, x) P.init (FullSuccess (H d x))
      ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ x : Bits n, (1 : ℝ) := by
        gcongr with x _
        exact (eventMass_le_mass _ _ _ _).trans P.init_mass
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, card_bits, nsmul_eq_mul, mul_one]
        push_cast
        exact inv_mul_cancel₀ (by positivity)

theorem fullProb_nonneg (H : HashFamily L n m) (P : Program W L n m) (d : Bits L) :
    0 ≤ fullProb H P d := by
  unfold fullProb
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => eventMass_nonneg _ _ _ _)

/-- Full success implies the one-coordinate short event, so the full-success probability
is at most the short-event probability for `k = 1`. -/
theorem fullProb_le_shortProb_one (hm : 1 ≤ m) (H : HashFamily L n m) (P : Program W L n m)
    (d : Bits L) : fullProb H P d ≤ shortProb H 1 P.steps d P.init := by
  unfold fullProb shortProb
  gcongr with x _
  exact eventMass_mono _ _ _ fun c hc => shortSuccess_one_of_fullSuccess hm hc

/-- **The sliced bound.** For a good description and a slicing of the program into slices
with at most `t₀` queries each, if `m > |cs| (k-1)` then the full-success probability is at
most `|cs| · |W| · (2^{-k} + δ)`. -/
theorem fullProb_le_slices {H : HashFamily L n m} {d : Bits L} (hd : Good H d)
    (P : Program W L n m) (cs : List (List (Step W L n m))) (hflat : cs.flatten = P.steps)
    (hcs : ∀ c ∈ cs, queries c ≤ t0 n) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ gBound n m)
    (hm : cs.length * (k - 1) < m) :
    fullProb H P d ≤ (cs.length : ℝ) * ((Fintype.card W : ℝ) * (((2 : ℝ) ^ k)⁻¹ + delta n)) := by
  unfold fullProb eventMass
  have hmain : ∀ (l : List (Step W L n m)) (hl : cs.flatten = l),
      ∑ x, ∑ h : Hist l, (if FullSuccess (H d x) (claims l h) then mass (run l (d, x) P.init h)
        else 0) ≤
      (cs.length : ℝ) * ((Fintype.card W : ℝ) * ((((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n)) := by
    intro l hl
    subst hl
    have h1 := sliceEvent_sum_le hd hk1 hk2 cs hcs (J := Unit) (fun _ _ => P.init)
      (fun x => by simpa using P.init_mass)
    simp only [Finset.univ_unique, Finset.sum_singleton] at h1
    refine le_trans ?_ h1
    gcongr with x _ h _
    split_ifs with hfull hslice
    · exact le_rfl
    · exact absurd (sliceEvent_of_fullSuccess cs h hfull hm) hslice
    · exact mass_nonneg _
    · exact le_rfl
  calc ((2 : ℝ) ^ n)⁻¹ * ∑ x, ∑ h : Hist P.steps,
        (if FullSuccess (H d x) (claims P.steps h) then mass (run P.steps (d, x) P.init h) else 0)
      ≤ ((2 : ℝ) ^ n)⁻¹ * ((cs.length : ℝ) *
          ((Fintype.card W : ℝ) * ((((2 : ℝ) ^ k)⁻¹ + delta n) * (2 : ℝ) ^ n))) := by
        gcongr
        exact hmain P.steps hflat
    _ = (cs.length : ℝ) * ((Fintype.card W : ℝ) * (((2 : ℝ) ^ k)⁻¹ + delta n)) := by
        field_simp

end

end QuantumNoiseStability.Hashing
end

-- Solutions.HashingCore.TimeSpace
section
/-!
# The time-space tradeoff

For `n ≥ 256`, `1 ≤ m ≤ n`, `n ≤ 2^S`, a strongly universal
family, and a program on a workspace of dimension at most `2^S` making at most `T` query
steps, average complete success at least `2/3` implies `65536 · T · S ≥ n · m`.

The proof fixes one good description with conditional success greater than `3/5`
(`exists_good_fullProb`), rules out `T ≤ t₀` by Lemma 4 with `k = 1`, handles `T > n²`
and the large-space case `4S + 4 > g` by direct arithmetic, and otherwise slices the
program into at most `⌈T/t₀⌉` slices of at most `t₀` queries, applies the sliced bound
with `k = 4S + 4`, and concludes `m ≤ ⌈T/t₀⌉ (k - 1)` (`nm_le_of_sliced`).

Corollary 7: under `4S + 4 ≤ g`, average complete success at least `2^{-S}` already gives
`896 · T · S ≥ n · m`.
-/


namespace QuantumNoiseStability.Hashing

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

variable {L n m : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- The complete-success probability averaged over independent uniform descriptions and
arguments. -/
def fullProbAvg (H : HashFamily L n m) (P : Program W L n m) : ℝ :=
  ((2 : ℝ) ^ L)⁻¹ * ∑ d, fullProb H P d

theorem delta_le_small (hn : 256 ≤ n) : delta n ≤ 1 / 16 := by
  have h := delta_le_inv_pow (n := n) (k := 32) (by omega)
  have : ((2 : ℝ) ^ 32)⁻¹ ≤ 1 / 16 := by norm_num
  linarith

/-- **Choosing a good description.** If the average complete success is at least `θ + δ`
plus a margin, some good description has conditional complete success greater than `θ`:
precisely, if `∀ good d, fullProb ≤ θ` then `avg ≤ θ + δ`. -/
theorem fullProbAvg_le_of_good_le {H : HashFamily L n m} (hH : StronglyUniversal H)
    (hn : 1 ≤ n) (hmn : m ≤ n) (P : Program W L n m) {θ : ℝ} (hθ : 0 ≤ θ)
    (hcon : ∀ d, Good H d → fullProb H P d ≤ θ) : fullProbAvg H P ≤ θ + delta n := by
  have hbad := card_not_good_le hH hn hmn
  rw [card_bits, Nat.cast_pow, Nat.cast_ofNat] at hbad
  have hsum : ∑ d, fullProb H P d ≤ (2 : ℝ) ^ L * θ +
      ((univ.filter fun d => ¬ Good H d).card : ℝ) := by
    calc ∑ d, fullProb H P d ≤ ∑ d, (θ + if Good H d then 0 else 1) := by
          apply Finset.sum_le_sum
          intro d _
          by_cases hd : Good H d
          · rw [if_pos hd, add_zero]
            exact hcon d hd
          · rw [if_neg hd]
            have h1 := fullProb_le_one H P d
            linarith
      _ = (2 : ℝ) ^ L * θ + ((univ.filter fun d => ¬ Good H d).card : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_bits,
            nsmul_eq_mul, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
            nsmul_eq_mul, mul_one]
          push_cast
          ring
  unfold fullProbAvg
  have h2L : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  calc ((2 : ℝ) ^ L)⁻¹ * ∑ d, fullProb H P d
      ≤ ((2 : ℝ) ^ L)⁻¹ * ((2 : ℝ) ^ L * θ + delta n * (2 : ℝ) ^ L) := by
        gcongr
        linarith
    _ = θ + delta n := by
        field_simp

/-- If the average complete success is at least `2/3`, some good description has
conditional complete success greater than `3/5`. -/
theorem exists_good_fullProb {H : HashFamily L n m} (hH : StronglyUniversal H) (hn : 256 ≤ n)
    (hmn : m ≤ n) (P : Program W L n m) (hsucc : 2 / 3 ≤ fullProbAvg H P) :
    ∃ d, Good H d ∧ 3 / 5 < fullProb H P d := by
  by_contra hcon
  push Not at hcon
  have := fullProbAvg_le_of_good_le hH (by omega) hmn P (by norm_num) hcon
  have := delta_le_small hn
  linarith

/-- The numerical slice-union bound: with `k = 4S + 4`, `r ≤ 2^{2S}`, `c ≤ 2^S`, and
`δ ≤ 2^{-k}`, `r · c · (2^{-k} + δ) ≤ 2^{-S-3}`. -/
theorem slice_union_small (S : ℕ) {r : ℝ} (_hr0 : 0 ≤ r) (hr : r ≤ (2 : ℝ) ^ (2 * S))
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ (2 : ℝ) ^ S) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ ((2 : ℝ) ^ (4 * S + 4))⁻¹) :
    r * (c * (((2 : ℝ) ^ (4 * S + 4))⁻¹ + δ)) ≤ ((2 : ℝ) ^ (S + 3))⁻¹ := by
  set p : ℝ := ((2 : ℝ) ^ (4 * S + 4))⁻¹ with hp
  have hp0 : 0 ≤ p := by positivity
  calc r * (c * (p + δ)) ≤ (2 : ℝ) ^ (2 * S) * ((2 : ℝ) ^ S * (p + p)) := by gcongr
    _ = (2 : ℝ) ^ (3 * S + 1) / (2 : ℝ) ^ (4 * S + 4) := by
        rw [hp, div_eq_mul_inv]
        have : (2 : ℝ) ^ (3 * S + 1) = (2 : ℝ) ^ (2 * S) * ((2 : ℝ) ^ S * 2) := by
          rw [← pow_succ, ← pow_add]
          congr 1
          ring
        rw [this]
        ring
    _ = ((2 : ℝ) ^ (S + 3))⁻¹ := by
        rw [show 4 * S + 4 = (3 * S + 1) + (S + 3) by ring, pow_add]
        field_simp
        ring

theorem inv_pow_S3_le (S : ℕ) : ((2 : ℝ) ^ (S + 3))⁻¹ ≤ 1 / 8 := by
  rw [pow_add]
  have : (0 : ℝ) < (2 : ℝ) ^ S := by positivity
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ S := one_le_pow₀ (by norm_num)
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  norm_num
  linarith

/-- Full success implies the `k`-coordinate short event for `k ≤ m`, so the full-success
probability is at most the short-event probability. -/
theorem fullProb_le_shortProb {k : ℕ} (hk : k ≤ m) (H : HashFamily L n m)
    (P : Program W L n m) (d : Bits L) : fullProb H P d ≤ shortProb H k P.steps d P.init := by
  unfold fullProb shortProb
  gcongr with x _
  apply eventMass_mono
  intro c hc
  apply shortSuccess_of_correct _ hc.2
  rw [coords_eq_univ_of_fullSuccess hc, Finset.card_univ, Fintype.card_fin]
  exact hk

/-- **The sliced case.** For a good description with conditional complete success greater
than `θ ≥ 2^{-S-3}`, if the number of query steps `T` satisfies `t₀ < T ≤ n²` and
`k = 4S + 4 ≤ g`, then `n · m ≤ 896 · T · S`. This is the output-counting step: the
sliced bound forces `m ≤ ⌈T/t₀⌉ (k - 1)`. -/
theorem nm_le_of_sliced {H : HashFamily L n m} {d : Bits L} (hd : Good H d) (hn : 256 ≤ n)
    (hmn : m ≤ n) {S : ℕ} (hS : n ≤ 2 ^ S) (hW : Fintype.card W ≤ 2 ^ S)
    (P : Program W L n m) (hT'gt : t0 n < queries P.steps) (hbig : queries P.steps ≤ n ^ 2)
    (hkg : 4 * S + 4 ≤ gBound n m) {θ : ℝ} (hθ : ((2 : ℝ) ^ (S + 3))⁻¹ ≤ θ)
    (hd_succ : θ < fullProb H P d) :
    n * m ≤ 896 * queries P.steps * S := by
  set T' := queries P.steps with hT'
  have ht0 : 1 ≤ t0 n := by unfold t0; omega
  have hT'1 : 1 ≤ T' := by omega
  set k := 4 * S + 4 with hk
  have hk1 : 1 ≤ k := by omega
  -- slice the program into at most `⌈T'/t₀⌉` slices of at most `t₀` queries
  obtain ⟨cs, hflat, hcs, hlen⟩ := exists_chunks (t0 n) ht0 P.steps
  rw [← hT'] at hlen
  have hr_t0 : cs.length * t0 n ≤ T' + t0 n - 1 := by
    have h1 : sliceCount T' (t0 n) = (T' + t0 n - 1) / t0 n := by
      unfold sliceCount
      apply max_eq_right
      rw [Nat.le_div_iff_mul_le (by omega)]
      omega
    rw [h1] at hlen
    calc cs.length * t0 n ≤ (T' + t0 n - 1) / t0 n * t0 n := Nat.mul_le_mul_right _ hlen
      _ ≤ T' + t0 n - 1 := Nat.div_mul_le_self _ _
  have hr_T : cs.length ≤ T' := by
    by_contra hcon
    push Not at hcon
    have h3 : T' + t0 n ≤ T' * t0 n + 1 := by
      have h4 : T' * t0 n = T' * (t0 n - 1) + T' := by
        conv_lhs => rw [show t0 n = (t0 n - 1) + 1 by omega]
        ring
      have h5 := Nat.mul_le_mul_right (t0 n - 1) hT'1
      omega
    have h5 : (T' + 1) * t0 n = T' * t0 n + t0 n := by ring
    have h6 : (T' + 1) * t0 n ≤ cs.length * t0 n := Nat.mul_le_mul_right _ hcon
    omega
  -- the slice bound forces `m ≤ |cs| (k - 1)`
  have hm_le : m ≤ cs.length * (k - 1) := by
    by_contra hlt
    push Not at hlt
    have hbound := fullProb_le_slices hd P cs hflat hcs hk1 hkg hlt
    have hδk : delta n ≤ ((2 : ℝ) ^ k)⁻¹ := by
      apply delta_le_inv_pow
      have : gBound n m ≤ n / 64 := min_le_right _ _
      omega
    have hr2S : (cs.length : ℝ) ≤ (2 : ℝ) ^ (2 * S) := by
      have h1 : cs.length ≤ 2 ^ (2 * S) := by
        calc cs.length ≤ T' := hr_T
          _ ≤ n ^ 2 := hbig
          _ ≤ (2 ^ S) ^ 2 := Nat.pow_le_pow_left hS 2
          _ = 2 ^ (2 * S) := by rw [← pow_mul, mul_comm]
      exact_mod_cast h1
    have hW' : (Fintype.card W : ℝ) ≤ (2 : ℝ) ^ S := by exact_mod_cast hW
    have := slice_union_small S (Nat.cast_nonneg _) hr2S (Nat.cast_nonneg _) hW'
      (delta_pos n).le hδk
    rw [hk] at hbound
    linarith
  -- arithmetic: `n ≤ 64 t₀`, `|cs| t₀ < 2 T'`, `k - 1 = 4S + 3 ≤ 7S`
  have hS1 : 1 ≤ S := by
    by_contra h0
    push Not at h0
    have : S = 0 := by omega
    rw [this] at hS
    omega
  have hn64 : n ≤ 64 * t0 n := by
    have : t0 n = n / 32 := rfl
    omega
  have hk7 : k - 1 ≤ 7 * S := by omega
  have hr2 : cs.length * t0 n ≤ 2 * T' := by omega
  calc n * m ≤ (64 * t0 n) * (cs.length * (k - 1)) := Nat.mul_le_mul hn64 hm_le
    _ = 64 * (cs.length * t0 n) * (k - 1) := by ring
    _ ≤ 64 * (2 * T') * (7 * S) := by
        apply Nat.mul_le_mul _ hk7
        exact Nat.mul_le_mul_left _ hr2
    _ = 896 * T' * S := by ring

/-- **Theorem 6 (time-space tradeoff).** Let `n ≥ 256`, `1 ≤ m ≤ n`, `n ≤ 2^S`, and let
`H` be strongly universal. Any program in the bit-query model on a workspace of dimension
at most `2^S` making at most `T` query steps, with complete success at least `2/3`
averaged over independent uniform descriptions and arguments, satisfies
`65536 · T · S ≥ n · m`. -/
theorem time_space_tradeoff {H : HashFamily L n m} (hH : StronglyUniversal H)
    (hn : 256 ≤ n) (hm1 : 1 ≤ m) (hmn : m ≤ n) {S : ℕ} (hS : n ≤ 2 ^ S)
    (hW : Fintype.card W ≤ 2 ^ S) (P : Program W L n m) {T : ℕ} (hT : queries P.steps ≤ T)
    (hsucc : 2 / 3 ≤ fullProbAvg H P) :
    n * m ≤ 65536 * T * S := by
  obtain ⟨d, hd, hd35⟩ := exists_good_fullProb hH hn hmn P hsucc
  set T' := queries P.steps with hT'
  have hS1 : 1 ≤ S := by
    by_contra h0
    push Not at h0
    have : S = 0 := by omega
    rw [this] at hS
    omega
  have hδsmall := delta_le_small hn
  have hg1 : 1 ≤ gBound n m := by unfold gBound; omega
  -- the whole program is not a short computation: `T' > t₀`
  have hT'gt : t0 n < T' := by
    by_contra hle
    push Not at hle
    have h1 := fullProb_le_shortProb hm1 H P d
    have h2 := shortProb_le_of_good hd P.steps hle P.init_mass (k := 1) le_rfl hg1
    have : ((2 : ℝ) ^ 1)⁻¹ = 1 / 2 := by norm_num
    linarith
  -- it suffices to prove the bound for the exact number of query steps
  suffices hmain : n * m ≤ 65536 * T' * S by
    calc n * m ≤ 65536 * T' * S := hmain
      _ ≤ 65536 * T * S := by gcongr
  by_cases hbig : n ^ 2 < T'
  · -- more than `n²` queries
    calc n * m ≤ n * n := Nat.mul_le_mul_left n hmn
      _ = n ^ 2 := by ring
      _ ≤ T' := hbig.le
      _ ≤ 65536 * T' * S := by nlinarith
  · push Not at hbig
    by_cases hkg : gBound n m < 4 * S + 4
    · -- large space: `m ≤ 128 g < 128 (4S + 4)` and `n < 32 T'`
      have hn32 : n < 32 * T' := by
        have : t0 n = n / 32 := rfl
        omega
      have hg128 : m ≤ 128 * gBound n m := by
        unfold gBound
        rcases le_total m (n / 64) with h | h
        · rw [min_eq_left h]; omega
        · rw [min_eq_right h]; omega
      have hm896 : m ≤ 896 * S := by omega
      calc n * m ≤ (32 * T') * (896 * S) := Nat.mul_le_mul hn32.le hm896
        _ = 28672 * T' * S := by ring
        _ ≤ 65536 * T' * S := by nlinarith
    · push Not at hkg
      have h := nm_le_of_sliced hd hn hmn hS hW P hT'gt hbig hkg
        ((inv_pow_S3_le S).trans (by norm_num)) hd35
      calc n * m ≤ 896 * T' * S := h
        _ ≤ 65536 * T' * S := by nlinarith

/-- **Corollary 7 (restricted success).** Under the model and parameter assumptions of
Theorem 6 and the space restriction `4S + 4 ≤ min{m, ⌊n/64⌋}`, average complete success
at least `2^{-S}` already implies `896 · T · S ≥ n · m`. -/
theorem time_space_tradeoff_small_success {H : HashFamily L n m} (hH : StronglyUniversal H)
    (hn : 256 ≤ n) (hmn : m ≤ n) {S : ℕ} (hS : n ≤ 2 ^ S) (hW : Fintype.card W ≤ 2 ^ S)
    (hSg : 4 * S + 4 ≤ gBound n m) (P : Program W L n m) {T : ℕ}
    (hT : queries P.steps ≤ T) (hsucc : ((2 : ℝ) ^ S)⁻¹ ≤ fullProbAvg H P) :
    n * m ≤ 896 * T * S := by
  set T' := queries P.steps with hT'
  set k := 4 * S + 4 with hk
  have hkm : k ≤ m := hSg.trans (min_le_left _ _)
  have hk1 : 1 ≤ k := by omega
  -- the excluded probability is below `2^{-S-1}`, so some good description has
  -- conditional success greater than `2^{-S-1}`
  have hδ : delta n ≤ ((2 : ℝ) ^ (S + 1))⁻¹ := by
    apply delta_le_inv_pow
    have : gBound n m ≤ n / 64 := min_le_right _ _
    omega
  have hδlt : delta n < ((2 : ℝ) ^ (S + 1))⁻¹ := by
    have h2 : delta n ≤ ((2 : ℝ) ^ (S + 2))⁻¹ := by
      apply delta_le_inv_pow
      have : gBound n m ≤ n / 64 := min_le_right _ _
      omega
    have : ((2 : ℝ) ^ (S + 2))⁻¹ < ((2 : ℝ) ^ (S + 1))⁻¹ := by
      apply inv_strictAnti₀ (by positivity)
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  have hhalf : ((2 : ℝ) ^ S)⁻¹ = ((2 : ℝ) ^ (S + 1))⁻¹ + ((2 : ℝ) ^ (S + 1))⁻¹ := by
    rw [pow_succ]
    field_simp
    ring
  obtain ⟨d, hd, hdsucc⟩ : ∃ d, Good H d ∧ ((2 : ℝ) ^ (S + 1))⁻¹ < fullProb H P d := by
    by_contra hcon
    push Not at hcon
    have := fullProbAvg_le_of_good_le hH (by omega) hmn P (by positivity) hcon
    linarith
  -- the whole program is not a short computation: `T' > t₀`
  have hT'gt : t0 n < T' := by
    by_contra hle
    push Not at hle
    have h1 := fullProb_le_shortProb hkm H P d
    have h2 := shortProb_le_of_good hd P.steps hle P.init_mass hk1 hSg
    have h3 : ((2 : ℝ) ^ k)⁻¹ + delta n ≤ ((2 : ℝ) ^ (S + 1))⁻¹ := by
      have hδk : delta n ≤ ((2 : ℝ) ^ k)⁻¹ := by
        apply delta_le_inv_pow
        have : gBound n m ≤ n / 64 := min_le_right _ _
        omega
      have hk' : ((2 : ℝ) ^ k)⁻¹ + ((2 : ℝ) ^ k)⁻¹ ≤ ((2 : ℝ) ^ (S + 1))⁻¹ := by
        have : ((2 : ℝ) ^ k)⁻¹ + ((2 : ℝ) ^ k)⁻¹ = ((2 : ℝ) ^ (k - 1))⁻¹ := by
          rw [hk, show 4 * S + 4 - 1 = 4 * S + 3 by omega, show 4 * S + 4 = (4 * S + 3) + 1 by ring,
            pow_succ]
          field_simp
          ring
        rw [this]
        apply inv_anti₀ (by positivity)
        apply pow_le_pow_right₀ (by norm_num)
        omega
      linarith
    linarith
  suffices hmain : n * m ≤ 896 * T' * S by
    calc n * m ≤ 896 * T' * S := hmain
      _ ≤ 896 * T * S := by gcongr
  have hS1 : 1 ≤ S := by
    by_contra h0
    push Not at h0
    have : S = 0 := by omega
    rw [this] at hS
    omega
  by_cases hbig : n ^ 2 < T'
  · calc n * m ≤ n * n := Nat.mul_le_mul_left n hmn
      _ = n ^ 2 := by ring
      _ ≤ T' := hbig.le
      _ ≤ 896 * T' * S := by nlinarith
  · push Not at hbig
    have hθ : ((2 : ℝ) ^ (S + 3))⁻¹ ≤ ((2 : ℝ) ^ (S + 1))⁻¹ := by
      apply inv_anti₀ (by positivity)
      apply pow_le_pow_right₀ (by norm_num)
      omega
    exact nm_le_of_sliced hd hn hmn hS hW P hT'gt hbig hSg hθ hdsucc

end

end QuantumNoiseStability.Hashing
end

-- Solutions.HashingCore.FixedHash
section
/-!
# Time-space bounds for individual hash functions

These results use a single set of good seeds for every space bound and every circuit.
The underlying bit-query program may measure its state and emit coordinates in any order.
-/


namespace QuantumNoiseStability.Hashing

open Finset
open scoped Classical

noncomputable section

variable {L n m S T : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- Exponent of the success threshold in Theorem 4.3, rounded down. -/
def successExponent (S m : ℕ) : ℕ := min S (m / 1024)

private theorem inv_pow_lt_succ (b : ℕ) : ((2 : ℝ) ^ (b + 1))⁻¹ < ((2 : ℝ) ^ b)⁻¹ := by
  apply inv_strictAnti₀ (by positivity)
  exact pow_lt_pow_right₀ (by norm_num) (by omega)

private theorem inv_pow_double (b : ℕ) :
    ((2 : ℝ) ^ (b + 1))⁻¹ + ((2 : ℝ) ^ (b + 1))⁻¹ = ((2 : ℝ) ^ b)⁻¹ := by
  rw [pow_succ]
  field_simp
  ring

private theorem tradeoff_of_good_aux {H : HashFamily L n m} {d : Bits L} (hd : Good H d)
    (hm : 1024 ≤ m) (hmn : m ≤ n) (hS : n ≤ 2 ^ S) (hW : Fintype.card W ≤ 2 ^ S)
    (P : Program W L n m) (hT : queries P.steps ≤ T)
    (hsucc : ((2 : ℝ) ^ (successExponent S m + 2))⁻¹ < fullProb H P d) :
    n * m ≤ 28672 * T * S := by
  let b := successExponent S m
  have hbS : b ≤ S := min_le_left _ _
  have hbm : b ≤ m / 1024 := min_le_right _ _
  have hSpos : 1 ≤ S := by
    by_contra! h
    have h0 : S = 0 := by omega
    rw [h0] at hS
    omega
  have hk : b + 3 ≤ gBound n m := by unfold gBound; omega
  have hq : t0 n < queries P.steps := by
    by_contra! hq
    have hu := shortProb_le_of_good hd P.steps hq P.init_mass (k := b + 3) (by omega) hk
    have hf := fullProb_le_shortProb (k := b + 3) (m := m) (by omega) H P d
    have he := delta_le_inv_pow (n := n) (k := b + 3) (by omega)
    have hi := inv_pow_double (b + 2)
    change ((2 : ℝ) ^ (b + 2))⁻¹ < _ at hsucc
    linarith
  suffices hx : n * m ≤ 28672 * queries P.steps * S by
    exact hx.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hT))
  by_cases hbig : n ^ 2 < queries P.steps
  · calc n * m ≤ n * n := Nat.mul_le_mul_left _ hmn
         _ = n ^ 2 := by ring
         _ ≤ queries P.steps := hbig.le
         _ ≤ 28672 * queries P.steps * S := by nlinarith
  by_cases hsmall : 4 * S + 4 ≤ gBound n m
  · have hh : ((2 : ℝ) ^ (S + 3))⁻¹ ≤ ((2 : ℝ) ^ (b + 2))⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h := nm_le_of_sliced hd (by omega) hmn hS hW P hq (Nat.le_of_not_gt hbig) hsmall hh hsucc
    exact h.trans (by gcongr; norm_num)
  · have hn32 : n < 32 * queries P.steps := by unfold t0 at hq; omega
    have hm896 : m ≤ 896 * S := by unfold gBound at hsmall; omega
    calc n * m ≤ (32 * queries P.steps) * (896 * S) := Nat.mul_le_mul hn32.le hm896
         _ = 28672 * queries P.steps * S := by ring

/-- The time-space bound for a good hash. The program may query a binary seed. -/
theorem tradeoff_of_good {H : HashFamily L n m} {d : Bits L} (hd : Good H d)
    (hm : 1024 ≤ m) (hmn : m ≤ n) (hS : n ≤ 2 ^ S) (hW : Fintype.card W ≤ 2 ^ S)
    (P : Program W L n m) (hT : queries P.steps ≤ T)
    (hsucc : ((2 : ℝ) ^ (successExponent S m + 1))⁻¹ < fullProb H P d) :
    n * m ≤ 28672 * T * S :=
  tradeoff_of_good_aux hd hm hmn hS hW P hT ((inv_pow_lt_succ _).trans hsucc)

/-- Success on a uniform argument for a fixed hash. The query register addresses argument bits. -/
def fixedFullProb (h : Bits n → Bits m) (P : Program W 0 n m) : ℝ :=
  fullProb (fun _ => h) P (fun i : Fin 0 => i.elim0)

/-- The quantitative bound for any one good seed. The program may depend arbitrarily on the seed. -/
theorem fixed_hash_tradeoff {K : Type*} {H : Family K n m} {d : K} (hd : Good H d)
    (hm : 1024 ≤ m) (hmn : m ≤ n) (hS : n ≤ 2 ^ S) (hW : Fintype.card W ≤ 2 ^ S)
    (P : Program W 0 n m) (hT : queries P.steps ≤ T)
    (hsucc : ((2 : ℝ) ^ successExponent S m)⁻¹ ≤ fixedFullProb (H d) P) :
    n * m ≤ 28672 * T * S := by
  exact tradeoff_of_good (H := fun _ : Bits 0 => H d) (d := fun i : Fin 0 => i.elim0)
    hd hm hmn hS hW P hT ((inv_pow_lt_succ _).trans_le hsucc)

/-- **Theorem 4.3.** The discarded fraction is at most `2^(-9ℓ)` for the reference space `S`.
The complementary seeds satisfy the small-success tradeoff for every larger space `S'`,
with success threshold evaluated at `S'`. The set actually works simultaneously for every space. -/
theorem almost_all_fixed_hash_tradeoff {K : Type*} [Fintype K]
    (H : Family K n m) (hH : StronglyUniversal H) (hm : 1024 ≤ m) (hmn : m ≤ n) (S : ℕ) :
    ∃ bad : Finset K,
      (bad.card : ℝ) ≤ ((2 : ℝ) ^ (9 * successExponent S m))⁻¹ * Fintype.card K ∧
      ∀ d ∉ bad, ∀ (S' T : ℕ), S ≤ S' → n ≤ 2 ^ S' →
        ∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W ≤ 2 ^ S' →
        ∀ P : Program W 0 n m, queries P.steps ≤ T →
          ((2 : ℝ) ^ successExponent S' m)⁻¹ ≤ fixedFullProb (H d) P →
          n * m ≤ 28672 * T * S' := by
  classical
  refine ⟨univ.filter (fun d => ¬ Good H d), ?_, ?_⟩
  · apply (card_not_good_le hH (by omega) hmn).trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply delta_le_inv_pow
    have : successExponent S m ≤ m / 1024 := min_le_right _ _
    omega
  · intro d hd S' T _ hS W _ _ hW P hT hsucc
    exact fixed_hash_tradeoff (by simpa using hd) hm hmn hS hW P hT hsucc

/-- **Corollary 4.4.** When a uniform binary seed is also part of the input, the same
resource bound holds at success `2^(-min(S,⌊m/1024⌋))` averaged over seed and argument. -/
theorem evaluation_tradeoff {H : HashFamily L n m} (hH : StronglyUniversal H)
    (hm : 1024 ≤ m) (hmn : m ≤ n) (hS : n ≤ 2 ^ S) (hW : Fintype.card W ≤ 2 ^ S)
    (P : Program W L n m) (hT : queries P.steps ≤ T)
    (hsucc : ((2 : ℝ) ^ successExponent S m)⁻¹ ≤ fullProbAvg H P) :
    n * m ≤ 28672 * T * S := by
  let b := successExponent S m
  have hb : b ≤ m / 1024 := min_le_right _ _
  have hdelta := delta_le_inv_pow (n := n) (k := b + 2) (by omega)
  have hstrict := inv_pow_lt_succ (b + 1)
  have hdouble := inv_pow_double b
  obtain ⟨d, hd, hs⟩ : ∃ d, Good H d ∧ ((2 : ℝ) ^ (b + 1))⁻¹ < fullProb H P d := by
    by_contra! hall
    have hle := fullProbAvg_le_of_good_le hH (by omega) hmn P (by positivity) hall
    change ((2 : ℝ) ^ b)⁻¹ ≤ _ at hsucc
    linarith
  exact tradeoff_of_good hd hm hmn hS hW P hT hs

/-- The real success exponent used in the paper is strictly less than the integer
exponent plus one, including when the space bound is the smaller term. -/
theorem successExponent_real_lt (S m : ℕ) :
    min (S : ℝ) ((m : ℝ) / 1024) < (successExponent S m : ℝ) + 1 := by
  by_cases h : S ≤ m / 1024
  · rw [successExponent, min_eq_left h]
    exact (min_le_left _ _).trans_lt (by linarith)
  · have hlt : m < 1024 * (m / 1024 + 1) := by omega
    have hR : (m : ℝ) < 1024 * ((m / 1024 : ℕ) + 1 : ℝ) := by exact_mod_cast hlt
    rw [successExponent, min_eq_right (by omega : m / 1024 ≤ S)]
    exact (min_le_right _ _).trans_lt (by linarith)

private theorem exponent_probability_lt (S m : ℕ) :
    ((2 : ℝ) ^ (successExponent S m + 1))⁻¹ <
      (2 : ℝ) ^ (-min (S : ℝ) ((m : ℝ) / 1024)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  push_cast
  linarith [successExponent_real_lt S m]

/-- **Theorem 4.3**, with the real exponent `min S (m/1024)` in both probabilities. -/
theorem theorem_4_3 {K : Type*} [Fintype K] (H : Family K n m) (hH : StronglyUniversal H)
    (hm : 1024 ≤ m) (hmn : m ≤ n) (S : ℕ) :
    ∃ bad : Finset K,
      (bad.card : ℝ) ≤ (2 : ℝ) ^ (-(9 * min (S : ℝ) ((m : ℝ) / 1024))) * Fintype.card K ∧
      ∀ d ∉ bad, ∀ (S' T : ℕ), S ≤ S' → n ≤ 2 ^ S' →
        ∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W ≤ 2 ^ S' →
        ∀ P : Program W 0 n m, queries P.steps ≤ T →
          (2 : ℝ) ^ (-min (S' : ℝ) ((m : ℝ) / 1024)) ≤ fixedFullProb (H d) P →
          n * m ≤ 28672 * T * S' := by
  classical
  refine ⟨univ.filter (fun d => ¬ Good H d), (card_not_good_le hH (by omega) hmn).trans ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith [min_le_right (S : ℝ) ((m : ℝ) / 1024), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  · intro d hd S' T _ hS W _ _ hW P hT hs
    have hg : Good H d := by simpa using hd
    exact tradeoff_of_good (H := fun _ : Bits 0 => H d) (d := fun i : Fin 0 => i.elim0)
      hg hm hmn hS hW P hT ((exponent_probability_lt _ _).trans_le hs)

/-- **Corollary 4.4**, with the paper's real success exponent. -/
theorem corollary_4_4 {H : HashFamily L n m} (hH : StronglyUniversal H)
    (hm : 1024 ≤ m) (hmn : m ≤ n) (hS : n ≤ 2 ^ S) (hW : Fintype.card W ≤ 2 ^ S)
    (P : Program W L n m) (hT : queries P.steps ≤ T)
    (hsucc : (2 : ℝ) ^ (-min (S : ℝ) ((m : ℝ) / 1024)) ≤ fullProbAvg H P) :
    n * m ≤ 28672 * T * S := by
  let b := successExponent S m
  have hb : b ≤ m / 1024 := min_le_right _ _
  have hdelta := delta_le_inv_pow (n := n) (k := b + 2) (by omega)
  have hdouble := inv_pow_double (b + 1)
  have hthreshold : ((2 : ℝ) ^ (b + 1))⁻¹ < fullProbAvg H P :=
    (exponent_probability_lt _ _).trans_le hsucc
  obtain ⟨d, hd, hs⟩ : ∃ d, Good H d ∧ ((2 : ℝ) ^ (b + 2))⁻¹ < fullProb H P d := by
    by_contra! hall
    have hle := fullProbAvg_le_of_good_le hH (by omega) hmn P (by positivity) hall
    linarith
  exact tradeoff_of_good_aux hd hm hmn hS hW P hT hs

end

end QuantumNoiseStability.Hashing
end

-- Solutions.HashProgram
section
/-! Compile a public binary space-bounded algorithm on its original memory. -/

noncomputable section

namespace QNoiseStab.Supplement.HashProgram

open Matrix QuantumNoiseStability.Hashing BranchExecution
open scoped Classical

variable {n m T : ℕ} {W V κ : Type} [Fintype W] [DecidableEq W] [Fintype V] [Fintype κ]
local notation "Mem" => (Fin n × ZMod 2) × W
local notation "Outcome" => Option (Fin m × V)

variable (A : SpaceBoundedAlg n 2 W (Fin m) V κ T) (q : V → Bool)
  (enc : Bool ≃ ZMod 2) (ω : ℂ) (hω : ω^2 = 1)

include A in
/-- The compiled program starts at a basis vector and prepares the columns of the public
density-matrix factor in a silent operation. Its remaining steps compile the instruments. -/
def program : Program Mem 0 n m :=
  let L := (exists_start_factor A).choose
  let w := Classical.choice A.memory_nonempty
  let prep := operation (prepareMatrix L w) (fun _ => [])
    (prepare_sub L w (exists_start_factor A).choose_spec.2)
  ⟨.op prep :: compiledSteps q (HashBitOracle.query enc ω) (HashBitOracle.offset enc ω)
    (HashBitOracle.mass_offset enc ω hω) A.step, basis w, (mass_basis w).le⟩

/-- Preparation adds no queries to the public algorithm's query count. -/
theorem queries_program : queries (program A q enc ω hω).steps = T :=
  queries_compiledSteps ..

private theorem sum_separate {O R : Type} [Fintype O] [Fintype R] {k : ℕ}
    (g : (Fin k → O) → (Fin k → R) → ℝ) :
    (∑ p : Fin k → O × R, g (fun t => (p t).1) (fun t => (p t).2)) =
    ∑ o, ∑ r, g o r := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => O) (fun _ => R))
    _ _ (fun _ => rfl)

/-- For each input and target output the compiled program has exactly the public success mass. -/
theorem eventMass_program (x : Bits n) (z : Bits m) (d₀ : Bits 0) :
    eventMass (program A q enc ω hω).steps (d₀,x) (program A q enc ω hω).init (FullSuccess z) =
    ∑ o, if CommitsCorrect q z o then A.commitProb ω (enc ∘ x) o else 0 := by
  let L := (exists_start_factor A).choose
  let w := Classical.choice A.memory_nonempty
  let Q : Query Mem 0 n := HashBitOracle.query enc ω
  let D : Matrix Mem Mem ℂ := HashBitOracle.offset enc ω
  let hD := HashBitOracle.mass_offset (n := n) (W := W) enc ω hω
  let l := compiledSteps q Q D hD A.step
  let g := fun (c : List (Fin m × Bool)) (v : State Mem) => if FullSuccess z c then mass v else 0
  have hprep := sum_operation (prepareMatrix L w) (fun _ => [])
    (prepare_sub L w (exists_start_factor A).choose_spec.2) l (d₀,x) (basis w) g
  trans ∑ j : Mem, ∑ p : Fin (T+1) → Outcome × κ, g (transcript q (fun t => (p t).1))
    (pathState (fun t => (A.step t).kraus (p t).1 (p t).2)
      (D * Q.matrix (d₀,x)) (fun i => L i j))
  · trans ∑ j : Mem, ∑ h, g (claims l h) (run l (d₀,x) (fun i => L i j) h)
    · simp only [prepare_basis, List.nil_append] at hprep
      convert hprep using 1
      rfl
    · exact Finset.sum_congr rfl fun j _ =>
        sum_compiledSteps q Q D hD A.step (d₀,x) (fun i => L i j) g
  rw [Finset.sum_comm]
  let weight := fun (o : Fin (T+1) → Outcome) (r : Fin (T+1) → κ) =>
    ∑ j, g (transcript q o) (pathState (fun t => (A.step t).kraus (o t) (r t))
      (D * Q.matrix (d₀,x)) (fun i => L i j))
  change (∑ p : Fin (T+1) → Outcome × κ, weight (fun t => (p t).1) (fun t => (p t).2)) = _
  rw [sum_separate weight]
  apply Finset.sum_congr rfl
  intro o _
  have hO : D * Q.matrix (d₀,x) = oracle (W := W) ω (enc ∘ x) :=
    (HashBitOracle.oracle_eq enc ω hω x d₀).symm
  by_cases hc : CommitsCorrect q z o <;>
    simp [weight, g, fullSuccess_transcript, hc, hO, mass,
      commitProb_eq_sum A ω _ o L (exists_start_factor A).choose_spec.1]

/-- Averaging over the uniform input preserves success exactly for every target function. -/
theorem success_eq (f : Bits n → Bits m) :
    A.successProb enc ω q f = fixedFullProb f (program A q enc ω hω) := by
  simp only [SpaceBoundedAlg.successProb, fixedFullProb, fullProb, eventMass_program,
    Fintype.card_bool, Nat.cast_ofNat, Function.comp_def]

include hω in
/-- Every public binary algorithm admits a bit-query program with the same memory and query
count and at least its uniform success probability. -/
theorem exists_program (f : (Fin n → Bool) → (Fin m → Bool)) :
    ∃ P : Program ((Fin n × ZMod 2) × W) 0 n m,
      queries P.steps = T ∧ A.successProb enc ω q f ≤ fixedFullProb f P :=
  ⟨program A q enc ω hω, queries_program A q enc ω hω, (success_eq A q enc ω hω f).le⟩

end QNoiseStab.Supplement.HashProgram
end
end

-- Solutions.Theorem43
section
set_option autoImplicit false

namespace QNoiseStab.Supplement

/-- **Theorem 4.3** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §4.1, p.19): "Let H be a strongly universal family of hash functions
from {0,1}^n to {0,1}^m for n ≥ m for sufficiently large m. Let S be a space bound and
ℓ = min(S, m/1024). For all but a 2^{−9ℓ} fraction of functions h ∈ H, any quantum query
algorithm that computes the function h using S qubits of memory, and succeeds with probability at
least 2^{−ℓ} on inputs uniformly chosen from {0,1}^n, must make a number of queries T that is
Ω(mn/S). Moreover, this statement also holds if functions identified as hard for space S must be
hard for all space bounds S′ such that S ≤ S′."

Stated in the strong ("Moreover") form: there are an absolute constant `C > 0` and a threshold
`m₀` such that for all `m ≥ m₀`, `n ≥ m`, every strongly universal indexed family `H` and every
`S`, some set `Bad` of at most a `2^{−9 ℓ(S)}` fraction of the indices has the property: for every
`i ∉ Bad`, every `S′ ≥ S` and every `T`-query algorithm using at most `S′` qubits that computes
`h_i` (all `m` output bits committed, all commits correct) with success probability at least
`2^{−ℓ(S′)}` on a uniform input, `T ≥ C·m·n/S′`. Here `ℓ(S) = min(S, m/1024)`.

**Formalization Note** The model is `SpaceBoundedAlg` (one instrument per step; the query and
phase registers count against the space). Bits are `Bool`, encoded into `ZMod 2` by any bijection
`enc`; the oracle's root `ω` is any `ω` with `ω^2 = 1`. The output coordinates are the `m` bits of
`h(x)`. Ω and "sufficiently large" are the constants `C`, `m₀`, chosen before everything else. -/
private theorem submission_proof :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m n : ℕ, m₀ ≤ m → m ≤ n →
      ∀ (ι : Type) [Fintype ι] (H : ι → (Fin n → Bool) → (Fin m → Bool)),
        IsStronglyUniversal H →
      ∀ S : ℕ, ∃ Bad : Finset ι,
        (Bad.card : ℝ) ≤ (2 : ℝ) ^ (-9 * min (S : ℝ) ((m : ℝ) / 1024)) * Fintype.card ι ∧
        ∀ i, i ∉ Bad → ∀ S' : ℕ, S ≤ S' →
        ∀ (W V κ : Type) [Fintype W] [DecidableEq W] [Fintype V] [Fintype κ] (T : ℕ)
          (A : SpaceBoundedAlg n 2 W (Fin m) V κ T) (q : V → Bool) (enc : Bool ≃ ZMod 2)
          (ω : ℂ), ω ^ 2 = 1 → A.FitsInSpace S' →
          (2 : ℝ) ^ (-min (S' : ℝ) ((m : ℝ) / 1024)) ≤ A.successProb enc ω q (fun x => H i x) →
          C * m * n / S' ≤ T := by
  classical
  refine ⟨1 / 28672, by norm_num, 1024, ?_⟩
  intro m n hm hmn ι _ H hH S
  obtain ⟨bad, hbad, hhard⟩ :=
    QuantumNoiseStability.Hashing.theorem_4_3 H hH.binary_counts hm hmn S
  refine ⟨bad, by simpa only [neg_mul] using hbad, ?_⟩
  intro i hi S' hS W V κ _ _ _ _ T A q enc ω hω hfit hsucc
  obtain ⟨P, htime, hprob⟩ := HashProgram.exists_program A q enc ω hω (H i)
  have haddr := A.address_fits hfit
  have h := hhard i hi S' T hS haddr _ (A.card_memory_le hfit) P htime.le (hsucc.trans hprob)
  have hpos : 0 < S' := by
    by_contra! hzero
    have hz : S' = 0 := by omega
    simp [hz] at haddr
    omega
  have hr : (n : ℝ) * m ≤ 28672 * (T : ℝ) * S' := by exact_mod_cast h
  apply (div_le_iff₀ (Nat.cast_pos.mpr hpos : (0 : ℝ) < S')).mpr
  linarith only [hr]

end QNoiseStab.Supplement
end

section
set_option autoImplicit false
open QNoiseStab QNoiseStab.Supplement

set_option linter.unusedVariables false in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m n : ℕ, m₀ ≤ m → m ≤ n →
      ∀ (ι : Type) [Fintype ι] (H : ι → (Fin n → Bool) → (Fin m → Bool)),
        IsStronglyUniversal H →
      ∀ S : ℕ, ∃ Bad : Finset ι,
        (Bad.card : ℝ) ≤ (2 : ℝ) ^ (-9 * min (S : ℝ) ((m : ℝ) / 1024)) * Fintype.card ι ∧
        ∀ i, i ∉ Bad → ∀ S' : ℕ, S ≤ S' →
        ∀ (W V κ : Type) [Fintype W] [DecidableEq W] [Fintype V] [Fintype κ] (T : ℕ)
          (A : SpaceBoundedAlg n 2 W (Fin m) V κ T) (q : V → Bool) (enc : Bool ≃ ZMod 2)
          (ω : ℂ), ω ^ 2 = 1 → A.FitsInSpace S' →
          (2 : ℝ) ^ (-min (S' : ℝ) ((m : ℝ) / 1024)) ≤ A.successProb enc ω q (fun x => H i x) →
          C * m * n / S' ≤ T :=
  @QNoiseStab.Supplement.submission_proof

end
