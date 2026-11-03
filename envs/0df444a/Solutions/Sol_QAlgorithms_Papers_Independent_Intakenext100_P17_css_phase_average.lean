-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P17.css_phase_average
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T23:55:53.945233+00:00
-- url     : https://prove2.me/submissions/f54e4384-47df-4f9c-b96d-d31bf8028511

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P17

section Mod_NPK_F2
/-!
# Arithmetic over `F₂ = ZMod 2`: characters, weights, counting

Toolkit for the one-way hashing protocol of `near_private_bit_key`.
-/

open scoped Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

abbrev F2 := ZMod 2

/-- The nontrivial character of `F₂`: `χ(0) = 1`, `χ(1) = -1`. -/
def chi (x : F2) : ℂ := if x = 0 then 1 else -1

lemma F2_cases (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma F2_ne_zero_iff (x : F2) : x ≠ 0 ↔ x = 1 := by
  rcases F2_cases x with h | h <;> simp [h]

lemma F2_add_self (x : F2) : x + x = 0 := by
  rcases F2_cases x with rfl | rfl <;> decide

lemma vec_add_self {ι : Type*} (v : ι → F2) : v + v = 0 := by
  funext i; exact F2_add_self _

@[simp] lemma chi_zero : chi 0 = 1 := by simp [chi]

@[simp] lemma chi_one : chi 1 = -1 := by simp [chi]

lemma chi_add (x y : F2) : chi (x + y) = chi x * chi y := by
  rcases F2_cases x with rfl | rfl <;> rcases F2_cases y with rfl | rfl <;> simp [chi] <;> decide

lemma chi_mul_self (x : F2) : chi x * chi x = 1 := by
  rcases F2_cases x with rfl | rfl <;> simp

lemma star_chi (x : F2) : star (chi x) = chi x := by
  rcases F2_cases x with rfl | rfl <;> simp

lemma chi_ne_zero (x : F2) : chi x ≠ 0 := by
  rcases F2_cases x with rfl | rfl <;> simp

lemma chi_sum {ι : Type*} (s : Finset ι) (f : ι → F2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, chi_add, ih]

lemma univ_F2 : (Finset.univ : Finset F2) = {0, 1} := by decide

lemma sum_F2 {M : Type*} [AddCommMonoid M] (f : F2 → M) : ∑ x, f x = f 0 + f 1 := by
  rw [univ_F2, Finset.sum_pair (by decide)]

lemma sum_chi_mul (c : F2) : ∑ x : F2, chi (x * c) = if c = 0 then 2 else 0 := by
  rw [sum_F2]
  rcases F2_cases c with rfl | rfl
  · simp; norm_num
  · simp

/-- Orthogonality of characters on `F₂ⁿ`. -/
lemma sum_chi_dot {n : ℕ} (v : Fin n → F2) :
    ∑ a : Fin n → F2, chi (a ⬝ᵥ v) = if v = 0 then (2 : ℂ) ^ n else 0 := by
  have h1 : ∀ a : Fin n → F2, chi (a ⬝ᵥ v) = ∏ i, chi (a i * v i) := by
    intro a
    simp only [dotProduct]
    exact chi_sum _ _
  simp only [h1]
  rw [← Fintype.prod_sum (fun (i : Fin n) (x : F2) => chi (x * v i))]
  simp only [sum_chi_mul]
  by_cases hv : v = 0
  · subst hv; simp
  · rw [if_neg hv]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have hi' : v i ≠ 0 := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi'])

/-- Hamming weight. -/
def wt {n : ℕ} (v : Fin n → F2) : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card

lemma wt_zero {n : ℕ} : wt (0 : Fin n → F2) = 0 := by simp [wt]

lemma wt_eq_zero_iff {n : ℕ} (v : Fin n → F2) : wt v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    by_contra hi
    have hi' : v i ≠ 0 := hi
    have : i ∈ Finset.univ.filter fun i => v i ≠ 0 := by simp [hi']
    rw [wt, Finset.card_eq_zero] at h
    rw [h] at this
    simp at this
  · rintro rfl; exact wt_zero

lemma wt_add_le {n : ℕ} (u v : Fin n → F2) : wt (u + v) ≤ wt u + wt v := by
  classical
  unfold wt
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Pi.add_apply] at hi ⊢
  by_contra h
  rw [not_or, not_not, not_not] at h
  rw [h.1, h.2, add_zero] at hi
  exact hi rfl

lemma wt_le {n : ℕ} (v : Fin n → F2) : wt v ≤ n := by
  unfold wt
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-- Product formula for the Bernoulli weight of a vector. -/
lemma prod_bernoulli {n : ℕ} (β : ℝ) (v : Fin n → F2) :
    ∏ i, (if v i ≠ 0 then β else 1 - β) = β ^ wt v * (1 - β) ^ (n - wt v) := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => v i ≠ 0)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  unfold wt
  omega

/-- **Ball-size bound.** For `0 < β ≤ 1/2` and `j ≤ n`, the number of vectors of weight at most
`j` is at most `β^{-j} (1 - β)^{-(n - j)}`. -/
lemma card_ball_le {n : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ : β ≤ 1 / 2) (j : ℕ) (hj : j ≤ n) :
    ((Finset.univ.filter fun v : Fin n → F2 => wt v ≤ j).card : ℝ) * (β ^ j * (1 - β) ^ (n - j))
      ≤ 1 := by
  classical
  have h1β : β ≤ 1 - β := by linarith
  have h1β0 : 0 < 1 - β := by linarith
  have hpt : ∀ v : Fin n → F2, wt v ≤ j →
      β ^ j * (1 - β) ^ (n - j) ≤ β ^ wt v * (1 - β) ^ (n - wt v) := by
    intro v hv
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hv
    have e1 : n - wt v = d + (n - j) := by omega
    have hj' : β ^ j = β ^ wt v * β ^ d := by rw [hd, pow_add]
    have hn' : (1 - β) ^ (n - wt v) = (1 - β) ^ d * (1 - β) ^ (n - j) := by rw [e1, pow_add]
    rw [hj', hn']
    have : β ^ d ≤ (1 - β) ^ d := pow_le_pow_left₀ hβ0.le h1β d
    calc β ^ wt v * β ^ d * (1 - β) ^ (n - j)
        ≤ β ^ wt v * (1 - β) ^ d * (1 - β) ^ (n - j) := by gcongr
      _ = β ^ wt v * ((1 - β) ^ d * (1 - β) ^ (n - j)) := by ring
  have htot : ∑ v : Fin n → F2, β ^ wt v * (1 - β) ^ (n - wt v) = 1 := by
    simp only [← prod_bernoulli]
    rw [← Fintype.prod_sum (fun (i : Fin n) (x : F2) => if x ≠ 0 then β else 1 - β)]
    have : ∀ i : Fin n, ∑ x : F2, (if x ≠ 0 then β else 1 - β) = 1 := by
      intro i
      rw [sum_F2]
      simp only [ne_eq, not_true_eq_false, if_false]
      rw [if_pos (by decide)]; ring
    exact Finset.prod_eq_one fun i _ => this i
  calc ((Finset.univ.filter fun v : Fin n → F2 => wt v ≤ j).card : ℝ) * (β ^ j * (1 - β) ^ (n - j))
      = ∑ v ∈ Finset.univ.filter (fun v : Fin n → F2 => wt v ≤ j), β ^ j * (1 - β) ^ (n - j) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v : Fin n → F2 => wt v ≤ j),
          β ^ wt v * (1 - β) ^ (n - wt v) :=
        Finset.sum_le_sum fun v hv => hpt v (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v : Fin n → F2, β ^ wt v * (1 - β) ^ (n - wt v) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun v _ _ => by positivity)
    _ = 1 := htot

/-! ### Counting solutions of linear equations -/

lemma card_dot_eq {ι : Type} [Fintype ι] [DecidableEq ι] (y : ι → F2) (hy : y ≠ 0) (c : F2) :
    (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = c).card = 2 ^ Fintype.card ι / 2 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
  have hyi : y i = 1 := (F2_ne_zero_iff _).mp hi
  let τ : (ι → F2) → (ι → F2) := fun h => h + Pi.single i 1
  have hτ : ∀ h, τ h ⬝ᵥ y = h ⬝ᵥ y + 1 := by
    intro h
    simp only [τ, add_dotProduct, single_dotProduct, one_mul, hyi]
  have hττ : ∀ h, τ (τ h) = h := by
    intro h
    simp only [τ, add_assoc]
    have : (Pi.single i (1 : F2) : ι → F2) + Pi.single i 1 = 0 := by
      rw [← Pi.single_add]; simp; decide
    rw [this, add_zero]
  have hcard : ∀ c' : F2, (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = c').card =
      (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = c' + 1).card := by
    intro c'
    refine Finset.card_bij (fun h _ => τ h) ?_ ?_ ?_
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      rw [hτ, hh]
    · intro h1 _ h2 _ h12
      have := congrArg τ h12
      rwa [hττ, hττ] at this
    · intro h hh
      refine ⟨τ h, ?_, hττ h⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      rw [hτ, hh, add_assoc]
      have : (1 : F2) + 1 = 0 := by decide
      rw [this, add_zero]
  have htot : (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = 0).card +
      (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = 1).card = 2 ^ Fintype.card ι := by
    rw [← Finset.card_union_of_disjoint]
    · have : (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = 0) ∪
          (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = 1) = Finset.univ := by
        ext h
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact F2_cases _
      rw [this, Finset.card_univ, Fintype.card_fun, ZMod.card]
    · rw [Finset.disjoint_filter]
      intro h _ h0 h1
      rw [h0] at h1
      exact absurd h1 (by decide)
  have h01 := hcard 0
  simp only [zero_add] at h01
  rcases F2_cases c with rfl | rfl
  · omega
  · omega

lemma card_mulVec_eq {ρ ι : Type} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (y : ι → F2) (hy : y ≠ 0) (z : ρ → F2) :
    (Finset.univ.filter fun M : Matrix ρ ι F2 => M *ᵥ y = z).card =
      (2 ^ Fintype.card ι / 2) ^ Fintype.card ρ := by
  classical
  rw [← Fintype.card_subtype]
  have e : {M : Matrix ρ ι F2 // M *ᵥ y = z} ≃
      ((i : ρ) → {h : ι → F2 // h ⬝ᵥ y = z i}) :=
    (Equiv.subtypeEquivRight (fun M => by
      constructor
      · intro hM i; exact congrFun hM i
      · intro hM; funext i; exact hM i)).trans
      (Equiv.subtypePiEquivPi (p := fun (i : ρ) (h : ι → F2) => h ⬝ᵥ y = z i))
  rw [Fintype.card_congr e, Fintype.card_pi]
  simp only [Fintype.card_subtype, card_dot_eq y hy, Finset.prod_const, Finset.card_univ]

lemma half_pow_bound (N k : ℕ) :
    (((2 ^ N / 2) ^ k : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N * k) * (1 / 2) ^ k := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simp [zero_pow hk.ne']
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have h2 : 2 ^ (M + 1) / 2 = 2 ^ M := by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rw [h2]
    push_cast
    rw [← pow_mul, show (M + 1) * k = M * k + k by ring, pow_add, mul_assoc, ← mul_pow]
    norm_num

end NPK

end Mod_NPK_F2

set_option autoImplicit false

open scoped ComplexConjugate
open Classical
open QAlgorithms QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Intakenext100.P17
open QAlgorithms.Papers.Independent.Support50.P04 (BinaryWord)

noncomputable section

namespace BB84CSS

open NPK

lemma neg_one_pow_val (x : ZMod 2) : (-1 : ℂ) ^ x.val = chi x := by
  rcases F2_cases x with rfl | rfl
  · simp [chi]
  · simp [chi, ZMod.val_one]

lemma phaseCharacter_eq {n : ℕ} (z w : BinaryWord n) : phaseCharacter z w = chi (z ⬝ᵥ w) := by
  unfold phaseCharacter
  rw [neg_one_pow_val]
  rfl

lemma star_phaseCharacter {n : ℕ} (z w : BinaryWord n) :
    conj (phaseCharacter z w) = phaseCharacter z w := by
  rw [phaseCharacter_eq]
  exact star_chi _

/-- Orthogonality of the characters of `F₂ⁿ`. -/
lemma sum_phase_mul {n : ℕ} (w w' : BinaryWord n) :
    ∑ z : BinaryWord n, phaseCharacter z w * phaseCharacter z w' =
      if w = w' then (2 : ℂ) ^ n else 0 := by
  simp only [phaseCharacter_eq, ← chi_add, ← dotProduct_add]
  rw [sum_chi_dot]
  congr 1
  apply propext
  constructor
  · intro h
    calc w = w + w' + w' := by rw [add_assoc, vec_add_self, add_zero]
      _ = w' := by rw [h, zero_add]
  · rintro rfl; exact vec_add_self w

lemma ket_apply {ι : Type} [DecidableEq ι] (i j : ι) : (ket i : EuclideanSpace ℂ ι) j =
    if j = i then 1 else 0 := by
  simp [ket]

lemma cssPhaseWord_apply {n : ℕ} (C2 : Submodule (ZMod 2) (BinaryWord n)) (v x z : BinaryWord n)
    (a : Qubits n) :
    cssPhaseWord C2 v x z a = ((Real.sqrt (Fintype.card C2 : ℝ))⁻¹ : ℂ) *
      ∑ w : C2, phaseCharacter z (w : BinaryWord n) *
        (if a = bitsOfZMod (x + v + (w : BinaryWord n)) then 1 else 0) := by
  unfold cssPhaseWord
  simp only [PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply, ket_apply]

lemma conj_ite_one (p : Prop) [Decidable p] :
    (starRingEnd ℂ) (if p then (1 : ℂ) else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

lemma sqrt_card_sq {n : ℕ} (C2 : Submodule (ZMod 2) (BinaryWord n)) :
    ((Real.sqrt (Fintype.card C2 : ℝ))⁻¹ : ℂ) * conj ((Real.sqrt (Fintype.card C2 : ℝ))⁻¹ : ℂ) =
      (Fintype.card C2 : ℂ)⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg _)]
  push_cast
  rfl

end BB84CSS

open BB84CSS NPK in
theorem solution {n : ℕ}
    (C1 C2 : Submodule (ZMod 2) (BinaryWord n)) (h21 : C2 ≤ C1)
    (v : C1) (x : BinaryWord n) :
    ((2 : ℂ) ^ n)⁻¹ •
        (∑ z : BinaryWord n, pureDensity (cssPhaseWord C2 (v : BinaryWord n) x z)) =
      (Fintype.card C2 : ℂ)⁻¹ •
        (∑ w : C2, pureDensity
          (ket (bitsOfZMod ((v : BinaryWord n) + (w : BinaryWord n) + x)))) := by
  classical
  ext a b
  simp only [Matrix.smul_apply, Matrix.sum_apply, pureDensity, Matrix.of_apply, smul_eq_mul,
    cssPhaseWord_apply, ket_apply, map_mul, map_sum, star_phaseCharacter]
  set s : ℂ := ((Real.sqrt (Fintype.card C2 : ℝ))⁻¹ : ℂ) with hs
  -- expand the product of the two sums
  have e1 : ∀ z : BinaryWord n,
      s * (∑ w : C2, phaseCharacter z (w : BinaryWord n) *
          (if a = bitsOfZMod (x + (v : BinaryWord n) + (w : BinaryWord n)) then 1 else 0)) *
        (conj s * ∑ w' : C2, phaseCharacter z (w' : BinaryWord n) *
          conj (if b = bitsOfZMod (x + (v : BinaryWord n) + (w' : BinaryWord n)) then (1 : ℂ) else 0)) =
      s * conj s * ∑ w : C2, ∑ w' : C2,
        (phaseCharacter z (w : BinaryWord n) * phaseCharacter z (w' : BinaryWord n)) *
          ((if a = bitsOfZMod (x + (v : BinaryWord n) + (w : BinaryWord n)) then 1 else 0) *
            (if b = bitsOfZMod (x + (v : BinaryWord n) + (w' : BinaryWord n)) then 1 else 0)) := by
    intro z
    rw [mul_mul_mul_comm, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
    rw [conj_ite_one]
    ring
  simp only [e1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have e2 : ∀ w : C2, ∑ z : BinaryWord n, ∑ w' : C2,
      (phaseCharacter z (w : BinaryWord n) * phaseCharacter z (w' : BinaryWord n)) *
        ((if a = bitsOfZMod (x + (v : BinaryWord n) + (w : BinaryWord n)) then (1 : ℂ) else 0) *
          (if b = bitsOfZMod (x + (v : BinaryWord n) + (w' : BinaryWord n)) then 1 else 0)) =
      (2 : ℂ) ^ n * ((if a = bitsOfZMod ((v : BinaryWord n) + (w : BinaryWord n) + x) then 1 else 0) *
        (if b = bitsOfZMod ((v : BinaryWord n) + (w : BinaryWord n) + x) then 1 else 0)) := by
    intro w
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, sum_phase_mul]
    rw [Finset.sum_eq_single w]
    · rw [if_pos rfl]
      have hxv : x + (v : BinaryWord n) + (w : BinaryWord n) =
          (v : BinaryWord n) + (w : BinaryWord n) + x := by abel
      rw [hxv]
    · intro w' _ hw'
      rw [if_neg (fun h => hw' (Subtype.ext h.symm)), zero_mul]
    · simp
  simp only [e2, ← Finset.mul_sum]
  rw [sqrt_card_sq]
  rw [← mul_assoc, ← mul_assoc, mul_comm ((2 : ℂ) ^ n)⁻¹, mul_assoc _ ((2 : ℂ) ^ n)⁻¹,
    inv_mul_cancel₀ (pow_ne_zero n (two_ne_zero)), mul_one]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [conj_ite_one]
