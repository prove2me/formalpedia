-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P40.cat_jointProbabilities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:18:46.530847+00:00
-- url     : https://prove2.me/submissions/31ca1d57-e63e-4bcb-84cd-caff8124056a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40


namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- per-qubit error weight -/
def x5ctW (f : ℝ) (x : Pauli) : ℝ := if x = .I then f else noiseG f

/-- sign of a bit -/
def x5ctS (b : Bool) : ℝ := if b then -1 else 1

lemma x5ct_S_add (a b : Bool) : x5ctS (a + b) = x5ctS a * x5ctS b := by
  cases a <;> cases b <;> norm_num [x5ctS] <;> rfl

lemma x5ct_S_sum {n : ℕ} (u : Fin n → Bool) : x5ctS (∑ q, u q) = ∏ q, x5ctS (u q) := by
  induction n with
  | zero => simp [x5ctS]
  | succ n ih => rw [Fin.sum_univ_succ, Fin.prod_univ_succ, x5ct_S_add, ih]

lemma x5ct_ind (s π : Bool) :
    (if s = π then (1 : ℝ) else 0) = (1 + x5ctS π * x5ctS s) / 2 := by
  cases s <;> cases π <;> norm_num [x5ctS]

lemma x5ct_sumP (F : Pauli → ℝ) : ∑ x : Pauli, F x = F .I + F .X + F .Y + F .Z := by
  rw [show (Finset.univ : Finset Pauli) = {.I, .X, .Y, .Z} from rfl]
  simp [Finset.sum_insert]; ring

lemma x5ct_prod_ite {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (α β : ℝ) :
    ∏ q, (if P q then α else β) =
      α ^ (Finset.univ.filter P).card * β ^ (n - (Finset.univ.filter P).card) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) P
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

lemma x5ct_wprod {n : ℕ} (e : ErrorLabel n) (f : ℝ) :
    ∏ q, x5ctW f (e q) = f ^ (n - opsWeight e) * noiseG f ^ opsWeight e := by
  unfold x5ctW
  rw [x5ct_prod_ite (fun q => e q = Pauli.I) f (noiseG f)]
  have h2 : (Finset.univ.filter fun q => e q = Pauli.I).card + opsWeight e = n := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun q => e q = Pauli.I)
    simpa [opsWeight] using this
  rw [show n - opsWeight e = (Finset.univ.filter fun q => e q = Pauli.I).card by omega,
    show n - (Finset.univ.filter fun q => e q = Pauli.I).card = opsWeight e by omega]

open Classical in
lemma x5ct_mass {n : ℕ} (f : ℝ) (P : ErrorLabel n → Prop) :
    errorEventMass f P = ∑ e, if P e then ∏ q, x5ctW f (e q) else 0 := by
  classical
  unfold errorEventMass weightPolynomial
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [x5ct_wprod]

/-- the core factorized count -/
lemma x5ct_core {n : ℕ} (f : ℝ) (c : Fin n → Bool) (π : Bool) :
    (∑ e : ErrorLabel n, if (∀ q, amplitudeBit (e q) = c q) ∧ (∑ q, phaseBit (e q)) = π
      then ∏ q, x5ctW f (e q) else 0) =
    ((∏ q, if c q then 2 * noiseG f else f + noiseG f) +
      x5ctS π * ∏ q, if c q then 0 else f - noiseG f) / 2 := by
  classical
  have key : ∀ e : ErrorLabel n,
      (if (∀ q, amplitudeBit (e q) = c q) ∧ (∑ q, phaseBit (e q)) = π
        then ∏ q, x5ctW f (e q) else 0) =
      ((∏ q, (if amplitudeBit (e q) = c q then x5ctW f (e q) else 0)) +
        x5ctS π * ∏ q, (if amplitudeBit (e q) = c q then x5ctW f (e q) * x5ctS (phaseBit (e q))
          else 0)) / 2 := by
    intro e
    by_cases hA : ∀ q, amplitudeBit (e q) = c q
    · simp only [hA, implies_true, if_true, true_and]
      rw [Finset.prod_mul_distrib, ← x5ct_S_sum]
      have := x5ct_ind (∑ q, phaseBit (e q)) π
      by_cases hs : (∑ q, phaseBit (e q)) = π
      · rw [if_pos hs]; rw [if_pos hs] at this
        linear_combination (∏ q, x5ctW f (e q)) * this
      · rw [if_neg hs]; rw [if_neg hs] at this
        have : (1 + x5ctS π * x5ctS (∑ q, phaseBit (e q))) = 0 := by linarith
        linear_combination (-(∏ q, x5ctW f (e q)) / 2) * this
    · push Not at hA
      obtain ⟨q, hq⟩ := hA
      have h1 : ¬ ((∀ q, amplitudeBit (e q) = c q) ∧ (∑ q, phaseBit (e q)) = π) :=
        fun h => hq (h.1 q)
      rw [if_neg h1, Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq),
        Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)]
      ring
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun q x => if amplitudeBit x = c q then x5ctW f x else 0),
    ← Fintype.prod_sum (fun q x => if amplitudeBit x = c q then x5ctW f x * x5ctS (phaseBit x)
      else 0)]
  congr 2
  · refine Finset.prod_congr rfl (fun q _ => ?_)
    rw [x5ct_sumP]
    cases c q <;> simp [amplitudeBit, x5ctW] <;> ring
  · congr 1
    refine Finset.prod_congr rfl (fun q _ => ?_)
    rw [x5ct_sumP]
    cases c q <;> simp [amplitudeBit, phaseBit, x5ctW, x5ctS] <;> ring

end

end QAlgorithms.Papers.Independent.Support50.P40


namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

lemma x5ct_pob (a b : Bool) (j : Pauli) :
    pauliOfBits a b = j ↔ a = amplitudeBit j ∧ b = phaseBit j := by
  cases a <;> cases b <;> cases j <;> simp [pauliOfBits, amplitudeBit, phaseBit]

lemma x5ct_xor (x y b : Bool) : x + b = y ↔ x = y + b := by
  cases x <;> cases y <;> cases b <;> decide

lemma x5ct_cond {m : ℕ} (i : Qubits m) (j : Pauli) (e : ErrorLabel (m + 1)) :
    (catSyndrome e = i ∧ catLogical e = j) ↔
      (∀ q, amplitudeBit (e q) =
        (Fin.cons (amplitudeBit j) (fun q => i q + amplitudeBit j) : Fin (m + 1) → Bool) q) ∧
      (∑ q, phaseBit (e q)) = phaseBit j := by
  unfold catLogical catSyndrome
  rw [x5ct_pob, Fin.forall_fin_succ, funext_iff]
  simp only [Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h2, fun q => ?_⟩, h3⟩
    rw [← h2]; exact (x5ct_xor _ _ _).1 (h1 q)
  · rintro ⟨⟨h2, h1⟩, h3⟩
    refine ⟨fun q => ?_, h2, h3⟩
    rw [h2]; exact (x5ct_xor _ _ _).2 (h1 q)

lemma x5ct_hw_le {m : ℕ} (i : Qubits m) : hammingWeight i ≤ m := by
  unfold hammingWeight
  exact (Finset.card_le_univ _).trans (by simp)

lemma x5ct_prodB {m : ℕ} (i : Qubits m) (α β : ℝ) :
    ∏ q, (if i q then α else β) = α ^ hammingWeight i * β ^ (m - hammingWeight i) := by
  have := x5ct_prod_ite (fun q => i q = true) α β
  simpa [hammingWeight] using this

lemma x5ct_prodBn {m : ℕ} (i : Qubits m) (α β : ℝ) :
    ∏ q, (if i q + true then α else β) = β ^ hammingWeight i * α ^ (m - hammingWeight i) := by
  rw [← x5ct_prodB]
  refine Finset.prod_congr rfl (fun q _ => ?_)
  cases i q <;> rfl

lemma x5ct_prodBf {m : ℕ} (i : Qubits m) (α β : ℝ) :
    ∏ q, (if i q + false then α else β) = α ^ hammingWeight i * β ^ (m - hammingWeight i) := by
  rw [← x5ct_prodB]
  refine Finset.prod_congr rfl (fun q _ => ?_)
  cases i q <;> rfl

lemma x5ct_joint {m : ℕ} (f : ℝ) (i : Qubits m) (j : Pauli) :
    catJoint m f i j =
      ((if amplitudeBit j then 2 * noiseG f else f + noiseG f) *
          (∏ q, if i q + amplitudeBit j then 2 * noiseG f else f + noiseG f) +
        x5ctS (phaseBit j) * ((if amplitudeBit j then 0 else f - noiseG f) *
          ∏ q, if i q + amplitudeBit j then 0 else f - noiseG f)) / 2 := by
  classical
  unfold catJoint
  rw [x5ct_mass]
  simp_rw [x5ct_cond]
  rw [x5ct_core, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

lemma x5ct_joint' {m : ℕ} (f : ℝ) (i : Qubits m) (j : Pauli) (b π : Bool)
    (hb : amplitudeBit j = b) (hπ : phaseBit j = π) :
    catJoint m f i j =
      ((if b then 2 * noiseG f else f + noiseG f) *
          (∏ q, if i q + b then 2 * noiseG f else f + noiseG f) +
        x5ctS π * ((if b then 0 else f - noiseG f) *
          ∏ q, if i q + b then 0 else f - noiseG f)) / 2 := by
  subst hb hπ; exact x5ct_joint f i j

theorem x5ct_four (m : ℕ) (f : ℝ) (i : Qubits m) :
    catJoint m f i .X = (2 : ℝ) ^ (m + 1 - hammingWeight i - 1) * noiseG f ^ (m + 1 - hammingWeight i) *
      (f + noiseG f) ^ hammingWeight i ∧
    catJoint m f i .Y = (2 : ℝ) ^ (m + 1 - hammingWeight i - 1) * noiseG f ^ (m + 1 - hammingWeight i) *
      (f + noiseG f) ^ hammingWeight i ∧
    catJoint m f i .I = (if hammingWeight i = 0 then
        ((f + noiseG f) ^ (m + 1) + (f - noiseG f) ^ (m + 1)) / 2
      else (2 : ℝ) ^ (hammingWeight i - 1) * noiseG f ^ hammingWeight i *
        (f + noiseG f) ^ (m + 1 - hammingWeight i)) ∧
    catJoint m f i .Z = (if hammingWeight i = 0 then
        ((f + noiseG f) ^ (m + 1) - (f - noiseG f) ^ (m + 1)) / 2
      else (2 : ℝ) ^ (hammingWeight i - 1) * noiseG f ^ hammingWeight i *
        (f + noiseG f) ^ (m + 1 - hammingWeight i)) := by
  rw [x5ct_joint' f i .X true false rfl rfl, x5ct_joint' f i .Y true true rfl rfl,
    x5ct_joint' f i .I false false rfl rfl, x5ct_joint' f i .Z false true rfl rfl,
    x5ct_prodBn, x5ct_prodBn, x5ct_prodBf, x5ct_prodBf]
  have hr := x5ct_hw_le i
  generalize hammingWeight i = r at *
  set g := noiseG f
  simp only [x5ctS, if_true, Bool.false_eq_true, if_false]
  have e1 : m + 1 - r - 1 = m - r := by omega
  have e2 : m + 1 - r = m - r + 1 := by omega
  rw [e1, e2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_pow, pow_succ]; ring
  · rw [mul_pow, pow_succ]; ring
  · rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; simp; ring
    · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      rw [if_neg (by omega), zero_pow (by omega), mul_pow, pow_succ, pow_succ,
        show k + 1 - 1 = k by omega]
      ring
  · rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; simp; ring
    · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      rw [if_neg (by omega), zero_pow (by omega), mul_pow, pow_succ, pow_succ,
        show k + 1 - 1 = k by omega]
      ring

end

end QAlgorithms.Papers.Independent.Support50.P40


namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

lemma x5ct_card (m t : ℕ) :
    (Finset.univ.filter (fun s : Qubits m => hammingWeight s = t)).card = Nat.choose m t := by
  classical
  have : (Finset.univ.filter (fun s : Qubits m => hammingWeight s = t)).card =
      (Finset.powersetCard t (Finset.univ : Finset (Fin m))).card := by
    refine Finset.card_nbij' (fun s => Finset.univ.filter (fun q => s q = true))
      (fun S => fun q => decide (q ∈ S)) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hs
      simpa [Finset.mem_powersetCard, hammingWeight] using hs
    · intro S hS
      have hS' : S.card = t := by simpa [Finset.mem_powersetCard] using hS
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      show hammingWeight _ = t
      rw [← hS']; unfold hammingWeight; congr 1; ext q; simp
    · intro s _; funext q; simp
    · intro S _; ext q; simp
  rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma x5ct_byweight (m : ℕ) (F : ℕ → ℝ) :
    (∑ i : Qubits m, F (hammingWeight i)) =
      ∑ t ∈ Finset.range (m + 1), (Nat.choose m t : ℝ) * F t := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (m + 1))
    (g := hammingWeight) (fun i _ => Finset.mem_range.2 (Nat.lt_succ_of_le (x5ct_hw_le i)))]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => F t) (fun i hi => by
    rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const, x5ct_card, nsmul_eq_mul]

lemma x5ct_closed (m : ℕ) (f : ℝ) (i : Qubits m) (j : Pauli) :
    catJoint m f i j = catClosedMass m f (hammingWeight i) j := by
  obtain ⟨hX, hY, hI, hZ⟩ := x5ct_four m f i
  cases j
  · rw [hI]; rfl
  · rw [hX]; rfl
  · rw [hY]; rfl
  · rw [hZ]; rfl

theorem x5ct_yield (m : ℕ) (f : ℝ) :
    catYield m f =
      (1 + ∑ t ∈ Finset.range (m + 1), (Nat.choose m t : ℝ) *
        (let a := ∑ j : Pauli, catClosedMass m f t j;
         -a * Real.logb 2 a + ∑ j : Pauli,
           catClosedMass m f t j * Real.logb 2 (catClosedMass m f t j))) / (m + 1) := by
  unfold catYield finiteEntropyBits catSyndromeMass
  simp_rw [x5ct_closed]
  rw [Fintype.sum_prod_type]
  rw [← x5ct_byweight m (fun t => -(∑ j : Pauli, catClosedMass m f t j) *
      Real.logb 2 (∑ j : Pauli, catClosedMass m f t j) + ∑ j : Pauli,
        catClosedMass m f t j * Real.logb 2 (catClosedMass m f t j))]
  congr 1
  simp only [Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
  ring

end

end QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Papers.Independent.Support50.P40
open scoped ComplexConjugate Matrix

theorem solution (m : ℕ) (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (i : Qubits m) :
    let p := m + 1
    let r := hammingWeight i
    let g := noiseG f
    catJoint m f i .X = (2 : ℝ) ^ (p - r - 1) * g ^ (p - r) * (f + g) ^ r ∧
    catJoint m f i .Y = (2 : ℝ) ^ (p - r - 1) * g ^ (p - r) * (f + g) ^ r ∧
    catJoint m f i .I = (if r = 0 then ((f + g) ^ p + (f - g) ^ p) / 2
      else (2 : ℝ) ^ (r - 1) * g ^ r * (f + g) ^ (p - r)) ∧
    catJoint m f i .Z = (if r = 0 then ((f + g) ^ p - (f - g) ^ p) / 2
      else (2 : ℝ) ^ (r - 1) * g ^ r * (f + g) ^ (p - r)) ∧
    (∀ t : ℕ, t ≤ m →
      (Finset.univ.filter (fun s : Qubits m => hammingWeight s = t)).card = Nat.choose m t) ∧
    catYield m f =
      (1 + ∑ t ∈ Finset.range (m + 1), (Nat.choose m t : ℝ) *
        (let a := ∑ j : Pauli, catClosedMass m f t j;
         -a * Real.logb 2 a + ∑ j : Pauli,
           catClosedMass m f t j * Real.logb 2 (catClosedMass m f t j))) / (m + 1) := by
  intro p r g
  obtain ⟨hX, hY, hI, hZ⟩ := x5ct_four m f i
  exact ⟨hX, hY, hI, hZ, fun t _ => x5ct_card m t, x5ct_yield m f⟩

