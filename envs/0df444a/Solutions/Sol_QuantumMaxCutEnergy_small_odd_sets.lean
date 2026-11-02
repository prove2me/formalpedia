-- Prove2me | solution 1 for QuantumMaxCutEnergy.small_odd_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T14:40:04.673734+00:00
-- url     : https://prove2.me/submissions/d8ea173d-c678-4f17-b8b9-853b8579ef4c

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib.Tactic
import Mathlib.Data.NNRat.BigOperators

noncomputable section
open scoped BigOperators
namespace QuantumMaxCutEnergy

def totalWeight {n : ℕ} (w : Weights n) : ℝ := ∑ e, (w e : ℝ)

lemma normSq_sub_bound (z v : ℂ) :
    Complex.normSq (z - v) ≤ 2 * Complex.normSq z + 2 * Complex.normSq v := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (z.re + v.re), sq_nonneg (z.im + v.im)]

def swapBasis {n : ℕ} (a b : Fin n) : Basis n ≃ Basis n where
  toFun x := x ∘ Equiv.swap a b
  invFun x := x ∘ Equiv.swap a b
  left_inv x := by funext i; simp [Function.comp_def]
  right_inv x := by funext i; simp [Function.comp_def]

lemma squaredNorm_swap_sum {n : ℕ} (ψ : Wave n) (a b : Fin n) :
    (∑ x, Complex.normSq (ψ (x ∘ Equiv.swap a b))) = squaredNorm ψ := by
  exact (swapBasis a b).sum_comp (fun x => Complex.normSq (ψ x))

lemma energy_nonnegative {n : ℕ} (w : Weights n)
    (ψ : Wave n) : 0 ≤ energy w ψ := by
  apply Finset.sum_nonneg
  intro e _
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun x _ => Complex.normSq_nonneg _)

lemma energy_upper_bound {n : ℕ} (w : Weights n)
    (ψ : Wave n) :
    energy w ψ ≤ 2 * totalWeight w * squaredNorm ψ := by
  have edge_bound (a b : Fin n) :
      (∑ x, Complex.normSq (ψ x - ψ (x ∘ Equiv.swap a b))) ≤ 4 * squaredNorm ψ := by
    calc
      _ ≤ ∑ x, (2 * Complex.normSq (ψ x) +
            2 * Complex.normSq (ψ (x ∘ Equiv.swap a b))) :=
        Finset.sum_le_sum (fun x _ => normSq_sub_bound _ _)
      _ = 4 * squaredNorm ψ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          squaredNorm_swap_sum]
        unfold squaredNorm
        ring
  calc
    energy w ψ ≤ ∑ e, (w e : ℝ) / 2 * (4 * squaredNorm ψ) := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (edge_bound _ _) (by positivity)
    _ = ∑ e, (w e : ℝ) * (2 * squaredNorm ψ) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = 2 * totalWeight w * squaredNorm ψ := by
      rw [← Finset.sum_mul]
      unfold totalWeight
      ring

end QuantumMaxCutEnergy

namespace QuantumMaxCutEnergy.BaselineSemantic

def ket {n : ℕ} (b : Basis n) : Wave n := fun x => if x = b then 1 else 0

def cutWeight {n : ℕ} (w : Weights n) (b : Basis n) : ℝ :=
  ∑ e, if b e.val.1 = b e.val.2 then 0 else (w e : ℝ)

lemma squaredNorm_ket {n : ℕ} (b : Basis n) : squaredNorm (ket b) = 1 := by
  classical
  simp [squaredNorm, ket]

lemma sum_delta_difference {α : Type} [Fintype α] [DecidableEq α] (a b : α) :
    (∑ x, Complex.normSq
      ((if x = a then (1 : ℂ) else 0) - (if x = b then (1 : ℂ) else 0))) =
      if a = b then 0 else 2 := by
  classical
  by_cases h : a = b
  · subst b
    simp
  · have hp : ∀ x, Complex.normSq
        ((if x = a then (1 : ℂ) else 0) - (if x = b then (1 : ℂ) else 0)) =
        (if x = a then (1 : ℝ) else 0) + (if x = b then (1 : ℝ) else 0) := by
      intro x
      by_cases ha : x = a
      · subst x
        simp [h]
      · by_cases hb : x = b
        · subst x
          simp [Ne.symm h]
        · simp [ha, hb]
    simp_rw [hp]
    rw [Finset.sum_add_distrib]
    norm_num [h]

lemma ket_swap {n : ℕ} (b x : Basis n) (i j : Fin n) :
    ket b (x ∘ Equiv.swap i j) = ket (b ∘ Equiv.swap i j) x := by
  classical
  have h : (x ∘ Equiv.swap i j = b) ↔ (x = b ∘ Equiv.swap i j) := by
    constructor <;> intro h
    · have hh := congrArg (fun f => f ∘ Equiv.swap i j) h
      simpa only [Function.comp_def, Equiv.swap_apply_self] using hh
    · subst x
      funext k
      simp [Function.comp_def]
  simp only [ket, h]

lemma eq_swap_iff {n : ℕ} (b : Basis n) (i j : Fin n) :
    (b = b ∘ Equiv.swap i j) ↔ b i = b j := by
  constructor
  · intro h
    simpa using congrFun h i
  · intro h
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [Equiv.swap_apply_def]

lemma pairEnergy_ket {n : ℕ} (b : Basis n) (i j : Fin n) :
    (∑ x, Complex.normSq (ket b x - ket b (x ∘ Equiv.swap i j))) =
      if b i = b j then 0 else 2 := by
  simp_rw [ket_swap]
  change (∑ x, Complex.normSq
    ((if x = b then (1 : ℂ) else 0) -
      (if x = b ∘ Equiv.swap i j then (1 : ℂ) else 0))) = _
  rw [sum_delta_difference]
  simp only [eq_swap_iff]

lemma energy_ket {n : ℕ} (w : Weights n) (b : Basis n) :
    energy w (ket b) = cutWeight w b := by
  classical
  unfold energy cutWeight
  apply Finset.sum_congr rfl
  intro e _
  change (w e : ℝ) / 2 *
    (∑ x, Complex.normSq (ket b x - ket b (x ∘ Equiv.swap e.val.1 e.val.2))) = _
  rw [pairEnergy_ket]
  split_ifs <;> ring

def flipBit {n : ℕ} (i : Fin n) (b : Basis n) : Basis n :=
  Function.update b i (!(b i))

lemma flipBit_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flipBit i) := by
  intro b
  funext k
  by_cases hk : k = i
  · subst k
    simp [flipBit]
  · simp [flipBit, hk]

lemma uniform_cut_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (∑ b : Basis n, if b i = b j then (0 : ℝ) else 1) =
      (Fintype.card (Basis n) : ℝ) / 2 := by
  classical
  let f : Basis n → ℝ := fun b => if b i = b j then 0 else 1
  have hflip (b : Basis n) : f (flipBit i b) = 1 - f b := by
    simp only [f, flipBit, Function.update_self,
      Function.update_of_ne (Ne.symm hij)]
    cases hi : b i <;> cases hj : b j <;> norm_num
  have hs : (∑ b, f b) = ∑ b : Basis n, (1 - f b) := by
    calc
      (∑ b, f b) = ∑ b, f (flipBit i b) :=
        ((flipBit_involutive i).bijective.sum_comp f).symm
      _ = _ := by simp_rw [hflip]
  rw [Finset.sum_sub_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  change (∑ b, f b) = _
  linarith

lemma uniform_cut_sum {n : ℕ} (w : Weights n) :
    (∑ b : Basis n, cutWeight w b) =
      (Fintype.card (Basis n) : ℝ) / 2 * ∑ e, (w e : ℝ) := by
  classical
  unfold cutWeight
  rw [Finset.sum_comm]
  calc
    (∑ e, ∑ b : Basis n, if b e.val.1 = b e.val.2 then 0 else (w e : ℝ)) =
        ∑ e, (w e : ℝ) * ((Fintype.card (Basis n) : ℝ) / 2) := by
      apply Finset.sum_congr rfl
      intro e _
      have h := uniform_cut_pair e.val.1 e.val.2 (ne_of_lt e.property)
      rw [← h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> ring
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma uniform_basis_energy_sum {n : ℕ} (w : Weights n) :
    (∑ b : Basis n, energy w (ket b)) =
      (Fintype.card (Basis n) : ℝ) / 2 * ∑ e, (w e : ℝ) := by
  simp_rw [energy_ket]
  exact uniform_cut_sum w

def uniformBasisEnergy {n : ℕ} (w : Weights n) : ℝ :=
  (∑ b : Basis n, energy w (ket b)) /
    (Fintype.card (Basis n) : ℝ)

lemma uniformBasisEnergy_eq {n : ℕ} (w : Weights n) :
    uniformBasisEnergy w = (∑ e, (w e : ℝ)) / 2 := by
  have hcard : (Fintype.card (Basis n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformBasisEnergy
  rw [uniform_basis_energy_sum]
  field_simp

lemma uniformBasis_quarter_of_upper {n : ℕ} (w : Weights n) (ψ : Wave n)
    (hψ : squaredNorm ψ = 1)
    (hupper : energy w ψ ≤
      2 * (∑ e, (w e : ℝ)) * squaredNorm ψ) :
    (1 / 4 : ℝ) * energy w ψ ≤
      uniformBasisEnergy w := by
  rw [uniformBasisEnergy_eq]
  rw [hψ] at hupper
  linarith

end QuantumMaxCutEnergy.BaselineSemantic

namespace QuantumMaxCutEnergy

open BaselineSemantic

lemma energy_values_nonempty (G : Input) :
    {v : ℝ | ∃ ψ : Wave G.n, squaredNorm ψ = 1 ∧ v = energy G.weights ψ}.Nonempty := by
  refine ⟨_, _, squaredNorm_ket (fun _ => false), rfl⟩

lemma energy_values_bddAbove (G : Input) :
    BddAbove {v : ℝ | ∃ ψ : Wave G.n, squaredNorm ψ = 1 ∧ v = energy G.weights ψ} := by
  refine ⟨2 * totalWeight G.weights, ?_⟩
  rintro v ⟨ψ, hψ, rfl⟩
  simpa [hψ] using energy_upper_bound G.weights ψ

lemma energy_le_optimum (G : Input) (ψ : Wave G.n) (hψ : squaredNorm ψ = 1) :
    energy G.weights ψ ≤ optimum G := by
  exact le_csSup (energy_values_bddAbove G) ⟨ψ, hψ, rfl⟩

lemma optimum_le_two_totalWeight (G : Input) :
    optimum G ≤ 2 * totalWeight G.weights := by
  apply csSup_le (energy_values_nonempty G)
  rintro v ⟨ψ, hψ, rfl⟩
  simpa [hψ] using energy_upper_bound G.weights ψ

lemma half_totalWeight_le_optimum (G : Input) :
    totalWeight G.weights / 2 ≤ optimum G := by
  have hcard : (0 : ℝ) < (Fintype.card (Basis G.n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have havg : uniformBasisEnergy G.weights ≤ optimum G := by
    unfold uniformBasisEnergy
    apply (div_le_iff₀ hcard).2
    calc
      (∑ b : Basis G.n, energy G.weights (ket b)) ≤
          ∑ _b : Basis G.n, optimum G := by
        exact Finset.sum_le_sum (fun b _ => energy_le_optimum G (ket b) (squaredNorm_ket b))
      _ = optimum G * (Fintype.card (Basis G.n) : ℝ) := by
        simp [mul_comm]
  simpa [uniformBasisEnergy_eq, totalWeight] using havg

lemma quarter_optimum_le_half_totalWeight (G : Input) :
    (0.25 : ℝ) * optimum G ≤ totalWeight G.weights / 2 := by
  have h := optimum_le_two_totalWeight G
  linarith

def quarterValue (G : Input) : ℚ≥0 := (∑ e, G.weights e) / 2

lemma quarterValue_cast (G : Input) :
    (quarterValue G : ℝ) = totalWeight G.weights / 2 := by
  simp [quarterValue, totalWeight, NNRat.cast_sum]

def quarterEstimator : Algorithm where
  randomFactor := 0
  randomDegree := 0
  run G _ := quarterValue G

theorem quarterEstimator_ratio : ApproximationRatio quarterEstimator (0.25 : ℝ) := by
  intro G
  constructor
  · intro r
    simpa [quarterEstimator, quarterValue_cast] using half_totalWeight_le_optimum G
  · have hcard : (Fintype.card (Fin (randomBits quarterEstimator G) → Bool) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    change (0.25 : ℝ) * optimum G ≤
      (∑ _r : Fin (randomBits quarterEstimator G) → Bool, (quarterValue G : ℝ)) /
        (Fintype.card (Fin (randomBits quarterEstimator G) → Bool) : ℝ)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_div_cancel_left₀ _ hcard]
    simpa only [quarterValue_cast] using quarter_optimum_le_half_totalWeight G

#print axioms half_totalWeight_le_optimum
#print axioms quarterEstimator_ratio

end QuantumMaxCutEnergy


noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.LP24

def internalEdges {n : ℕ} (S : Finset (Fin n)) : Finset (Edge n) :=
  Finset.univ.filter (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)

def vertexLoad {n : ℕ} (x : Edge n → ℝ) (v : Fin n) : ℝ :=
  ∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0

def IsFractionalMatching {n : ℕ} (x : Edge n → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧ (∀ v, vertexLoad x v ≤ 1) ∧
    ∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ internalEdges S, x e) ≤ ((S.card : ℝ) - 1) / 2

lemma incident_subset_sum {n : ℕ} (x : Edge n → ℝ) (S : Finset (Fin n)) :
    (∑ v ∈ S, vertexLoad x v) = ∑ e : Edge n,
      ((if e.val.1 ∈ S then x e else 0) +
       (if e.val.2 ∈ S then x e else 0)) := by
  classical
  unfold vertexLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hsplit (v : Fin n) :
      (if v = e.val.1 ∨ v = e.val.2 then x e else 0) =
      (if v = e.val.1 then x e else 0) +
      (if v = e.val.2 then x e else 0) := by
    have hne := ne_of_lt e.property
    by_cases h1 : v = e.val.1 <;> by_cases h2 : v = e.val.2
    · exact False.elim (hne (h1.symm.trans h2))
    · simp [h1, hne]
    · simp [h2, hne.symm]
    · simp [h1, h2]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp

lemma internal_mass_le_half_card {n : ℕ} (x : Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hload : ∀ v, vertexLoad x v ≤ 1)
    (S : Finset (Fin n)) :
    (∑ e ∈ internalEdges S, x e) ≤ (S.card : ℝ) / 2 := by
  classical
  have hdouble : 2 * (∑ e ∈ internalEdges S, x e) ≤
      ∑ v ∈ S, vertexLoad x v := by
    rw [incident_subset_sum]
    simp only [internalEdges, Finset.sum_filter]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    by_cases h1 : e.val.1 ∈ S <;> by_cases h2 : e.val.2 ∈ S <;>
      simp [h1, h2] <;> linarith [hx e]
  have hsum : (∑ v ∈ S, vertexLoad x v) ≤ (S.card : ℝ) := by
    calc
      _ ≤ ∑ _v ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun v hv => hload v)
      _ = _ := by simp
  linarith

lemma internalEdges_singleton {n : ℕ} (v : Fin n) :
    internalEdges {v} = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp he).2
  have hne := ne_of_lt e.property
  simp only [Finset.mem_singleton] at h1 h2
  exact hne (h1.trans h2.symm)

/-- LP24 Lemma 9: the vertex capacities and size-three odd-set
constraints suffice after scaling by exactly four fifths. -/
theorem four_fifths_fractional_matching {n : ℕ} (x : Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hload : ∀ v, vertexLoad x v ≤ 1)
    (htriangle : ∀ S : Finset (Fin n), S.card = 3 →
      (∑ e ∈ internalEdges S, x e) ≤ 1) :
    IsFractionalMatching (fun e => (4 / 5 : ℝ) * x e) := by
  classical
  refine ⟨fun e => mul_nonneg (by norm_num) (hx e), ?_, ?_⟩
  · intro v
    have heq : vertexLoad (fun e => (4 / 5 : ℝ) * x e) v =
        (4 / 5 : ℝ) * vertexLoad x v := by
      unfold vertexLoad
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> ring
    rw [heq]
    linarith [hload v]
  · intro S hodd
    rw [← Finset.mul_sum]
    obtain ⟨k, hk⟩ := hodd
    by_cases hs1 : S.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hs1
      simp [internalEdges_singleton]
    by_cases hs3 : S.card = 3
    · have ht := htriangle S hs3
      rw [hs3]
      norm_num
      linarith
    · have hs5 : 5 ≤ S.card := by omega
      have hcard : (5 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hs5
      have hb := internal_mass_le_half_card x hx hload S
      linarith


end QuantumMaxCutEnergy.LP24

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.LP24

/-- General small-odd-set scaling lemma. For an even cutoff q, only
odd sets through q-1 are relevant. Thus q=4,6,14 gives 4/5,6/7,14/15. -/
theorem scaled_of_small_odd_sets {n : ℕ} (q : ℕ) (x : Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hload : ∀ v, vertexLoad x v ≤ 1)
    (hsmall : ∀ S : Finset (Fin n), Odd S.card → S.card ≤ q →
      (∑ e ∈ internalEdges S, x e) ≤ ((S.card : ℝ) - 1) / 2) :
    IsFractionalMatching (fun e => ((q : ℝ) / (q + 1)) * x e) := by
  classical
  have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hβ0 : (0 : ℝ) ≤ (q : ℝ) / (q + 1) := by positivity
  have hβ1 : (q : ℝ) / (q + 1) ≤ 1 := by
    apply (div_le_one hq).mpr
    linarith
  refine ⟨fun e => mul_nonneg hβ0 (hx e), ?_, ?_⟩
  · intro v
    have heq : vertexLoad (fun e => ((q : ℝ) / (q + 1)) * x e) v =
        ((q : ℝ) / (q + 1)) * vertexLoad x v := by
      unfold vertexLoad
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> ring
    rw [heq]
    exact (mul_le_mul_of_nonneg_left (hload v) hβ0).trans (by simpa using hβ1)
  · intro S hodd
    rw [← Finset.mul_sum]
    by_cases hs : S.card ≤ q
    · have hmass : 0 ≤ ∑ e ∈ internalEdges S, x e :=
        Finset.sum_nonneg (fun e he => hx e)
      exact (mul_le_mul_of_nonneg_right hβ1 hmass).trans (by
        simpa using hsmall S hodd hs)
    · have hslarge : q + 1 ≤ S.card := by omega
      have hcast : (q : ℝ) + 1 ≤ (S.card : ℝ) := by exact_mod_cast hslarge
      have hscale : ((q : ℝ) / (q + 1)) * (S.card : ℝ) ≤ (S.card : ℝ) - 1 := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hq).mpr
        nlinarith
      have hmass := mul_le_mul_of_nonneg_left
        (internal_mass_le_half_card x hx hload S) hβ0
      nlinarith

/-- Selecting precisely the positive-excess edges turns unweighted
subgraph energy bounds into the odd-set inequalities. This is the
finite transformation in GSS Lemma3.5, also used with the BBKL bound. -/
theorem positive_excess_odd_set {n : ℕ} (g : Edge n → ℝ)
    (S : Finset (Fin n))
    (hsubgraph : ∀ F : Finset (Edge n), F ⊆ internalEdges S →
      (∑ e ∈ F, g e) ≤ (F.card : ℝ) + ((S.card : ℝ) - 1) / 2) :
    (∑ e ∈ internalEdges S, max (g e - 1) 0) ≤ ((S.card : ℝ) - 1) / 2 := by
  classical
  let F := (internalEdges S).filter (fun e => 0 < g e - 1)
  have hsum : (∑ e ∈ internalEdges S, max (g e - 1) 0) =
      ∑ e ∈ F, (g e - 1) := by
    unfold F
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hp : 0 < g e - 1
    · simp [hp, max_eq_left hp.le]
    · simp [hp, max_eq_right (not_lt.mp hp)]
  have hb := hsubgraph F (Finset.filter_subset _ _)
  rw [hsum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

/-- All-size unweighted subgraph bounds yield strength one, provided
the star/vertex constraints are available. The BBKL spectral theorem
is a separate, substantial proof obligation that can feed this lemma. -/
theorem positive_excess_fractional_matching {n : ℕ} (g : Edge n → ℝ)
    (hload : ∀ v, vertexLoad (fun e => max (g e - 1) 0) v ≤ 1)
    (hsubgraph : ∀ S : Finset (Fin n), Odd S.card →
      ∀ F : Finset (Edge n), F ⊆ internalEdges S →
        (∑ e ∈ F, g e) ≤ (F.card : ℝ) + ((S.card : ℝ) - 1) / 2) :
    IsFractionalMatching (fun e => max (g e - 1) 0) := by
  refine ⟨fun e => le_max_right _ _, hload, ?_⟩
  intro S hodd
  exact positive_excess_odd_set g S (hsubgraph S hodd)

/-- The finite-size version directly connects GSS's unweighted
certificates to its parameterized matching-strength conclusion. -/
theorem positive_excess_scaled_matching {n : ℕ} (q : ℕ) (g : Edge n → ℝ)
    (hload : ∀ v, vertexLoad (fun e => max (g e - 1) 0) v ≤ 1)
    (hsubgraph : ∀ S : Finset (Fin n), Odd S.card → S.card ≤ q →
      ∀ F : Finset (Edge n), F ⊆ internalEdges S →
        (∑ e ∈ F, g e) ≤ (F.card : ℝ) + ((S.card : ℝ) - 1) / 2) :
    IsFractionalMatching (fun e =>
      ((q : ℝ) / (q + 1)) * max (g e - 1) 0) := by
  apply scaled_of_small_odd_sets q _ (fun e => le_max_right _ _) hload
  intro S hodd hs
  exact positive_excess_odd_set g S (hsubgraph S hodd hs)


end QuantumMaxCutEnergy.LP24

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.LP24

/-- If U is a valid relaxation value and γU is below the true optimum,
scale a lower numerical approximation to U by γ. Additive error εW is
absorbed using W ≤ 2OPT. All constants and output products are exact. -/
theorem scaled_relaxation_value_bounds (G : Input) (U : ℝ)
    (L γ : ℚ≥0) (α ε : ℝ)
    (hε : 0 ≤ ε)
    (hupper : optimum G ≤ U)
    (hgap : (γ : ℝ) * U ≤ optimum G)
    (hbelow : (L : ℝ) ≤ U)
    (hprecision : U - ε * totalWeight G.weights ≤ (L : ℝ))
    (hmargin : α ≤ (γ : ℝ) * (1 - 2 * ε)) :
    ((γ * L : ℚ≥0) : ℝ) ≤ optimum G ∧
      α * optimum G ≤ ((γ * L : ℚ≥0) : ℝ) := by
  have hhalf := half_totalWeight_le_optimum G
  have hweight : 0 ≤ totalWeight G.weights := by
    unfold totalWeight
    positivity
  have hopt : 0 ≤ optimum G := (by linarith : 0 ≤ totalWeight G.weights / 2).trans hhalf
  have hγ : (0 : ℝ) ≤ (γ : ℝ) := by positivity
  have hεW : ε * totalWeight G.weights ≤ 2 * ε * optimum G := by
    nlinarith
  have hlow : (1 - 2 * ε) * optimum G ≤ (L : ℝ) := by linarith
  have hs := mul_le_mul_of_nonneg_left hbelow hγ
  have hl := mul_le_mul_of_nonneg_left hlow hγ
  have hm := mul_le_mul_of_nonneg_right hmargin hopt
  simp only [NNRat.cast_mul]
  constructor
  · exact hs.trans hgap
  · nlinarith

def scaledRelaxationEstimator (γ : ℚ≥0) (L : Input → ℚ≥0) : Algorithm where
  randomFactor := 0
  randomDegree := 0
  run G _ := γ * L G

/-- The scaled solver is a genuine deterministic estimator in the
campaign model. This theorem does not assume an approximation algorithm;
its hypotheses are relaxation soundness, integrality gap, and numerical
value accuracy, all stated independently of the target predicate. -/
theorem scaledRelaxationEstimator_ratio (γ : ℚ≥0) (L : Input → ℚ≥0)
    (U : Input → ℝ) (α ε : ℝ) (hε : 0 ≤ ε)
    (hupper : ∀ G, optimum G ≤ U G)
    (hgap : ∀ G, (γ : ℝ) * U G ≤ optimum G)
    (hbelow : ∀ G, (L G : ℝ) ≤ U G)
    (hprecision : ∀ G, U G - ε * totalWeight G.weights ≤ (L G : ℝ))
    (hmargin : α ≤ (γ : ℝ) * (1 - 2 * ε)) :
    ApproximationRatio (scaledRelaxationEstimator γ L) α := by
  intro G
  have hb := scaled_relaxation_value_bounds G (U G) (L G) γ α ε hε
    (hupper G) (hgap G) (hbelow G) (hprecision G) hmargin
  constructor
  · intro r
    exact hb.1
  · have hc : (Fintype.card (Fin (randomBits (scaledRelaxationEstimator γ L) G) → Bool) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    change α * optimum G ≤
      (∑ _r : Fin (randomBits (scaledRelaxationEstimator γ L) G) → Bool,
        ((γ * L G : ℚ≥0) : ℝ)) /
        (Fintype.card (Fin (randomBits (scaledRelaxationEstimator γ L) G) → Bool) : ℝ)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_div_cancel_left₀ _ hc]
    exact hb.2

#print axioms scaled_relaxation_value_bounds
#print axioms scaledRelaxationEstimator_ratio

end QuantumMaxCutEnergy.LP24


open scoped BigOperators

-- Rename the chosen publication declaration to `solution` when submitting.
theorem publication_scaled_bounds
    (G : QuantumMaxCutEnergy.Input) (U : ℝ) (L γ : ℚ≥0) (α ε : ℝ)
    (hε : 0 ≤ ε)
    (hupper : QuantumMaxCutEnergy.optimum G ≤ U)
    (hgap : (γ : ℝ) * U ≤ QuantumMaxCutEnergy.optimum G)
    (hbelow : (L : ℝ) ≤ U)
    (hprecision : U - ε * (∑ e, (G.weights e : ℝ)) ≤ (L : ℝ))
    (hmargin : α ≤ (γ : ℝ) * (1 - 2 * ε)) :
    ((γ * L : ℚ≥0) : ℝ) ≤ QuantumMaxCutEnergy.optimum G ∧
      α * QuantumMaxCutEnergy.optimum G ≤ ((γ * L : ℚ≥0) : ℝ) := by
  exact QuantumMaxCutEnergy.LP24.scaled_relaxation_value_bounds
    G U L γ α ε hε hupper hgap hbelow hprecision hmargin

theorem publication_scaled_ratio
    (γ : ℚ≥0) (L : QuantumMaxCutEnergy.Input → ℚ≥0)
    (U : QuantumMaxCutEnergy.Input → ℝ) (α ε : ℝ) (hε : 0 ≤ ε)
    (hupper : ∀ G, QuantumMaxCutEnergy.optimum G ≤ U G)
    (hgap : ∀ G, (γ : ℝ) * U G ≤ QuantumMaxCutEnergy.optimum G)
    (hbelow : ∀ G, (L G : ℝ) ≤ U G)
    (hprecision : ∀ G, U G - ε * (∑ e, (G.weights e : ℝ)) ≤ (L G : ℝ))
    (hmargin : α ≤ (γ : ℝ) * (1 - 2 * ε)) :
    QuantumMaxCutEnergy.ApproximationRatio
      ({ randomFactor := 0, randomDegree := 0, run := fun G _ => γ * L G } :
        QuantumMaxCutEnergy.Algorithm) α := by
  exact QuantumMaxCutEnergy.LP24.scaledRelaxationEstimator_ratio
    γ L U α ε hε hupper hgap hbelow hprecision hmargin

theorem solution
    {n : ℕ} (q : ℕ) (x : QuantumMaxCutEnergy.Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v : Fin n,
      (∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0) ≤ 1)
    (hsmall : ∀ S : Finset (Fin n), Odd S.card → S.card ≤ q →
      (∑ e ∈ (Finset.univ.filter (fun e : QuantumMaxCutEnergy.Edge n =>
        e.val.1 ∈ S ∧ e.val.2 ∈ S)), x e) ≤ ((S.card : ℝ) - 1) / 2) :
    (∀ e, 0 ≤ ((q : ℝ) / (q + 1)) * x e) ∧
    (∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then
      ((q : ℝ) / (q + 1)) * x e else 0) ≤ 1) ∧
    (∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ (Finset.univ.filter (fun e : QuantumMaxCutEnergy.Edge n =>
        e.val.1 ∈ S ∧ e.val.2 ∈ S)), ((q : ℝ) / (q + 1)) * x e) ≤
        ((S.card : ℝ) - 1) / 2) := by
  exact QuantumMaxCutEnergy.LP24.scaled_of_small_odd_sets q x hx hload hsmall

theorem publication_positive_excess
    {n : ℕ} (g : QuantumMaxCutEnergy.Edge n → ℝ) (S : Finset (Fin n))
    (hsubgraph : ∀ F : Finset (QuantumMaxCutEnergy.Edge n),
      F ⊆ Finset.univ.filter (fun e : QuantumMaxCutEnergy.Edge n =>
        e.val.1 ∈ S ∧ e.val.2 ∈ S) →
      (∑ e ∈ F, g e) ≤ (F.card : ℝ) + ((S.card : ℝ) - 1) / 2) :
    (∑ e ∈ (Finset.univ.filter (fun e : QuantumMaxCutEnergy.Edge n =>
      e.val.1 ∈ S ∧ e.val.2 ∈ S)), max (g e - 1) 0) ≤
      ((S.card : ℝ) - 1) / 2 := by
  exact QuantumMaxCutEnergy.LP24.positive_excess_odd_set g S hsubgraph

#print axioms publication_scaled_bounds
#print axioms publication_scaled_ratio
#print axioms solution
#print axioms publication_positive_excess
