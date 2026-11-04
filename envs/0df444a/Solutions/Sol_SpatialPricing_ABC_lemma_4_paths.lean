-- Prove2me | solution 1 for SpatialPricing.ABC.lemma_4_paths
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T12:15:06.392018+00:00
-- url     : https://prove2.me/submissions/e259370f-796e-4a65-9e55-5634eb3dac84

import Mathlib
import Definitions.Def_SpatialPricing_ABC_Setting
import Definitions.Def_SpatialPricing_ABC_Control

noncomputable section

namespace L4P

open SpatialPricing.ABC Finset

/-! ## Batch combinatorics -/

section Batch

variable (Q : Instance) (ζ b : ℝ) (i j : Fin Q.N)

lemma bE_zero : Q.batchEnd ζ b i j 0 = 0 := rfl

lemma bE_succ_le (k : ℕ) : Q.batchEnd ζ b i j (k + 1) ≤ Q.T := by
  classical
  rw [Instance.batchEnd]
  dsimp only
  split_ifs with h h2
  · exact le_rfl
  · exact (Nat.find_spec h).2.1
  · exact le_rfl

lemma bE_le (k : ℕ) : Q.batchEnd ζ b i j k ≤ Q.T := by
  cases k with
  | zero => simp [bE_zero]
  | succ k => exact bE_succ_le Q ζ b i j k

lemma bE_succ_unfold (k : ℕ) (p : ℕ) (hp : Q.batchEnd ζ b i j k = p) :
    p < Q.T → p < Q.batchEnd ζ b i j (k + 1) := by
  classical
  have key : Q.batchEnd ζ b i j (k + 1) = Q.batchEnd ζ b i j (k + 1) := rfl
  conv at key => rhs; rw [Instance.batchEnd]
  dsimp only at key
  rw [hp] at key
  rw [key]
  intro hpT
  split_ifs with h h2
  · exact hpT
  · exact (Nat.find_spec h).1
  · exact hpT

lemma bE_lt_succ (k : ℕ) (hk : Q.batchEnd ζ b i j k < Q.T) :
    Q.batchEnd ζ b i j k < Q.batchEnd ζ b i j (k + 1) :=
  bE_succ_unfold Q ζ b i j k _ rfl hk

lemma bE_eq_of_eq (k : ℕ) (hk : Q.batchEnd ζ b i j k = Q.T) :
    Q.batchEnd ζ b i j (k + 1) = Q.T := by
  classical
  have key : Q.batchEnd ζ b i j (k + 1) = Q.batchEnd ζ b i j (k + 1) := rfl
  conv at key => rhs; rw [Instance.batchEnd]
  dsimp only at key
  rw [hk] at key
  rw [key]
  split_ifs with h h2
  · rfl
  · exfalso
    obtain ⟨h1, h2', _⟩ := Nat.find_spec h
    omega
  · rfl

lemma bE_le_succ (k : ℕ) : Q.batchEnd ζ b i j k ≤ Q.batchEnd ζ b i j (k + 1) := by
  rcases lt_or_eq_of_le (bE_le Q ζ b i j k) with h | h
  · exact (bE_lt_succ Q ζ b i j k h).le
  · rw [bE_eq_of_eq Q ζ b i j k h, h]

lemma bE_mono : Monotone (Q.batchEnd ζ b i j) :=
  monotone_nat_of_le_succ (bE_le_succ Q ζ b i j)

lemma bE_ge_min (k : ℕ) : min k Q.T ≤ Q.batchEnd ζ b i j k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases lt_or_eq_of_le (bE_le Q ζ b i j k) with h | h
    · have := bE_lt_succ Q ζ b i j k h
      omega
    · rw [bE_eq_of_eq Q ζ b i j k h]
      omega

lemma bE_T : Q.batchEnd ζ b i j Q.T = Q.T :=
  le_antisymm (bE_le Q ζ b i j _) (by simpa using bE_ge_min Q ζ b i j Q.T)

/-- Characterisation of `kappa`. -/
lemma kappa_eq (t k : ℕ) (hk : 1 ≤ k) (ht : t ≤ Q.T)
    (h1 : Q.batchEnd ζ b i j (k - 1) < t) (h2 : t ≤ Q.batchEnd ζ b i j k) :
    Q.kappa ζ b t i j = k := by
  classical
  have hkT : k - 1 < Q.T := by
    by_contra hc
    push Not at hc
    have := bE_mono Q ζ b i j hc
    rw [bE_T] at this
    omega
  have hfil : (Finset.Icc 1 Q.T).filter (fun k' => Q.batchEnd ζ b i j k' < t)
      = Finset.Icc 1 (k - 1) := by
    ext k'
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1', _⟩, h3⟩
      refine ⟨h1', ?_⟩
      by_contra hc
      push Not at hc
      have := bE_mono Q ζ b i j (show k ≤ k' by omega)
      omega
    · rintro ⟨h1', h2'⟩
      refine ⟨⟨h1', by omega⟩, ?_⟩
      exact lt_of_le_of_lt (bE_mono Q ζ b i j h2') h1
  unfold Instance.kappa
  rw [hfil]
  simp
  omega

lemma kappa_spec (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ Q.T) :
    1 ≤ Q.kappa ζ b t i j ∧ Q.kappa ζ b t i j ≤ Q.T ∧
    Q.batchEnd ζ b i j (Q.kappa ζ b t i j - 1) < t ∧
    t ≤ Q.batchEnd ζ b i j (Q.kappa ζ b t i j) := by
  classical
  have hex : ∃ k, t ≤ Q.batchEnd ζ b i j k := ⟨Q.T, by rw [bE_T]; exact ht⟩
  set k := Nat.find hex with hkdef
  have hk1 : 1 ≤ k := by
    by_contra hc
    push Not at hc
    have h0 : k = 0 := by omega
    have := Nat.find_spec hex
    rw [← hkdef, h0, bE_zero] at this
    omega
  have hkle : k ≤ Q.T := Nat.find_min' hex (by rw [bE_T]; exact ht)
  have h1 : Q.batchEnd ζ b i j (k - 1) < t := by
    have := Nat.find_min hex (show k - 1 < k by omega)
    omega
  have h2 : t ≤ Q.batchEnd ζ b i j k := Nat.find_spec hex
  rw [kappa_eq Q ζ b i j t k hk1 ht h1 h2]
  exact ⟨hk1, hkle, h1, h2⟩

lemma batch_zero : Q.batch ζ b i j 0 = ∅ := by
  simp [Instance.batch, bE_zero]

lemma mem_batch (k s : ℕ) :
    s ∈ Q.batch ζ b i j k ↔
      Q.batchEnd ζ b i j (k - 1) < s ∧ s ≤ Q.batchEnd ζ b i j k := by
  simp only [Instance.batch, Finset.mem_Icc]
  omega

lemma bE_succ_cases (k : ℕ) :
    Q.batchEnd ζ b i j (k + 1) = Q.T ∨
      (b ≤ ∑ v ∈ Finset.Icc (Q.batchEnd ζ b i j k + 1) (Q.batchEnd ζ b i j (k + 1)),
          Q.weight ζ v i j ∧
        b ≤ ∑ v ∈ Finset.Icc (Q.batchEnd ζ b i j (k + 1) + 1) Q.T, Q.weight ζ v i j) := by
  classical
  generalize hp : Q.batchEnd ζ b i j k = p
  have key : Q.batchEnd ζ b i j (k + 1) = Q.batchEnd ζ b i j (k + 1) := rfl
  conv at key => rhs; rw [Instance.batchEnd]
  dsimp only at key
  rw [hp] at key
  rw [key]
  split_ifs with h h2
  · exact Or.inl rfl
  · exact Or.inr ⟨(Nat.find_spec h).2.2, not_lt.mp h2⟩
  · exact Or.inl rfl

/-- Weight lower bound for a batch after the first. -/
lemma batch_weight_ge (k : ℕ) (hk : 1 ≤ k) (hkT : Q.batchEnd ζ b i j k < Q.T) :
    b ≤ ∑ v ∈ Q.batch ζ b i j (k + 1), Q.weight ζ v i j := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have htail : b ≤ ∑ v ∈ Finset.Icc (Q.batchEnd ζ b i j (k' + 1) + 1) Q.T,
      Q.weight ζ v i j := by
    rcases bE_succ_cases Q ζ b i j k' with h | h
    · omega
    · exact h.2
  have hb : Q.batch ζ b i j (k' + 1 + 1) =
      Finset.Icc (Q.batchEnd ζ b i j (k' + 1) + 1) (Q.batchEnd ζ b i j (k' + 1 + 1)) := by
    simp [Instance.batch]
  rw [hb]
  rcases bE_succ_cases Q ζ b i j (k' + 1) with h | h
  · rw [h]; exact htail
  · exact h.1

end Batch


/-! ## ABC dynamics -/

section Dyn

variable (Q : Instance) (ε ζ b : ℝ) (ω : Q.Path)

lemma hist_eq (m s : ℕ) (hs : s ≤ m) :
    Q.abcHist ε ζ b ω m s = Q.abcHist ε ζ b ω s s := by
  induction m with
  | zero =>
    have : s = 0 := by omega
    subst this; rfl
  | succ m ih =>
    rcases Nat.lt_or_ge s (m + 1) with h | h
    · funext i j
      have hne : s ≠ m + 1 := by omega
      simp only [Instance.abcHist, hne, if_false]
      rw [ih (by omega)]
    · have : s = m + 1 := by omega
      subst this; rfl

lemma rate_eq_step (t : ℕ) (ht : 1 ≤ t) (i j : Fin Q.N) :
    Q.abcRate ε ζ b t ω i j =
      Q.abcStep ε ζ b t ω (Q.abcHist ε ζ b ω (t - 1)) i j := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  simp [Instance.abcRate, Instance.abcHist]

lemma dwh_eq (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ Q.T) (i j : Fin Q.N) :
    Q.deltaWithHistory ζ b t ω (Q.abcHist ε ζ b ω (t - 1)) i j =
      Q.deltaPrev ε ζ b t ω i j := by
  unfold Instance.deltaWithHistory Instance.deltaPrev
  apply Finset.sum_congr rfl
  intro s hs
  rw [mem_batch] at hs
  obtain ⟨_, _, h1, _⟩ := kappa_spec Q ζ b i j t ht1 ht
  have hsle : s ≤ t - 1 := by
    have := bE_mono Q ζ b i j (show Q.kappa ζ b t i j - 1 - 1 ≤ Q.kappa ζ b t i j - 1 by omega)
    omega
  rw [hist_eq Q ε ζ b ω (t - 1) s hsle]
  rfl

lemma clamp01_of (y : ℝ) (h0 : 0 < y) (h1 : y < 1) : clamp01 y = y := by
  unfold clamp01
  rw [min_eq_right h1.le, max_eq_right h0.le]

lemma rate_eq_target (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ Q.T) (i j : Fin Q.N)
    (hav : (Q.N : ℝ) ≤ Q.avail t ω i)
    (h0 : 0 < Q.lamD ζ t i j - ε - Q.u ζ b t i j * Q.deltaPrev ε ζ b t ω i j)
    (h1 : Q.lamD ζ t i j - ε - Q.u ζ b t i j * Q.deltaPrev ε ζ b t ω i j < 1) :
    Q.abcRate ε ζ b t ω i j =
      Q.lamD ζ t i j - ε - Q.u ζ b t i j * Q.deltaPrev ε ζ b t ω i j := by
  rw [rate_eq_step Q ε ζ b ω t ht1]
  unfold Instance.abcStep
  rw [if_pos hav, dwh_eq Q ε ζ b ω t ht1 ht, clamp01_of _ h0 h1]

/-- Realized surplus of batch `k`. -/
def dbar (i j : Fin Q.N) (k : ℕ) : ℝ :=
  ∑ s ∈ Q.batch ζ b i j k, (Q.D s ω i j - Q.abcRate ε ζ b s ω i j)

lemma dbar_zero (i j : Fin Q.N) : dbar Q ε ζ b ω i j 0 = 0 := by
  simp [dbar, batch_zero]

lemma deltaPrev_eq (t : ℕ) (i j : Fin Q.N) :
    Q.deltaPrev ε ζ b t ω i j = dbar Q ε ζ b ω i j (Q.kappa ζ b t i j - 1) := rfl

variable (η : ℝ)

lemma dbar_bound (hA : Q.inA ε ζ b η ω) (hη : 0 ≤ η) (i j : Fin Q.N)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ Q.T) :
    |dbar Q ε ζ b ω i j (Q.kappa ζ b t i j - 1)| ≤ η := by
  obtain ⟨hk1, hkT, h1, h2⟩ := kappa_spec Q ζ b i j t ht1 ht
  set k := Q.kappa ζ b t i j with hk
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have : k - 1 = 0 := by omega
    rw [this, dbar_zero]; simpa using hη
  · have hlt : Q.batchEnd ζ b i j (k - 1 - 1) < Q.batchEnd ζ b i j (k - 1) := by
      have := bE_lt_succ Q ζ b i j (k - 1 - 1)
        (lt_of_le_of_lt (bE_mono Q ζ b i j (show k - 1 - 1 ≤ k - 1 by omega)) (by omega))
      rwa [show k - 1 - 1 + 1 = k - 1 by omega] at this
    have := hA i j (k - 1) (by simp only [Finset.mem_Icc]; omega)
      (Q.batchEnd ζ b i j (k - 1)) (by rw [mem_batch]; exact ⟨hlt, le_rfl⟩)
    exact this.le

end Dyn


/-! ## Target interior -/

section Target

variable (Q : Instance) (ε ζ b η : ℝ) (ω : Q.Path)

lemma weight_pos (hε : 0 < ε) (hζ : ζ = 2 * ε)
    (hx : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j, ζ ≤ Q.lamD ζ t i j ∧ Q.lamD ζ t i j ≤ 1 - ζ)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 Q.T) (i j : Fin Q.N) :
    0 < Q.weight ζ t i j := by
  obtain ⟨h1, h2⟩ := hx t ht i j
  unfold Instance.weight
  apply mul_pos <;> linarith

lemma u_bound (hε : 0 < ε) (hζ : ζ = 2 * ε) (hb : 0 < b)
    (hx : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j, ζ ≤ Q.lamD ζ t i j ∧ Q.lamD ζ t i j ≤ 1 - ζ)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ Q.T) (i j : Fin Q.N)
    (hk : 2 ≤ Q.kappa ζ b t i j) :
    0 ≤ Q.u ζ b t i j ∧ Q.u ζ b t i j ≤ Q.weight ζ t i j / b := by
  obtain ⟨hk1, hkT, h1, h2⟩ := kappa_spec Q ζ b i j t ht1 ht
  have hW := batch_weight_ge Q ζ b i j (Q.kappa ζ b t i j - 1) (by omega) (by omega)
  rw [show Q.kappa ζ b t i j - 1 + 1 = Q.kappa ζ b t i j by omega] at hW
  have hw := (weight_pos Q ε ζ hε hζ hx t (by simp only [Finset.mem_Icc]; omega) i j).le
  unfold Instance.u
  constructor
  · exact div_nonneg hw (by linarith)
  · exact div_le_div_of_nonneg_left hw hb hW

lemma ud_bound (hε : 0 < ε) (hζ : ζ = 2 * ε) (hb : 0 < b) (hη : 0 ≤ η)
    (hA : Q.inA ε ζ b η ω)
    (hx : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j, ζ ≤ Q.lamD ζ t i j ∧ Q.lamD ζ t i j ≤ 1 - ζ)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ Q.T) (i j : Fin Q.N) :
    |Q.u ζ b t i j * Q.deltaPrev ε ζ b t ω i j| ≤ Q.weight ζ t i j * η / b := by
  have hw := (weight_pos Q ε ζ hε hζ hx t (by simp only [Finset.mem_Icc]; omega) i j).le
  rcases Nat.lt_or_ge (Q.kappa ζ b t i j) 2 with hk2 | hk2
  · rw [deltaPrev_eq, show Q.kappa ζ b t i j - 1 = 0 by omega, dbar_zero]
    simp only [mul_zero, abs_zero]
    positivity
  · obtain ⟨hu0, hu1⟩ := u_bound Q ε ζ b hε hζ hb hx t ht1 ht i j hk2
    have hd := dbar_bound Q ε ζ b ω η hA hη i j t ht1 ht
    rw [deltaPrev_eq, abs_mul, abs_of_nonneg hu0]
    calc Q.u ζ b t i j * |dbar Q ε ζ b ω i j (Q.kappa ζ b t i j - 1)|
        ≤ (Q.weight ζ t i j / b) * η := mul_le_mul hu1 hd (abs_nonneg _) (by positivity)
      _ = Q.weight ζ t i j * η / b := by ring

lemma target_bounds (hε : 0 < ε) (hζ : ζ = 2 * ε) (hb : 0 < b) (hη : 0 ≤ η)
    (hC2 : 2 * η / b < 1)
    (hA : Q.inA ε ζ b η ω)
    (hx : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j, ζ ≤ Q.lamD ζ t i j ∧ Q.lamD ζ t i j ≤ 1 - ζ)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ Q.T) (i j : Fin Q.N) :
    0 < Q.lamD ζ t i j - ε - Q.u ζ b t i j * Q.deltaPrev ε ζ b t ω i j ∧
      Q.lamD ζ t i j - ε - Q.u ζ b t i j * Q.deltaPrev ε ζ b t ω i j < 1 := by
  have hud := ud_bound Q ε ζ b η ω hε hζ hb hη hA hx t ht1 ht i j
  have hwp := weight_pos Q ε ζ hε hζ hx t (by simp only [Finset.mem_Icc]; omega) i j
  obtain ⟨hx1, hx2⟩ := hx t (by simp only [Finset.mem_Icc]; omega) i j
  have hηb : η / b < 1 / 2 := by
    rw [div_lt_iff₀ hb] at hC2 ⊢; linarith
  have hlt : Q.weight ζ t i j * η / b < Q.weight ζ t i j / 2 := by
    rw [mul_div_assoc]
    nlinarith
  have hwe : Q.weight ζ t i j = Q.lamD ζ t i j * (1 - Q.lamD ζ t i j) := rfl
  have habs := abs_le.mp (le_trans hud hlt.le)
  constructor
  · have : Q.u ζ b t i j * Q.deltaPrev ε ζ b t ω i j < Q.weight ζ t i j / 2 :=
      lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt hud hlt)
    nlinarith
  · have : -(Q.weight ζ t i j / 2) < Q.u ζ b t i j * Q.deltaPrev ε ζ b t ω i j := by
      have := neg_abs_le (Q.u ζ b t i j * Q.deltaPrev ε ζ b t ω i j)
      linarith [lt_of_le_of_lt hud hlt]
    nlinarith

end Target


/-! ## Cumulative deviation -/

section Cum

variable (Q : Instance) (ε ζ b η : ℝ) (ω : Q.Path) (i j : Fin Q.N)

def Pm (m : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc (Q.batchEnd ζ b i j (Q.kappa ζ b m i j - 1) + 1) m,
    (Q.D s ω i j - Q.abcRate ε ζ b s ω i j)

def Um (m : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc (Q.batchEnd ζ b i j (Q.kappa ζ b m i j - 1) + 1) m, Q.u ζ b s i j

def Rm (m : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 m, (Q.D s ω i j - Q.lamD ζ s i j) + ε * m

lemma kappa_const (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ Q.T) (s : ℕ)
    (hs : s ∈ Finset.Icc (Q.batchEnd ζ b i j (Q.kappa ζ b m i j - 1) + 1) m) :
    Q.kappa ζ b s i j = Q.kappa ζ b m i j := by
  obtain ⟨hk1, hkT, h1, h2⟩ := kappa_spec Q ζ b i j m hm1 hm
  simp only [Finset.mem_Icc] at hs
  exact kappa_eq Q ζ b i j s _ hk1 (by omega) (by omega) (by omega)

lemma Um_eq (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ Q.T) :
    Um Q ζ b i j m =
      (∑ s ∈ Finset.Icc (Q.batchEnd ζ b i j (Q.kappa ζ b m i j - 1) + 1) m,
          Q.weight ζ s i j) /
        ∑ v ∈ Q.batch ζ b i j (Q.kappa ζ b m i j), Q.weight ζ v i j := by
  unfold Um
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  unfold Instance.u
  rw [kappa_const Q ζ b i j m hm1 hm s hs]

lemma Um_bounds (hε : 0 < ε) (hζ : ζ = 2 * ε) (hb : 0 < b)
    (hx : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j, ζ ≤ Q.lamD ζ t i j ∧ Q.lamD ζ t i j ≤ 1 - ζ)
    (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ Q.T) (hk : 2 ≤ Q.kappa ζ b m i j) :
    0 ≤ Um Q ζ b i j m ∧ Um Q ζ b i j m ≤ 1 ∧
      (Q.batchEnd ζ b i j (Q.kappa ζ b m i j) = m → Um Q ζ b i j m = 1) := by
  obtain ⟨hk1, hkT, h1, h2⟩ := kappa_spec Q ζ b i j m hm1 hm
  have hW := batch_weight_ge Q ζ b i j (Q.kappa ζ b m i j - 1) (by omega) (by omega)
  rw [show Q.kappa ζ b m i j - 1 + 1 = Q.kappa ζ b m i j by omega] at hW
  have hWpos : 0 < ∑ v ∈ Q.batch ζ b i j (Q.kappa ζ b m i j), Q.weight ζ v i j := by linarith
  have hbatch : Q.batch ζ b i j (Q.kappa ζ b m i j) =
      Finset.Icc (Q.batchEnd ζ b i j (Q.kappa ζ b m i j - 1) + 1)
        (Q.batchEnd ζ b i j (Q.kappa ζ b m i j)) := rfl
  have hwnn : ∀ s ∈ Finset.Icc (Q.batchEnd ζ b i j (Q.kappa ζ b m i j - 1) + 1)
      (Q.batchEnd ζ b i j (Q.kappa ζ b m i j)), 0 ≤ Q.weight ζ s i j := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    have := bE_le Q ζ b i j (Q.kappa ζ b m i j)
    exact (weight_pos Q ε ζ hε hζ hx s (by simp only [Finset.mem_Icc]; omega) i j).le
  have hsub : (∑ s ∈ Finset.Icc (Q.batchEnd ζ b i j (Q.kappa ζ b m i j - 1) + 1) m,
          Q.weight ζ s i j) ≤ ∑ v ∈ Q.batch ζ b i j (Q.kappa ζ b m i j), Q.weight ζ v i j := by
    rw [hbatch]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs; simp only [Finset.mem_Icc] at hs ⊢; omega
    · intro s hs _; exact hwnn s hs
  have hnn : 0 ≤ ∑ s ∈ Finset.Icc (Q.batchEnd ζ b i j (Q.kappa ζ b m i j - 1) + 1) m,
      Q.weight ζ s i j := by
    apply Finset.sum_nonneg
    intro s hs; apply hwnn; simp only [Finset.mem_Icc] at hs ⊢; omega
  rw [Um_eq Q ζ b i j m hm1 hm]
  refine ⟨div_nonneg hnn hWpos.le, (div_le_one hWpos).mpr hsub, ?_⟩
  intro hE
  rw [div_eq_one_iff_eq hWpos.ne', hbatch, hE]

lemma Pm_bound (hA : Q.inA ε ζ b η ω) (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ Q.T) :
    |Pm Q ε ζ b ω i j m| < η := by
  obtain ⟨hk1, hkT, h1, h2⟩ := kappa_spec Q ζ b i j m hm1 hm
  exact hA i j (Q.kappa ζ b m i j) (by simp only [Finset.mem_Icc]; omega) m
    (by rw [mem_batch]; exact ⟨h1, h2⟩)

lemma Rm_ident (hε : 0 < ε) (hζ : ζ = 2 * ε) (hb : 0 < b)
    (hx : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j, ζ ≤ Q.lamD ζ t i j ∧ Q.lamD ζ t i j ≤ 1 - ζ)
    (m : ℕ) (hm1 : 1 ≤ m) :
    m ≤ Q.T →
    (∀ s ∈ Finset.Icc 1 m, Q.abcRate ε ζ b s ω i j =
        Q.lamD ζ s i j - ε - Q.u ζ b s i j * Q.deltaPrev ε ζ b s ω i j) →
    Rm Q ε ζ ω i j m = dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1) + Pm Q ε ζ b ω i j m -
      Um Q ζ b i j m * dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1) := by
  induction m, hm1 using Nat.le_induction with
  | base =>
    intro hT hr
    have hk : Q.kappa ζ b 1 i j = 1 := by
      apply kappa_eq Q ζ b i j 1 1 le_rfl hT (by simp [bE_zero])
      have := bE_lt_succ Q ζ b i j 0 (by rw [bE_zero]; omega)
      rw [bE_zero] at this; exact this
    have h1 := hr 1 (by simp)
    rw [deltaPrev_eq, hk, show 1 - 1 = 0 from rfl, dbar_zero] at h1
    unfold Rm Pm Um
    rw [hk, show 1 - 1 = 0 from rfl, dbar_zero, bE_zero]
    simp only [zero_add, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, mul_zero,
      sub_zero, h1, mul_one]
    ring
  | succ m hm1 ih =>
    intro hT hr
    have ih' := ih (by omega) (fun s hs => hr s (by simp only [Finset.mem_Icc] at hs ⊢; omega))
    have hrm := hr (m + 1) (by simp only [Finset.mem_Icc]; omega)
    obtain ⟨hk1, hkT, h1, h2⟩ := kappa_spec Q ζ b i j m hm1 (by omega)
    set k := Q.kappa ζ b m i j with hkdef
    have hR : Rm Q ε ζ ω i j (m + 1) = Rm Q ε ζ ω i j m +
        (Q.D (m + 1) ω i j - Q.lamD ζ (m + 1) i j) + ε := by
      unfold Rm
      rw [Finset.sum_Icc_succ_top (by omega)]
      push_cast; ring
    rcases Nat.lt_or_ge (Q.batchEnd ζ b i j k) (m + 1) with hE | hE
    · -- batch k ends at m
      have hEm : Q.batchEnd ζ b i j k = m := by omega
      have hk' : Q.kappa ζ b (m + 1) i j = k + 1 := by
        apply kappa_eq Q ζ b i j (m + 1) (k + 1) (by omega) hT (by simpa using hE)
        have := bE_lt_succ Q ζ b i j k (by omega)
        omega
      have hP : Pm Q ε ζ b ω i j (m + 1) =
          Q.D (m + 1) ω i j - Q.abcRate ε ζ b (m + 1) ω i j := by
        unfold Pm; rw [hk']; simp [hEm]
      have hU : Um Q ζ b i j (m + 1) = Q.u ζ b (m + 1) i j := by
        unfold Um; rw [hk']; simp [hEm]
      have hdk : dbar Q ε ζ b ω i j k = Pm Q ε ζ b ω i j m := by
        unfold dbar Pm Instance.batch
        rw [← hkdef, hEm]
      have hzero : dbar Q ε ζ b ω i j (k - 1) -
          Um Q ζ b i j m * dbar Q ε ζ b ω i j (k - 1) = 0 := by
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · rw [show k - 1 = 0 by omega, dbar_zero]; ring
        · rw [(Um_bounds Q ε ζ b i j hε hζ hb hx m hm1 (by omega) hk2).2.2 hEm]; ring
      rw [deltaPrev_eq, hk', show k + 1 - 1 = k by omega] at hrm
      rw [hR, ih', hP, hU, hk', show k + 1 - 1 = k by omega, hrm]
      linear_combination hzero - hdk
    · -- same batch
      have hk' : Q.kappa ζ b (m + 1) i j = k :=
        kappa_eq Q ζ b i j (m + 1) k hk1 hT (by omega) hE
      have hP : Pm Q ε ζ b ω i j (m + 1) = Pm Q ε ζ b ω i j m +
          (Q.D (m + 1) ω i j - Q.abcRate ε ζ b (m + 1) ω i j) := by
        unfold Pm; rw [hk', ← hkdef, Finset.sum_Icc_succ_top (by omega)]
      have hU : Um Q ζ b i j (m + 1) = Um Q ζ b i j m + Q.u ζ b (m + 1) i j := by
        unfold Um; rw [hk', ← hkdef, Finset.sum_Icc_succ_top (by omega)]
      rw [deltaPrev_eq, hk'] at hrm
      rw [hR, ih', hP, hU, hk', hrm]
      ring

lemma Rm_bound (hε : 0 < ε) (hζ : ζ = 2 * ε) (hb : 0 < b) (hη : 0 ≤ η)
    (hA : Q.inA ε ζ b η ω)
    (hx : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j, ζ ≤ Q.lamD ζ t i j ∧ Q.lamD ζ t i j ≤ 1 - ζ)
    (m : ℕ) (hm : m ≤ Q.T)
    (hr : ∀ s ∈ Finset.Icc 1 m, Q.abcRate ε ζ b s ω i j =
        Q.lamD ζ s i j - ε - Q.u ζ b s i j * Q.deltaPrev ε ζ b s ω i j) :
    |Rm Q ε ζ ω i j m| ≤ 2 * η := by
  rcases Nat.eq_zero_or_pos m with h0 | hm1
  · subst h0; simp [Rm]; linarith
  rw [Rm_ident Q ε ζ b ω i j hε hζ hb hx m hm1 hm hr]
  have hP := Pm_bound Q ε ζ b η ω i j hA m hm1 hm
  have hD : |dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1) -
      Um Q ζ b i j m * dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1)| ≤ η := by
    rcases Nat.lt_or_ge (Q.kappa ζ b m i j) 2 with hk2 | hk2
    · rw [show Q.kappa ζ b m i j - 1 = 0 by omega, dbar_zero]; simpa using hη
    · obtain ⟨hu0, hu1, _⟩ := Um_bounds Q ε ζ b i j hε hζ hb hx m hm1 hm hk2
      have hd := dbar_bound Q ε ζ b ω η hA hη i j m hm1 hm
      rw [show dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1) -
          Um Q ζ b i j m * dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1) =
          (1 - Um Q ζ b i j m) * dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1) by ring,
        abs_mul, abs_of_nonneg (by linarith)]
      calc (1 - Um Q ζ b i j m) * |dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1)|
          ≤ 1 * η := mul_le_mul (by linarith) hd (abs_nonneg _) zero_le_one
        _ = η := one_mul η
  have := abs_add_le (dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1) -
      Um Q ζ b i j m * dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1)) (Pm Q ε ζ b ω i j m)
  rw [show dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1) + Pm Q ε ζ b ω i j m -
      Um Q ζ b i j m * dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1) =
      (dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1) -
      Um Q ζ b i j m * dbar Q ε ζ b ω i j (Q.kappa ζ b m i j - 1)) + Pm Q ε ζ b ω i j m by ring]
  linarith

end Cum


/-! ## Availability -/

section Avail

variable (Q : Instance) (ε ζ b η : ℝ) (ω : Q.Path)

lemma XS_incr (hε : 0 < ε) (hζ : ζ = 2 * ε)
    (hx : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j, ζ ≤ Q.lamD ζ t i j ∧ Q.lamD ζ t i j ≤ 1 - ζ)
    (i j : Fin Q.N) (n n' : ℕ) (hnn : n ≤ n') :
    n' ≤ Q.T → 2 * ε * ((n' : ℝ) - n) ≤
      ∑ s ∈ Finset.Icc 1 n', Q.lamD ζ s i j - ∑ s ∈ Finset.Icc 1 n, Q.lamD ζ s i j := by
  induction n', hnn using Nat.le_induction with
  | base => intro _; simp
  | succ n' hn ih =>
    intro hT
    have := ih (by omega)
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hx1 := (hx (n' + 1) (by simp only [Finset.mem_Icc]; omega) i j).1
    push_cast
    linarith

lemma DS_eq (a c : Fin Q.N) (n : ℕ) :
    ∑ s ∈ Finset.Icc 1 n, Q.D s ω a c =
      ∑ s ∈ Finset.Icc 1 n, Q.lamD ζ s a c + Rm Q ε ζ ω a c n - ε * n := by
  unfold Rm
  rw [Finset.sum_sub_distrib]
  ring

lemma avail_bound (hε : 0 < ε) (hζ : ζ = 2 * ε) (hb : 0 < b) (hη : 0 ≤ η)
    (hA : Q.inA ε ζ b η ω)
    (hfeas : Q.DCPFeasible ζ (Q.lamD ζ))
    (L : ℕ) (hL1 : 1 ≤ L) (hLT : L ≤ Q.T) (hτ : ∀ i j, L ≤ Q.τ i j)
    (hLε : ε * L = 4 * η + 1)
    (m : ℕ) (hmT : m + 1 ≤ Q.T)
    (hr : ∀ s ∈ Finset.Icc 1 m, ∀ i j, Q.abcRate ε ζ b s ω i j =
        Q.lamD ζ s i j - ε - Q.u ζ b s i j * Q.deltaPrev ε ζ b s ω i j)
    (i : Fin Q.N) :
    (Q.N : ℝ) ≤ Q.avail (m + 1) ω i := by
  have hx : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j, ζ ≤ Q.lamD ζ t i j ∧ Q.lamD ζ t i j ≤ 1 - ζ :=
    hfeas.2
  have hR : ∀ a c (n : ℕ), n ≤ m → |Rm Q ε ζ ω a c n| ≤ 2 * η := by
    intro a c n hn
    apply Rm_bound Q ε ζ b η ω a c hε hζ hb hη hA hx n (by omega)
    intro s hs
    exact hr s (by simp only [Finset.mem_Icc] at hs ⊢; omega) a c
  have hcard : (∑ _j : Fin Q.N, (1 : ℝ)) = Q.N := by simp
  unfold Instance.avail
  rw [show m + 1 - 1 = m by omega]
  rcases Nat.lt_or_ge m L with hmL | hmL
  · -- Case B: no arrivals yet
    have harr : ∀ j, Finset.Icc 1 (m + 1 - Q.τ j i) = ∅ := by
      intro j; have := hτ j i; ext s; simp only [Finset.mem_Icc]; simp; omega
    have hslack := hfeas.1 L (by simp only [Finset.mem_Icc]; omega) i
    have harr2 : ∀ j, Finset.Icc 1 (L - Q.τ j i) = ∅ := by
      intro j; have := hτ j i; ext s; simp only [Finset.mem_Icc]; simp; omega
    simp only [harr, harr2, Finset.sum_empty, add_zero] at hslack ⊢
    have hper : ∀ j, (1 : ℝ) ≤ ∑ s ∈ Finset.Icc 1 L, Q.lamD ζ s i j -
        ∑ s ∈ Finset.Icc 1 m, Q.D s ω i j := by
      intro j
      rw [DS_eq Q ε ζ ω i j m]
      have h1 := XS_incr Q ε ζ hε hζ hx i j m L hmL.le hLT
      have h2 := (abs_le.mp (hR i j m le_rfl)).2
      have h3 : (m : ℝ) ≤ L := by exact_mod_cast hmL.le
      nlinarith
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hper j)
    rw [hcard, Finset.sum_sub_distrib] at this
    linarith
  · -- Case A
    have hm1 : 1 ≤ m := le_trans hL1 hmL
    have hslack := hfeas.1 m (by simp only [Finset.mem_Icc]; omega) i
    have hper : ∀ j, (1 : ℝ) ≤ (∑ s ∈ Finset.Icc 1 (m + 1 - Q.τ j i), Q.D s ω j i) -
        (∑ s ∈ Finset.Icc 1 (m - Q.τ j i), Q.lamD ζ s j i) +
        (∑ s ∈ Finset.Icc 1 m, Q.lamD ζ s i j) - (∑ s ∈ Finset.Icc 1 m, Q.D s ω i j) := by
      intro j
      have hRij := (abs_le.mp (hR i j m le_rfl)).2
      have hmL' : (L : ℝ) ≤ m := by exact_mod_cast hmL
      rw [DS_eq Q ε ζ ω i j m]
      rcases Nat.lt_or_ge m (Q.τ j i) with hτm | hτm
      · rw [show m + 1 - Q.τ j i = 0 by omega, show m - Q.τ j i = 0 by omega]
        simp only [Finset.Icc_eq_empty_of_lt (show 0 < 1 by norm_num), Finset.sum_empty]
        nlinarith
      · rw [DS_eq Q ε ζ ω j i (m + 1 - Q.τ j i)]
        have hτji := hτ j i
        have hRji := (abs_le.mp (hR j i (m + 1 - Q.τ j i) (by omega))).1
        have hinc := XS_incr Q ε ζ hε hζ hx j i (m - Q.τ j i) (m + 1 - Q.τ j i) (by omega)
          (by omega)
        have hc1 : ((m + 1 - Q.τ j i : ℕ) : ℝ) = m + 1 - Q.τ j i := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        have hc2 : ((m - Q.τ j i : ℕ) : ℝ) = m - Q.τ j i := by
          rw [Nat.cast_sub (by omega)]
        rw [hc1, hc2] at hinc
        rw [hc1]
        have hτL : (L : ℝ) ≤ Q.τ j i := by exact_mod_cast hτ j i
        nlinarith
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hper j)
    rw [hcard] at this
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at this
    linarith

end Avail


/-! ## Main sample-path induction -/

theorem main_general (Q : Instance) (ε ζ b η : ℝ)
    (hε : 0 < ε) (hζ : ζ = 2 * ε) (hb : 0 < b) (hη : 0 ≤ η) (hC2 : 2 * η / b < 1)
    (hfeas : Q.DCPFeasible ζ (Q.lamD ζ))
    (L : ℕ) (hL1 : 1 ≤ L) (hLT : L ≤ Q.T) (hτ : ∀ i j, L ≤ Q.τ i j)
    (hLε : ε * L = 4 * η + 1)
    (ω : Q.Path) (hA : Q.inA ε ζ b η ω) :
    ∀ t ∈ Finset.Icc 1 Q.T,
      (∀ i, (Q.N : ℝ) ≤ Q.avail t ω i) ∧
      ∀ i j,
        Q.abcRate ε ζ b t ω i j =
            Q.lamD ζ t i j - ε - Q.u ζ b t i j * Q.deltaPrev ε ζ b t ω i j ∧
          0 < Q.lamD ζ t i j - ε - Q.u ζ b t i j * Q.deltaPrev ε ζ b t ω i j ∧
          Q.lamD ζ t i j - ε - Q.u ζ b t i j * Q.deltaPrev ε ζ b t ω i j < 1 := by
  have hx : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j, ζ ≤ Q.lamD ζ t i j ∧ Q.lamD ζ t i j ≤ 1 - ζ :=
    hfeas.2
  have claim : ∀ m, m ≤ Q.T → ∀ s ∈ Finset.Icc 1 m, ∀ i j, Q.abcRate ε ζ b s ω i j =
      Q.lamD ζ s i j - ε - Q.u ζ b s i j * Q.deltaPrev ε ζ b s ω i j := by
    intro m
    induction m with
    | zero => intro _ s hs; simp at hs
    | succ m ih =>
      intro hmT s hs i j
      have ih' := ih (by omega)
      simp only [Finset.mem_Icc] at hs
      rcases Nat.lt_or_ge s (m + 1) with hsm | hsm
      · exact ih' s (by simp only [Finset.mem_Icc]; omega) i j
      · have : s = m + 1 := by omega
        subst this
        have hav := avail_bound Q ε ζ b η ω hε hζ hb hη hA hfeas L hL1 hLT hτ hLε m hmT ih' i
        obtain ⟨h0, h1⟩ := target_bounds Q ε ζ b η ω hε hζ hb hη hC2 hA hx (m + 1)
          (by omega) hmT i j
        exact rate_eq_target Q ε ζ b ω (m + 1) (by omega) hmT i j hav h0 h1
  intro t ht
  simp only [Finset.mem_Icc] at ht
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  refine ⟨fun i => avail_bound Q ε ζ b η ω hε hζ hb hη hA hfeas L hL1 hLT hτ hLε m ht.2
    (claim m (by omega)) i, fun i j => ⟨claim (m + 1) ht.2 (m + 1)
      (by simp only [Finset.mem_Icc]; omega) i j, ?_⟩⟩
  exact target_bounds Q ε ζ b η ω hε hζ hb hη hC2 hA hx (m + 1) (by omega) ht.2 i j

/-! ## Existence of a DCP optimum -/

section Opt

variable (Q : Instance)

def emb (v : Fin Q.T → Fin Q.N → Fin Q.N → ℝ) : ℕ → Fin Q.N → Fin Q.N → ℝ :=
  fun t i j => if h : 1 ≤ t ∧ t ≤ Q.T then v ⟨t - 1, by omega⟩ i j else 0

def restr (x : ℕ → Fin Q.N → Fin Q.N → ℝ) : Fin Q.T → Fin Q.N → Fin Q.N → ℝ :=
  fun t i j => x (t.1 + 1) i j

lemma emb_restr (x : ℕ → Fin Q.N → Fin Q.N → ℝ) (t : ℕ) (ht : t ∈ Finset.Icc 1 Q.T) :
    emb Q (restr Q x) t = x t := by
  simp only [Finset.mem_Icc] at ht
  funext i j
  simp only [emb, restr, dif_pos ht]
  congr 1
  omega

lemma emb_cont (t : ℕ) (i j : Fin Q.N) :
    Continuous (fun v : Fin Q.T → Fin Q.N → Fin Q.N → ℝ => emb Q v t i j) := by
  by_cases h : 1 ≤ t ∧ t ≤ Q.T
  · simp only [emb, dif_pos h]
    fun_prop
  · simp only [emb, dif_neg h]
    exact continuous_const

lemma feas_congr (ζ : ℝ) (x y : ℕ → Fin Q.N → Fin Q.N → ℝ)
    (h : ∀ t ∈ Finset.Icc 1 Q.T, x t = y t) (hx : Q.DCPFeasible ζ x) :
    Q.DCPFeasible ζ y := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun t ht i => ?_, fun t ht i j => ?_⟩
  · have e1 : ∀ j, ∑ s ∈ Finset.Icc 1 t, y s i j = ∑ s ∈ Finset.Icc 1 t, x s i j := by
      intro j
      apply Finset.sum_congr rfl
      intro s hs
      simp only [Finset.mem_Icc] at hs ht
      rw [h s (by simp only [Finset.mem_Icc]; omega)]
    have e2 : ∀ j, ∑ s ∈ Finset.Icc 1 (t - Q.τ j i), y s j i =
        ∑ s ∈ Finset.Icc 1 (t - Q.τ j i), x s j i := by
      intro j
      apply Finset.sum_congr rfl
      intro s hs
      simp only [Finset.mem_Icc] at hs ht
      rw [h s (by simp only [Finset.mem_Icc]; omega)]
    simp only [e1, e2]
    exact h1 t ht i
  · rw [← h t ht]; exact h2 t ht i j

lemma obj_congr (x y : ℕ → Fin Q.N → Fin Q.N → ℝ)
    (h : ∀ t ∈ Finset.Icc 1 Q.T, x t = y t) : Q.DCPObj x = Q.DCPObj y := by
  unfold Instance.DCPObj
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t ht]

lemma exists_opt (ζ : ℝ) (hr : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j, Continuous (Q.r t i j))
    (hfeas : ∃ x, Q.DCPFeasible ζ x) : ∃ x, Q.IsDCPOpt ζ x := by
  set S : Set (Fin Q.T → Fin Q.N → Fin Q.N → ℝ) := {v | Q.DCPFeasible ζ (emb Q v)} with hS
  have hclosed : IsClosed S := by
    have : S = {v | ∀ t ∈ Finset.Icc 1 Q.T, ∀ i,
        0 ≤ (Q.C i : ℝ) - ∑ j, ∑ s ∈ Finset.Icc 1 t, emb Q v s i j +
          ∑ j, ∑ s ∈ Finset.Icc 1 (t - Q.τ j i), emb Q v s j i} ∩
        {v | ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j, ζ ≤ emb Q v t i j ∧ emb Q v t i j ≤ 1 - ζ} := rfl
    rw [this]
    apply IsClosed.inter
    · simp only [Set.setOf_forall]
      refine isClosed_iInter fun t => isClosed_iInter fun _ => isClosed_iInter fun i => ?_
      apply isClosed_le continuous_const
      exact (continuous_const.sub (continuous_finset_sum _ fun j _ =>
        continuous_finset_sum _ fun s _ => emb_cont Q s i j)).add
        (continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun s _ => emb_cont Q s j i)
    · simp only [Set.setOf_forall, Set.setOf_and]
      refine isClosed_iInter fun t => isClosed_iInter fun _ => isClosed_iInter fun i =>
        isClosed_iInter fun j => ?_
      exact (isClosed_le continuous_const (emb_cont Q t i j)).inter
        (isClosed_le (emb_cont Q t i j) continuous_const)
  have hsub : S ⊆ Set.Icc (fun _ _ _ => ζ) (fun _ _ _ => 1 - ζ) := by
    intro v hv
    have h2 := hv.2
    constructor
    · intro t i j
      have := (h2 (t.1 + 1) (by simp only [Finset.mem_Icc]; omega) i j).1
      simpa [emb, restr] using this
    · intro t i j
      have := (h2 (t.1 + 1) (by simp only [Finset.mem_Icc]; omega) i j).2
      simpa [emb, restr] using this
  have hcpt : IsCompact S := (isCompact_Icc).of_isClosed_subset hclosed hsub
  obtain ⟨x0, hx0⟩ := hfeas
  have hne : S.Nonempty := ⟨restr Q x0, feas_congr Q ζ x0 _
    (fun t ht => (emb_restr Q x0 t ht).symm) hx0⟩
  have hcont : Continuous (fun v => Q.DCPObj (emb Q v)) := by
    unfold Instance.DCPObj
    exact continuous_finset_sum _ fun t ht => continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ => (hr t ht i j).comp (emb_cont Q t i j)
  obtain ⟨v, hvS, hmax⟩ := hcpt.exists_isMaxOn hne hcont.continuousOn
  refine ⟨emb Q v, hvS, fun y hy => ?_⟩
  have hyS : restr Q y ∈ S :=
    feas_congr Q ζ y _ (fun t ht => (emb_restr Q y t ht).symm) hy
  have := hmax hyS
  simp only [Set.mem_setOf_eq] at this
  rw [obj_congr Q y (emb Q (restr Q y)) (fun t ht => (emb_restr Q y t ht).symm)]
  exact this

lemma lamD_opt (ζ : ℝ) (h : ∃ x, Q.IsDCPOpt ζ x) : Q.IsDCPOpt ζ (Q.lamD ζ) := by
  unfold Instance.lamD
  rw [dif_pos h]
  exact Classical.choose_spec h

end Opt

end L4P

open SpatialPricing.ABC in
theorem solution (P : Instance) (Ψ3 : ℝ) (hP : P.Standing Ψ3)
    (hτT : P.tauMin ≤ P.T)
    (n : ℕ) (hn : 1 ≤ n)
    (hfeas : ∃ x, (P.scale n).DCPFeasible (P.zetaN n) x)
    (hC2 : 2 * P.etaN n / P.bN n < 1) :
    ∀ ω : (P.scale n).Path,
      0 < (P.scale n).pathProb
        ((P.scale n).abcRate (P.epsN n) (P.zetaN n) (P.bN n)) ω →
      (P.scale n).inA (P.epsN n) (P.zetaN n) (P.bN n) (P.etaN n) ω →
      ∀ t ∈ Finset.Icc 1 (P.scale n).T,
        (∀ i, ((P.scale n).N : ℝ) ≤ (P.scale n).avail t ω i) ∧
        ∀ i j,
          let target := (P.scale n).lamD (P.zetaN n) t i j - P.epsN n -
            (P.scale n).u (P.zetaN n) (P.bN n) t i j *
              (P.scale n).deltaPrev (P.epsN n) (P.zetaN n) (P.bN n) t ω i j
          (P.scale n).abcRate (P.epsN n) (P.zetaN n) (P.bN n) t ω i j = target ∧
            0 < target ∧ target < 1 := by
  obtain ⟨hN, hT, hτ1, hC, hΨ, hreg⟩ := hP
  intro ω _ hA
  haveI : Nonempty (Fin P.N × Fin P.N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have htmin_le : ∀ i j, P.tauMin ≤ P.τ i j := fun i j =>
    ciInf_le (OrderBot.bddBelow _) (i, j)
  have htmin1 : 1 ≤ P.tauMin := le_ciInf (fun p => hτ1 p.1 p.2)
  set L : ℕ := n * P.tauMin with hLdef
  have hL1 : 1 ≤ L := by
    have := Nat.mul_le_mul hn htmin1; simpa using this
  have hLT : L ≤ (P.scale n).T := Nat.mul_le_mul_left n hτT
  have hτ : ∀ i j, L ≤ (P.scale n).τ i j := fun i j => Nat.mul_le_mul_left n (htmin_le i j)
  have htauN : P.tauN n = (L : ℝ) := by simp [Instance.tauN, hLdef]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hsq : 0 ≤ Real.sqrt (2 * (P.bN n + 1) * Real.log (P.TN n)) := Real.sqrt_nonneg _
  have hε : 0 < P.epsN n := by
    unfold Instance.epsN; rw [htauN]; positivity
  have hεL : P.epsN n * L = 1 + 16 * Real.sqrt (2 * (P.bN n + 1) * Real.log (P.TN n)) := by
    unfold Instance.epsN; rw [htauN]; field_simp
  have hLε : P.epsN n * L = 4 * P.etaN n + 1 := by
    unfold Instance.etaN; rw [htauN]; ring
  have hη : 0 ≤ P.etaN n := by linarith
  have hb : 0 < P.bN n := by
    unfold Instance.bN; rw [htauN]; exact Real.rpow_pos_of_pos hLpos _
  have hr : ∀ t ∈ Finset.Icc 1 (P.scale n).T, ∀ i j, Continuous ((P.scale n).r t i j) := by
    intro t ht i j
    simp only [Finset.mem_Icc] at ht
    have hTn : (P.scale n).T = n * P.T := rfl
    rw [hTn] at ht
    have hk : (t + n - 1) / n ∈ Finset.Icc 1 P.T := by
      simp only [Finset.mem_Icc]
      constructor
      · rw [Nat.le_div_iff_mul_le (by omega)]; omega
      · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by omega)]
        have : (P.T).succ * n = n * P.T + n := by rw [Nat.succ_mul, Nat.mul_comm]
        omega
    exact (hreg _ hk i j).2.1.continuous
  have hopt := L4P.lamD_opt (P.scale n) (P.zetaN n)
    (L4P.exists_opt (P.scale n) (P.zetaN n) hr hfeas)
  have := L4P.main_general (P.scale n) (P.epsN n) (P.zetaN n) (P.bN n) (P.etaN n)
    hε rfl hb hη hC2 hopt.1 L hL1 hLT hτ hLε ω hA
  intro t ht
  exact this t ht
