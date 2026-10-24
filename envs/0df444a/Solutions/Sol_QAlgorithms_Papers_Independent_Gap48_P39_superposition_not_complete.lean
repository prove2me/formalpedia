-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P39.superposition_not_complete
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:18:14.878692+00:00
-- url     : https://prove2.me/submissions/8d1fd32a-3253-41b1-a384-766bda125f4d

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P39

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Gap48.P39

open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)
open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks holevoInfo)
open QAlgorithms.Papers.Independent.Dependency50.P19 (both epr mutualInformation marginalRA marginalRB)
open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)
open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity conditionalEntropy groupedChannelPower)

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7B20

open scoped ComplexOrder

lemma state_apply (x : Bool) (a b : Unit × Bool) :
    binaryExample.state x a b = if a.2 = x ∧ b.2 = x then 1 else 0 := by
  obtain ⟨⟨⟩, a2⟩ := a
  obtain ⟨⟨⟩, b2⟩ := b
  simp only [binaryExample, pureDensity, ket, Matrix.of_apply]
  by_cases ha : a2 = x <;> by_cases hb : b2 = x <;> simp [ha, hb]

lemma word_apply {n : ℕ} (x : Fin n → Bool) (i j : (Fin n → Unit) × (Fin n → Bool)) :
    binaryExample.word x i j = if i.2 = x ∧ j.2 = x then 1 else 0 := by
  simp only [CQChannel.word, state_apply]
  by_cases h : i.2 = x ∧ j.2 = x
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro k _
    rw [if_pos ⟨by rw [h.1], by rw [h.2]⟩]
  · rw [if_neg h]
    have : ∃ k, ¬ (i.2 k = x k ∧ j.2 k = x k) := by
      by_contra hc
      push Not at hc
      exact h ⟨funext fun k => (hc k).1, funext fun k => (hc k).2⟩
    obtain ⟨k, hk⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

lemma traceRight_word {n : ℕ} (x : Fin n → Bool) :
    traceRight (binaryExample.word x) = (1 : Matrix (Fin n → Unit) (Fin n → Unit) ℂ) := by
  ext a b
  have hab : a = b := Subsingleton.elim a b
  subst hab
  simp only [traceRight, Matrix.of_apply, word_apply, Matrix.one_apply_eq]
  simp

lemma holevo_zero {n t : ℕ} (p : Distribution (Fin t × (Fin n → Bool))) :
    holevoInfo (fun x => ∑ s, p.val (s, x)) (fun x => traceRight (binaryExample.word x)) = 0 := by
  have hsum : ∑ x : Fin n → Bool, ∑ s, p.val (s, x) = 1 := by
    have h := p.prop.2
    rw [Fintype.sum_prod_type] at h
    rw [Finset.sum_comm]; exact h
  simp only [holevoInfo, traceRight_word]
  rw [← Finset.sum_smul, ← Finset.sum_mul]
  have : (∑ x : Fin n → Bool, ((∑ s, p.val (s, x) : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum, hsum]; simp
  rw [this, hsum]
  simp

/-- generic zero-error code: Charlie decodes with `g`, words given by `f`. -/
def code (n l : ℕ) (f : Fin l → (Fin n → Bool)) (g : (Fin n → Bool) → Fin l) :
    CQBroadcastCode Bool Unit Bool n 1 1 l where
  word _ _ j := f j
  bob _ := 1
  bob_povm := by
    refine ⟨fun _ => Matrix.PosSemidef.one, ?_⟩
    simp
  charlie q := Matrix.diagonal fun c => if ((0 : Fin 1), g c) = q then 1 else 0
  charlie_povm := by
    refine ⟨fun q => ?_, ?_⟩
    · apply Matrix.PosSemidef.diagonal
      intro c
      simp only [Pi.zero_apply]
      split_ifs <;> simp
    · ext a b
      rw [Matrix.sum_apply]
      by_cases hab : a = b
      · subst hab
        simp [Matrix.diagonal_apply]
      · simp [Matrix.diagonal_apply, hab]

lemma code_good (n l : ℕ) (f : Fin l → (Fin n → Bool)) (g : (Fin n → Bool) → Fin l)
    (hfg : ∀ j, g (f j) = j) : (code n l f g).Good binaryExample 0 := by
  intro s i j
  have hs : s = 0 := Subsingleton.elim _ _
  subst hs
  have hw : binaryExample.word (f j) = Matrix.kronecker
      (1 : Matrix (Fin n → Unit) (Fin n → Unit) ℂ)
      (Matrix.diagonal fun c => if c = f j then 1 else 0) := by
    ext a b
    have h1 : a.1 = b.1 := Subsingleton.elim _ _
    have h1' : (1 : Matrix (Fin n → Unit) (Fin n → Unit) ℂ) a.1 b.1 = 1 := by
      rw [h1, Matrix.one_apply_eq]
    rw [word_apply]
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, h1', one_mul,
      Matrix.diagonal_apply]
    by_cases ha : a.2 = f j <;> by_cases hb : b.2 = f j
    · simp [ha, hb]
    · have hb' : f j ≠ b.2 := fun h => hb h.symm
      simp [ha, hb, hb']
    · have : a.2 ≠ b.2 := fun h => ha (h.trans hb)
      simp [ha, hb, this]
    · simp [ha, hb]
  simp only [code, effectProb]
  rw [hw]
  unfold Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Matrix.mul_one, Matrix.trace_one]
  rw [Finset.sum_eq_single (f j)]
  · simp [hfg]
  · intro c _ hc; simp [hc]
  · simp

lemma rank_one (n : ℕ) : rank n 1 = 2 ^ n := by
  unfold rank
  rw [mul_one]
  have : Real.rpow 2 (n : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
    show (2:ℝ) ^ (n:ℝ) = _
    rw [Real.rpow_natCast]; push_cast; ring
  rw [this, Nat.floor_natCast]

lemma rank_zero (n : ℕ) : rank n 0 = 1 := by
  simp [rank]

lemma code_exists_one (n : ℕ) :
    ∃ D : CQBroadcastCode Bool Unit Bool n 1 1 (rank n 1), D.Good binaryExample 0 := by
  let e : (Fin n → Bool) ≃ Fin (rank n 1) :=
    Fintype.equivFinOfCardEq (by simp [rank_one])
  exact ⟨code n _ e.symm e, code_good _ _ _ _ (fun j => by simp)⟩

lemma good_mono {n m k l : ℕ} {D : CQBroadcastCode Bool Unit Bool n m k l} {ε : ℝ}
    (h : D.Good binaryExample 0) (hε : 0 ≤ ε) : D.Good binaryExample ε :=
  fun s i j => le_trans (by linarith) (h s i j)

lemma ach001 : cqBroadcastAchievable binaryExample (0, 0, 1) := by
  refine ⟨⟨le_refl _, le_refl _, zero_le_one⟩, fun ε hε => ⟨1, one_pos, fun n _ => ?_⟩⟩
  show ∃ D : CQBroadcastCode Bool Unit Bool n (rank n 0) (rank n 0) (rank n 1),
    D.Good binaryExample ε
  rw [rank_zero]
  obtain ⟨D, hD⟩ := code_exists_one n
  exact ⟨D, good_mono hD hε.le⟩

lemma ach000 : cqBroadcastAchievable binaryExample (0, 0, 0) := by
  refine ⟨⟨le_refl _, le_refl _, le_refl _⟩, fun ε hε => ⟨1, one_pos, fun n _ => ?_⟩⟩
  show ∃ D : CQBroadcastCode Bool Unit Bool n (rank n 0) (rank n 0) (rank n 0),
    D.Good binaryExample ε
  rw [rank_zero]
  exact ⟨code n 1 (fun _ _ => false) (fun _ => 0),
    good_mono (code_good _ _ _ _ (fun j => Subsingleton.elim _ _)) hε.le⟩

lemma raw_zero (r : ℝ × ℝ × ℝ) (hr : r ∈ rawRegularizedSuperposition binaryExample) :
    r = (0, 0, 0) ∧ r.1 + r.2.1 + r.2.2 = 0 := by
  obtain ⟨⟨h0, h1, h2⟩, n, t, hn, ht, hcap, p, hb, hc, htot⟩ := hr
  rw [holevo_zero] at htot
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : r.1 + r.2.1 + r.2.2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have := mul_pos hn' hcon
    linarith
  obtain ⟨a, b, c⟩ := r
  simp only at h0 h1 h2 hs ⊢
  refine ⟨?_, by linarith⟩
  have ha : a = 0 := by linarith
  have hb : b = 0 := by linarith
  have hc : c = 0 := by linarith
  rw [ha, hb, hc]

end X7B20

end QAlgorithms.Papers.Independent.Gap48.P39

end

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Gap48.P39 QAlgorithms.Papers.Independent.Gap48.P39.X7B20 in
theorem solution :
    rawRegularizedSuperposition binaryExample ⊂ cqBroadcastCapacity binaryExample ∧
    (∀ r ∈ rawRegularizedSuperposition binaryExample, r.1 + r.2.1 + r.2.2 = 0) ∧
    cqBroadcastAchievable binaryExample (0, 0, 1) ∧
    (∀ n : ℕ, 0 < n → ∃ D : CQBroadcastCode Bool Unit Bool n 1 1 (rank n 1),
      D.Good binaryExample 0) := by
  refine ⟨ssubset_iff_subset_not_subset.2 ⟨fun r hr => ?_, fun h => ?_⟩,
    fun r hr => (raw_zero r hr).2, ach001, fun n _ => code_exists_one n⟩
  · rw [(raw_zero r hr).1]
    exact subset_closure ach000
  · have h1 := (raw_zero _ (h (subset_closure ach001))).2
    norm_num at h1

end
