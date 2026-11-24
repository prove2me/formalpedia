-- Prove2me | solution 1 for SampleCRS.AlmostGreedy.Supplement.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:27:24.146451+00:00
-- url     : https://prove2.me/submissions/90d0c5bc-b70b-4e4e-9339-6ab9063b748f

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_threshold

open SampleCRS.AlmostGreedy SampleCRS.AlmostGreedy.Supplement CommitteeVoting.SingleVoter

namespace L32Aux

lemma prod_exp_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → ℝ)
    (h0 : ∀ k ∈ s, 0 ≤ p k) (h1 : ∀ k ∈ s, p k < 1) (q : ℝ) (hq : ∑ k ∈ s, p k = q)
    (hq1 : q ≤ 1) :
    q * Real.exp (-q) ≤ ∑ j ∈ s, p j * ∏ k ∈ s.erase j, (1 - p k) := by
  obtain ⟨m, hm⟩ : ∃ m : ι → ℝ, ∀ k, m k = p k / (1 - p k) := ⟨_, fun _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∑ k ∈ s, m k = M := ⟨_, rfl⟩
  have hexp : ∀ k ∈ s, Real.exp (-(m k)) ≤ 1 - p k := by
    intro k hk
    have hpos : 0 < 1 - p k := by linarith [h1 k hk]
    have h := Real.add_one_le_exp (m k)
    have e : m k + 1 = 1 / (1 - p k) := by
      rw [hm k, div_add_one hpos.ne']
      congr 1
      ring
    rw [e] at h
    rw [Real.exp_neg]
    have h2 := inv_anti₀ (one_div_pos.mpr hpos) h
    simpa using h2
  have hz : ∀ j ∈ s, Real.exp (-q) * (1 + q - M + m j) ≤ ∏ k ∈ s.erase j, (1 - p k) := by
    intro j hj
    have hsum : ∑ k ∈ s.erase j, m k = M - m j := by
      rw [← hM, ← Finset.add_sum_erase s m hj]
      ring
    calc Real.exp (-q) * (1 + q - M + m j)
        ≤ Real.exp (-q) * Real.exp (q - M + m j) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          linarith [Real.add_one_le_exp (q - M + m j)]
      _ = Real.exp (-∑ k ∈ s.erase j, m k) := by
          rw [← Real.exp_add, hsum]
          congr 1
          ring
      _ = ∏ k ∈ s.erase j, Real.exp (-(m k)) := by
          rw [← Finset.sum_neg_distrib, Real.exp_sum]
      _ ≤ ∏ k ∈ s.erase j, (1 - p k) := by
          apply Finset.prod_le_prod
          · intro k _
            exact (Real.exp_pos _).le
          · intro k hk
            exact hexp k (Finset.mem_of_mem_erase hk)
  have hterm : ∀ j ∈ s, Real.exp (-q) * (p j * (1 + q - M + m j))
      ≤ p j * ∏ k ∈ s.erase j, (1 - p k) := by
    intro j hj
    have h := mul_le_mul_of_nonneg_left (hz j hj) (h0 j hj)
    calc Real.exp (-q) * (p j * (1 + q - M + m j))
        = p j * (Real.exp (-q) * (1 + q - M + m j)) := by ring
      _ ≤ _ := h
  have hsum2 : ∑ j ∈ s, (q * p j - q * m j + p j * m j)
      = q * q - q * M + ∑ j ∈ s, p j * m j := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hq, hM]
  have hnn : 0 ≤ ∑ j ∈ s, (q * p j - q * m j + p j * m j) := by
    apply Finset.sum_nonneg
    intro j hj
    have hpos : 0 < 1 - p j := by linarith [h1 j hj]
    have e : q * p j - q * m j + p j * m j = p j * p j * (1 - q) / (1 - p j) := by
      rw [hm j, eq_div_iff hpos.ne']
      have hc : p j / (1 - p j) * (1 - p j) = p j := div_mul_cancel₀ _ hpos.ne'
      linear_combination (p j - q) * hc
    rw [e]
    exact div_nonneg (mul_nonneg (mul_nonneg (h0 j hj) (h0 j hj)) (by linarith)) hpos.le
  have hsum3 : ∑ j ∈ s, p j * (1 + q - M + m j)
      = q * (1 + q - M) + ∑ j ∈ s, p j * m j := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hq]
  rw [hsum2] at hnn
  calc q * Real.exp (-q) = Real.exp (-q) * q := mul_comm _ _
    _ ≤ Real.exp (-q) * ∑ j ∈ s, p j * (1 + q - M + m j) := by
        rw [hsum3]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = ∑ j ∈ s, Real.exp (-q) * (p j * (1 + q - M + m j)) := by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum hterm

lemma single_sum_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → ℝ)
    (h0 : ∀ k ∈ s, 0 ≤ p k) (h1 : ∀ k ∈ s, p k ≤ 1) (hq1 : ∑ k ∈ s, p k ≤ 1) :
    (∑ k ∈ s, p k) * Real.exp (-1) ≤ ∑ j ∈ s, p j * ∏ k ∈ s.erase j, (1 - p k) := by
  by_cases hall : ∀ k ∈ s, p k < 1
  · have h := prod_exp_bound s p h0 hall _ rfl hq1
    have hq0 : 0 ≤ ∑ k ∈ s, p k := Finset.sum_nonneg h0
    have he : Real.exp (-1) ≤ Real.exp (-(∑ k ∈ s, p k)) :=
      Real.exp_le_exp.mpr (by linarith)
    exact le_trans (mul_le_mul_of_nonneg_left he hq0) h
  · push Not at hall
    obtain ⟨k, hk, hk1⟩ := hall
    have hpk : p k = 1 := le_antisymm (h1 k hk) hk1
    have hsplit := Finset.add_sum_erase s p hk
    have hrest : ∑ j ∈ s.erase k, p j = 0 := by
      have : 0 ≤ ∑ j ∈ s.erase k, p j :=
        Finset.sum_nonneg (fun j hj => h0 j (Finset.mem_of_mem_erase hj))
      linarith
    have hz : ∀ j ∈ s.erase k, p j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => h0 j (Finset.mem_of_mem_erase hj))).mp hrest
    have hprod : ∏ j ∈ s.erase k, (1 - p j) = 1 :=
      Finset.prod_eq_one (fun j hj => by rw [hz j hj]; ring)
    have hsingle : p k * ∏ j ∈ s.erase k, (1 - p j)
        ≤ ∑ j ∈ s, p j * ∏ k ∈ s.erase j, (1 - p k) := by
      apply Finset.single_le_sum (f := fun j => p j * ∏ k ∈ s.erase j, (1 - p k)) _ hk
      intro j hj
      exact mul_nonneg (h0 j hj) (Finset.prod_nonneg
        (fun k hk => by linarith [h1 k (Finset.mem_of_mem_erase hk)]))
    rw [hprod, hpk] at hsingle
    have hsum1 : ∑ j ∈ s, p j = 1 := by linarith
    rw [hsum1]
    have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith

lemma sum_superset {n : ℕ} (p : Fin n → ℝ) (T : Finset (Fin n)) :
    ∑ A : Finset (Fin n), (if T ⊆ A then pbWeight p Finset.univ A else 0) = ∏ k ∈ T, p k := by
  have h := Finset.prod_add (fun k => p k) (fun k => if k ∈ T then (0:ℝ) else 1 - p k)
    (Finset.univ : Finset (Fin n))
  rw [Finset.powerset_univ] at h
  have hl : ∏ k : Fin n, (p k + if k ∈ T then (0:ℝ) else 1 - p k) = ∏ k ∈ T, p k := by
    calc ∏ k : Fin n, (p k + if k ∈ T then (0:ℝ) else 1 - p k)
        = ∏ k : Fin n, (if k ∈ T then p k else 1) := by
          apply Finset.prod_congr rfl
          intro k _
          split_ifs <;> ring
      _ = ∏ k ∈ T, p k := by
          rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [← hl, h]
  apply Finset.sum_congr rfl
  intro A _
  unfold pbWeight
  by_cases hTA : T ⊆ A
  · rw [if_pos hTA]
    congr 1
    apply Finset.prod_congr rfl
    intro a ha
    have : a ∉ T := fun haT => (Finset.mem_sdiff.mp ha).2 (hTA haT)
    rw [if_neg this]
  · rw [if_neg hTA]
    obtain ⟨a, haT, haA⟩ := Finset.not_subset.mp hTA
    have hzero : ∏ a ∈ Finset.univ \ A, (if a ∈ T then (0:ℝ) else 1 - p a) = 0 :=
      Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haA⟩) (if_pos haT)
    rw [hzero, mul_zero]

lemma sampleSet_sum {n : ℕ} (F : Finset (Fin n) → ℝ) :
    ∑ Y : Fin n → Bool, F (sampleSet Y) = ∑ A : Finset (Fin n), F A := by
  let e : (Fin n → Bool) ≃ Finset (Fin n) :=
    { toFun := fun Y => sampleSet Y
      invFun := fun A k => decide (k ∈ A)
      left_inv := by
        intro Y
        funext k
        simp [sampleSet]
      right_inv := by
        intro A
        ext k
        simp [sampleSet] }
  exact Fintype.sum_equiv e _ _ (fun Y => rfl)

lemma activationWeight_eq {n : ℕ} (p : Fin n → ℝ) (Y : Fin n → Bool) :
    activationWeight p Y = pbWeight p Finset.univ (sampleSet Y) := by
  unfold activationWeight
  congr 1

noncomputable def twf {n : ℕ} (i : Fin n) (A : Finset (Fin n)) : ℝ :=
  if A.card = 0 then 0
  else if A.card = 1 then (if i ∈ A then (1:ℝ)/2 else 0)
  else (if i ∈ A then (1:ℝ) else 0) / (A.card : ℝ)

noncomputable def lbf {n : ℕ} (i : Fin n) (A : Finset (Fin n)) : ℝ :=
  (7/12) * (if i ∈ A then (1:ℝ) else 0)
    - (1/12) * ∑ j : Fin n, (if ({i,j} : Finset (Fin n)) ⊆ A then (1:ℝ) else 0)
    + (1/12) * ∑ j ∈ Finset.univ.erase i, (if A = {i,j} then (1:ℝ) else 0)

lemma tw_eq {n : ℕ} (Y : Fin n → Bool) (i : Fin n) :
    threshold3Weight Y (some i) = twf i (sampleSet Y) := by
  unfold threshold3Weight twf
  simp only [Option.some.injEq, reduceCtorEq, ↓reduceIte, zero_add, Finset.sum_ite_eq]

lemma pair_count {n : ℕ} (i : Fin n) (A : Finset (Fin n)) :
    ∑ j ∈ Finset.univ.erase i, (if A = {i,j} then (1:ℝ) else 0)
      ≤ (if A.card = 2 then (1:ℝ) else 0) := by
  by_cases hA : ∃ j ∈ Finset.univ.erase i, A = {i,j}
  · obtain ⟨j, hj, rfl⟩ := hA
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hcard : ({i,j} : Finset (Fin n)).card = 2 := Finset.card_pair (Ne.symm hji)
    rw [if_pos hcard]
    have hterm : ∀ j' ∈ Finset.univ.erase i,
        (if ({i,j} : Finset (Fin n)) = {i,j'} then (1:ℝ) else 0) = (if j' = j then 1 else 0) := by
      intro j' hj'
      have hj'i : j' ≠ i := Finset.ne_of_mem_erase hj'
      by_cases h : j' = j
      · subst h
        simp
      · rw [if_neg h, if_neg]
        intro heq
        have hmem : j' ∈ ({i,j} : Finset (Fin n)) := by
          rw [heq]
          simp
        rcases Finset.mem_insert.mp hmem with h' | h'
        · exact hj'i h'
        · exact h (Finset.mem_singleton.mp h')
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hj]
  · push Not at hA
    rw [Finset.sum_eq_zero (fun j hj => if_neg (hA j hj))]
    split_ifs <;> norm_num

lemma num (c : ℕ) (hc : 1 ≤ c) (x : ℝ) (hx : x ≤ if c = 2 then (1:ℝ) else 0) :
    (7:ℝ)/12 * 1 - (1/12) * (c:ℝ) + (1/12) * x
      ≤ (if c = 0 then (0:ℝ) else if c = 1 then (1:ℝ)/2 else 1 / (c:ℝ)) := by
  obtain rfl | rfl | rfl | h4 : c = 1 ∨ c = 2 ∨ c = 3 ∨ 4 ≤ c := by omega
  · norm_num at hx ⊢
    linarith
  · norm_num at hx ⊢
    linarith
  · norm_num at hx ⊢
    linarith
  · have h0 : c ≠ 0 := by omega
    have h1 : c ≠ 1 := by omega
    have h2 : c ≠ 2 := by omega
    rw [if_neg h0, if_neg h1]
    rw [if_neg h2] at hx
    have hc4 : (4:ℝ) ≤ c := by exact_mod_cast h4
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) (sub_nonneg.mpr hc4),
      mul_nonneg (neg_nonneg.mpr hx) (by linarith : (0:ℝ) ≤ c)]

lemma lb {n : ℕ} (i : Fin n) (A : Finset (Fin n)) : lbf i A ≤ twf i A := by
  unfold lbf twf
  by_cases hi : i ∈ A
  · have hcount : ∑ j : Fin n, (if ({i,j} : Finset (Fin n)) ⊆ A then (1:ℝ) else 0)
        = (A.card : ℝ) := by
      have hiff : ∀ j : Fin n, (({i,j} : Finset (Fin n)) ⊆ A) ↔ j ∈ A := by
        intro j
        simp [Finset.insert_subset_iff, hi]
      simp only [hiff]
      rw [Finset.sum_boole]
      simp
    have hc1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hnum := num A.card hc1 _ (pair_count i A)
    rw [hcount]
    simp only [hi, if_true]
    exact hnum
  · have h2 : ∑ j ∈ Finset.univ.erase i, (if A = {i,j} then (1:ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro hA
      apply hi
      rw [hA]
      exact Finset.mem_insert_self _ _
    have h1 : 0 ≤ ∑ j : Fin n, (if ({i,j} : Finset (Fin n)) ⊆ A then (1:ℝ) else 0) :=
      Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
    rw [h2]
    simp only [hi, if_false, zero_div]
    split_ifs <;> linarith

end L32Aux

open L32Aux in
theorem solution {n : ℕ} (p : Fin n → ℝ) (hp : ValidProb p) (hmass : (∑ i, p i) = 1) :
    ∀ i : Fin n, thresholdError p i ≤ ((1 - 1 / Real.exp 1) / 12) * p i * (1 - p i) := by
  intro i
  have h0 : ∀ k, 0 ≤ p k := fun k => (hp k).1
  have h1 : ∀ k, p k ≤ 1 := fun k => (hp k).2
  have hw : ∀ A : Finset (Fin n), 0 ≤ pbWeight p Finset.univ A := by
    intro A
    unfold pbWeight
    exact mul_nonneg (Finset.prod_nonneg (fun k _ => h0 k))
      (Finset.prod_nonneg (fun k _ => by linarith [h1 k]))
  have hlaw : threshold3Law p (some i)
      = ∑ A : Finset (Fin n), pbWeight p Finset.univ A * twf i A := by
    unfold threshold3Law
    rw [← sampleSet_sum (fun A => pbWeight p Finset.univ A * twf i A)]
    apply Finset.sum_congr rfl
    intro Y _
    rw [activationWeight_eq, tw_eq]
  have hge : ∑ A : Finset (Fin n), pbWeight p Finset.univ A * lbf i A
      ≤ ∑ A : Finset (Fin n), pbWeight p Finset.univ A * twf i A :=
    Finset.sum_le_sum (fun A _ => mul_le_mul_of_nonneg_left (lb i A) (hw A))
  have e1 : ∀ A : Finset (Fin n), pbWeight p Finset.univ A * lbf i A
      = (7/12) * (if ({i} : Finset (Fin n)) ⊆ A then pbWeight p Finset.univ A else 0)
        - (1/12) * ∑ j : Fin n,
            (if ({i,j} : Finset (Fin n)) ⊆ A then pbWeight p Finset.univ A else 0)
        + (1/12) * ∑ j ∈ Finset.univ.erase i,
            (if A = {i,j} then pbWeight p Finset.univ A else 0) := by
    intro A
    have a : ∀ (c : Prop) [Decidable c], (if c then pbWeight p Finset.univ A else 0)
        = pbWeight p Finset.univ A * (if c then (1:ℝ) else 0) := by
      intro c _
      split_ifs <;> simp
    unfold lbf
    simp only [a, ← Finset.mul_sum, Finset.singleton_subset_iff]
    ring
  have s1 : ∑ A : Finset (Fin n),
      (if ({i} : Finset (Fin n)) ⊆ A then pbWeight p Finset.univ A else 0) = p i := by
    rw [sum_superset, Finset.prod_singleton]
  have s2 : ∑ A : Finset (Fin n), ∑ j : Fin n,
      (if ({i,j} : Finset (Fin n)) ⊆ A then pbWeight p Finset.univ A else 0)
      = ∑ j : Fin n, ∏ k ∈ ({i,j} : Finset (Fin n)), p k := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => sum_superset p {i,j})
  have s3 : ∑ A : Finset (Fin n), ∑ j ∈ Finset.univ.erase i,
      (if A = {i,j} then pbWeight p Finset.univ A else 0)
      = ∑ j ∈ Finset.univ.erase i, pbWeight p Finset.univ {i,j} := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hcomp : ∑ A : Finset (Fin n), pbWeight p Finset.univ A * lbf i A
      = (7/12) * p i - (1/12) * ∑ j : Fin n, ∏ k ∈ ({i,j} : Finset (Fin n)), p k
        + (1/12) * ∑ j ∈ Finset.univ.erase i, pbWeight p Finset.univ {i,j} := by
    rw [Finset.sum_congr rfl (fun A _ => e1 A), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, s1, s2, s3]
  have hE : ∑ j ∈ Finset.univ.erase i, p j = 1 - p i := by
    have := Finset.add_sum_erase Finset.univ p (Finset.mem_univ i)
    linarith
  have s4 : ∑ j : Fin n, ∏ k ∈ ({i,j} : Finset (Fin n)), p k = p i + p i * (1 - p i) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), Finset.pair_eq_singleton,
      Finset.prod_singleton, ← hE, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.prod_pair (Ne.symm (Finset.ne_of_mem_erase hj))]
  have s5 : ∑ j ∈ Finset.univ.erase i, pbWeight p Finset.univ {i,j}
      = p i * ∑ j ∈ Finset.univ.erase i,
          p j * ∏ k ∈ (Finset.univ.erase i).erase j, (1 - p k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hset : (Finset.univ : Finset (Fin n)) \ {i,j} = (Finset.univ.erase i).erase j := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_erase, not_or]
      tauto
    unfold pbWeight
    rw [Finset.prod_pair (Ne.symm hji), hset]
    ring
  have hB := single_sum_bound (Finset.univ.erase i) p (fun k _ => h0 k) (fun k _ => h1 k)
    (by rw [hE]; linarith [h0 i])
  rw [hE] at hB
  have hpB := mul_le_mul_of_nonneg_left hB (h0 i)
  have hfin : thresholdError p i = p i / 2 - threshold3Law p (some i) := rfl
  rw [hfin, hlaw, one_div, ← Real.exp_neg]
  rw [hcomp, s4, s5] at hge
  nlinarith [hge, hpB]
