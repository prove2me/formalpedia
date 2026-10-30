-- Prove2me | solution 1 for RendezvousKn.Sym.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:35:08.535248+00:00
-- url     : https://prove2.me/submissions/9bcc36c8-cfcd-48b6-afd9-58c6c0d44eb7

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model
import Theorems.Thm_RendezvousKn_Sym_assertion_2
namespace RdvCore

open RendezvousKn.Sym Finset

lemma card_perm_pos (n : ℕ) : (0:ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  exact_mod_cast Fintype.card_pos

lemma avgPerm_add (n : ℕ) (f g : Equiv.Perm (Fin n) → ℝ) :
    avgPerm n (fun π => f π + g π) = avgPerm n f + avgPerm n g := by
  unfold avgPerm; rw [Finset.sum_add_distrib, add_div]

lemma avgPerm_sub (n : ℕ) (f g : Equiv.Perm (Fin n) → ℝ) :
    avgPerm n (fun π => f π - g π) = avgPerm n f - avgPerm n g := by
  unfold avgPerm; rw [Finset.sum_sub_distrib, sub_div]

lemma avgPerm_sum {ι : Type*} (s : Finset ι) (n : ℕ) (f : ι → Equiv.Perm (Fin n) → ℝ) :
    avgPerm n (fun π => ∑ i ∈ s, f i π) = ∑ i ∈ s, avgPerm n (f i) := by
  unfold avgPerm; rw [Finset.sum_comm, Finset.sum_div]

lemma avgPerm_const_mul (n : ℕ) (c : ℝ) (f : Equiv.Perm (Fin n) → ℝ) :
    avgPerm n (fun π => c * f π) = c * avgPerm n f := by
  unfold avgPerm; rw [← Finset.mul_sum, mul_div_assoc]

lemma avgPerm_const (n : ℕ) (c : ℝ) : avgPerm n (fun _ => c) = c := by
  unfold avgPerm
  have := card_perm_pos n
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

lemma avgPerm_mono (n : ℕ) {f g : Equiv.Perm (Fin n) → ℝ} (h : ∀ π, f π ≤ g π) :
    avgPerm n f ≤ avgPerm n g := by
  unfold avgPerm
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun π _ => h π) (card_perm_pos n).le

lemma avgPerm_nonneg (n : ℕ) {f : Equiv.Perm (Fin n) → ℝ} (h : ∀ π, 0 ≤ f π) :
    0 ≤ avgPerm n f := by
  have := avgPerm_mono n (f := fun _ => 0) h
  rwa [avgPerm_const] at this

lemma avgPerm_mulLeft (n : ℕ) (σ : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin n) → ℝ) :
    avgPerm n (fun π => f (σ * π)) = avgPerm n f := by
  unfold avgPerm; congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun _ => rfl)

lemma prob_eval (n : ℕ) (i j : Fin n) :
    avgPerm n (fun π => if π i = j then 1 else 0) = 1 / n := by
  have hsame : ∀ j' : Fin n, avgPerm n (fun π => if π i = j' then (1:ℝ) else 0) =
      avgPerm n (fun π => if π i = j then 1 else 0) := by
    intro j'
    rw [← avgPerm_mulLeft n (Equiv.swap j j') (fun π => if π i = j' then (1:ℝ) else 0)]
    congr 1; funext π
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  have htot : ∑ j' : Fin n, avgPerm n (fun π => if π i = j' then (1:ℝ) else 0) = 1 := by
    rw [← avgPerm_sum]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact avgPerm_const n 1
  simp only [hsame, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htot
  have hn : (0:ℝ) < n := by exact_mod_cast (Fin.pos i)
  field_simp
  linarith

lemma waitTime_le {n : ℕ} (τA τB : Tactic n) (π : Equiv.Perm (Fin n)) :
    waitTime τA τB π ≤ n + 1 :=
  Finset.min'_le _ _ (mem_union_right _ (mem_singleton_self _))

lemma lt_waitTime_iff {n : ℕ} (τA τB : Tactic n) (π : Equiv.Perm (Fin n)) (k : ℕ)
    (hk : k ≤ n) :
    k < waitTime τA τB π ↔ ∀ i : Fin n, i.val < k → π (τA i) ≠ τB i := by
  unfold waitTime
  refine (Finset.lt_min'_iff _ _).trans ?_
  simp only [mem_union, mem_image, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h i hi heq
    have := h (i.val + 1) (Or.inl ⟨i, heq, rfl⟩)
    omega
  · rintro h y (⟨i, heq, rfl⟩ | rfl)
    · by_contra hc
      exact h i (by omega) heq
    · omega

lemma waitTime_eq_sum {n : ℕ} (τA τB : Tactic n) (π : Equiv.Perm (Fin n)) :
    (waitTime τA τB π : ℝ) =
      ∑ k ∈ range (n + 1), (if k < waitTime τA τB π then (1:ℝ) else 0) := by
  rw [Finset.sum_boole]
  have hle := waitTime_le τA τB π
  have : (range (n + 1)).filter (fun k => k < waitTime τA τB π) = range (waitTime τA τB π) := by
    ext k; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

lemma prob_lt_wait_ge {n : ℕ} (τA τB : Tactic n) (k : ℕ) (hk : k ≤ n) :
    1 - (k:ℝ) / n ≤ avgPerm n (fun π => if k < waitTime τA τB π then 1 else 0) ∧
      noRdvProb τA τB ≤ avgPerm n (fun π => if k < waitTime τA τB π then 1 else 0) := by
  constructor
  · have hpt : ∀ π : Equiv.Perm (Fin n),
        1 - ∑ i ∈ univ.filter (fun i : Fin n => i.val < k),
          (if π (τA i) = τB i then (1:ℝ) else 0) ≤
        (if k < waitTime τA τB π then 1 else 0) := by
      intro π
      by_cases h : ∀ i : Fin n, i.val < k → π (τA i) ≠ τB i
      · rw [if_pos ((lt_waitTime_iff τA τB π k hk).2 h)]
        have : ∑ i ∈ univ.filter (fun i : Fin n => i.val < k),
            (if π (τA i) = τB i then (1:ℝ) else 0) = 0 := by
          apply Finset.sum_eq_zero; intro i hi
          simp only [mem_filter, mem_univ, true_and] at hi
          rw [if_neg (h i hi)]
        linarith
      · push Not at h
        obtain ⟨i, hi, heq⟩ := h
        have h1 : (1:ℝ) ≤ ∑ i ∈ univ.filter (fun i : Fin n => i.val < k),
            (if π (τA i) = τB i then (1:ℝ) else 0) := by
          have := Finset.single_le_sum (f := fun i => if π (τA i) = τB i then (1:ℝ) else 0)
            (fun j _ => by positivity) (show i ∈ univ.filter (fun i : Fin n => i.val < k) by
              simp [hi])
          simpa [heq] using this
        have h2 : (0:ℝ) ≤ (if k < waitTime τA τB π then 1 else 0) := by positivity
        linarith
    have := avgPerm_mono n hpt
    rw [avgPerm_sub, avgPerm_const, avgPerm_sum] at this
    simp only [prob_eval, Finset.sum_const, Fin.card_filter_val_lt, nsmul_eq_mul,
      min_eq_right hk] at this
    convert this using 2
    ring
  · unfold noRdvProb
    apply avgPerm_mono; intro π
    split_ifs with h1 h2 <;> try norm_num
    exact h2 ((lt_waitTime_iff τA τB π k hk).2 fun i _ => h1 i)

lemma W_eq_sum {n : ℕ} (τA τB : Tactic n) :
    W τA τB = ∑ k ∈ range (n + 1),
      avgPerm n (fun π => if k < waitTime τA τB π then (1:ℝ) else 0) := by
  unfold W
  simp only [waitTime_eq_sum]
  rw [avgPerm_sum]

lemma W_ge (n : ℕ) (τA τB : Tactic n) : ((n:ℝ) + 1) / 2 ≤ W τA τB := by
  rw [W_eq_sum]
  have h : ∑ k ∈ range (n + 1), (1 - (k:ℝ) / n) ≤ ∑ k ∈ range (n + 1),
      avgPerm n (fun π => if k < waitTime τA τB π then (1:ℝ) else 0) :=
    Finset.sum_le_sum fun k hk => (prob_lt_wait_ge τA τB k (by
      simp at hk; omega)).1
  refine le_trans ?_ h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have hnR : (0:ℝ) < n := by exact_mod_cast hn
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    have hs : ∑ k ∈ range (n + 1), (k:ℝ) = n * (n + 1) / 2 := by
      have := Finset.sum_range_id_mul_two (n + 1)
      simp only [Nat.add_sub_cancel] at this
      have h' : ((∑ k ∈ range (n + 1), k : ℕ) : ℝ) * 2 = ((n + 1) * n : ℕ) := by
        exact_mod_cast this
      push_cast at h'
      linarith
    rw [hs]; simp
    field_simp
    ring_nf; nlinarith

end RdvCore

namespace RdvCore
open RendezvousKn.Sym Finset

lemma matchCount_eq_sum {n : ℕ} (F : Finset (Fin n × Fin n)) (π : Equiv.Perm (Fin n)) :
    (matchCount F π : ℝ) = ∑ f ∈ F, matchInd f π := by
  unfold matchCount matchInd
  rw [Finset.sum_boole]

lemma avg_matchInd {n : ℕ} (f : Fin n × Fin n) : avgPerm n (matchInd f) = 1 / n := by
  unfold matchInd; exact prob_eval n f.1 f.2

lemma mean_X {n : ℕ} (F : Finset (Fin n × Fin n)) :
    avgPerm n (fun π => (matchCount F π : ℝ)) = F.card / n := by
  simp only [matchCount_eq_sum]
  rw [avgPerm_sum]
  simp only [avg_matchInd, Finset.sum_const, nsmul_eq_mul]
  ring

lemma probXZero_ge_markov {n : ℕ} (F : Finset (Fin n × Fin n)) :
    1 - F.card / (n:ℝ) ≤ probXZero F := by
  unfold probXZero
  rw [← mean_X, ← avgPerm_const n 1, ← avgPerm_sub, avgPerm_const]
  apply avgPerm_mono; intro π
  split_ifs with h
  · simp [h]
  · have : (1:ℝ) ≤ matchCount F π := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h
    linarith

lemma card_pairSet_le {n : ℕ} (τA τB : Tactic n) : (pairSet τA τB).card ≤ n := by
  unfold pairSet
  calc _ ≤ (univ : Finset (Fin n)).card := card_image_le
    _ = n := by simp

end RdvCore

namespace RdvCore
open RendezvousKn.Sym Finset

lemma avg_cs (n : ℕ) (f g : Equiv.Perm (Fin n) → ℝ) :
    (avgPerm n (fun π => f π * g π)) ^ 2 ≤
      avgPerm n (fun π => f π ^ 2) * avgPerm n (fun π => g π ^ 2) := by
  unfold avgPerm
  have hN := card_perm_pos n
  have := Finset.sum_mul_sq_le_sq_mul_sq univ f g
  rw [div_pow, div_mul_div_comm, ← sq]
  exact div_le_div_of_nonneg_right this (by positivity)

end RdvCore

open RendezvousKn.Sym Finset

theorem solution (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n) (α : ℝ) (hα : 0 < α)
    (hm : (1 - Real.sqrt (α / 2)) * n ≤ ((pairSet τA τB).card : ℝ))
    (hvar : α ≤ varX (pairSet τA τB)) :
    α ^ 2 / 128 ≤ probXZero (pairSet τA τB) := by
  have h4 := assertion_2 n hn τA τB
  set F := pairSet τA τB with hFdef
  have hmn : F.card ≤ n := RdvCore.card_pairSet_le τA τB
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  set μ : ℝ := (F.card : ℝ) / n with hμ
  have hμ0 : 0 ≤ μ := by positivity
  have hμ1 : μ ≤ 1 := by rw [hμ, div_le_one (by linarith)]; exact_mod_cast hmn
  have hmean : avgPerm n (fun π => (matchCount F π : ℝ)) = μ := RdvCore.mean_X F
  -- Z = (X - μ)^2
  set Z : Equiv.Perm (Fin n) → ℝ := fun π => ((matchCount F π : ℝ) - μ) ^ 2 with hZ
  have hEZ : avgPerm n Z = varX F := by
    unfold varX
    have : Z = fun π => ((matchCount F π : ℝ) ^ 2 - (2 * μ) * (matchCount F π : ℝ)) + μ ^ 2 := by
      funext π; simp only [hZ]; ring
    rw [this, RdvCore.avgPerm_add, RdvCore.avgPerm_sub, RdvCore.avgPerm_const_mul,
      RdvCore.avgPerm_const, hmean]
    ring
  have hEZ2 : avgPerm n (fun π => Z π ^ 2) ≤ 16 := by
    have hpt : ∀ π, Z π ^ 2 ≤ (matchCount F π : ℝ) ^ 4 + 1 := by
      intro π
      simp only [hZ]
      have hx : (0:ℝ) ≤ matchCount F π := by positivity
      rcases le_total μ (matchCount F π : ℝ) with h | h
      · have h1 : 0 ≤ (matchCount F π : ℝ) - μ := by linarith
        have h2 : (matchCount F π : ℝ) - μ ≤ matchCount F π := by linarith
        have := pow_le_pow_left₀ h1 h2 4
        nlinarith [pow_nonneg hx 4]
      · have h1 : 0 ≤ μ - (matchCount F π : ℝ) := by linarith
        have h2 : μ - (matchCount F π : ℝ) ≤ 1 := by linarith
        have := pow_le_pow_left₀ h1 h2 4
        have e : (((matchCount F π : ℝ) - μ) ^ 2) ^ 2 = (μ - (matchCount F π : ℝ)) ^ 4 := by ring
        rw [e]; nlinarith [pow_nonneg hx 4]
    have := RdvCore.avgPerm_mono n hpt
    rw [RdvCore.avgPerm_add, RdvCore.avgPerm_const] at this
    linarith
  -- indicator of Z > α/2
  set I : Equiv.Perm (Fin n) → ℝ := fun π => if α / 2 < Z π then 1 else 0 with hI
  have hZI : avgPerm n Z ≤ α / 2 + avgPerm n (fun π => Z π * I π) := by
    rw [← RdvCore.avgPerm_const n (α / 2), ← RdvCore.avgPerm_add]
    apply RdvCore.avgPerm_mono; intro π
    simp only [hI]
    split_ifs with h
    · have : 0 ≤ Z π := by simp only [hZ]; positivity
      linarith
    · linarith [not_lt.1 h]
  have hcs := RdvCore.avg_cs n Z I
  have hI2 : (fun π => I π ^ 2) = I := by
    funext π; simp only [hI]; split_ifs <;> norm_num
  rw [hI2] at hcs
  have hPI : α ^ 2 / 64 ≤ avgPerm n I := by
    have h1 : α / 2 ≤ avgPerm n (fun π => Z π * I π) := by linarith
    have h2 : (α / 2) ^ 2 ≤ (avgPerm n (fun π => Z π * I π)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have hI0 : 0 ≤ avgPerm n I := RdvCore.avgPerm_nonneg n (fun π => by
      simp only [hI]; split_ifs <;> norm_num)
    nlinarith
  -- I ≤ [X = 0] + [X ≥ 2]
  have hsq : (1 - μ) ^ 2 ≤ α / 2 := by
    have hs : 1 - μ ≤ Real.sqrt (α / 2) := by
      have : (1 - Real.sqrt (α / 2)) ≤ μ := by
        rw [hμ, le_div_iff₀ (by linarith)]; exact hm
      linarith
    have := pow_le_pow_left₀ (by linarith) hs 2
    rwa [Real.sq_sqrt (by positivity)] at this
  set P0 : ℝ := avgPerm n (fun π => if matchCount F π = 0 then 1 else 0)
  set P1 : ℝ := avgPerm n (fun π => if matchCount F π = 1 then 1 else 0)
  set P2 : ℝ := avgPerm n (fun π => if 2 ≤ matchCount F π then 1 else 0)
  have hIle : avgPerm n I ≤ P0 + P2 := by
    rw [← RdvCore.avgPerm_add]
    apply RdvCore.avgPerm_mono; intro π
    simp only [hI]
    split_ifs with h a b c <;> norm_num
    · -- Z > α/2 but X ≠ 0 and X < 2, so X = 1
      have h1 : matchCount F π = 1 := by omega
      simp only [hZ, h1, Nat.cast_one] at h
      linarith
    all_goals omega
  have hsum : P0 + P1 + P2 = 1 := by
    have e1 : P0 + P1 + P2 = avgPerm n (fun π => ((if matchCount F π = 0 then (1:ℝ) else 0) +
        (if matchCount F π = 1 then (1:ℝ) else 0)) + (if 2 ≤ matchCount F π then (1:ℝ) else 0)) := by
      rw [RdvCore.avgPerm_add, RdvCore.avgPerm_add]
    have e2 : (fun π => ((if matchCount F π = 0 then (1:ℝ) else 0) +
        (if matchCount F π = 1 then (1:ℝ) else 0)) + (if 2 ≤ matchCount F π then (1:ℝ) else 0)) =
        fun _ => (1:ℝ) := by
      funext π
      by_cases h0 : matchCount F π = 0
      · simp [h0]
      · by_cases h1 : matchCount F π = 1
        · simp [h1]
        · have h2 : 2 ≤ matchCount F π := by omega
          simp [h0, h1, h2]
    rw [e1, e2, RdvCore.avgPerm_const]
  have hmom : P1 + 2 * P2 ≤ μ := by
    rw [← hmean, ← RdvCore.avgPerm_const_mul, ← RdvCore.avgPerm_add]
    apply RdvCore.avgPerm_mono; intro π
    by_cases h1 : matchCount F π = 1
    · have : ¬ 2 ≤ matchCount F π := by omega
      simp [h1, this]
    · by_cases h2 : 2 ≤ matchCount F π
      · simp only [h1, h2, if_true, if_false]
        have : (2:ℝ) ≤ matchCount F π := by exact_mod_cast h2
        linarith
      · simp only [h1, h2, if_false]
        have : (0:ℝ) ≤ matchCount F π := by positivity
        linarith
  have : P2 ≤ P0 := by linarith
  have hP0 : probXZero F = P0 := rfl
  rw [hP0]
  linarith
