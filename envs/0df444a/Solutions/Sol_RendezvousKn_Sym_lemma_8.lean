-- Prove2me | solution 1 for RendezvousKn.Sym.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:30:14.979722+00:00
-- url     : https://prove2.me/submissions/b73750ab-95a0-45f2-88f0-fc586fcec7d9

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model
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

end RdvCore

namespace RdvCore
open RendezvousKn.Sym Finset

lemma ite_mul_ite (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1:ℝ) else 0) * (if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma avg_ind_false {n : ℕ} (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P]
    (h : ∀ π, ¬ P π) : avgPerm n (fun π => if P π then (1:ℝ) else 0) = 0 := by
  simp only [h, if_false]; exact avgPerm_const n 0

lemma avg_ind_nonneg {n : ℕ} (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] :
    0 ≤ avgPerm n (fun π => if P π then (1:ℝ) else 0) :=
  avgPerm_nonneg n (fun π => by positivity)

lemma step {n : ℕ} (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] (J : Finset (Fin n))
    (i j : Fin n) (hj : j ∉ J) (hP : ∀ π, P π → π i ∉ J)
    (hinv : ∀ a b, a ∉ J → b ∉ J → ∀ π, (P (Equiv.swap a b * π) ↔ P π)) :
    avgPerm n (fun π => if P π ∧ π i = j then (1:ℝ) else 0) * ((n:ℝ) - J.card) =
      avgPerm n (fun π => if P π then (1:ℝ) else 0) ∧ (J.card : ℝ) < n := by
  have hsame : ∀ j' ∈ Jᶜ, avgPerm n (fun π => if P π ∧ π i = j' then (1:ℝ) else 0) =
      avgPerm n (fun π => if P π ∧ π i = j then (1:ℝ) else 0) := by
    intro j' hj'
    rw [mem_compl] at hj'
    rw [← avgPerm_mulLeft n (Equiv.swap j j') (fun π => if P π ∧ π i = j' then (1:ℝ) else 0)]
    congr 1; funext π
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right,
      hinv j j' hj hj' π]
  have htot : ∑ j' ∈ Jᶜ, avgPerm n (fun π => if P π ∧ π i = j' then (1:ℝ) else 0) =
      avgPerm n (fun π => if P π then (1:ℝ) else 0) := by
    rw [← avgPerm_sum]
    congr 1; funext π
    by_cases h : P π
    · simp only [h, true_and, if_true]
      rw [Finset.sum_ite_eq]
      simp [hP π h]
    · simp [h]
  rw [Finset.sum_congr rfl hsame, Finset.sum_const, nsmul_eq_mul] at htot
  have hc : Jᶜ.card + J.card = n := by
    rw [Finset.card_compl, Fintype.card_fin]; have := Finset.card_le_univ J
    simp at this; omega
  have hpos : 1 ≤ Jᶜ.card := Finset.card_pos.2 ⟨j, mem_compl.2 hj⟩
  have hcR : ((Jᶜ.card : ℕ) : ℝ) = n - J.card := by
    have : ((Jᶜ.card + J.card : ℕ) : ℝ) = n := by exact_mod_cast hc
    push_cast at this; linarith
  refine ⟨by rw [← htot, hcR]; ring, ?_⟩
  have : (1:ℝ) ≤ Jᶜ.card := by exact_mod_cast hpos
  linarith

/-- Two indicator events of distinct non-disjoint pairs cannot hold together. -/
lemma not_both {n : ℕ} (e f : Fin n × Fin n) (hef : e ≠ f) (hnd : ¬ PairsDisjoint e f)
    (π : Equiv.Perm (Fin n)) : ¬ (π e.1 = e.2 ∧ π f.1 = f.2) := by
  rintro ⟨h1, h2⟩
  unfold PairsDisjoint at hnd
  apply hef
  by_cases h : e.1 = f.1
  · exact Prod.ext h (by rw [← h1, ← h2, h])
  · have : e.2 = f.2 := by
      by_contra h'; exact hnd ⟨h, h'⟩
    exact absurd (π.injective (h1.trans (this.trans h2.symm))) h

lemma avg_pair_disj {n : ℕ} (e f : Fin n × Fin n) (hd : PairsDisjoint e f) :
    avgPerm n (fun π => if π e.1 = e.2 ∧ π f.1 = f.2 then (1:ℝ) else 0) * ((n:ℝ) - 1) =
      1 / n ∧ (1:ℝ) < n := by
  have := step (fun π => π e.1 = e.2) {e.2} f.1 f.2 (by simpa [eq_comm] using hd.2)
    (by
      intro π h hm
      rw [mem_singleton, ← h] at hm
      exact hd.1 (π.injective hm).symm)
    (by
      intro a b ha hb π
      rw [mem_singleton] at ha hb
      simp only [Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)])
  rw [card_singleton, Nat.cast_one, prob_eval] at this
  exact this

lemma avg_triple_disj {n : ℕ} (e f g : Fin n × Fin n) (hef : PairsDisjoint e f)
    (heg : PairsDisjoint e g) (hfg : PairsDisjoint f g) :
    avgPerm n (fun π => if (π e.1 = e.2 ∧ π f.1 = f.2) ∧ π g.1 = g.2 then (1:ℝ) else 0) *
      ((n:ℝ) - 2) =
      avgPerm n (fun π => if π e.1 = e.2 ∧ π f.1 = f.2 then (1:ℝ) else 0) ∧ (2:ℝ) < n := by
  have hJ : ({e.2, f.2} : Finset (Fin n)).card = 2 := card_pair hef.2
  have := step (fun π => π e.1 = e.2 ∧ π f.1 = f.2) {e.2, f.2} g.1 g.2
    (by simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm heg.2, Ne.symm hfg.2⟩)
    (by
      rintro π ⟨h1, h2⟩ hm
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with hm | hm
      · rw [← h1] at hm; exact heg.1 (π.injective hm).symm
      · rw [← h2] at hm; exact hfg.1 (π.injective hm).symm)
    (by
      intro a b ha hb π
      simp only [mem_insert, mem_singleton, not_or] at ha hb
      simp only [Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha.1) (Ne.symm hb.1),
        Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha.2) (Ne.symm hb.2)])
  rw [hJ] at this
  exact_mod_cast this

lemma avg_quad_disj {n : ℕ} (e f g h : Fin n × Fin n) (hef : PairsDisjoint e f)
    (heg : PairsDisjoint e g) (hfg : PairsDisjoint f g) (heh : PairsDisjoint e h)
    (hfh : PairsDisjoint f h) (hgh : PairsDisjoint g h) :
    avgPerm n (fun π => if ((π e.1 = e.2 ∧ π f.1 = f.2) ∧ π g.1 = g.2) ∧ π h.1 = h.2
      then (1:ℝ) else 0) * ((n:ℝ) - 3) =
      avgPerm n (fun π => if (π e.1 = e.2 ∧ π f.1 = f.2) ∧ π g.1 = g.2 then (1:ℝ) else 0) ∧
        (3:ℝ) < n := by
  have hJ : ({e.2, f.2, g.2} : Finset (Fin n)).card = 3 := by
    rw [card_insert_of_notMem, card_pair hfg.2]
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨hef.2, heg.2⟩
  have := step (fun π => (π e.1 = e.2 ∧ π f.1 = f.2) ∧ π g.1 = g.2) {e.2, f.2, g.2} h.1 h.2
    (by simp only [mem_insert, mem_singleton, not_or]
        exact ⟨Ne.symm heh.2, Ne.symm hfh.2, Ne.symm hgh.2⟩)
    (by
      rintro π ⟨⟨h1, h2⟩, h3⟩ hm
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with hm | hm | hm
      · rw [← h1] at hm; exact heh.1 (π.injective hm).symm
      · rw [← h2] at hm; exact hfh.1 (π.injective hm).symm
      · rw [← h3] at hm; exact hgh.1 (π.injective hm).symm)
    (by
      intro a b ha hb π
      simp only [mem_insert, mem_singleton, not_or] at ha hb
      simp only [Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha.1) (Ne.symm hb.1),
        Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha.2.1) (Ne.symm hb.2.1),
        Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha.2.2) (Ne.symm hb.2.2)])
  rw [hJ] at this
  exact_mod_cast this

end RdvCore

namespace RdvCore
open RendezvousKn.Sym Finset

lemma mi2 {n : ℕ} (e f : Fin n × Fin n) (π : Equiv.Perm (Fin n)) :
    matchInd e π * matchInd f π = if π e.1 = e.2 ∧ π f.1 = f.2 then 1 else 0 := by
  unfold matchInd; exact ite_mul_ite _ _

lemma mi3 {n : ℕ} (e f g : Fin n × Fin n) (π : Equiv.Perm (Fin n)) :
    matchInd e π * matchInd f π * matchInd g π =
      if (π e.1 = e.2 ∧ π f.1 = f.2) ∧ π g.1 = g.2 then 1 else 0 := by
  rw [mi2]; unfold matchInd; exact ite_mul_ite _ _

lemma mi4 {n : ℕ} (e f g h : Fin n × Fin n) (π : Equiv.Perm (Fin n)) :
    matchInd e π * matchInd f π * matchInd g π * matchInd h π =
      if ((π e.1 = e.2 ∧ π f.1 = f.2) ∧ π g.1 = g.2) ∧ π h.1 = h.2 then 1 else 0 := by
  rw [mi3]; unfold matchInd; exact ite_mul_ite _ _

lemma pair_val {n : ℕ} (e f : Fin n × Fin n) (hd : PairsDisjoint e f) :
    avgPerm n (fun π => matchInd e π * matchInd f π) = 1 / ((n:ℝ) * (n - 1)) := by
  simp only [mi2]
  obtain ⟨h, hn⟩ := avg_pair_disj e f hd
  rw [eq_div_iff (by nlinarith)]
  field_simp at h ⊢
  linarith

lemma triple_val {n : ℕ} (e f g : Fin n × Fin n) (hef : PairsDisjoint e f)
    (heg : PairsDisjoint e g) (hfg : PairsDisjoint f g) :
    avgPerm n (fun π => matchInd e π * matchInd f π * matchInd g π) =
      1 / ((n:ℝ) * (n - 1) * (n - 2)) := by
  have h2 := pair_val e f hef
  simp only [mi2] at h2
  simp only [mi3]
  obtain ⟨h, hn⟩ := avg_triple_disj e f g hef heg hfg
  rw [h2] at h
  rw [eq_div_iff (by have : (0:ℝ) < n - 2 := by linarith
                     have : (0:ℝ) < n - 1 := by linarith
                     positivity)]
  have : (0:ℝ) < n - 1 := by linarith
  field_simp at h
  nlinarith [h]

lemma quad_val {n : ℕ} (e f g h : Fin n × Fin n) (hef : PairsDisjoint e f)
    (heg : PairsDisjoint e g) (hfg : PairsDisjoint f g) (heh : PairsDisjoint e h)
    (hfh : PairsDisjoint f h) (hgh : PairsDisjoint g h) :
    avgPerm n (fun π => matchInd e π * matchInd f π * matchInd g π * matchInd h π) =
      1 / ((n:ℝ) * (n - 1) * (n - 2) * (n - 3)) := by
  have h3 := triple_val e f g hef heg hfg
  simp only [mi3] at h3
  simp only [mi4]
  obtain ⟨hh, hn⟩ := avg_quad_disj e f g h hef heg hfg heh hfh hgh
  rw [h3] at hh
  have : (0:ℝ) < n - 3 := by linarith
  have : (0:ℝ) < n - 2 := by linarith
  have : (0:ℝ) < n - 1 := by linarith
  rw [eq_div_iff (by positivity)]
  field_simp at hh
  nlinarith [hh]

end RdvCore

namespace RdvCore
open RendezvousKn.Sym Finset

lemma pd_symm {n : ℕ} {e f : Fin n × Fin n} (h : PairsDisjoint e f) : PairsDisjoint f e :=
  ⟨Ne.symm h.1, Ne.symm h.2⟩

lemma pd_ne {n : ℕ} {e f : Fin n × Fin n} (h : PairsDisjoint e f) : e ≠ f := by
  rintro rfl; exact h.1 rfl

lemma ordered_count {n : ℕ} (F : Finset (Fin n × Fin n)) :
    ((F ×ˢ F).filter (fun p => PairsDisjoint p.1 p.2)).card = 2 * disjointPairCount F := by
  unfold disjointPairCount
  set S := (F.powersetCard 2).filter fun s => ∀ e ∈ s, ∀ f ∈ s, e ≠ f → PairsDisjoint e f
  have hmaps : ∀ p ∈ (F ×ˢ F).filter (fun p => PairsDisjoint p.1 p.2),
      (fun p : (Fin n × Fin n) × (Fin n × Fin n) => ({p.1, p.2} : Finset (Fin n × Fin n))) p ∈ S := by
    rintro ⟨e, f⟩ hp
    simp only [mem_filter, mem_product] at hp
    obtain ⟨⟨he, hf⟩, hd⟩ := hp
    simp only [S, mem_filter, mem_powersetCard]
    refine ⟨⟨?_, card_pair (pd_ne hd)⟩, ?_⟩
    · intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · intro x hx y hy hxy
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hd
      · exact pd_symm hd
      · exact absurd rfl hxy
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' := hs
  simp only [S, mem_filter, mem_powersetCard] at hs'
  obtain ⟨⟨hsub, hcard⟩, hdisj⟩ := hs'
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hcard
  have ha : a ∈ F := hsub (by simp)
  have hb : b ∈ F := hsub (by simp)
  have hdab : PairsDisjoint a b := hdisj a (by simp) b (by simp) hab
  have : ((F ×ˢ F).filter (fun p => PairsDisjoint p.1 p.2)).filter
      (fun p => ({p.1, p.2} : Finset (Fin n × Fin n)) = {a, b}) = {(a, b), (b, a)} := by
    ext ⟨e, f⟩
    simp only [mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨he, hf⟩, hd⟩, heq⟩
      have he' : e ∈ ({a, b} : Finset _) := heq ▸ (by simp)
      have hf' : f ∈ ({a, b} : Finset _) := heq ▸ (by simp)
      simp only [mem_insert, mem_singleton] at he' hf'
      have hne := pd_ne hd
      rcases he' with rfl | rfl <;> rcases hf' with rfl | rfl
      · exact absurd rfl hne
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
      · exact absurd rfl hne
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨⟨ha, hb⟩, hdab⟩, rfl⟩
      · exact ⟨⟨⟨hb, ha⟩, pd_symm hdab⟩, pair_comm _ _⟩
  rw [this, card_pair]
  intro h; simp only [Prod.mk.injEq] at h; exact hab h.1

lemma X_sq_eq {n : ℕ} (F : Finset (Fin n × Fin n)) :
    avgPerm n (fun π => (matchCount F π : ℝ) ^ 2) =
      ∑ e ∈ F, ∑ f ∈ F, avgPerm n (fun π => matchInd e π * matchInd f π) := by
  simp only [matchCount_eq_sum, sq, Finset.sum_mul_sum]
  rw [avgPerm_sum]
  apply Finset.sum_congr rfl; intro e _
  rw [avgPerm_sum]

lemma mi_nonneg {n : ℕ} (e : Fin n × Fin n) (π : Equiv.Perm (Fin n)) : 0 ≤ matchInd e π := by
  unfold matchInd; split_ifs <;> norm_num

lemma mi_sq {n : ℕ} (e : Fin n × Fin n) (π : Equiv.Perm (Fin n)) :
    matchInd e π * matchInd e π = matchInd e π := by
  unfold matchInd; split_ifs <;> norm_num

lemma card_pairSet_le {n : ℕ} (τA τB : Tactic n) : (pairSet τA τB).card ≤ n := by
  unfold pairSet
  calc _ ≤ (univ : Finset (Fin n)).card := card_image_le
    _ = n := by simp

lemma var_ge {n : ℕ} (hn : 2 ≤ n) (F : Finset (Fin n × Fin n)) (hm : F.card ≤ n) :
    (F.card : ℝ) / n - (F.card / n) ^ 2 + 2 * disjointPairCount F / ((n:ℝ) * (n - 1))
      ≤ varX F := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < n * (n - 1) := by nlinarith
  unfold varX
  rw [mean_X, X_sq_eq]
  have hrow : ∀ e ∈ F, 1 / (n:ℝ) + ((F.filter fun f => PairsDisjoint e f).card : ℝ) *
      (1 / ((n:ℝ) * (n - 1))) ≤ ∑ f ∈ F, avgPerm n (fun π => matchInd e π * matchInd f π) := by
    intro e he
    have hnot : e ∉ F.filter fun f => PairsDisjoint e f := by
      simp only [mem_filter, not_and]; intro _ h; exact h.1 rfl
    have hsub : insert e (F.filter fun f => PairsDisjoint e f) ⊆ F := by
      intro x hx; simp only [mem_insert, mem_filter] at hx
      rcases hx with rfl | hx
      · exact he
      · exact hx.1
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun f => avgPerm n (fun π => matchInd e π * matchInd f π))
      (fun f _ _ => avgPerm_nonneg n (fun π => mul_nonneg (mi_nonneg e π) (mi_nonneg f π)))
    rw [Finset.sum_insert hnot] at h1
    have h2 : ∑ f ∈ F.filter (fun f => PairsDisjoint e f),
        avgPerm n (fun π => matchInd e π * matchInd f π) =
        ((F.filter fun f => PairsDisjoint e f).card : ℝ) * (1 / ((n:ℝ) * (n - 1))) := by
      rw [Finset.sum_congr rfl (g := fun _ => 1 / ((n:ℝ) * (n - 1)))]
      · rw [Finset.sum_const, nsmul_eq_mul]
      · intro f hf; simp only [mem_filter] at hf; exact pair_val e f hf.2
    have h3 : avgPerm n (fun π => matchInd e π * matchInd e π) = 1 / n := by
      simp only [mi_sq]; exact avg_matchInd e
    linarith
  have hsum := Finset.sum_le_sum hrow
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul] at hsum
  have hO : (∑ e ∈ F, ((F.filter fun f => PairsDisjoint e f).card : ℝ)) =
      2 * (disjointPairCount F : ℝ) := by
    have := ordered_count F
    rw [Finset.card_filter, Finset.sum_product] at this
    simp only [← Finset.card_filter] at this
    exact_mod_cast this
  rw [hO] at hsum
  have : (F.card : ℝ) * (1 / n) + 2 * (disjointPairCount F : ℝ) * (1 / ((n:ℝ) * (n - 1))) =
      (F.card : ℝ) / n + 2 * disjointPairCount F / ((n:ℝ) * (n - 1)) := by ring
  linarith

end RdvCore

open RendezvousKn.Sym

theorem solution (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n) (α : ℝ) (hα : 0 < α)
    (hpairs : α * (n.choose 2 : ℝ) ≤ (disjointPairCount (pairSet τA τB) : ℝ)) :
    α ≤ varX (pairSet τA τB) := by
  have hm := RdvCore.card_pairSet_le τA τB
  have h := RdvCore.var_ge hn (pairSet τA τB) hm
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hmR : ((pairSet τA τB).card : ℝ) ≤ n := by exact_mod_cast hm
  have hch : (n.choose 2 : ℝ) = n * (n - 1) / 2 := by
    rw [Nat.cast_choose_two]
  have hden : (0:ℝ) < n * (n - 1) := by nlinarith
  have h1 : α ≤ 2 * (disjointPairCount (pairSet τA τB) : ℝ) / ((n:ℝ) * (n - 1)) := by
    rw [le_div_iff₀ hden]; rw [hch] at hpairs; linarith
  have h2 : 0 ≤ ((pairSet τA τB).card : ℝ) / n - (((pairSet τA τB).card : ℝ) / n) ^ 2 := by
    have h0 : 0 ≤ ((pairSet τA τB).card : ℝ) / n := by positivity
    have h1' : ((pairSet τA τB).card : ℝ) / n ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hmR
    nlinarith
  linarith
