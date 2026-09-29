-- Prove2me | solution 1 for TSPHeuristics.Insertion.optimal_ge_two_mul_sum_tail
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:04:10.464701+00:00
-- url     : https://prove2.me/submissions/ee6175f2-ec04-4054-81c1-52338903604a

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

open TSPHeuristics.Shared

/-- Length of the open path visiting the entries of a list in order. -/
def aux_ogt_pathLen {n : ℕ} (d : Fin n → Fin n → ℝ) : List (Fin n) → ℝ
  | [] => 0
  | [_] => 0
  | x :: y :: r => d x y + aux_ogt_pathLen d (y :: r)

lemma aux_ogt_zip_eq_path {n : ℕ} (d : Fin n → Fin n → ℝ) (b : Fin n) :
    ∀ (a : Fin n) (l : List (Fin n)),
      (List.zipWith d (a :: l) (l ++ [b])).sum = aux_ogt_pathLen d (a :: (l ++ [b]))
  | a, [] => by simp [aux_ogt_pathLen]
  | a, x :: l => by
      simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
      rw [← List.cons_append, aux_ogt_zip_eq_path d b x l]
      rfl

lemma aux_ogt_cycle_eq_path {n : ℕ} (d : Fin n → Fin n → ℝ) (a : Fin n) (l : List (Fin n)) :
    cycleLength d (a :: l) = aux_ogt_pathLen d (a :: (l ++ [a])) := by
  unfold cycleLength
  rw [List.rotate_cons_succ, List.rotate_zero]
  exact aux_ogt_zip_eq_path d a a l

lemma aux_ogt_path_step {n : ℕ} {d : Fin n → Fin n → ℝ} (hd : IsTSPDist d) (a x : Fin n) :
    ∀ L : List (Fin n), aux_ogt_pathLen d (a :: L) ≤ d a x + aux_ogt_pathLen d (x :: L)
  | [] => by simp [aux_ogt_pathLen]; exact hd.nonneg a x
  | y :: r => by
      simp only [aux_ogt_pathLen]
      linarith [hd.triangle a x y]

lemma aux_ogt_path_filter {n : ℕ} {d : Fin n → Fin n → ℝ} (hd : IsTSPDist d)
    (P : Fin n → Bool) :
    ∀ (L : List (Fin n)) (a : Fin n), aux_ogt_pathLen d (a :: L.filter P) ≤ aux_ogt_pathLen d (a :: L)
  | [], a => le_refl _
  | x :: L, a => by
      by_cases hx : P x = true
      · rw [List.filter_cons_of_pos hx]
        show d a x + aux_ogt_pathLen d (x :: L.filter P) ≤ d a x + aux_ogt_pathLen d (x :: L)
        linarith [aux_ogt_path_filter hd P L x]
      · rw [List.filter_cons_of_neg hx]
        show aux_ogt_pathLen d (a :: L.filter P) ≤ d a x + aux_ogt_pathLen d (x :: L)
        linarith [aux_ogt_path_filter hd P L a, aux_ogt_path_step hd a x L]

lemma aux_ogt_cycle_filter {n : ℕ} {d : Fin n → Fin n → ℝ} (hd : IsTSPDist d)
    (P : Fin n → Bool) (a : Fin n) (l : List (Fin n)) (ha : P a = true) :
    cycleLength d ((a :: l).filter P) ≤ cycleLength d (a :: l) := by
  rw [List.filter_cons_of_pos ha, aux_ogt_cycle_eq_path, aux_ogt_cycle_eq_path]
  have : l.filter P ++ [a] = (l ++ [a]).filter P := by simp [List.filter_append, ha]
  rw [this]
  exact aux_ogt_path_filter hd P _ a

lemma aux_ogt_cycle_ofFn {n m : ℕ} (d : Fin n → Fin n → ℝ) (f : Fin m → Fin n) :
    cycleLength d (List.ofFn f) = ∑ i, d (f i) (f (finRotate m i)) := by
  unfold cycleLength
  have h1 : (List.ofFn f).rotate 1 = List.ofFn (fun i => f (finRotate m i)) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_rotate, List.getElem_ofFn, List.length_ofFn]
      congr 1
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at h1; omega⟩
      rw [finRotate_apply]
      ext
      simp [Fin.val_add]
  rw [h1]
  have h2 : List.zipWith d (List.ofFn f) (List.ofFn (fun i => f (finRotate m i)))
      = List.ofFn (fun i => d (f i) (f (finRotate m i))) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  rw [h2, List.sum_ofFn]

lemma aux_ogt_fin_ge {n m : ℕ} (hm : 2 ≤ m) (d : Fin n → Fin n → ℝ) (ψ : Fin n → ℝ)
    (hψ : ∀ u v, u ≠ v → ψ u + ψ v ≤ d u v) (f : Fin m → Fin n) (hf : Function.Injective f) :
    2 * ∑ i, ψ (f i) ≤ ∑ i, d (f i) (f (finRotate m i)) := by
  have h2 : ∑ i, ψ (f (finRotate m i)) = ∑ i, ψ (f i) :=
    Equiv.sum_comp (finRotate m) (fun i => ψ (f i))
  have hrot : ∀ i : Fin m, finRotate m i ≠ i := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    intro i h
    rw [finRotate_apply] at h
    simp at h
  have key : ∀ i, ψ (f i) + ψ (f (finRotate m i)) ≤ d (f i) (f (finRotate m i)) := by
    intro i
    exact hψ _ _ (hf.ne (hrot i).symm)
  calc 2 * ∑ i, ψ (f i) = ∑ i, (ψ (f i) + ψ (f (finRotate m i))) := by
        rw [Finset.sum_add_distrib, h2]; ring
    _ ≤ _ := Finset.sum_le_sum (fun i _ => key i)

lemma aux_ogt_list_ge {n : ℕ} (d : Fin n → Fin n → ℝ) (ψ : Fin n → ℝ)
    (hψ : ∀ u v, u ≠ v → ψ u + ψ v ≤ d u v) (L : List (Fin n)) (hnd : L.Nodup)
    (hlen : 2 ≤ L.length) : 2 * (L.map ψ).sum ≤ cycleLength d L := by
  have e : List.ofFn (fun i : Fin L.length => L[i]) = L := List.ofFn_getElem
  have hinj : Function.Injective (fun i : Fin L.length => L[i]) := by
    intro i j h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 h)
  have := aux_ogt_fin_ge hlen d ψ hψ _ hinj
  have hc := aux_ogt_cycle_ofFn d (fun i : Fin L.length => L[i])
  rw [e] at hc
  rw [hc]
  calc 2 * (L.map ψ).sum = 2 * ∑ i : Fin L.length, ψ L[i] := by
        congr 1
        conv_lhs => rw [← e]
        rw [List.map_ofFn, List.sum_ofFn]
        rfl
    _ ≤ _ := this

end TSPHeuristics.Insertion

open TSPHeuristics.Insertion
open TSPHeuristics.Shared

theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (l : Fin n → ℝ) (hl : Antitone l)
    (ha : ∀ p q, p ≠ q → min (l p) (l q) ≤ d p q) :
    ∀ k : ℕ, 1 ≤ k → k ≤ n →
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val ∧ i.val < min (2 * k) n), l i
        ≤ TSPHeuristics.Shared.optimal d := by
  intro k hk1 hkn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  set m := min (2 * k) (n' + 1) with hm
  set B := Finset.univ.filter (fun i : Fin (n' + 1) => k ≤ i.val ∧ i.val < m) with hB
  set L := l ⟨k - 1, by omega⟩ with hL
  have hopt_nonneg : 0 ≤ optimal d := by
    unfold optimal
    apply Finset.le_inf'
    intro τ _
    unfold tourLength
    exact Finset.sum_nonneg (fun _ _ => hd.nonneg _ _)
  by_cases htriv : L < 0 ∨ m ≤ k
  · have : ∑ i ∈ B, l i ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      rw [hB, Finset.mem_filter] at hi
      rcases htriv with h | h
      · have : l i ≤ L := hl (show (⟨k - 1, by omega⟩ : Fin (n' + 1)) ≤ i from by
          rw [Fin.le_def]; simp; omega)
        linarith
      · omega
    linarith
  push Not at htriv
  obtain ⟨hL0, hkm⟩ := htriv
  have hlu : ∀ w : Fin (n' + 1), w.val < k → L ≤ l w := fun w hw =>
    hl (Fin.le_def.2 (by simp; omega))
  have hlu' : ∀ w : Fin (n' + 1), k ≤ w.val → l w ≤ L := fun w hw =>
    hl (Fin.le_def.2 (by simp; omega))
  let ψ : Fin (n' + 1) → ℝ := fun v => if k ≤ v.val then l v - L / 2 else L / 2
  have hψ : ∀ u v, u ≠ v → ψ u + ψ v ≤ d u v := by
    intro u v huv
    refine le_trans ?_ (ha u v huv)
    simp only [ψ]
    split_ifs with h1 h2 h2
    · have := hlu' u h1
      have := hlu' v h2
      rw [le_min_iff]; constructor <;> linarith
    · have : l u ≤ l v := hl (Fin.le_def.2 (by omega))
      rw [le_min_iff]; constructor <;> linarith [hlu v (by omega)]
    · have : l v ≤ l u := hl (Fin.le_def.2 (by omega))
      rw [le_min_iff]; constructor <;> linarith [hlu u (by omega)]
    · rw [le_min_iff]; constructor <;> linarith [hlu u (by omega), hlu v (by omega)]
  set H := Finset.univ.filter (fun v : Fin (n' + 1) => v.val < m) with hH
  have hsum : 2 * ∑ i ∈ B, l i ≤ 2 * ∑ v ∈ H, ψ v := by
    simp only [ψ]
    rw [Finset.sum_ite]
    have hHB : H.filter (fun v : Fin (n' + 1) => k ≤ v.val) = B := by
      ext v; simp [hH, hB]; omega
    rw [hHB]
    set N := H.filter (fun v : Fin (n' + 1) => ¬ k ≤ v.val) with hN
    have hcard : B.card ≤ N.card := by
      apply Finset.card_le_card_of_injOn
        (fun v : Fin (n' + 1) => (⟨v.val - k, by omega⟩ : Fin (n' + 1)))
      · intro v hv
        simp only [hB, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        simp only [hN, hH, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq]
        omega
      · intro v hv w hw hvw
        simp only [hB, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
        simp only [Fin.mk.injEq] at hvw
        ext; omega
    have hcard' : (B.card : ℝ) ≤ N.card := by exact_mod_cast hcard
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    nlinarith
  unfold optimal
  apply Finset.le_inf'
  intro τ _
  set c := τ.symm 0 with hc
  let τ' : Equiv.Perm (Fin (n' + 1)) := (Equiv.addRight c).trans τ
  have hτ'0 : τ' 0 = 0 := by simp [τ', c]
  have htl : tourLength d τ' = tourLength d τ := by
    unfold tourLength
    simp only [τ', Equiv.trans_apply, Equiv.coe_addRight, finRotate_apply]
    have : ∀ x : Fin (n' + 1), x + 1 + c = (x + c) + 1 := fun x => add_right_comm x 1 c
    simp only [this]
    exact Equiv.sum_comp (Equiv.addRight c) (fun x => d (τ x) (τ (x + 1)))
  rw [← htl]
  set T := List.ofFn τ' with hT
  have hTlen : tourLength d τ' = cycleLength d T := by
    rw [hT, aux_ogt_cycle_ofFn]; rfl
  let P : Fin (n' + 1) → Bool := fun v => decide (v.val < m)
  set L' := T.filter P with hL'
  have hshort : cycleLength d L' ≤ cycleLength d T := by
    rw [hL', hT, List.ofFn_succ, hτ'0]
    apply aux_ogt_cycle_filter hd
    simp only [P, Fin.val_zero]
    exact decide_eq_true (by omega)
  have hTnd : T.Nodup := List.nodup_ofFn.2 τ'.injective
  have hL'nd : L'.Nodup := hTnd.filter _
  have hmem : ∀ v, v ∈ L' ↔ v.val < m := by
    intro v
    rw [hL', List.mem_filter, hT, List.mem_ofFn]
    simp only [P, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨τ'.surjective v, h⟩⟩
  have hfin : L'.toFinset = H := by
    ext v; simp [hmem, hH]
  have hlen : 2 ≤ L'.length := by
    rw [← List.toFinset_card_of_nodup hL'nd]
    have h0 : (0 : Fin (n' + 1)) ∈ L'.toFinset := by
      rw [List.mem_toFinset, hmem]; simp; omega
    have hk' : (⟨k, by omega⟩ : Fin (n' + 1)) ∈ L'.toFinset := by
      rw [List.mem_toFinset, hmem]; simp; omega
    calc 2 = ({0, ⟨k, by omega⟩} : Finset (Fin (n' + 1))).card := by
          rw [Finset.card_pair]
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
      _ ≤ _ := Finset.card_le_card (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)
  have hmain := aux_ogt_list_ge d ψ hψ L' hL'nd hlen
  rw [← List.sum_toFinset ψ hL'nd, hfin] at hmain
  linarith
