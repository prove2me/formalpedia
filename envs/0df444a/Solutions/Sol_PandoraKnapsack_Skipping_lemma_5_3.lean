-- Prove2me | solution 1 for PandoraKnapsack.Skipping.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:11:52.047422+00:00
-- url     : https://prove2.me/submissions/0de6d4a6-4cf3-4217-b75c-4fc0bb7aa3c4

import Definitions.Def_PandoraKnapsack_Skipping_Algorithm1

open scoped Classical
open PandoraKnapsack.Skipping

namespace PandoraKnapsack.Skipping
variable {n m T : ℕ}
private abbrev Single (m T : ℕ) := Option (Fin m × Fin (T+1))
private abbrev Entry (n m : ℕ) := Fin n × Fin m × ℕ
private def clip (q : ℕ) (a : Single m T) (s : Fin (T+2)) : ℕ :=
  match a with
  | none => 0
  | some (_, u) => if u.val ≤ q then min q s.val else 0

private lemma order_mem (a : Assignment n m T) (k : Fin n) (j : Fin m) (t : ℕ) :
    (k,j,t) ∈ scanOrder a ↔ ∃ u : Fin (T+1), a k = some (j,u) ∧ u.val = t := by
  simp [scanOrder, retained, Option.map_eq_some_iff, Prod.ext_iff]

private lemma order_sorted (a : Assignment n m T) :
    (scanOrder a).Pairwise (fun e f => e.2.2 ≤ f.2.2) := by
  let cmp (e f : Entry n m) := decide (e.2.2 < f.2.2 ∨ (e.2.2 = f.2.2 ∧ e.1 ≤ f.1))
  have htrans (x y z : Entry n m) : cmp x y → cmp y z → cmp x z := by simp [cmp]; omega
  have htotal (x y : Entry n m) : cmp x y || cmp y x := by simp [cmp]; omega
  exact (List.pairwise_mergeSort htrans htotal (retained a)).imp (by simp [cmp]; omega)

private lemma order_distinct (a : Assignment n m T) :
    ((scanOrder a).map Prod.fst).Nodup := by
  apply ((List.mergeSort_perm (retained a) _).map Prod.fst).nodup_iff.mpr
  rw [List.Nodup, List.pairwise_map, retained, List.pairwise_filterMap]
  apply (List.nodup_finRange n).imp
  intro i k hik u hu v hv
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hu
  obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hv
  exact hik

private lemma scan_bound (ω : Outcome n m T) (i : Fin n) (j : Fin m) (t : Fin (T+1))
    (q : ℕ) (htq : t.val ≤ q) (hsome : ω.1 i = some (j,t)) :
    min q (predecessorLoad ω i) ≤
      ∑ k ∈ Finset.univ.erase i, clip q (ω.1 k) (ω.2 k) := by
  let L := scanOrder ω.1
  have general (l : List (Entry n m)) (S : ℕ) (U : Finset (Fin n))
      (hs : l.Pairwise (fun e f => e.2.2 ≤ f.2.2))
      (hd : (l.map Prod.fst).Nodup)
      (ht : (i,j,t.val) ∈ l)
      (hu : ∀ e ∈ l, e.1 ≠ i → e.1 ∈ U)
      (hm : ∀ e ∈ l, e ∈ L) :
      min q (loadBefore (fun k => (ω.2 k).val) i l S) ≤
      min q S + ∑ k ∈ U, clip q (ω.1 k) (ω.2 k) := by
    induction l generalizing S U with
    | nil => simp at ht
    | cons e l ih =>
      obtain ⟨k,c,b⟩ := e
      by_cases hki : k = i
      · simp [loadBefore, hki]
      · have htl : (i,j,t.val) ∈ l := by simpa [hki, eq_comm (a := i)] using ht
        have hb := (List.pairwise_cons.mp hs).1 _ htl
        have hkU := hu (k,c,b) (by simp) hki
        obtain ⟨u, ha, hub⟩ := (order_mem ω.1 k c b).mp (hm _ (by simp))
        have hc : clip q (ω.1 k) (ω.2 k) = min q (ω.2 k).val := by
          rw [ha]; simp [clip, show u.val ≤ q by simpa [hub] using hb.trans htq]
        have htu : ∀ f ∈ l, f.1 ≠ i → f.1 ∈ U.erase k := by
          intro f hf hfi
          apply Finset.mem_erase.mpr
          refine ⟨?_, hu _ (.tail _ hf) hfi⟩
          have hn := (List.nodup_cons.mp hd).1
          exact fun he => hn (List.mem_map.mpr ⟨f,hf,he⟩)
        have hi := ih (if S ≤ b then S + (ω.2 k).val else S) (U.erase k)
          (List.pairwise_cons.mp hs).2 (List.nodup_cons.mp hd).2 htl htu
          (fun f hf => hm f (.tail _ hf))
        rw [← Finset.add_sum_erase U _ hkU, hc]
        simp only [loadBefore, if_neg hki]
        split_ifs at hi ⊢ <;> omega
  have htarget := (order_mem ω.1 i j t.val).mpr ⟨t,hsome,rfl⟩
  simpa [predecessorLoad, L] using general L 0 (Finset.univ.erase i) (order_sorted ω.1)
    (order_distinct ω.1) htarget (fun e he h => by simp [h]) (fun _ he => he)

private noncomputable def wt (I : Instance n m T) (x : LPArray n m) (k : Fin n)
    (a : Single m T) (s : Fin (T+2)) : ℝ := assignWeight x k a * sizeWeight I k a s

private lemma size_norm (I : Instance n m T) (k : Fin n) (a : Single m T) :
    ∑ s, sizeWeight I k a s = 1 := by
  cases a with
  | none =>
    have h : ∀ s : Fin (T+2), s.val = 0 ↔ s = 0 := by simp
    simp [sizeWeight,h]
  | some a =>
    rcases a with ⟨j,t⟩
    simp only [sizeWeight]
    rw [← ENNReal.toReal_sum (fun s _ => (I.sizeLaw k j).apply_ne_top s)]
    have hs := (I.sizeLaw k j).tsum_coe
    rw [tsum_fintype] at hs
    rw [hs, ENNReal.toReal_one]

private lemma wt_norm (I : Instance n m T) (x : LPArray n m) (k : Fin n) :
    ∑ a, ∑ s, wt I x k a s = 1 := by
  simp only [wt, ← Finset.mul_sum, size_norm, mul_one]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [assignWeight, Fin.sum_univ_eq_sum_range, ← Finset.sum_div]
  ring

private lemma wt_pos (I : Instance n m T) (x : LPArray n m) (hx : PsiFeasible I T x)
    (ω : Outcome n m T) : 0 ≤ outcomeWeight I x ω := by
  apply Finset.prod_nonneg
  intro k _
  cases ha : ω.1 k with
  | none =>
    simp only [assignWeight,sizeWeight]
    split_ifs <;> linarith [hx.2.1 k]
  | some p =>
    rcases p with ⟨j,u⟩
    apply mul_nonneg _ ENNReal.toReal_nonneg
    exact div_nonneg (hx.2.2 k j u (by omega)).1 (by norm_num)

private lemma factor (f : Fin n → Single m T → Fin (T+2) → ℝ) :
    (∑ ω : Outcome n m T, ∏ k, f k (ω.1 k) (ω.2 k)) =
    ∏ k, ∑ a, ∑ s, f k a s := by
  let e := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Single m T) (fun _ => Fin (T+2))
  rw [← e.sum_comp (fun ω => ∏ k, f k (ω.1 k) (ω.2 k))]
  change (∑ z : Fin n → Single m T × Fin (T+2), ∏ k, f k (z k).1 (z k).2) = _
  rw [← Fintype.prod_sum (fun k (p : Single m T × Fin (T+2)) => f k p.1 p.2)]
  simp [Fintype.sum_prod_type]

private lemma split_factor {α : Type*} [Fintype α] [DecidableEq α]
    (k : α) (f g : α → ℝ) :
    (∏ l, if l = k then f l else g l) = f k * ∏ l ∈ Finset.univ.erase k, g l := by
  rw [← Finset.mul_prod_erase Finset.univ (fun l => if l = k then f l else g l)
    (Finset.mem_univ k), if_pos rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  simp [(Finset.mem_erase.mp hl).1]

private noncomputable def gate (I : Instance n m T) (x : LPArray n m) (i : Fin n)
    (o : Single m T) (k : Fin n) (a : Single m T) (s : Fin (T+2)) : ℝ :=
    if k = i ∧ a ≠ o then 0 else wt I x k a s

private lemma gate_prod (I : Instance n m T) (x : LPArray n m) (i : Fin n) (o : Single m T)
    (ω : Outcome n m T) :
    (∏ k, gate I x i o k (ω.1 k) (ω.2 k)) = if ω.1 i = o then outcomeWeight I x ω else 0 := by
  by_cases h : ω.1 i = o
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro k hk
    by_cases hk' : k = i <;> simp [gate, wt, hk', h]
  · rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [gate,h]

private lemma gate_sum (I : Instance n m T) (x : LPArray n m) (i : Fin n) (o : Single m T)
    (k : Fin n) :
    (∑ a, ∑ s, gate I x i o k a s) = if k = i then assignWeight x i o else 1 := by
  by_cases h : k = i
  · subst k
    simp [gate, wt, ← Finset.mul_sum, size_norm,
      Finset.sum_ite_irrel, eq_comm, ite_not]
  · simp only [gate, h, false_and, if_false, wt_norm]

private lemma prob_sum (I : Instance n m T) (x : LPArray n m) (E : Outcome n m T → Prop)
    [DecidablePred E] : alg1Prob I x E = ∑ ω, if E ω then outcomeWeight I x ω else 0 := by
  unfold alg1Prob
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h]

private lemma event_mass (I : Instance n m T) (x : LPArray n m) (i : Fin n) (o : Single m T) :
    alg1Prob I x (fun ω => ω.1 i = o) = assignWeight x i o := by
  rw [prob_sum]
  simp_rw [← gate_prod I x i o]
  rw [factor]
  simp only [gate_sum, Finset.prod_ite_eq', Finset.mem_univ, if_true]

private lemma clip_moment (I : Instance n m T) (x : LPArray n m) (i k : Fin n)
    (hki : k ≠ i) (o : Single m T) (q : ℕ) :
    (∑ ω : Outcome n m T, (if ω.1 i = o then outcomeWeight I x ω else 0) *
      (clip q (ω.1 k) (ω.2 k) : ℝ)) =
    assignWeight x i o * ∑ a, ∑ s, wt I x k a s * (clip q a s : ℝ) := by
  let f (l : Fin n) (a : Single m T) (s : Fin (T+2)) :=
    gate I x i o l a s * (if l = k then (clip q a s : ℝ) else 1)
  have eqn (ω : Outcome n m T) :
      ∏ l, f l (ω.1 l) (ω.2 l) =
        (if ω.1 i = o then outcomeWeight I x ω else 0) * (clip q (ω.1 k) (ω.2 k) : ℝ) := by
    simp only [f, Finset.prod_mul_distrib, gate_prod, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  simp_rw [← eqn]
  rw [factor]
  have hsum (l : Fin n) : (∑ a, ∑ s, f l a s) =
      if l = k then ∑ a, ∑ s, wt I x k a s * (clip q a s : ℝ)
      else if l = i then assignWeight x i o else 1 := by
    by_cases hl : l = k
    · subst l; simp [f,gate,hki]
    · simp only [f,hl,if_false,mul_one,gate_sum]
  simp_rw [hsum]
  rw [split_factor k (fun _ => _) (fun l => if l = i then _ else 1)]
  simp [hki.symm,mul_comm]

private lemma local_moment (I : Instance n m T) (x : LPArray n m) (k : Fin n)
    (q : ℕ) (hq : q ≤ T) :
    (∑ a, ∑ s, wt I x k a s * (clip q a s : ℝ)) =
    (∑ j, ∑ u ∈ Finset.range (q+1), x k j u * mu I k j q) / 4 := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [clip, Nat.cast_zero, mul_zero, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hs (u : Fin (T+1)) :
      (∑ s : Fin (T+2), wt I x k (some (j,u)) s * ((if u.val ≤ q then min q s.val else 0 : ℕ) : ℝ)) =
      if u.val ≤ q then x k j u.val * mu I k j q / 4 else 0 := by
    by_cases hu : u.val ≤ q
    · simp only [hu,if_true, wt,assignWeight,sizeWeight, Nat.cast_min, mul_assoc, ← Finset.mul_sum]
      simp [mu,truncMean,min_comm (q : ℝ),div_mul_eq_mul_div]
    · simp [hu]
  simp_rw [hs]
  rw [Fin.sum_univ_eq_sum_range (fun u => if u ≤ q then x k j u * mu I k j q / 4 else 0), ← Finset.sum_filter]
  have hsets : (Finset.range (T+1)).filter (fun u => u ≤ q) = Finset.range (q+1) := by
    ext u; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hsets, Finset.sum_div]

private lemma total_moment (I : Instance n m T) (x : LPArray n m) (hx : PsiFeasible I T x)
    (i : Fin n) (o : Single m T) (q : ℕ) (hq : q ≤ T) :
    (∑ ω : Outcome n m T, (if ω.1 i = o then outcomeWeight I x ω else 0) *
      ∑ k ∈ Finset.univ.erase i, (clip q (ω.1 k) (ω.2 k) : ℝ)) ≤
    assignWeight x i o * (q : ℝ) / 2 := by
  have hp : 0 ≤ assignWeight x i o := by
    rw [← event_mass I x i o, prob_sum]
    apply Finset.sum_nonneg
    intro ω _
    split_ifs <;> first | exact wt_pos I x hx ω | rfl
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  let M (k : Fin n) := ∑ j, ∑ u ∈ Finset.range (q+1), x k j u * mu I k j q
  have heq (k : Fin n) (hk : k ∈ Finset.univ.erase i) :
      (∑ ω : Outcome n m T, (if ω.1 i = o then outcomeWeight I x ω else 0) *
        (clip q (ω.1 k) (ω.2 k) : ℝ)) = assignWeight x i o * (M k / 4) := by
    rw [clip_moment I x i k (Finset.mem_erase.mp hk).1, local_moment I x k q hq]
  rw [Finset.sum_congr rfl heq, ← Finset.mul_sum, ← Finset.sum_div]
  have hi : 0 ≤ M i := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro u hu
    refine mul_nonneg (hx.2.2 i j u (by have := Finset.mem_range.mp hu; omega)).1 ?_
    unfold mu truncMean
    positivity
  have hcap : ∑ k ∈ Finset.univ.erase i, M k ≤ 2*q := by
    have hh : (∑ k, M k) ≤ 2*(q:ℝ) := hx.1 q hq
    rw [← Finset.add_sum_erase Finset.univ M (Finset.mem_univ i)] at hh
    linarith
  calc
    _ ≤ assignWeight x i o * ((2 * (q:ℝ)) / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) hp
    _ = _ := by ring

end PandoraKnapsack.Skipping

theorem solution {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) (xStar : LPArray n m)
    (hx : PsiOptimal I T xStar) (i : Fin n) (j : Fin m) (t : Fin (T + 1)) :
    (1 / 2 : ℝ) * alg1Prob I xStar (fun ω => ω.1 i = some (j, t)) ≤
      alg1Prob I xStar (fun ω => ω.1 i = some (j, t) ∧ predecessorLoad ω i ≤ (t : ℕ)) := by
  let q := max 1 t.val
  let o : Single m T := some (j,t)
  let A (ω : Outcome n m T) : ℝ := if ω.1 i = o then outcomeWeight I xStar ω else 0
  let G (ω : Outcome n m T) : ℝ :=
    if ω.1 i = o ∧ predecessorLoad ω i ≤ t.val then outcomeWeight I xStar ω else 0
  have qpos : (0:ℝ) < q := by exact_mod_cast (show 0 < q by dsimp [q]; omega)
  have hpoint (ω : Outcome n m T) : (q : ℝ) * (A ω - G ω) ≤
      A ω * ∑ k ∈ Finset.univ.erase i, (clip q (ω.1 k) (ω.2 k) : ℝ) := by
    by_cases ha : ω.1 i = o
    · have hw := wt_pos I xStar hx.1 ω
      by_cases hg : predecessorLoad ω i ≤ t.val
      · simp only [A,G,ha,hg,true_and,if_true,sub_self,mul_zero]
        positivity
      · have hmin : min q (predecessorLoad ω i) = q := by dsimp [q]; omega
        have hdet := scan_bound ω i j t q (le_max_right ..) ha
        rw [hmin] at hdet
        have hreal : (q:ℝ) ≤ ∑ k ∈ Finset.univ.erase i, (clip q (ω.1 k) (ω.2 k) : ℝ) := by
          exact_mod_cast hdet
        simpa [A,G,ha,hg,mul_comm] using mul_le_mul_of_nonneg_left hreal hw
    · simp [A,G,ha]
  have summed := Finset.sum_le_sum (s:=Finset.univ) (fun ω _ => hpoint ω)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at summed
  have hqT : q ≤ T := by have := t.isLt; have := hI.1; dsimp [q]; omega
  have hh := summed.trans (total_moment I xStar hx.1 i o q hqT)
  have hA : ∑ ω, A ω = alg1Prob I xStar (fun ω => ω.1 i = o) := (prob_sum ..).symm
  have hG : ∑ ω, G ω = alg1Prob I xStar
    (fun ω => ω.1 i = o ∧ predecessorLoad ω i ≤ t.val) := (prob_sum ..).symm
  rw [← event_mass I xStar i o, ← hA] at hh
  change (1/2:ℝ) * alg1Prob I xStar (fun ω => ω.1 i = o) ≤ _
  rw [← hA]
  change _ ≤ alg1Prob I xStar (fun ω => ω.1 i = o ∧ predecessorLoad ω i ≤ t.val)
  rw [← hG]
  apply (le_of_mul_le_mul_left _ qpos)
  linarith
