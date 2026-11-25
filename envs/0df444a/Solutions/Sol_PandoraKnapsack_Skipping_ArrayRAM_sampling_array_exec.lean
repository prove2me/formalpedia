-- Prove2me | solution 1 for PandoraKnapsack.Skipping.ArrayRAM.sampling_array_exec
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:49:52.342793+00:00
-- url     : https://prove2.me/submissions/aaa18873-f936-4eb8-8cf4-785c9486ac54

import Definitions.Def_PandoraKnapsack_Skipping_SamplingRAM

namespace PandoraKnapsack.Skipping.ArrayRAM

variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

theorem forN_inv {idx : ℕ} {bound : N} {body : C} {s : Store} {M : ℕ}
    (Inv : ℕ → Store → Prop) (h0 : Inv 0 s)
    (hs : ∀ j, j < bound.eval s → ∀ u, Inv j u →
      ∃ v k, Exec I ω body (u.setN idx j) v k ∧ k ≤ M ∧ Inv (j+1) v) :
    ∃ v k, Exec I ω (.forN idx bound body) s (v.setN idx (bound.eval s)) k ∧
      k ≤ bound.work+4+5*(bound.eval s)+(bound.eval s)*M ∧ Inv (bound.eval s) v := by
  classical
  let L := bound.eval s
  have nextExists (j : ℕ) (u : Store) : ∃ v k, j < L ∧ Inv j u →
      Exec I ω body (u.setN idx j) v k ∧ k ≤ M ∧ Inv (j+1) v := by
    by_cases h : j < L ∧ Inv j u
    · obtain ⟨v,k,hv⟩ := hs j h.1 u h.2
      exact ⟨v,k,fun _ => hv⟩
    · exact ⟨u,0,fun a => (h a).elim⟩
  choose next price hnext using nextExists
  let states : ℕ → Store := Nat.rec s (fun j u => next j u)
  have good : ∀ j, j ≤ L → Inv j (states j) := by
    intro j
    induction j with
    | zero => exact fun _ => h0
    | succ j ih =>
      intro hj
      exact (hnext j (states j) ⟨by omega,ih (by omega)⟩).2.2
  have h := Exec.forN (I := I) (ω := ω) idx bound body states (fun j => price j (states j))
    (fun j hj => (hnext j (states j) ⟨hj,good j (by exact Nat.le_of_lt hj)⟩).1)
  refine ⟨states L,_,h,?_,good L le_rfl⟩
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _j ∈ Finset.range L, M := Finset.sum_le_sum fun j hj =>
      (hnext j (states j) ⟨Finset.mem_range.mp hj, good j (Nat.le_of_lt (Finset.mem_range.mp hj))⟩).2.1
    _ = _ := by simp [L]

end PandoraKnapsack.Skipping.ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM
variable {n m T : ℕ}
abbrev Marks (n m T : ℕ) := Fin n → Option (Fin m × Fin (labelCount T))
abbrev Triple (n m : ℕ) := Fin n × Fin m × ℕ
def markLabel (jh : Fin m × Fin (labelCount T)) : Fin m × Fin (T+1) :=
  (jh.1,⟨timeLabel jh.2, Nat.lt_succ_of_le (samplingLabel_le _)⟩)
def markAssignment (a : Marks n m T) : Assignment n m T := fun i => (a i).map markLabel

def entryAt (a : Marks n m T) (h : Fin (labelCount T)) (i : Fin n) : Option (Triple n m) :=
  (a i).bind fun p => if p.2 = h then some (i,p.1,timeLabel h) else none

def atTime (a : Marks n m T) (h : Fin (labelCount T)) : List (Triple n m) :=
  (List.finRange n).filterMap (entryAt a h)

def entries (a : Marks n m T) : List (Triple n m) :=
  (List.finRange (labelCount T)).flatMap (atTime a)

theorem label_strict : StrictMono (@timeLabel T) := by
  intro k l hk
  unfold timeLabel
  split_ifs with h h' h'
  · omega
  · positivity
  · omega
  · exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem entry_eq (a : Marks n m T) (h : Fin (labelCount T)) (i : Fin n) (e : Triple n m) :
    entryAt a h i = some e ↔ e.1 = i ∧ e.2.2 = timeLabel h ∧ a i = some (e.2.1,h) := by
  obtain ⟨k,j,b⟩ := e
  rcases eq : a i with _ | ⟨j',h'⟩
  · simp [entryAt,eq]
  · by_cases hn : h' = h <;> simp [entryAt,eq,hn,Prod.ext_iff,eq_comm,and_comm,and_left_comm,and_assoc]

theorem atTime_mem (a : Marks n m T) (h : Fin (labelCount T)) (e : Triple n m) :
    e ∈ atTime a h ↔ e.2.2 = timeLabel h ∧ a e.1 = some (e.2.1,h) := by
  simp [atTime,entry_eq]

theorem entries_mem (a : Marks n m T) (e : Triple n m) :
    e ∈ entries a ↔ ∃ h, e.2.2 = timeLabel h ∧ a e.1 = some (e.2.1,h) := by
  simp [entries,atTime_mem]

private def prior (e f : Triple n m) := e.2.2 < f.2.2 ∨ e.2.2 = f.2.2 ∧ e.1 < f.1
private abbrev priorEq (e f : Triple n m) := e.2.2 < f.2.2 ∨ e.2.2 = f.2.2 ∧ e.1 ≤ f.1

private lemma entries_pairwise (a : Marks n m T) : (entries a).Pairwise prior := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro h _
    apply List.pairwise_filterMap.mpr
    apply (List.pairwise_lt_finRange n).imp
    intro i k hik e he f hf
    obtain ⟨rfl,he',_⟩ := (entry_eq ..).mp he
    obtain ⟨rfl,hf',_⟩ := (entry_eq ..).mp hf
    exact Or.inr ⟨he'.trans hf'.symm,hik⟩
  · apply (List.pairwise_lt_finRange _).imp
    intro h k hlt e he f hf
    exact Or.inl (by rw [(atTime_mem ..).mp he |>.1, (atTime_mem ..).mp hf |>.1]; exact label_strict hlt)

theorem sorted_entries (a : Marks n m T) : entries a = scanOrder (markAssignment a) := by
  let b := markAssignment a
  have hmem (e : Triple n m) : e ∈ entries a ↔ e ∈ scanOrder b := by
    obtain ⟨i,j,u⟩ := e
    simp only [entries_mem,scanOrder,List.mem_mergeSort,retained,List.mem_filterMap,
      List.mem_finRange,true_and, b,markAssignment,Option.map_eq_some_iff,markLabel]
    constructor
    · rintro ⟨h,rfl,ha⟩
      exact ⟨i,(_,⟨_,_⟩),⟨(j,h),ha,rfl⟩,rfl⟩
    · rintro ⟨i',p,⟨⟨j',k⟩,ha,rfl⟩,he⟩
      cases he
      exact ⟨k,rfl,ha⟩
  have hsort : (scanOrder b).Pairwise priorEq := by
    let cmp (x y : Triple n m) := decide (priorEq x y)
    have ht (x y z : Triple n m) : cmp x y → cmp y z → cmp x z := by simp [cmp,priorEq]; omega
    have htot (x y : Triple n m) : cmp x y || cmp y x := by simp [cmp,priorEq]; omega
    exact (List.pairwise_mergeSort ht htot (retained b)).imp (by simp [cmp])
  have hn : ((scanOrder b).map Prod.fst).Nodup := by
    apply ((List.mergeSort_perm (retained b) _).map Prod.fst).nodup_iff.mpr
    rw [List.Nodup, List.pairwise_map, retained, List.pairwise_filterMap]
    apply (List.nodup_finRange n).imp
    intro i k hik u hu v hv
    obtain ⟨p,hp,rfl⟩ := Option.map_eq_some_iff.mp hu
    obtain ⟨p',hp',rfl⟩ := Option.map_eq_some_iff.mp hv
    exact hik
  have pair := entries_pairwise a
  refine List.Perm.eq_of_pairwise (le := priorEq) ?_ ?_ hsort ?_
  · intro e f he hf hef hfe
    obtain ⟨p,hep,hea⟩ := (entries_mem a e).mp he
    obtain ⟨q,hfq,hfa⟩ := (entries_mem a f).mp ((hmem f).mpr hf)
    have htime : e.2.2 = f.2.2 := by dsimp [priorEq] at hef hfe; omega
    have hitem : e.1 = f.1 := by dsimp [priorEq] at hef hfe; omega
    rw [← hitem,hea] at hfa
    have hc := congrArg (fun o : Option (Fin m × Fin (labelCount T)) => o.map Prod.fst) hfa
    simp only [Option.map_some,Option.some.injEq] at hc
    exact Prod.ext hitem (Prod.ext hc htime)
  · apply pair.imp
    intro x y h
    dsimp [prior,priorEq] at *; omega
  · apply (List.perm_ext_iff_of_nodup _ (List.Nodup.of_map Prod.fst hn)).mpr hmem
    apply pair.imp
    intro x y h e
    subst y
    simp [prior] at h

end PandoraKnapsack.Skipping.ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM
variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

abbrev rowIndex (s : Store) := s.ns 45
abbrev colIndex (s : Store) := (s.ns 45*s.ns 1+s.ns 46)*s.ns 2+s.ns 47
noncomputable def cellProb (s : Store) : ℝ :=
  if s.tab 1 (colIndex s) < 0 then 0 else s.tab 4 (colIndex s) / 4
noncomputable def record (s : Store) : Store :=
  (s.put 9 (s.ns 45) ((s.ns 47:ℝ)+1)).put 10 (s.ns 45) (s.ns 46)
noncomputable def hit (s : Store) : Prop := s.rs 46 ≤ s.rs 45 ∧ s.rs 45 < s.rs 46 + s.rs 47
noncomputable def afterHit (s : Store) : Store := by
  classical
  exact if hit s then record s else s
noncomputable def cellState (s : Store) : Store :=
  (afterHit (s.setR 47 (cellProb s))).setR 46 (s.rs 46 + cellProb s)
def cellBudget (s : Store) : ℕ := 2000*(1+colIndex s+rowIndex s)

@[simp] theorem sEvalNadd (s : Store) (a b : N) : (a + b).eval s = a.eval s + b.eval s := rfl
@[simp] theorem sWorkNadd (a b : N) : (a + b).work = a.work + b.work + 1 := rfl
@[simp] theorem sEvalNmul (s : Store) (a b : N) : (a * b).eval s = a.eval s * b.eval s := rfl
@[simp] theorem sWorkNmul (a b : N) : (a * b).work = a.work + b.work + 1 := rfl
@[simp] theorem sEvalNNat (s : Store) (v : ℕ) : (N.eval s (OfNat.ofNat v)) = v := rfl
@[simp] theorem sWorkNNat (v : ℕ) : (N.work (OfNat.ofNat v)) = 1 := rfl
@[simp] theorem sEvalRadd (s : Store) (a b : R) : (a + b).eval s = a.eval s + b.eval s := rfl
@[simp] theorem sWorkRadd (s : Store) (a b : R) : (a + b).work s = a.work s + b.work s + 1 := rfl
@[simp] theorem sEvalRsub (s : Store) (a b : R) : (a - b).eval s = a.eval s - b.eval s := rfl
@[simp] theorem sWorkRsub (s : Store) (a b : R) : (a - b).work s = a.work s + b.work s + 1 := rfl
@[simp] theorem sEvalRmul (s : Store) (a b : R) : (a * b).eval s = a.eval s * b.eval s := rfl
@[simp] theorem sWorkRmul (s : Store) (a b : R) : (a * b).work s = a.work s + b.work s + 1 := rfl
@[simp] theorem sEvalRdiv (s : Store) (a b : R) : (a / b).eval s = a.eval s / b.eval s := rfl
@[simp] theorem sWorkRdiv (s : Store) (a b : R) : (a / b).work s = a.work s + b.work s + 1 := rfl
@[simp] theorem sEvalRNat (s : Store) (v : ℕ) : (R.eval s (OfNat.ofNat v)) = (v:ℝ) := rfl
@[simp] theorem sWorkRNat (s : Store) (v : ℕ) : (R.work s (OfNat.ofNat v)) = 1 := rfl

private lemma pick_prob (s : Store) :
    ∃ k, Exec I ω (.itePos (0 - .get 1 sampleColumn) (.letR 47 0)
      (.letR 47 (.get 4 sampleColumn / 4))) s (s.setR 47 (cellProb s)) k ∧
      k ≤ 500*(1+colIndex s) := by
  by_cases h : s.tab 1 (colIndex s) < 0
  · unfold cellProb
    rw [if_pos h]
    have hb := Exec.letR (I:=I) (ω:=ω) s 47 (0:R)
    have hz : (0:R).eval s = 0 := by change ((0:ℕ):ℝ) = 0; norm_num
    rw [hz] at hb
    refine ⟨_,Exec.ite_true ?_ hb,?_⟩
    · simpa [N.eval,R.eval,sampleColumn,colIndex] using h
    · simp [sampleColumn,colIndex,rowIndex,N.eval,R.eval,N.work,R.work,tableOffset,Store.put,Store.setN,Store.setR,Store.writeOut,Function.update_of_ne] <;> try norm_num <;> omega
  · unfold cellProb
    rw [if_neg h]
    have hb := Exec.letR (I:=I) (ω:=ω) s 47 (.get 4 sampleColumn / 4)
    simp [R.eval,sampleColumn,N.eval,colIndex] at hb
    refine ⟨_,Exec.ite_false ?_ hb,?_⟩
    · simpa [N.eval,R.eval,sampleColumn,colIndex] using le_of_not_gt h
    · simp [sampleColumn,colIndex,rowIndex,N.eval,R.eval,N.work,R.work,tableOffset,Store.put,Store.setN,Store.setR,Store.writeOut,Function.update_of_ne] <;> try norm_num <;> omega

private lemma record_exec (s : Store) :
    ∃ k, Exec I ω (.seq (.put 9 (.var 45) (.nat (.var 47 + 1))) (.put 10 (.var 45) (.nat (.var 46))))
      s (record s) k ∧ k ≤ 500*(1+rowIndex s) := by
  have a := Exec.put (I:=I) (ω:=ω) s 9 (.var 45) (.nat (.var 47 + 1))
  simp [R.eval,N.eval] at a
  let v := s.put 9 (s.ns 45) ((s.ns 47:ℝ)+1)
  have b := Exec.put (I:=I) (ω:=ω) v 10 (.var 45) (.nat (.var 46))
  refine ⟨_,Exec.seq a b,?_⟩
  dsimp [v]; simp [sampleColumn,colIndex,rowIndex,N.eval,R.eval,N.work,R.work,tableOffset,Store.put,Store.setN,Store.setR,Store.writeOut,Function.update_of_ne] <;> try norm_num <;> omega

private lemma check_hit (s : Store) :
    ∃ k, Exec I ω
      (.itePos (.var 46 - .var 45) .skip
        (.itePos ((.var 46 + .var 47) - .var 45)
          (.seq (.put 9 (.var 45) (.nat (.var 47 + 1)))
            (.put 10 (.var 45) (.nat (.var 46)))) .skip))
      s (afterHit s) k ∧ k ≤ 600*(1+rowIndex s) := by
  by_cases hleft : s.rs 46 ≤ s.rs 45
  · by_cases hright : s.rs 45 < s.rs 46 + s.rs 47
    · obtain ⟨k,hk,hw⟩ := record_exec (I:=I) (ω:=ω) s
      rw [show afterHit s = record s by simp [afterHit,hit,hleft,hright]]
      refine ⟨_,Exec.ite_false ?_ (Exec.ite_true ?_ hk),?_⟩ <;> simp [R.eval,R.work] at * <;> first | linarith | omega
    · rw [show afterHit s = s by simp [afterHit,hit,hleft,hright]]
      refine ⟨_,Exec.ite_false ?_ (Exec.ite_false ?_ (Exec.skip _)),?_⟩ <;> simp [R.eval,R.work] at * <;> first | linarith | omega
  · rw [show afterHit s = s by simp [afterHit,hit,hleft]]
    refine ⟨_,Exec.ite_true ?_ (Exec.skip _),?_⟩ <;> simp [R.eval,R.work] at * <;> first | linarith | omega

@[simp] theorem afterHit_ns (s : Store) : (afterHit s).ns = s.ns := by
  unfold afterHit; split <;> rfl
@[simp] theorem afterHit_rs (s : Store) : (afterHit s).rs = s.rs := by
  unfold afterHit; split <;> rfl
@[simp] theorem afterHit_out (s : Store) : (afterHit s).out = s.out := by
  unfold afterHit; split <;> rfl
@[simp] theorem afterHit_draws (s : Store) : (afterHit s).draws = s.draws := by
  unfold afterHit; split <;> rfl

theorem sampleCell_exec (s : Store) : ∃ k, Exec I ω sampleCellCode s (cellState s) k ∧ k ≤ cellBudget s := by
  obtain ⟨k,hk,hku⟩ := pick_prob (I:=I) (ω:=ω) s
  obtain ⟨b,hb,hbu⟩ := check_hit (I:=I) (ω:=ω) (s.setR 47 (cellProb s))
  unfold sampleCellCode cellState
  have hlast := Exec.letR (I:=I) (ω:=ω) (afterHit (s.setR 47 (cellProb s))) 46 (.var 46 + .var 47)
  have vv : (R.var 46 + R.var 47).eval (afterHit (s.setR 47 (cellProb s))) = s.rs 46 + cellProb s := by
    simp [R.eval,Store.setR]
  rw [vv] at hlast
  refine ⟨_,Exec.seq hk (Exec.seq hb hlast),?_⟩
  simp [R.work,cellBudget,rowIndex,Store.setR] at *; omega

end PandoraKnapsack.Skipping.ArrayRAM

open PandoraPacking
namespace PandoraKnapsack.Skipping.ArrayRAM
variable {n m T : ℕ}
structure SamplingInputs (I : Instance n m T) (s : Store) : Prop where
  items : s.ns 0 = n
  choices : s.ns 1 = m
  times : s.ns 2 = labelCount T
  cap : s.rs 0 = T
  labels : ∀ h : Fin (labelCount T), s.tab 0 h.val = timeLabel h
  weights : ∀ c : Fin (columnCount n m T), s.tab 1 c.val = columnWeight I c
  vector : ∀ c : Fin (columnCount n m T), s.tab 4 c.val = solve (packingRows I) (packingProfits I) c

abbrev Width (m T : ℕ) := m * labelCount T
noncomputable def sampleProb (I : Instance n m T) (i : Fin n) (c : Fin (Width m T)) : ℝ :=
  dyadicPlan I i (samplingLab m T c).1 (samplingLab m T c).2.val / 4

noncomputable def chosen (I : Instance n m T) (ω : ℕ → ℝ) (i : Fin n) :
    Option (Fin (Width m T)) := uniformCell (sampleProb I i) (ω i.val)
noncomputable def chosenMarks (I : Instance n m T) (ω : ℕ → ℝ) : Marks n m T :=
  fun i => (chosen I ω i).map finProdFinEquiv.symm

theorem marks_assignment (I : Instance n m T) {B : ℕ} (hB : n ≤ B) (u : Fin B → unitInterval) :
    markAssignment (chosenMarks I (extendDraws u)) = uniformAssignment hB (samplingLab m T) (dyadicPlan I) u := by
  funext i
  have h : i.val < B := lt_of_lt_of_le i.isLt hB
  simp [markAssignment,chosenMarks,chosen,extendDraws,h,uniformAssignment,sampleProb,
    Option.map_map,samplingLab,markLabel,Function.comp_def]; rfl

def MarkRep (s : Store) (i : Fin n) (o : Option (Fin m × Fin (labelCount T))) : Prop :=
  match o with
  | none => s.tab 9 i.val = 0
  | some (j,k) => s.tab 9 i.val = k.val+1 ∧ s.tab 10 i.val = j.val

private def prefixMark {d : ℕ} (c : Option (Fin d)) (pos : ℕ) : Option (Fin d) :=
  c.bind (fun k => if k.val < pos then some k else none)

private lemma prefix_zero {d} (c : Option (Fin d)) : prefixMark c 0 = none := by
  cases c <;> simp [prefixMark]
private lemma prefix_all {d} (c : Option (Fin d)) : prefixMark c d = c := by
  cases c with
  | none => rfl
  | some a => simp [prefixMark,a.isLt]
private lemma prefix_next {d} (c : Option (Fin d)) (k : Fin d) :
    prefixMark c (k.val+1) = if c = some k then some k else prefixMark c k.val := by
  rcases c with _ | l
  · simp [prefixMark]
  · by_cases h : l = k
    · simp [h,prefixMark]
    · have ht : l.val ≠ k.val := fun z => h (Fin.ext z)
      simp only [prefixMark,Option.bind_some,Option.some.injEq,if_neg h]
      split_ifs <;> first | rfl | omega

variable {d : ℕ}
private lemma cell_next (p : Fin d → ℝ) (k : Fin d) :
    cellStart p (k.val+1) = cellStart p k.val + p k := by
  have h : (Finset.univ.filter (fun z : Fin d => z.val < k.val+1)) =
      insert k (Finset.univ.filter (fun z : Fin d => z.val < k.val)) := by
    ext z; simp [Fin.ext_iff]; omega
  unfold cellStart
  rw [h,Finset.sum_insert (by simp)]
  ac_rfl

private lemma cell_mono (p : Fin d → ℝ) (hp : ∀ k, 0 ≤ p k) : Monotone (cellStart p) := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.trans_le hab⟩
  · exact fun i _ _ => hp i

private lemma cell_total (p : Fin d → ℝ) : cellStart p d = ∑ k, p k := by
  simp [cellStart]

private lemma cell_some (p : Fin d → ℝ) (hp : ∀ k, 0 ≤ p k) (u : ℝ) (k : Fin d) :
    uniformCell p u = some k ↔ cellStart p k.val ≤ u ∧ u < cellStart p k.val + p k := by
  change k ∈ Fin.find? _ ↔ _
  rw [Fin.mem_find?_iff]
  simp only [decide_eq_true_eq]
  refine ⟨And.left, fun h => ⟨h,?_⟩⟩
  intro j hj h'
  have hprefix : cellStart p (j.val+1) ≤ cellStart p k.val := cell_mono p hp (by exact hj)
  rw [cell_next] at hprefix
  linarith [h.1,h'.2]

private lemma iter_nonneg {d : ℕ} (rows : List (Row d)) (fuel : ℕ)
    (x y : Vec d) (hx : ∀ k, 0 ≤ x k) (h : iterate rows fuel x = some y) :
    ∀ k, 0 ≤ y k := by
  induction fuel generalizing x with
  | zero => simp [iterate] at h
  | succ f ih =>
    simp only [iterate] at h
    split at h
    · cases h; exact hx
    · apply ih _ _ h
      intro k; exact le_max_left ..  

private lemma solver_nonneg {r d : ℕ} (A : Matrix r d) (c : Vec d) (q : Fin d) :
    0 ≤ solve A c q := by
  have trial_nn (k : ℕ) : 0 ≤ trial A c k q := by
    unfold trial
    cases hy : iterate (rowsFor A c ((k:ℝ)/8)) (fuelBound d) 0 with
    | none => exact le_rfl
    | some y =>
      apply mul_nonneg (by norm_num : (0:ℝ) ≤ 8/9)
      exact iter_nonneg _ _ _ _ (fun _ => le_rfl) hy q
  have run_nn (k : ℕ) : 0 ≤ search A c k q := by
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      simp only [search,better]; split <;> first | assumption | exact trial_nn k
  exact run_nn _

private lemma spread_at (v : Vec (columnCount n m T)) (i : Fin n) (j : Fin m)
    (k : Fin (labelCount T)) :
    spreadVector v i j (timeLabel k) = v (columns n m T (i,j,k)) := by
  simp [spreadVector,label_strict.injective.eq_iff]

private lemma sampleProb_nonneg (I : Instance n m T) (i : Fin n) (c : Fin (Width m T)) :
    0 ≤ sampleProb I i c := by
  unfold sampleProb dyadicPlan spreadVector
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · unfold planVector
    split_ifs <;> first | exact le_rfl | exact solver_nonneg .. 
  · exact le_rfl

private theorem flat_col (i : Fin n) (j : Fin m) (k : Fin (labelCount T)) :
    (columns n m T (i,j,k)).val = (i.val*m+j.val)*labelCount T + k.val := by
  change ↑k + labelCount T * ↑j + (m*labelCount T)*↑i = _
  ring

private theorem flat_cell (j : Fin m) (k : Fin (labelCount T)) :
    (finProdFinEquiv (j,k)).val = j.val*labelCount T + k.val := by
  change ↑k + labelCount T * ↑j = _
  ring

private lemma prob_at (s : Store) (I : Instance n m T) (hs : SamplingInputs I s)
    (i : Fin n) (j : Fin m) (k : Fin (labelCount T))
    (hi : s.ns 45 = i.val) (hj : s.ns 46 = j.val) (hk : s.ns 47 = k.val) :
    cellProb s = sampleProb I i (finProdFinEquiv (j,k)) := by
  have hidx : colIndex s = (columns n m T (i,j,k)).val := by
    simp [colIndex,hi,hj,hk,hs.choices,hs.times,flat_col]
  simp only [cellProb,hidx,hs.weights,hs.vector,sampleProb,samplingLab,Equiv.symm_apply_apply,
    dyadicPlan,spread_at,planVector]
  split_ifs <;> first | rfl | positivity | linarith | simp_all

private lemma markRep_tab {s s' : Store} (i : Fin n) (o : Option (Fin m × Fin (labelCount T)))
    (h9 : s'.tab 9 i.val = s.tab 9 i.val) (h10 : s'.tab 10 i.val = s.tab 10 i.val)
    (h : MarkRep s i o) : MarkRep s' i o := by
  rcases o with _ | ⟨j,k⟩ <;> simp only [MarkRep,h9,h10] at * <;> exact h

structure Done (I : Instance n m T) (ω : ℕ → ℝ) (pos : ℕ) (s : Store) : Prop where
  static : SamplingInputs I s
  marks : ∀ i : Fin n, i.val < pos → MarkRep s i (chosenMarks I ω i)

private structure InRow (I : Instance n m T) (ω : ℕ → ℝ) (i : Fin n) (pos : ℕ)
    (s : Store) : Prop extends Done I ω i.val s where
  index : s.ns 45 = i.val
  draws : s.draws = i.val+1
  uniform : s.rs 45 = ω i.val
  sum : s.rs 46 = cellStart (sampleProb I i) pos
  marked : MarkRep s i ((prefixMark (chosen I ω i) pos).map finProdFinEquiv.symm)

private theorem cellState_tab (s : Store) {t : Fin 16} {idx : ℕ}
    (h : t ≠ 9 ∧ t ≠ 10 ∨ idx ≠ s.ns 45) : (cellState s).tab t idx = s.tab t idx := by
  unfold cellState afterHit
  split_ifs <;> try rfl
  simp only [Store.setR, record,Store.put]
  rcases h with ⟨h9,h10⟩ | hidx
  · simp [h9,h10]
  · by_cases ht : t = 9 <;> by_cases ht' : t = 10 <;> simp_all

private theorem static_cell (I : Instance n m T) (s : Store) (h : SamplingInputs I s) :
    SamplingInputs I (cellState s) := by
  have hn : (cellState s).ns = s.ns := by simp [cellState,Store.setR]
  have hr : (cellState s).rs 0 = s.rs 0 := by simp [cellState,Store.setR]
  refine ⟨hn ▸ h.items,hn ▸ h.choices,hn ▸ h.times,hr.trans h.cap,?_,?_,?_⟩
  · intro k; exact (cellState_tab _ (Or.inl (by decide))).trans (h.labels k)
  · intro k; exact (cellState_tab _ (Or.inl (by decide))).trans (h.weights k)
  · intro k; exact (cellState_tab _ (Or.inl (by decide))).trans (h.vector k)

private theorem cell_invariant (I : Instance n m T) (ω : ℕ → ℝ) (s : Store)
    (i : Fin n) (j : Fin m) (k : Fin (labelCount T)) (hj : s.ns 46 = j.val) (hk : s.ns 47 = k.val)
    (h : InRow I ω i (j.val*labelCount T+k.val) s) :
    InRow I ω i (j.val*labelCount T+k.val+1) (cellState s) := by
  let c : Fin (Width m T) := finProdFinEquiv (j,k)
  have hc : c.val = j.val*labelCount T+k.val := flat_cell j k
  have hp := prob_at s I h.static i j k h.index hj hk
  have hh : hit (s.setR 47 (cellProb s)) ↔ chosen I ω i = some c := by
    rw [chosen,cell_some _ (sampleProb_nonneg I i)]
    simp [hit,Store.setR,h.uniform,h.sum,hp,hc,c]
  have hdone : Done I ω i.val (cellState s) := by
    refine ⟨static_cell _ _ h.static,?_⟩
    intro i' hi'
    have hidx : i'.val ≠ s.ns 45 := by rw [h.index]; omega
    exact markRep_tab _ _ (cellState_tab _ (Or.inr hidx)) (cellState_tab _ (Or.inr hidx)) (h.marks _ hi')
  refine ⟨hdone,?_,?_,?_,?_,?_⟩
  · simpa [cellState,Store.setR] using h.index
  · simpa [cellState,Store.setR] using h.draws
  · simpa [cellState,Store.setR] using h.uniform
  · simpa [cellState,Store.setR,h.sum,hp,← hc,c] using (cell_next (sampleProb I i) c).symm
  · rw [← hc,prefix_next]
    by_cases he : chosen I ω i = some c
    · simp only [he,if_true,Option.map_some]
      change MarkRep (cellState s) i (some (finProdFinEquiv.symm (finProdFinEquiv (j,k))))
      rw [Equiv.symm_apply_apply]
      have hit' := hh.mpr he
      simp only [cellState,afterHit,if_pos hit']
      simp [MarkRep,record,Store.setR,Store.put,h.index,hj,hk]
    · have hit' := mt hh.mp he
      rw [if_neg he]
      apply markRep_tab (s:=s) _ _ _ _ (by simpa [hc] using h.marked)
      all_goals simp only [cellState,afterHit,if_neg hit']; rfl

private lemma static_setN (I : Instance n m T) (s : Store) (h : SamplingInputs I s)
    (idx v : ℕ) (hr : 2 < idx) : SamplingInputs I (s.setN idx v) := by
  refine ⟨?_,?_,?_,h.cap,h.labels,h.weights,h.vector⟩
  · simpa [Store.setN,show 0 ≠ idx by omega] using h.items
  · simpa [Store.setN,show 1 ≠ idx by omega] using h.choices
  · simpa [Store.setN,show 2 ≠ idx by omega] using h.times

private lemma InRow.setLoop {I : Instance n m T} {ω i pos s} (h : InRow I ω i pos s)
    (idx v : ℕ) (hr : 45 < idx) : InRow I ω i pos (s.setN idx v) := by
  refine ⟨⟨static_setN _ _ h.static _ _ (by omega),h.marks⟩,?_,h.draws,h.uniform,h.sum,h.marked⟩
  simpa [Store.setN,show 45 ≠ idx by omega] using h.index

def cellMax (n m T : ℕ) := 2000*(1+columnCount n m T+n)
def timeScanBudget (n m T : ℕ) := 5+5*labelCount T+labelCount T*cellMax n m T
def choiceScanBudget (n m T : ℕ) := 5+5*m+m*timeScanBudget n m T
def sampleItemBudget (n m T : ℕ) := 200*(n+1) + choiceScanBudget n m T
def sampleBudget (n m T : ℕ) := 5+5*n+n*sampleItemBudget n m T

private theorem scan_times {I : Instance n m T} {ω : ℕ → ℝ} {s : Store}
    (i : Fin n) (j : Fin m) (hj : s.ns 46 = j.val) (h : InRow I ω i (j.val*labelCount T) s) :
    ∃ v c, Exec I ω (.forN 47 (.var 2) sampleCellCode) s v c ∧ c ≤ timeScanBudget n m T ∧
      InRow I ω i ((j.val+1)*labelCount T) v := by
  let K := labelCount T
  let Inv (u : ℕ) (v : Store) := InRow I ω i (j.val*K+u) v ∧ v.ns 46 = j.val
  have hs0 : Inv 0 s := ⟨by simpa [K] using h,hj⟩
  have bound : (N.var 2).eval s = K := h.static.times
  obtain ⟨v,c,hc,ht,hh⟩ := forN_inv (I:=I) (ω:=ω) (idx:=47) (bound:=.var 2)
      (body:=sampleCellCode) (M:=cellMax n m T) Inv hs0 (by
    intro u hu s' hs'
    rw [bound] at hu
    let k : Fin K := ⟨u,hu⟩
    have hrow := hs'.1.setLoop 47 u (by decide)
    have h46 : (s'.setN 47 u).ns 46 = j.val := by simpa [Store.setN] using hs'.2
    have h47 : (s'.setN 47 u).ns 47 = k.val := by simp [Store.setN,k]
    obtain ⟨l,hl,hw⟩ := sampleCell_exec (I:=I) (ω:=ω) (s'.setN 47 u)
    refine ⟨_,l,hl,hw.trans ?_,cell_invariant I ω _ i j k h46 h47 hrow,?_⟩
    · have hi : colIndex (s'.setN 47 u) = (columns n m T (i,j,k)).val := by
        simp [colIndex,hrow.index,hrow.static.choices,hrow.static.times,h46,h47,flat_col]
      have hd := (columns n m T (i,j,k)).isLt
      simp only [cellBudget,cellMax,hi,rowIndex,hrow.index]
      omega
    · simpa [cellState,Store.setR] using h46)
  rw [bound] at hh hc ht
  refine ⟨_,c,hc,ht,?_⟩
  have hh' := hh.1.setLoop 47 K (by decide)
  simpa [K,Nat.add_mul] using hh'

private theorem scan_choices {I : Instance n m T} {ω : ℕ → ℝ} {s : Store} (i : Fin n)
    (h : InRow I ω i 0 s) :
    ∃ v c, Exec I ω (.forN 46 (.var 1) (.forN 47 (.var 2) sampleCellCode)) s v c ∧
      c ≤ choiceScanBudget n m T ∧ InRow I ω i (Width m T) v := by
  let Inv (j : ℕ) := InRow I ω i (j*labelCount T)
  have bound : (N.var 1).eval s = m := h.static.choices
  obtain ⟨v,c,hc,ht,hh⟩ := forN_inv (I:=I) (ω:=ω) (idx:=46) (bound:=.var 1)
      (body:=.forN 47 (.var 2) sampleCellCode) (M:=timeScanBudget n m T) Inv (by simpa [Inv] using h) (by
    intro u hu s' hu'
    rw [bound] at hu
    have hi := hu'.setLoop 46 u (by decide)
    exact scan_times i (⟨u,hu⟩ : Fin m) (by simp [Store.setN]) hi)
  rw [bound] at hh hc ht
  exact ⟨_,c,hc,ht,hh.setLoop 46 m (by decide)⟩

private theorem start_row {I : Instance n m T} {ω : ℕ → ℝ} {s : Store} (i : Fin n)
    (hd : Done I ω i.val s) (hi : s.ns 45 = i.val) (hdr : s.draws = i.val) :
    ∃ v c, Exec I ω
      (.seq (.uniform 45) (.seq (.letR 46 0) (.seq (.put 9 (.var 45) 0)
        (.forN 46 (.var 1) (.forN 47 (.var 2) sampleCellCode))))) s v c ∧
      c ≤ sampleItemBudget n m T ∧ Done I ω (i.val+1) v ∧ v.draws = i.val+1 := by
  let s1 := {s.setR 45 (ω s.draws) with draws := s.draws+1}
  let s2 := s1.setR 46 0
  let s3 := s2.put 9 (s.ns 45) 0
  have ss : SamplingInputs I s3 := by
    obtain ⟨hn,hm,hk,ht,htab,hw,hv⟩ := hd.static
    constructor <;> simp [s3,s2,s1,Store.put,Store.setR, hn,hm,hk,ht,htab,hw,hv]
  have hrow : InRow I ω i 0 s3 := by
    refine ⟨⟨ss,?_⟩,hi,by simp [s3,s2,s1,Store.put,Store.setR,hdr],?_,?_,?_⟩
    · intro z hz
      have hz' : z.val ≠ s.ns 45 := by omega
      apply markRep_tab (s:=s) _ _ _ _ (hd.marks _ hz)
      all_goals simp [s3,s2,s1,Store.put,Store.setR,hz']
    · simp [s3,s2,s1,Store.put,Store.setR,hdr]
    · simp [s3,s2,s1,Store.put,Store.setR,cellStart]
    · simp [prefix_zero,MarkRep,s3,s2,s1,Store.put,Store.setR,hi]
  obtain ⟨v,c,hc,ht,hh⟩ := scan_choices i hrow
  have h1 : Exec I ω (.uniform 45) s s1 1 := Exec.uniform _ _
  have h2 := Exec.letR (I:=I) (ω:=ω) s1 46 (0:R)
  have h3 := Exec.put (I:=I) (ω:=ω) s2 9 (.var 45) (0:R)
  have hz (u : Store) : (0:R).eval u = 0 := by change ((0:ℕ):ℝ) = 0; norm_num
  rw [hz] at h2 h3
  refine ⟨v,_,Exec.seq h1 (Exec.seq h2 (Exec.seq h3 hc)),?_,⟨hh.static,?_⟩,hh.draws⟩
  · simp [s2,s1,Store.setR,R.work,N.work,N.eval,tableOffset,sampleItemBudget,hi] at *; omega
  · intro z hz'
    by_cases e : z = i
    · subst z; simpa [prefix_all,chosenMarks] using hh.marked
    · exact hh.marks _ (by have hn : z.val ≠ i.val := fun h => e (Fin.ext h); omega)

theorem sampleRows_exec {I : Instance n m T} {ω : ℕ → ℝ} {s : Store}
    (h : SamplingInputs I s) (hdraws : s.draws = 0) :
    ∃ v c, Exec I ω sampleRowsCode s v c ∧ c ≤ sampleBudget n m T ∧ Done I ω n v ∧ v.draws=n := by
  let Inv (j : ℕ) (u : Store) := Done I ω j u ∧ u.draws=j
  have h0 : Inv 0 s := ⟨⟨h,by simp⟩,hdraws⟩
  let body : C := .seq (.uniform 45) (.seq (.letR 46 0) (.seq (.put 9 (.var 45) 0)
        (.forN 46 (.var 1) (.forN 47 (.var 2) sampleCellCode))))
  have bound : (N.var 0).eval s = n := h.items
  obtain ⟨v,c,hc,ht,hh⟩ := forN_inv (I:=I) (ω:=ω) (idx:=45) (bound:=.var 0)
      (body:=body) (M:=sampleItemBudget n m T) Inv h0 (by
    intro j hj u hu
    rw [bound] at hj
    let i : Fin n := ⟨j,hj⟩
    have dd : Done I ω j (u.setN 45 j) := ⟨static_setN _ _ hu.1.static _ _ (by decide),hu.1.marks⟩
    exact start_row i dd (by simp [Store.setN,i]) hu.2)
  rw [bound] at hc ht hh
  exact ⟨_,c,hc,ht,⟨static_setN _ _ hh.1.static _ _ (by decide),hh.1.marks⟩,hh.2⟩

end PandoraKnapsack.Skipping.ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM
variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

structure OutputsReady (a : Marks n m T) (s : Store) : Prop where
  items : s.ns 0 = n
  times : s.ns 2 = labelCount T
  cap : s.rs 0 = T
  labels : ∀ k : Fin (labelCount T), s.tab 0 k.val = timeLabel k
  marks : ∀ i, MarkRep s i (a i)
  draws : s.draws = n

/-- All entries in a prefix are written to the designated output cells. -/
def Encoded (T : ℕ) (s : Store) (l : List (Triple n m)) : Prop :=
  ∀ r (e : Triple n m), l[r]? = some e →
    s.out (1+3*r) = e.1.val ∧ s.out (2+3*r) = e.2.1.val ∧
    s.out (3+3*r) = (T-e.2.2 : ℕ)

def write3 (s : Store) (l : ℕ) (a b c : ℝ) : Store :=
  (((s.writeOut (1+3*l) a).writeOut (2+3*l) b).writeOut (3+3*l) c).setN 48 (l+1)

private lemma append_encoded (s : Store) (l : List (Triple n m)) (e : Triple n m) (hl : Encoded T s l) :
    Encoded T (write3 s l.length e.1.val e.2.1.val (T-e.2.2 : ℕ)) (l++[e]) := by
  intro r f hf
  by_cases hr : r < l.length
  · have old := hl r f (by rwa [List.getElem?_append_left hr] at hf)
    have keep (p q : ℕ) (hp : 1 ≤ p) (hp' : p ≤ 3) (hq : 1 ≤ q) (hq' : q ≤ 3) :
        p+3*r ≠ q+3*l.length := by omega
    simpa (disch := omega) only [write3,Store.setN,Store.writeOut,Function.update_of_ne] using old
  · have heq : r = l.length := by
      have hlen := List.getElem?_eq_some_iff.mp hf |>.choose
      simp at hlen
      omega
    subst r
    rw [List.getElem?_append_right le_rfl] at hf
    simp only [Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] at hf
    subst f
    simp [write3,Store.setN,Store.writeOut,Function.update_of_ne,
      show 1+3*l.length ≠ 2+3*l.length by omega,show 1+3*l.length ≠ 3+3*l.length by omega,
      show 2+3*l.length ≠ 3+3*l.length by omega]

noncomputable def emitState (s : Store) := write3 s (s.ns 48) (s.ns 45) (s.tab 10 (s.ns 45)) (s.rs 0 - s.tab 0 (s.ns 47))

private lemma emit_exec (s : Store) :
    ∃ k, Exec I ω emitEntryCode s (emitState s) k ∧ k ≤ 700*(1+s.ns 48+s.ns 45+s.ns 47) := by
  let s1 := s.writeOut (1+3*s.ns 48) (s.ns 45)
  let s2 := s1.writeOut (2+3*s.ns 48) (s.tab 10 (s.ns 45))
  let s3 := s2.writeOut (3+3*s.ns 48) (s.rs 0 - s.tab 0 (s.ns 47))
  have h1 := Exec.out (I:=I) (ω:=ω) s (1+3*.var 48) (.nat (.var 45))
  have h2 := Exec.out (I:=I) (ω:=ω) s1 (2+3*.var 48) (.get 10 (.var 45))
  have h3 := Exec.out (I:=I) (ω:=ω) s2 (3+3*.var 48) (.var 0 - .get 0 (.var 47))
  have h4 := Exec.letN (I:=I) (ω:=ω) s3 48 (.var 48+1)
  refine ⟨_,Exec.seq h1 (Exec.seq h2 (Exec.seq h3 h4)),?_⟩
  simp [R.work,R.eval,N.work,N.eval,tableOffset,s1,s2,s3,Store.writeOut]
  omega

private lemma emit_if_exec (s : Store) :
    ∃ k, Exec I ω emitIfCode s
      (if s.tab 9 (s.ns 45) = (s.ns 47:ℝ)+1 then emitState s else s) k ∧
      k ≤ 1000*(1+s.ns 48+s.ns 45+s.ns 47) := by
  let m := s.tab 9 (s.ns 45)
  let h : ℝ := (s.ns 47:ℝ)+1
  change ∃ k, Exec I ω _ _ (if m = h then _ else _) k ∧ _
  by_cases h1 : h < m
  · rw [if_neg (ne_of_gt h1)]
    refine ⟨_,Exec.ite_true ?_ (Exec.skip _),?_⟩
    · simpa [R.eval,N.eval,m,h] using h1
    · simp [N.work,R.work,tableOffset,N.eval]; omega
  · by_cases h2 : m < h
    · rw [if_neg (ne_of_lt h2)]
      refine ⟨_,Exec.ite_false ?_ (Exec.ite_true ?_ (Exec.skip _)),?_⟩
      · simpa [R.eval,N.eval,m,h] using le_of_not_gt h1
      · simpa [R.eval,N.eval,m,h] using h2
      · simp [N.work,R.work,tableOffset,N.eval]; omega
    · have he := le_antisymm (le_of_not_gt h1) (le_of_not_gt h2)
      rw [if_pos he]
      obtain ⟨k,hk,hw⟩ := emit_exec (I:=I) (ω:=ω) s
      refine ⟨_,Exec.ite_false ?_ (Exec.ite_false ?_ hk),?_⟩
      · simpa [R.eval,N.eval,m,h] using le_of_not_gt h1
      · simpa [R.eval,N.eval,m,h] using le_of_not_gt h2
      · simp [N.work,R.work,tableOffset,N.eval]; omega

structure Emitted (a : Marks n m T) (l : List (Triple n m)) (s : Store) : Prop
    extends OutputsReady a s where
  count : s.ns 48 = l.length
  encoded : Encoded T s l

private lemma emit_one (a : Marks n m T) (l : List (Triple n m)) (s : Store)
    (i : Fin n) (k : Fin (labelCount T)) (hi : s.ns 45 = i.val) (hk : s.ns 47 = k.val)
    (h : Emitted a l s) :
    ∃ v c, Exec I ω emitIfCode s v c ∧ c ≤ 1000*(1+l.length+i.val+k.val) ∧
      Emitted a (l ++ (entryAt a k i).toList) v ∧ v.ns 47 = k.val := by
  obtain ⟨c,hc,hcost⟩ := emit_if_exec (I:=I) (ω:=ω) s
  rw [hi,hk] at hc hcost
  rw [h.count] at hcost
  have hm := h.marks i
  rcases ha : a i with _ | ⟨j,k'⟩
  · rw [ha] at hm
    simp only [MarkRep] at hm
    rw [if_neg (by rw [hm]; positivity)] at hc
    exact ⟨_,c,hc,hcost,by simpa [entryAt,ha] using h,hk⟩
  · rw [ha] at hm
    obtain ⟨hmark,hj⟩ := hm
    by_cases he : k' = k
    · subst k'
      rw [if_pos hmark] at hc
      have ht : s.rs 0 - s.tab 0 (s.ns 47) = ((T-timeLabel k:ℕ):ℝ) := by
        rw [hk,h.labels,h.cap,Nat.cast_sub (samplingLabel_le _)]
      have hv : emitState s = write3 s l.length i.val j.val (T-timeLabel k:ℕ) := by
        simp [emitState,h.count,hi,hj,ht]
      refine ⟨_,c,hc,hcost,?_,?_⟩
      · have hentry := append_encoded (T:=T) s l (i,j,timeLabel k) h.encoded
        rw [hv]
        simp only [entryAt,ha,Option.bind_some,if_true,Option.toList_some]
        refine ⟨⟨?_,?_,h.cap,h.labels,h.marks,h.draws⟩,?_,hentry⟩
        · simpa [write3,Store.setN,Store.writeOut] using h.items
        · simpa [write3,Store.setN,Store.writeOut] using h.times
        · simp [write3,Store.setN,Store.writeOut]
      · simpa [emitState,write3,Store.setN,Store.writeOut] using hk
    · have hh : s.tab 9 i.val ≠ (k.val:ℝ)+1 := by
        rw [hmark]; exact fun e => he (Fin.ext (by exact_mod_cast add_right_cancel e))
      rw [if_neg hh] at hc
      exact ⟨_,c,hc,hcost,by simpa [entryAt,ha,he] using h,hk⟩

private lemma ready_setN {a : Marks n m T} {s : Store} (h : OutputsReady a s) (idx v : ℕ)
    (hr : 2 < idx) : OutputsReady a (s.setN idx v) := by
  refine ⟨?_,?_,h.cap,h.labels,h.marks,h.draws⟩
  · simpa [Store.setN,show 0 ≠ idx by omega] using h.items
  · simpa [Store.setN,show 2 ≠ idx by omega] using h.times
private lemma Emitted.setLoop {a : Marks n m T} {l s} (h : Emitted a l s) (idx v : ℕ)
    (hr : 2 < idx) (hc : 48 ≠ idx) : Emitted a l (s.setN idx v) := by
  refine ⟨ready_setN h.toOutputsReady _ _ hr,?_,h.encoded⟩
  simpa [Store.setN,hc] using h.count

private def beforeTime (a : Marks n m T) (r : ℕ) :=
  ((List.finRange (labelCount T)).take r).flatMap (atTime a)
private def beforeItem (a : Marks n m T) (h : Fin (labelCount T)) (r : ℕ) :=
  ((List.finRange n).take r).filterMap (entryAt a h)

private lemma before_time_len (a : Marks n m T) (r : ℕ) :
    (beforeTime a r).length ≤ labelCount T * n := by
  have h (l : List (Fin (labelCount T))) : (l.flatMap (atTime a)).length ≤ l.length*n := by
    induction l with
    | nil => simp
    | cons f l ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,one_mul]
      have hf : (atTime a f).length ≤ n := by
        simpa only [atTime,List.length_finRange] using List.length_filterMap_le (entryAt a f) (List.finRange n)
      omega
  apply (h _).trans
  apply Nat.mul_le_mul_right
  simp

private lemma before_item_len (a : Marks n m T) (h : Fin (labelCount T)) (r : ℕ) :
    (beforeItem a h r).length ≤ n := by
  apply (List.length_filterMap_le _ _).trans
  simp

def emitCellMax (n T : ℕ) := 1000*(1 + labelCount T*n+n+n+labelCount T)
def emitSweepBudget (n T : ℕ) := 5+5*n+n*emitCellMax n T
def emitBudget (n T : ℕ) := 20+5+5*labelCount T + labelCount T*emitSweepBudget n T

private lemma emit_sweep (a : Marks n m T) (k : Fin (labelCount T)) (s : Store)
    (h : Emitted a (beforeTime a k.val) s) (hk : s.ns 47 = k.val) :
    ∃ v c, Exec I ω (.forN 45 (.var 0) emitIfCode) s v c ∧ c ≤ emitSweepBudget n T ∧
      Emitted a (beforeTime a (k.val+1)) v := by
  let Inv (r : ℕ) (v : Store) := Emitted a (beforeTime a k.val ++ beforeItem a k r) v ∧ v.ns 47 = k.val
  have h0 : Inv 0 s := ⟨by simpa [beforeItem] using h,hk⟩
  have bound : (N.var 0).eval s = n := h.items
  obtain ⟨v,c,hc,ht,hh⟩ := forN_inv (I:=I) (ω:=ω) (idx:=45) (bound:=.var 0)
      (body:=emitIfCode) (M:=emitCellMax n T) Inv h0 (by
    intro r hr v hv
    rw [bound] at hr
    let i : Fin n := ⟨r,hr⟩
    have he := hv.1.setLoop 45 r (by decide) (by decide)
    obtain ⟨w,c,hw,hcost,hem,h47⟩ := emit_one (I:=I) (ω:=ω) a _ (v.setN 45 r) i k
      (by simp [Store.setN,i]) (by simpa [Store.setN] using hv.2) he
    refine ⟨w,c,hw,?_,?_,h47⟩
    · apply hcost.trans
      simp only [emitCellMax,List.length_append]
      have := before_time_len a k.val; have := before_item_len a k r
      dsimp [i]; omega
    · have hlist : beforeItem a k (r+1) = beforeItem a k r ++ (entryAt a k i).toList := by
        unfold beforeItem
        rw [List.take_succ_eq_append_getElem (by simpa using hr)]
        simp [i]
        cases he' : entryAt a k i <;> simp [List.filterMap,show entryAt a k ⟨r,hr⟩ = _ from he']
      simpa [hlist,List.append_assoc] using hem)
  rw [bound] at hc ht hh
  refine ⟨_,c,hc,ht,?_⟩
  have hpos : beforeTime a (k.val+1) = beforeTime a k.val ++ atTime a k := by
    unfold beforeTime
    rw [List.take_succ_eq_append_getElem (by simpa)]
    simp
  simpa [hpos,beforeItem,atTime,List.take_of_length_le (show (List.finRange n).length ≤ n by simp)] using hh.1.setLoop 45 n (by decide) (by decide)

private lemma sweep_all (a : Marks n m T) (s : Store) (h : Emitted a [] s) :
    ∃ v c, Exec I ω (.forN 47 (.var 2) (.forN 45 (.var 0) emitIfCode)) s v c ∧
      c ≤ 5+5*labelCount T + labelCount T*emitSweepBudget n T ∧ Emitted a (entries a) v := by
  let Inv (r : ℕ) := Emitted a (beforeTime a r)
  have h0 : Inv 0 s := by simpa [Inv,beforeTime] using h
  have bound : (N.var 2).eval s = labelCount T := h.times
  obtain ⟨v,c,hc,ht,hh⟩ := forN_inv (I:=I) (ω:=ω) (idx:=47) (bound:=.var 2)
      (body:=.forN 45 (.var 0) emitIfCode) (M:=emitSweepBudget n T) Inv h0 (by
    intro r hr u hu
    rw [bound] at hr
    let k : Fin (labelCount T) := ⟨r,hr⟩
    exact emit_sweep a k _ (hu.setLoop 47 r (by decide) (by decide)) (by simp [Store.setN,k]))
  rw [bound] at hc ht hh
  exact ⟨_,c,hc,ht,by simpa [Inv,beforeTime,entries,List.take_of_length_le (show (List.finRange (labelCount T)).length ≤ labelCount T by simp)] using hh.setLoop 47 (labelCount T) (by decide) (by decide)⟩

private lemma read_nat_cast (r : ℕ) : readNat (r:ℝ) = some r := by
  unfold readNat
  rw [dif_pos (show ∃ k : ℕ, (k:ℝ) = r from ⟨r,rfl⟩)]
  congr 1
  exact_mod_cast Nat.find_spec (show ∃ k : ℕ, (k:ℝ) = r from ⟨r,rfl⟩)

private lemma mapM_success {α β : Type*} (l : List α) (f : α → Option β) (g : α → β)
    (hs : ∀ x ∈ l, f x = some (g x)) : l.mapM f = some (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp [List.mapM_cons,hs a (.head _),ih (fun x hx => hs x (.tail _ hx))]

private lemma decode_encoded (T : ℕ) (s : Store) (l : List (Triple n m)) (mem : ℤ → ℝ)
    (hh : mem 0 = l.length) (he : Encoded T s l) (hpos : ∀ r : ℕ, r ≠ 0 → mem r = s.out r) :
    decodeOutput n m mem = some (l.map fun e => (e.1,e.2.1,T-e.2.2)) := by
  unfold decodeOutput
  rw [hh,read_nat_cast]
  let policy (e : Triple n m) := (e.1,e.2.1,T-e.2.2)
  have hd (r : Fin l.length) : decodeEntry n m mem r.val = some (policy (l.get r)) := by
    have hh' := he r.val (l.get r) (by simp)
    obtain ⟨e1,e2,e3⟩ := hh'
    have f1 : mem (1+3*(r.val:ℤ)) = ((l.get r).1.val:ℝ) := by simpa using (hpos (1+3*r.val) (by omega)).trans e1
    have f2 : mem (2+3*(r.val:ℤ)) = ((l.get r).2.1.val:ℝ) := by simpa using (hpos (2+3*r.val) (by omega)).trans e2
    have f3 : mem (3+3*(r.val:ℤ)) = ((T-(l.get r).2.2:ℕ):ℝ) := by simpa using (hpos (3+3*r.val) (by omega)).trans e3
    simp [decodeEntry,f1,f2,f3,read_nat_cast,policy,(l.get r).1.isLt,(l.get r).2.1.isLt]
  have hr : List.range l.length = (List.finRange l.length).map Fin.val := by
    apply List.ext_getElem <;> simp
  simp only [hr,List.mapM_map]
  rw [mapM_success (List.finRange l.length) (decodeEntry n m mem ∘ Fin.val) (fun r => policy (l.get r)) (fun r _ => hd r)]
  change some ((List.finRange l.length).map (policy ∘ l.get)) = some (l.map policy)
  rw [← List.map_map, List.map_get_finRange]

theorem emitRows_exec {a : Marks n m T} {s : Store} (h : OutputsReady a s) :
    ∃ v c, Exec I ω emitRowsCode s v c ∧ c ≤ emitBudget n T ∧ v.draws = n ∧
      ∀ mem : ℤ → ℝ, (∀ r : ℕ, mem r = v.out r) →
        decodeOutput n m mem = some (alg1Policy (markAssignment a)) := by
  have hh : Emitted a [] (s.setN 48 0) :=
    ⟨ready_setN h _ _ (by decide),by simp [Store.setN],by simp [Encoded]⟩
  obtain ⟨v,c,hc,ht,hr⟩ := sweep_all (I:=I) (ω:=ω) a _ hh
  have hinit := Exec.letN (I:=I) (ω:=ω) s 48 (0:N)
  have hlast := Exec.out (I:=I) (ω:=ω) v (0:N) (.nat (.var 48))
  refine ⟨_,_,Exec.seq hinit (Exec.seq hc hlast),?_,hr.draws,?_⟩
  · simp [N.work,R.work,R.eval,N.eval,emitBudget] at *; omega
  · intro mem hm
    rw [alg1Policy,← sorted_entries]
    refine decode_encoded T v _ mem ?_ hr.encoded ?_
    · simpa [N.eval,R.eval,Store.writeOut,hr.count] using hm 0
    · intro r hn
      simpa [N.eval,R.eval,Store.writeOut,hn] using hm r

end PandoraKnapsack.Skipping.ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM
variable {n m T : ℕ}

private def clockBound (n m K : ℕ) :=
  5+5*n+n*(200*(n+1)+(5+5*m+m*(5+5*K+K*(2000*(1+n*(m*K)+n))))) +
  (20+5+5*K+K*(5+5*n+n*(1000*(1+K*n+n+n+K))))

theorem samplingCost_poly (n m T : ℕ) :
    sampleBudget n m T + emitBudget n T ≤ (inputSize n m T+2)^24 := by
  change clockBound n m (labelCount T) ≤ _
  let z := inputSize n m T + 2
  have hn : n ≤ z := by simp [z,inputSize]; omega
  have hm : m ≤ z := by simp [z,inputSize]; omega
  have hk : labelCount T ≤ z := by
    unfold labelCount
    split_ifs with h
    · simp [z,inputSize]
    · have hl := Nat.lt_size.mpr (Nat.pow_log_le_self 2 h)
      dsimp [z,inputSize]; omega
  calc
    _ ≤ clockBound z z z := by unfold clockBound; gcongr
    _ ≤ z^24 := by
      obtain ⟨v,hv⟩ : ∃ v, z = v+2 := ⟨inputSize n m T,rfl⟩
      rw [hv]
      unfold clockBound
      zify
      rw [← sub_nonneg]
      ring_nf
      positivity

theorem sampling_exec {B : ℕ} (I : Instance n m T) (hB : n ≤ B)
    (ω : Fin B → unitInterval) (s : Store) (hs : SamplingInputs I s) (hdraws : s.draws = 0) :
    ∃ v c, Exec I (extendDraws ω) samplingCode s v c ∧ c ≤ (inputSize n m T+2)^24 ∧
      v.draws = n ∧ ∀ mem : ℤ → ℝ, (∀ r : ℕ, mem r = v.out r) →
        decodeOutput n m mem =
        some (alg1Policy (uniformAssignment hB (samplingLab m T) (dyadicPlan I) ω)) := by
  obtain ⟨u,c,hc,ht,hd,hu⟩ := sampleRows_exec (ω:=extendDraws ω) hs hdraws
  have ready : OutputsReady (chosenMarks I (extendDraws ω)) u :=
    ⟨hd.static.items,hd.static.times,hd.static.cap,hd.static.labels,fun i => hd.marks i i.isLt,hu⟩
  obtain ⟨v,k,hk,hb,hv,ho⟩ := emitRows_exec (I:=I) (ω:=extendDraws ω) ready
  refine ⟨v,c+k,Exec.seq hc hk,(Nat.add_le_add ht hb).trans (samplingCost_poly ..),hv,?_⟩
  simpa only [marks_assignment I hB ω] using ho

theorem samplingLab_inj (m T : ℕ) : Function.Injective (samplingLab m T) := by
  intro a b h
  apply finProdFinEquiv.symm.injective
  refine Prod.ext (congrArg (fun p : Fin m × Fin (T+1) => p.1) h) (label_strict.injective ?_)
  exact congrArg (fun v : Fin m × Fin (T+1) => v.2.val) h

theorem samplingLab_support (I : Instance n m T) (i : Fin n) (j : Fin m) (t : Fin (T+1))
    (h : dyadicPlan I i j t.val ≠ 0) : ∃ k, samplingLab m T k = (j,t) := by
  by_contra! hne
  apply h
  unfold dyadicPlan spreadVector
  apply Finset.sum_eq_zero
  intro k _
  apply if_neg
  intro he
  apply hne (finProdFinEquiv (j,k))
  simp [samplingLab,he,Fin.ext_iff]

end PandoraKnapsack.Skipping.ArrayRAM

open PandoraKnapsack.Skipping PandoraKnapsack.Skipping.ArrayRAM

theorem solution {n m T B : ℕ} (I : Instance n m T) (hB : n ≤ B)
    (ω : Fin B → unitInterval) (s : Store)
    (hitems : s.ns 0 = n) (hchoices : s.ns 1 = m) (htimes : s.ns 2 = labelCount T)
    (hcap : s.rs 0 = T)
    (hlabels : ∀ h : Fin (labelCount T), s.tab 0 h.val = timeLabel h)
    (hweights : ∀ c : Fin (columnCount n m T), s.tab 1 c.val = columnWeight I c)
    (hvector : ∀ c : Fin (columnCount n m T),
      s.tab 4 c.val = PandoraPacking.solve (packingRows I) (packingProfits I) c)
    (hdraws : s.draws = 0) :
    Function.Injective (samplingLab m T) ∧
    (∀ (i : Fin n) (j : Fin m) (t : Fin (T+1)), dyadicPlan I i j t.val ≠ 0 →
      ∃ k, samplingLab m T k = (j,t)) ∧
    ∃ v c, Exec I (extendDraws ω) samplingCode s v c ∧
      c ≤ (inputSize n m T+2)^24 ∧ v.draws = n ∧
      ∀ mem : ℤ → ℝ, (∀ r : ℕ, mem r = v.out r) →
        decodeOutput n m mem =
          some (alg1Policy (uniformAssignment hB (samplingLab m T) (dyadicPlan I) ω)) := by
  exact ⟨samplingLab_inj .., samplingLab_support I,
    sampling_exec I hB ω s ⟨hitems,hchoices,htimes,hcap,hlabels,hweights,hvector⟩ hdraws⟩
