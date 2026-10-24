-- Prove2me | solution 1 for PigeonholeDesign.Lower.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-23T10:24:03.799014+00:00
-- url     : https://prove2.me/submissions/67a915bc-1d2a-49e9-a558-0153538cb7b3

import Mathlib
import Definitions.Def_PigeonholeDesign_Lower_Setting

noncomputable section
open Finset PigeonholeDesign.Lower
namespace PigeonholeProof

def coinAvg {T : ℕ} (F : (Fin T → Bool) → ℝ) : ℝ := (∑ c, F c) / (2 : ℝ)^T

def sign (b : Bool) : ℝ := if b then 1 else -1

def cut {T : ℕ} (x : Fin T → ℝ) (w : Fin T → Bool) (a : ℝ) : ℝ :=
  ∑ t, if x t ≤ a then sign (w t) else 0

def midpoint {K : ℕ} (b : Breakpoints K) (i : Fin K) : ℝ :=
  (b.l i.castSucc + b.l i.succ)/2

def squareMass {K : ℕ} (b : Breakpoints K) : ℝ := ∑ i, len b i ^ 2

def pairedX {K N : ℕ} (b : Breakpoints K) (label : Fin N → Fin K) : Fin (2*N) → ℝ :=
  fun t => let i := label ⟨t.val/2, by omega⟩
           if t.val % 2 = 0 then b.l i.castSucc else midpoint b i

def spreadX (N r : ℕ) (hr : r ≤ N) (z : Fin r → ℝ) : Fin (2*N) → ℝ := by
  have _ := hr
  exact fun t => if ht : t.val < 2*(N-r) then 0 else
    if h : t.val < 2*(N-r)+r then z ⟨t.val-2*(N-r), by omega⟩ else 1

end PigeonholeProof
end

noncomputable section
open Finset
namespace PigeonholeProof

 theorem coinAvg_const {T : ℕ} (a : ℝ) : coinAvg (T := T) (fun _ => a) = a := by
  classical
  simp [coinAvg]

 theorem coinAvg_add {T : ℕ} (F G : (Fin T → Bool) → ℝ) :
    coinAvg (fun c => F c + G c) = coinAvg F + coinAvg G := by
  simp only [coinAvg, sum_add_distrib, add_div]

 theorem coinAvg_neg {T : ℕ} (F : (Fin T → Bool) → ℝ) :
    coinAvg (fun c => -F c) = -coinAvg F := by
  simp only [coinAvg, sum_neg_distrib, neg_div]

 theorem coinAvg_sub {T : ℕ} (F G : (Fin T → Bool) → ℝ) :
    coinAvg (fun c => F c - G c) = coinAvg F - coinAvg G := by
  simp only [coinAvg, sum_sub_distrib, sub_div]

 theorem coinAvg_mul_const {T : ℕ} (F : (Fin T → Bool) → ℝ) (a : ℝ) :
    coinAvg (fun c => F c * a) = coinAvg F * a := by
  unfold coinAvg
  rw [← sum_mul]
  ring

 theorem coinAvg_const_mul {T : ℕ} (a : ℝ) (F : (Fin T → Bool) → ℝ) :
    coinAvg (fun c => a * F c) = a * coinAvg F := by
  unfold coinAvg
  rw [← mul_sum]
  ring

 theorem coinAvg_sum {T : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → (Fin T → Bool) → ℝ) :
    coinAvg (fun c => ∑ i, F i c) = ∑ i, coinAvg (F i) := by
  unfold coinAvg
  rw [sum_comm, sum_div]

 theorem coinAvg_mono {T : ℕ} (F G : (Fin T → Bool) → ℝ)
    (h : ∀ c, F c ≤ G c) : coinAvg F ≤ coinAvg G := by
  exact div_le_div_of_nonneg_right (sum_le_sum fun c _ => h c) (by positivity)

 theorem coinAvg_nonneg {T : ℕ} (F : (Fin T → Bool) → ℝ)
    (h : ∀ c, 0 ≤ F c) : 0 ≤ coinAvg F := by
  have hh := coinAvg_mono (fun _ => 0) F h
  rw [coinAvg_const] at hh
  exact hh

 def coinFlip {T : ℕ} (i : Fin T) (c : Fin T → Bool) : Fin T → Bool :=
  Function.update c i (!c i)

 theorem coinFlip_same {T : ℕ} (i : Fin T) (c : Fin T → Bool) :
    coinFlip i c i = !c i := by
  simp only [coinFlip, Function.update_self]

 theorem coinFlip_other {T : ℕ} (i j : Fin T) (h : j ≠ i) (c : Fin T → Bool) :
    coinFlip i c j = c j := by
  exact Function.update_of_ne h _ _

 theorem coinFlip_involutive {T : ℕ} (i : Fin T) : Function.Involutive (coinFlip i) := by
  intro c
  funext j
  by_cases h : j = i
  · subst j
    rw [coinFlip_same, coinFlip_same, Bool.not_not]
  · rw [coinFlip_other i j h, coinFlip_other i j h]

 theorem coinAvg_flip {T : ℕ} (i : Fin T) (F : (Fin T → Bool) → ℝ) :
    coinAvg (fun c => F (coinFlip i c)) = coinAvg F := by
  unfold coinAvg
  rw [(coinFlip_involutive i).bijective.sum_comp F]

 theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

 theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

 theorem sign_four (b : Bool) : sign b ^ 4 = 1 := by
  cases b <;> norm_num [sign]

 theorem sign_cube (b : Bool) : sign b ^ 3 = sign b := by
  cases b <;> norm_num [sign]

 theorem coinAvg_fresh_sign {T : ℕ} (i : Fin T) (F : (Fin T → Bool) → ℝ)
    (hF : ∀ c, F (coinFlip i c) = F c) :
    coinAvg (fun c => F c * sign (c i)) = 0 := by
  have h := coinAvg_flip i (fun c => F c * sign (c i))
  simp only [hF, coinFlip_same, sign_not, mul_neg] at h
  rw [coinAvg_neg] at h
  linarith

end PigeonholeProof
end

noncomputable section
open Finset PigeonholeDesign.Upper
namespace PigeonholeProof

theorem bool_counts (l : List Bool) : l.count false + l.count true = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases a <;> simp only [List.count_cons, List.length_cons] <;> norm_num <;> omega

theorem run_length {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι)
    (coin : ℕ → Bool) (n : ℕ) : (prefixAssign T cell coin n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prefixAssign, ih]

theorem run_caps {ι : Type*} [DecidableEq ι] (N : ℕ) (cell : ℕ → ι)
    (coin : ℕ → Bool) (n : ℕ) (hn : n ≤ 2*N) :
    (prefixAssign (2*N) cell coin n).count false ≤ N ∧
      (prefixAssign (2*N) cell coin n).count true ≤ N := by
  induction n with
  | zero => simp [prefixAssign]
  | succ n ih =>
    have ih := ih (by omega)
    have hc := bool_counts (prefixAssign (2*N) cell coin n)
    rw [run_length] at hc
    simp only [prefixAssign, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    split_ifs <;> cases hcoin : coin n <;> simp_all <;> omega

theorem count_ofFn_bool {n : ℕ} (w : Fin n → Bool) (b : Bool) :
    (List.ofFn w).count b = (univ.filter (fun t => w t = b)).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.count_cons, ih, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Fin.sum_univ_succ]
    cases b <;> cases h : w 0 <;> simp [Nat.add_comm]

theorem list_ofFn_getD (l : List Bool) :
    List.ofFn (fun t : Fin l.length => l.getD t false) = l := by
  simpa only [List.getD_eq_get] using List.ofFn_get l

theorem assign_balanced {T : ℕ} (hT : Even T) {ι : Type*} [DecidableEq ι]
    (hole : ℝ → ι) (x : Fin T → ℝ) (coin : Fin T → Bool) :
    (univ.filter (fun t => assign hole x coin t = false)).card =
      (univ.filter (fun t => assign hole x coin t = true)).card := by
  obtain ⟨N, hN⟩ := hT
  have hT : T=2*N := by omega
  clear hN
  subst T
  let l := prefixAssign (2*N) (cellOf hole x) (coinOf coin) (2*N)
  have hl : l.length = 2*N := run_length ..
  have hc := run_caps N (cellOf hole x) (coinOf coin) (2*N) le_rfl
  have hsum := bool_counts l
  have heq : l.count false = l.count true := by dsimp [l] at hsum ⊢; rw [run_length] at hsum; omega
  have hf : List.ofFn (assign hole x coin) = l := by
    apply List.ext_getElem
    · simpa using hl.symm
    · intro i hi hj
      simp [PigeonholeDesign.Upper.assign, l, hj]
  rw [← count_ofFn_bool, ← count_ofFn_bool, hf]
  exact heq


def localCount {ι : Type*} [DecidableEq ι] (cell : ℕ → ι) (L : List Bool)
    (c : ι) (v : Bool) : ℕ :=
  ((List.range L.length).zip L).countP (fun sb => cell sb.1 = c ∧ sb.2 = v)

theorem localCount_append {ι : Type*} [DecidableEq ι] (cell : ℕ → ι)
    (L : List Bool) (c : ι) (v w : Bool) :
    localCount cell (L ++ [w]) c v = localCount cell L c v +
      if cell L.length = c ∧ w = v then 1 else 0 := by
  unfold localCount
  simp only [List.length_append, List.length_singleton, List.range_succ]
  rw [List.zip_append (by simp)]
  simp

theorem run_step {ι : Type*} [DecidableEq ι] (N : ℕ) (cell : ℕ → ι)
    (coin : ℕ → Bool) (n : ℕ) :
    prefixAssign (2*N) cell coin (n+1) =
      let L := prefixAssign (2*N) cell coin n
      L ++ [if L.count false = N then true else if L.count true = N then false
        else if localCount cell L (cell n) false < localCount cell L (cell n) true then false
        else if localCount cell L (cell n) true < localCount cell L (cell n) false then true
        else coin n] := by
  simp only [prefixAssign, localCount, run_length, Nat.mul_div_cancel_left _ (by omega : 0<2)]

theorem paired_prefix_balanced {ι : Type*} [DecidableEq ι] (N q : ℕ)
    (cell : ℕ → ι) (coin : ℕ → Bool) (hq : q ≤ N)
    (hcell : ∀ j < q, cell (2*j+1) = cell (2*j)) :
    (prefixAssign (2*N) cell coin (2*q)).count false = q ∧
    (prefixAssign (2*N) cell coin (2*q)).count true = q ∧
    ∀ c, localCount cell (prefixAssign (2*N) cell coin (2*q)) c false =
      localCount cell (prefixAssign (2*N) cell coin (2*q)) c true := by
  induction q with
  | zero => simp [prefixAssign, localCount]
  | succ q ih =>
    obtain ⟨hf, ht, hl⟩ := ih (by omega) (fun j hj => hcell j (by omega))
    have hqN : q < N := by omega
    have hfirst : prefixAssign (2*N) cell coin (2*q+1) =
        prefixAssign (2*N) cell coin (2*q) ++ [coin (2*q)] := by
      rw [run_step]
      simp [hf, ht, ne_of_lt hqN, hl]
    have hsecond : prefixAssign (2*N) cell coin (2*q+2) =
        (prefixAssign (2*N) cell coin (2*q) ++ [coin (2*q)]) ++ [!(coin (2*q))] := by
      rw [show 2*q+2=(2*q+1)+1 by omega, run_step, hfirst]
      simp only [List.count_append, List.count_singleton, localCount_append, run_length,
        hcell q (by omega), hf, ht]
      cases hc : coin (2*q) <;> simp [hl, hqN.ne]
    rw [show 2*(q+1)=2*q+2 by omega, hsecond]
    refine ⟨?_, ?_, ?_⟩
    · cases hc : coin (2*q) <;> simp [hf]
    · cases hc : coin (2*q) <;> simp [ht]
    · intro c
      simp only [localCount_append, List.length_append, List.length_singleton, run_length,
        hcell q (by omega)]
      cases hc : coin (2*q) <;> by_cases hh : cell (2*q)=c <;> simp [hh, hl]

theorem paired_prefix_step {ι : Type*} [DecidableEq ι] (N q : ℕ)
    (cell : ℕ → ι) (coin : ℕ → Bool) (hq : q < N)
    (hcell : ∀ j ≤ q, cell (2*j+1) = cell (2*j)) :
    prefixAssign (2*N) cell coin (2*q+2) =
      (prefixAssign (2*N) cell coin (2*q) ++ [coin (2*q)]) ++ [!(coin (2*q))] := by
  obtain ⟨hf, ht, hl⟩ := paired_prefix_balanced N q cell coin hq.le
    (fun j hj => hcell j (by omega))
  have hfirst : prefixAssign (2*N) cell coin (2*q+1) =
      prefixAssign (2*N) cell coin (2*q) ++ [coin (2*q)] := by
    rw [run_step]
    simp [hf, ht, ne_of_lt hq, hl]
  rw [show 2*q+2=(2*q+1)+1 by omega, run_step, hfirst]
  simp only [List.count_append, List.count_singleton, localCount_append, run_length,
    hcell q le_rfl, hf, ht]
  cases hc : coin (2*q) <;> simp [hl, hq.ne]

theorem prefix_mono {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι)
    (coin : ℕ → Bool) {n m : ℕ} (h : n ≤ m) :
    (prefixAssign T cell coin n).IsPrefix (prefixAssign T cell coin m) := by
  induction m with
  | zero =>
    have hn : n=0 := by omega
    subst n
    exact ⟨[], by simp⟩
  | succ m ih =>
    by_cases hn : n ≤ m
    · apply (ih hn).trans
      conv_rhs => rw [prefixAssign]
      exact List.prefix_append _ _
    · have : n=m+1 := by omega
      subst n
      exact ⟨[], by simp⟩


 theorem prefix_getD {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι)
    (coin : ℕ → Bool) {n m t : ℕ} (hnm : n ≤ m) (ht : t < n) :
    (PigeonholeDesign.Upper.prefixAssign T cell coin n).getD t false =
      (PigeonholeDesign.Upper.prefixAssign T cell coin m).getD t false := by
  have h := (prefix_mono T cell coin hnm).getElem (by simpa only [run_length] using ht)
  simpa only [List.getD_eq_getElem, run_length, ht, if_pos, lt_of_lt_of_le ht hnm] using h


/- Draft fragment only. Insert in RunInvariants after prefix_getD (relocated from PairedRun).
No import, compilation, or checked-PASS claim. Existing namespace opens Finset and Upper.
All helper proofs below are fresh; no prior accepted implementation was copied. -/

theorem prefix_count_growth {ι : Type*} [DecidableEq ι] (N n j : ℕ)
    (cell : ℕ → ι) (coin : ℕ → Bool) (v : Bool) :
    (prefixAssign (2*N) cell coin (n+j)).count v ≤
      (prefixAssign (2*N) cell coin n).count v + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show n+(j+1)=(n+j)+1 by omega, run_step]
    simp only [List.count_append, List.count_singleton]
    split_ifs <;> omega

theorem localCount_skip {ι : Type*} [DecidableEq ι] (N n j : ℕ)
    (cell : ℕ → ι) (coin : ℕ → Bool) (c : ι) (v : Bool)
    (hskip : ∀ k < j, cell (n+k) ≠ c) :
    localCount cell (prefixAssign (2*N) cell coin (n+j)) c v =
      localCount cell (prefixAssign (2*N) cell coin n) c v := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show n+(j+1)=(n+j)+1 by omega, run_step, localCount_append, run_length]
    simp only [hskip j (by omega), false_and, if_false, add_zero]
    exact ih (fun k hk => hskip k (by omega))

theorem fresh_block_step {ι : Type*} [DecidableEq ι] (N r : ℕ) (hr : r ≤ N)
    (cell : ℕ → ι) (coin : ℕ → Bool)
    (hpad : ∀ j < N-r, cell (2*j+1) = cell (2*j))
    (hfresh : ∀ i j, i < r → j < r → cell (2*(N-r)+i) = cell (2*(N-r)+j) → i=j)
    (j : ℕ) (hj : j < r) :
    prefixAssign (2*N) cell coin (2*(N-r)+j+1) =
      prefixAssign (2*N) cell coin (2*(N-r)+j) ++ [coin (2*(N-r)+j)] := by
  obtain ⟨hf, ht, hl⟩ := paired_prefix_balanced N (N-r) cell coin (by omega) hpad
  have hcf := prefix_count_growth N (2*(N-r)) j cell coin false
  have hct := prefix_count_growth N (2*(N-r)) j cell coin true
  rw [hf] at hcf
  rw [ht] at hct
  have hnf : (prefixAssign (2*N) cell coin (2*(N-r)+j)).count false ≠ N := by omega
  have hnt : (prefixAssign (2*N) cell coin (2*(N-r)+j)).count true ≠ N := by omega
  have hskip : ∀ k < j, cell (2*(N-r)+k) ≠ cell (2*(N-r)+j) := by
    intro k hk he
    have := hfresh k j (by omega) hj he
    omega
  have hlf := localCount_skip N (2*(N-r)) j cell coin (cell (2*(N-r)+j)) false hskip
  have hlt := localCount_skip N (2*(N-r)) j cell coin (cell (2*(N-r)+j)) true hskip
  rw [run_step]
  simp [hnf, hnt, hlf, hlt, hl]

theorem fresh_block_assignment {ι : Type*} [DecidableEq ι] (N r : ℕ) (hr : r ≤ N)
    (cell : ℕ → ι) (coin : ℕ → Bool)
    (hpad : ∀ j < N-r, cell (2*j+1) = cell (2*j))
    (hfresh : ∀ i j, i < r → j < r → cell (2*(N-r)+i) = cell (2*(N-r)+j) → i=j)
    (j : ℕ) (hj : j < r) :
    (prefixAssign (2*N) cell coin (2*N)).getD (2*(N-r)+j) false =
      coin (2*(N-r)+j) := by
  have hs := fresh_block_step N r hr cell coin hpad hfresh j hj
  have hg := prefix_getD (2*N) cell coin (n:=2*(N-r)+j+1) (m:=2*N)
    (t:=2*(N-r)+j) (by omega) (by omega)
  rw [hs] at hg
  rw [← hg, List.getD_append_right _ _ _ _ (by rw [run_length])]
  simp [run_length]

theorem list_sign_sum (l : List Bool) :
    (l.map sign).sum = (l.count true : ℝ) - (l.count false : ℝ) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    cases v <;> simp [sign, ih, Nat.cast_add] <;> ring

theorem list_getD_sign_sum (l : List Bool) :
    (∑ t ∈ range l.length, sign (l.getD t false)) =
      (l.count true : ℝ) - (l.count false : ℝ) := by
  rw [Finset.sum_range, ← List.sum_ofFn]
  have h : List.ofFn (fun t : Fin l.length => sign (l.getD t false)) = l.map sign := by
    calc
      List.ofFn (fun t : Fin l.length => sign (l.getD t false)) =
          (List.ofFn (fun t : Fin l.length => l.getD t false)).map sign := by
        rw [List.map_ofFn]
        rfl
      _ = l.map sign := by rw [list_ofFn_getD]
  rw [h, list_sign_sum]

theorem spread_run_cut {K N r : ℕ} (b : PigeonholeDesign.Lower.Breakpoints K) (hr : r ≤ N)
    (z : Fin r → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0:ℝ) (1/2))
    (hcell : Function.Injective (fun i => PigeonholeDesign.Lower.intervalHole b (z i)))
    (coin : Fin (2*N) → Bool) :
    cut (spreadX N r hr z) (assign (PigeonholeDesign.Lower.intervalHole b) (spreadX N r hr z) coin) (1/2) =
      ∑ i : Fin r, sign (coin ⟨2*(N-r)+i.val, by omega⟩) := by
  classical
  let P := 2*(N-r)
  let x := spreadX N r hr z
  let cell := cellOf (PigeonholeDesign.Lower.intervalHole b) x
  let co := coinOf coin
  let L := prefixAssign (2*N) cell co (2*N)
  have hzero (t : Fin (2*N)) (ht : t.val < P) : x t = 0 := by
    simp [x, spreadX, P, ht]
  have hzval (j : Fin r) : x ⟨P+j.val, by dsimp [P]; omega⟩ = z j := by
    simp [x, spreadX, P, show ¬ 2*(N-r)+j.val < 2*(N-r) by omega,
      show 2*(N-r)+j.val < 2*(N-r)+r by omega]
  have hone (t : Fin (2*N)) (ht : P+r ≤ t.val) : x t = 1 := by
    simp [x, spreadX, show ¬t.val<2*(N-r) by dsimp [P] at ht; omega,
      show ¬t.val<2*(N-r)+r by dsimp [P] at ht; omega]
  have hpad : ∀ j < N-r, cell (2*j+1) = cell (2*j) := by
    intro j hj
    have h0 : 2*j < 2*N := by omega
    have h1 : 2*j+1 < 2*N := by omega
    simp only [cell, cellOf, dif_pos h0, dif_pos h1]
    rw [hzero _ (by dsimp [P]; omega), hzero _ (by dsimp [P]; omega)]
  have hfresh : ∀ i j, i < r → j < r → cell (P+i) = cell (P+j) → i=j := by
    intro i j hi hj he
    have hiT : P+i < 2*N := by dsimp [P]; omega
    have hjT : P+j < 2*N := by dsimp [P]; omega
    simp only [cell, cellOf, dif_pos hiT, dif_pos hjT, Option.some.injEq] at he
    rw [hzval ⟨i,hi⟩, hzval ⟨j,hj⟩] at he
    have h := hcell he
    exact congrArg Fin.val h
  have hassign (j : Fin r) : L.getD (P+j.val) false = coin ⟨P+j.val, by dsimp [P]; omega⟩ := by
    have h := fresh_block_assignment N r hr cell co hpad hfresh j.val j.isLt
    simpa [L, co, coinOf, P, show 2*(N-r)+j.val < 2*N by omega] using h
  let F : ℕ → ℝ := fun t => if ht : t < 2*N then
      if x ⟨t,ht⟩ ≤ 1/2 then sign (L.getD t false) else 0 else 0
  have hcut : cut x (assign (PigeonholeDesign.Lower.intervalHole b) x coin) (1/2) =
      ∑ t ∈ range (2*N), F t := by
    unfold cut
    rw [Finset.sum_range]
    apply sum_congr rfl
    intro t _
    simp only [F, dif_pos t.isLt, assign, L, cell, co]
  have hpadSum : (∑ t ∈ range P, F t) = 0 := by
    obtain ⟨hf, ht, _⟩ := paired_prefix_balanced N (N-r) cell co (by omega) hpad
    have hsum := list_getD_sign_sum (prefixAssign (2*N) cell co P)
    rw [run_length] at hsum
    rw [show P=2*(N-r) from rfl, hf, ht, sub_self] at hsum
    calc
      (∑ t ∈ range P, F t) = ∑ t ∈ range P, sign ((prefixAssign (2*N) cell co P).getD t false) := by
        apply sum_congr rfl
        intro t ht
        have htP := mem_range.mp ht
        have htT : t < 2*N := by dsimp [P] at htP; omega
        have hp := prefix_getD (2*N) cell co (n:=P) (m:=2*N) (t:=t) (by dsimp [P]; omega) htP
        simp only [F, dif_pos htT, hzero ⟨t,htT⟩ htP, show (0:ℝ)≤1/2 by norm_num, if_true]
        exact congrArg sign hp.symm
      _ = 0 := hsum
  have hfreshSum : (∑ j ∈ range r, F (P+j)) = ∑ i : Fin r, sign (coin ⟨P+i.val, by dsimp [P]; omega⟩) := by
    rw [Finset.sum_range]
    apply sum_congr rfl
    intro j _
    have hjT : P+j.val < 2*N := by dsimp [P]; omega
    simp only [F, dif_pos hjT, hzval, if_pos (hz j).2, hassign]
  have htailSum : (∑ j ∈ range r, F (P+r+j)) = 0 := by
    apply sum_eq_zero
    intro j hj
    have hjr := mem_range.mp hj
    have hjT : P+r+j < 2*N := by dsimp [P]; omega
    simp only [F, dif_pos hjT, hone ⟨P+r+j,hjT⟩ (by simp)]
    norm_num
  change cut x (assign (PigeonholeDesign.Lower.intervalHole b) x coin) (1/2) = _
  rw [hcut]
  calc
    (∑ t ∈ range (2*N), F t) = ∑ t ∈ range ((P+r)+r), F t := by
      have heq : 2*N=(P+r)+r := by dsimp [P]; omega
      rw [heq]
    _ = (∑ t ∈ range P, F t) + (∑ j ∈ range r, F (P+j)) +
          (∑ j ∈ range r, F (P+r+j)) := by
      rw [sum_range_add, sum_range_add]
    _ = _ := by rw [hpadSum, hfreshSum, htailSum]; simp only [zero_add, add_zero]; rfl

end PigeonholeProof
end

noncomputable section
open Finset PigeonholeDesign.Lower
namespace PigeonholeProof

theorem breakpoint_bounds {K : ℕ} (b : Breakpoints K) (i : Fin (K+1)) :
    0 ≤ b.l i ∧ b.l i ≤ 1 := by
  constructor
  · simpa [b.zero] using b.strictMono.monotone (show (0 : Fin (K+1)) ≤ i by exact Fin.zero_le i)
  · simpa [b.last] using b.strictMono.monotone (Fin.le_last i)

theorem midpoint_bounds {K : ℕ} (b : Breakpoints K) (i : Fin K) :
    b.l i.castSucc < midpoint b i ∧ midpoint b i < b.l i.succ := by
  have h := b.strictMono (show i.castSucc < i.succ by simp)
  dsimp [midpoint]; constructor <;> linarith

theorem intervalHole_mem {K : ℕ} (b : Breakpoints K) (i : Fin K) (x : ℝ)
    (hx0 : b.l i.castSucc ≤ x) (hx1 : x < b.l i.succ) : intervalHole b x = i.val := by
  have hs : (univ.filter (fun j : Fin (K+1) => 0 < j.val ∧ j.val < K ∧ b.l j ≤ x)) =
      Ioc (0 : Fin (K+1)) i.castSucc := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_Ioc]
    constructor
    · rintro ⟨hj0, _, hjx⟩
      refine ⟨hj0, ?_⟩
      by_contra h
      have hj : i.succ ≤ j := by
        change i.val+1 ≤ j.val
        change ¬j.val ≤ i.val at h
        omega
      have := b.strictMono.monotone hj
      linarith
    · rintro ⟨hj0, hj⟩
      have hjval : j.val ≤ i.val := hj
      have hzero : 0 < j.val := hj0
      refine ⟨hzero, by omega, (b.strictMono.monotone hj).trans hx0⟩
  unfold intervalHole
  rw [hs, Fin.card_Ioc]
  simp

theorem fin_telescope (n : ℕ) (f : Fin (n+1) → ℝ) :
    (∑ i : Fin n, (f i.succ - f i.castSucc)) = f (Fin.last n) - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have h := ih (fun i => f i.succ)
    simp only [Fin.succ_last, Fin.castSucc_zero, Fin.castSucc_succ] at h ⊢
    rw [h]
    ring

theorem lengths_properties {K : ℕ} (hK : 1 ≤ K) (b : Breakpoints K) :
    (∀ i, 0 < len b i) ∧ (∑ i, len b i) = 1 ∧ 0 < squareMass b := by
  have hp : ∀ i, 0 < len b i := fun i => sub_pos.mpr (b.strictMono (by simp))
  have hs : (∑ i, len b i) = 1 := by
    simpa [len, b.last, b.zero] using fin_telescope K b.l
  refine ⟨hp, hs, ?_⟩
  apply sum_pos
  · intro i _; exact sq_pos_of_pos (hp i)
  · exact ⟨⟨0, by omega⟩, mem_univ _⟩


theorem sqrt_floor_lower (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt x - 1 ≤ Real.sqrt (⌊x⌋₊ : ℝ) := by
  have hf := Nat.lt_floor_add_one x
  have hs := Real.sq_sqrt hx
  have hq := Real.sq_sqrt (Nat.cast_nonneg ⌊x⌋₊ : (0:ℝ) ≤ ⌊x⌋₊)
  have hp := Real.sqrt_nonneg x
  have hpq := Real.sqrt_nonneg (⌊x⌋₊ : ℝ)
  by_cases h : Real.sqrt x ≤ 1
  · linarith
  · nlinarith

theorem allocation_exists {K : ℕ} (hK : 1 ≤ K) (b : Breakpoints K) (N : ℕ) :
    ∃ label : Fin N → Fin K,
      Real.sqrt ((N:ℝ)*squareMass b) - 1 ≤
        ∑ i, len b i * Real.sqrt ((univ.filter (fun j => label j = i)).card : ℝ) := by
  obtain ⟨hL, hsum, hS⟩ := lengths_properties hK b
  let v : Fin K → ℝ := fun i => (N:ℝ)*len b i^2/squareMass b
  let q : Fin K → ℕ := fun i => ⌊v i⌋₊
  have hv : ∀ i, 0 ≤ v i := fun i => div_nonneg (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _)) hS.le
  have hvsum : (∑ i, v i) = (N:ℝ) := by
    simp only [v, ← sum_div, ← mul_sum]
    change (N:ℝ)*squareMass b/squareMass b = (N:ℝ)
    field_simp [ne_of_gt hS]
  have hqsum : (∑ i, q i) ≤ N := by
    have h : (∑ i, (q i : ℝ)) ≤ (N:ℝ) := by
      rw [← hvsum]; exact sum_le_sum fun i _ => Nat.floor_le (hv i)
    exact_mod_cast h
  have hcard : Fintype.card (Σ i : Fin K, Fin (q i)) ≤ Fintype.card (Fin N) := by
    simpa using hqsum
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let label : Fin N → Fin K := fun j =>
    if h : ∃ a, e a = j then (Classical.choose h).1 else ⟨0, by omega⟩
  have he : ∀ a, label (e a) = a.1 := by
    intro a
    dsimp [label]
    rw [dif_pos ⟨a, rfl⟩]
    exact congrArg Sigma.fst (e.injective (Classical.choose_spec (show ∃ a', e a' = e a from ⟨a, rfl⟩)))
  have hcount : ∀ i, q i ≤ (univ.filter (fun j => label j = i)).card := by
    intro i
    let f : Fin (q i) → {j : Fin N // label j = i} := fun t => ⟨e ⟨i,t⟩, he _⟩
    have hf : Function.Injective f := by
      intro a c h
      have hh := e.injective (congrArg Subtype.val h)
      simpa using hh
    have h := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_fin, Fintype.card_subtype] using h
  have hroot : ∀ i, Real.sqrt (v i) = Real.sqrt ((N:ℝ)/squareMass b) * len b i := by
    intro i
    have hv' : v i = ((N:ℝ)/squareMass b) * len b i^2 := by dsimp [v]; ring
    rw [hv', Real.sqrt_mul (div_nonneg (Nat.cast_nonneg N) hS.le), Real.sqrt_sq (hL i).le]
  have heq : Real.sqrt ((N:ℝ)/squareMass b) * squareMass b = Real.sqrt ((N:ℝ)*squareMass b) := by
    have h0 := Real.sqrt_nonneg ((N:ℝ)/squareMass b)
    have hs := Real.sq_sqrt (div_nonneg (Nat.cast_nonneg N) hS.le)
    symm
    apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg (Nat.cast_nonneg N) hS.le) (mul_nonneg h0 hS.le)).2
    rw [mul_pow, hs]
    field_simp [ne_of_gt hS]
  refine ⟨label, ?_⟩
  calc
    Real.sqrt ((N:ℝ)*squareMass b)-1 = ∑ i, len b i*(Real.sqrt (v i)-1) := by
      simp_rw [hroot, mul_sub, mul_one]
      rw [sum_sub_distrib, hsum]
      congr 1
      rw [← heq]
      simp only [squareMass, mul_sum]
      apply sum_congr rfl
      intro i _; ring
    _ ≤ ∑ i, len b i*Real.sqrt (q i : ℝ) := by
      apply sum_le_sum; intro i _
      exact mul_le_mul_of_nonneg_left (sqrt_floor_lower (v i) (hv i)) (hL i).le
    _ ≤ _ := by
      apply sum_le_sum; intro i _
      apply mul_le_mul_of_nonneg_left _ (hL i).le
      apply Real.sqrt_le_sqrt
      exact_mod_cast hcount i

theorem left_representatives {K : ℕ} (hK : 1 ≤ K) (b : Breakpoints K) (r : ℕ)
    (hr : (r:ℝ)*squareMass b < 1/4) :
    ∃ z : Fin r → ℝ, (∀ i, z i ∈ Set.Icc (0:ℝ) (1/2)) ∧
      Function.Injective (fun i => intervalHole b (z i)) := by
  obtain ⟨hL, _, hS⟩ := lengths_properties hK b
  let I := univ.filter (fun i : Fin K => b.l i.castSucc < 1/2)
  have hhalf : (1/2:ℝ) ≤ ∑ i ∈ I, len b i := by
    have htel := fin_telescope K (fun j => min (b.l j) (1/2))
    simp only [b.last, b.zero] at htel
    norm_num at htel
    rw [← htel, ← sum_sub_distrib, sum_filter]
    apply sum_le_sum
    intro i _
    by_cases h : b.l i.castSucc < 1/2
    · rw [if_pos h, min_eq_left h.le]
      have hm := min_le_left (b.l i.succ) (1/2:ℝ)
      dsimp [len]; linarith
    · have hi : 1/2 ≤ b.l i.castSucc := le_of_not_gt h
      have hj : 1/2 ≤ b.l i.succ := hi.trans (b.strictMono.monotone (show i.castSucc ≤ i.succ by exact Nat.le_succ i.val))
      rw [if_neg h, min_eq_right hi, min_eq_right hj, sub_self]
  have hc := sum_mul_sq_le_sq_mul_sq I (fun _ => (1:ℝ)) (fun i => len b i)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hc
  have hsI : (∑ i ∈ I, len b i^2) ≤ squareMass b :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => sq_nonneg _)
  have hrI : r ≤ I.card := by
    by_contra h
    have hc0 : (0:ℝ) ≤ I.card := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hsI hc0
    have hcr : (I.card:ℝ) ≤ r := by exact_mod_cast (by omega : I.card ≤ r)
    have hmulr := mul_le_mul_of_nonneg_right hcr hS.le
    nlinarith
  have hcard : Fintype.card (Fin r) ≤ Fintype.card {i // i ∈ I} := by simpa using hrI
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun j => b.l (e j).val.castSucc, ?_, ?_⟩
  · intro j
    exact ⟨(breakpoint_bounds b _).1, (mem_filter.mp (e j).property).2.le⟩
  · intro i j h
    have hh (a : {i // i ∈ I}) : intervalHole b (b.l a.val.castSucc) = a.val.val :=
      intervalHole_mem b a.val _ le_rfl (b.strictMono (by simp))
    simp only [hh] at h
    apply e.injective
    apply Subtype.ext
    exact Fin.ext h

end PigeonholeProof
end

noncomputable section
open Finset
namespace PigeonholeProof

 theorem ordered_interval_packing {K : ℕ} (a b : Fin K → ℝ)
    (_hab : ∀ i, a i ≤ b i) (hord : ∀ i j, i < j → b i ≤ a j)
    (s : Finset (Fin K)) (l u : ℝ) (hlu : l ≤ u)
    (hlo : ∀ i ∈ s, l ≤ a i) (hhi : ∀ i ∈ s, b i ≤ u) :
    ∑ i ∈ s, (b i-a i) ≤ u-l := by
  classical
  induction s using Finset.strongInductionOn generalizing l u
  rename_i s ih
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using sub_nonneg.mpr hlu
  let j := s.max' hs
  have hj : j ∈ s := s.max'_mem hs
  have he (i : Fin K) (hi : i ∈ s.erase j) : b i ≤ a j := by
    have himem := (mem_erase.mp hi).2
    have hij := s.le_max' i himem
    exact hord i j (lt_of_le_of_ne hij (mem_erase.mp hi).1)
  have hh := ih (s.erase j) (erase_ssubset hj) l (a j) (hlo j hj)
    (fun i hi => hlo i (mem_erase.mp hi).2) he
  have hsum := sum_erase_add s (fun i => b i-a i) hj
  linarith [hhi j hj]

 def leftIndicator (x a : ℝ) : ℝ := if x ≤ a then 1 else 0

 theorem ordered_edge_gap_bound {K : ℕ} (a b : Fin K → ℝ)
    (hab : ∀ i, a i ≤ b i) (hord : ∀ i j, i < j → b i ≤ a j)
    (u v : ℝ) (huv : u ≤ v)
    (hgap : ∀ i, v ≤ a i ∨ b i ≤ v) :
    (∑ i, (b i-a i)*|leftIndicator v (a i)-leftIndicator u (a i)|) ≤ v-u := by
  classical
  let s := univ.filter (fun i => u ≤ a i ∧ ¬v ≤ a i)
  have hs : (∑ i, (b i-a i)*|leftIndicator v (a i)-leftIndicator u (a i)|) =
      ∑ i ∈ s, (b i-a i) := by
    dsimp [s]
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases hu : u ≤ a i
    · by_cases hv : v ≤ a i
      · simp [leftIndicator, hu, hv]
      · simp [leftIndicator, hu, hv]
    · have hv : ¬v ≤ a i := fun h => hu (huv.trans h)
      simp [leftIndicator, hu, hv]
  rw [hs]
  apply ordered_interval_packing a b hab hord s u v huv
  · intro i hi
    exact (mem_filter.mp hi).2.1
  · intro i hi
    exact (hgap i).resolve_left (mem_filter.mp hi).2.2

 theorem edge_gap_bound {K : ℕ} (a b : Fin K → ℝ)
    (hab : ∀ i, a i ≤ b i) (hord : ∀ i j, i < j → b i ≤ a j)
    (u v : ℝ) (hgu : ∀ i, u ≤ a i ∨ b i ≤ u)
    (hgv : ∀ i, v ≤ a i ∨ b i ≤ v) :
    (∑ i, (b i-a i)*|leftIndicator v (a i)-leftIndicator u (a i)|) ≤ |u-v| := by
  rcases le_total u v with huv | hvu
  · have h := ordered_edge_gap_bound a b hab hord u v huv hgv
    simpa only [abs_of_nonpos (sub_nonpos.mpr huv), neg_sub] using h
  · have h := ordered_edge_gap_bound a b hab hord v u hvu hgu
    simpa only [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hvu)] using h

 theorem cut_matching_identity {T : ℕ} (x : Fin T → ℝ) (w : Fin T → Bool)
    (e : {t // w t = false} ≃ {t // w t = true}) (a : ℝ) :
    cut x w a = ∑ t : {t // w t = false},
      (leftIndicator (x (e t)) a-leftIndicator (x t) a) := by
  classical
  have ht : (∑ t : {t // w t = true}, leftIndicator (x t) a) =
      ∑ t ∈ univ.filter (fun t => w t = true), leftIndicator (x t) a := by
    exact (Finset.sum_subtype (univ.filter (fun t => w t = true))
      (fun t => by simp) (fun t => leftIndicator (x t) a)).symm
  have hf : (∑ t : {t // w t = false}, leftIndicator (x t) a) =
      ∑ t ∈ univ.filter (fun t => w t = false), leftIndicator (x t) a := by
    exact (Finset.sum_subtype (univ.filter (fun t => w t = false))
      (fun t => by simp) (fun t => leftIndicator (x t) a)).symm
  have hc : cut x w a = (∑ t : {t // w t = true}, leftIndicator (x t) a) -
      ∑ t : {t // w t = false}, leftIndicator (x t) a := by
    rw [ht, hf, sum_filter, sum_filter, ← sum_sub_distrib]
    unfold cut
    apply sum_congr rfl
    intro t _
    cases w t <;> by_cases hx : x t ≤ a <;> simp [hx, sign, leftIndicator]
  rw [hc, ← e.sum_comp (fun t => leftIndicator (x t) a), sum_sub_distrib]

 theorem matching_gaps_lower {T K : ℕ} (x : Fin T → ℝ) (w : Fin T → Bool)
    (hbal : (univ.filter (fun t => w t = false)).card =
      (univ.filter (fun t => w t = true)).card)
    (a b : Fin K → ℝ) (hab : ∀ i, a i ≤ b i)
    (hord : ∀ i j, i < j → b i ≤ a j)
    (hgap : ∀ t i, x t ≤ a i ∨ b i ≤ x t) :
    (∑ i, (b i-a i)*|cut x w (a i)|) ≤ PigeonholeDesign.Upper.discrepancy x w := by
  classical
  have hcard : Fintype.card {t // w t = false} = Fintype.card {t // w t = true} := by
    simpa only [Fintype.card_subtype] using hbal
  have : Nonempty ({t // w t = false} ≃ {t // w t = true}) :=
    ⟨Fintype.equivOfCardEq hcard⟩
  unfold PigeonholeDesign.Upper.discrepancy
  apply le_ciInf
  intro e
  calc
    _ ≤ ∑ i, ∑ t : {t // w t = false},
        (b i-a i)*|leftIndicator (x (e t)) (a i)-leftIndicator (x t) (a i)| := by
      apply sum_le_sum
      intro i _
      rw [cut_matching_identity x w e, ← mul_sum]
      exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (sub_nonneg.mpr (hab i))
    _ = ∑ t : {t // w t = false}, ∑ i,
        (b i-a i)*|leftIndicator (x (e t)) (a i)-leftIndicator (x t) (a i)| := sum_comm
    _ ≤ ∑ t : {t // w t = false}, dist (x t) (x (e t)) := by
      apply sum_le_sum
      intro t _
      simpa only [Real.dist_eq] using
        edge_gap_bound a b hab hord (x t) (x (e t)) (hgap t) (hgap (e t))

 theorem matching_cut_lower {T : ℕ} (x : Fin T → ℝ) (w : Fin T → Bool)
    (hbal : (univ.filter (fun t => w t = false)).card =
      (univ.filter (fun t => w t = true)).card)
    (a b : ℝ) (hab : a ≤ b) (hgap : ∀ t, x t ≤ a ∨ b ≤ x t) :
    (b-a)*|cut x w a| ≤ PigeonholeDesign.Upper.discrepancy x w := by
  have h := matching_gaps_lower x w hbal (fun _ : Fin 1 => a) (fun _ => b)
    (fun _ => hab) (fun i j hij => by omega) (fun t _ => hgap t)
  simpa only [Fintype.sum_unique] using h

end PigeonholeProof
end

noncomputable section
open Finset
namespace PigeonholeProof

 def signSum {T n : ℕ} (e : Fin n → Fin T) (s : Finset (Fin n))
    (c : Fin T → Bool) : ℝ := ∑ i ∈ s, sign (c (e i))

 theorem signSum_flip {T n : ℕ} (e : Fin n → Fin T) (he : Function.Injective e)
    (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s) (c : Fin T → Bool) :
    signSum e s (coinFlip (e i) c) = signSum e s c := by
  unfold signSum
  apply sum_congr rfl
  intro j hj
  rw [coinFlip_other (e i) (e j)]
  intro h
  exact hi (he h ▸ hj)

 theorem sign_moments {T n : ℕ} (e : Fin n → Fin T) (he : Function.Injective e)
    (s : Finset (Fin n)) :
    coinAvg (signSum e s) = 0 ∧
      coinAvg (fun c => signSum e s c ^ 2) = (s.card : ℝ) ∧
      coinAvg (fun c => signSum e s c ^ 4) = 3*(s.card : ℝ)^2-2*(s.card : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [signSum, coinAvg]
  | @insert i s hi ih =>
    have hsum (c : Fin T → Bool) : signSum e (insert i s) c =
        signSum e s c + sign (c (e i)) := by
      rw [signSum, sum_insert hi]
      unfold signSum
      ring
    have h1 := coinAvg_fresh_sign (e i) (fun _ => 1) (fun _ => rfl)
    simp only [one_mul] at h1
    have hodd := coinAvg_fresh_sign (e i) (signSum e s) (signSum_flip e he s i hi)
    have hodd3 := coinAvg_fresh_sign (e i) (fun c => signSum e s c ^ 3)
      (fun c => congrArg (fun x : ℝ => x^3) (signSum_flip e he s i hi c))
    have h2 (c : Fin T → Bool) : signSum e (insert i s) c ^ 2 =
        signSum e s c ^ 2 + 2*(signSum e s c * sign (c (e i))) + 1 := by
      rw [hsum]
      nlinarith only [sign_sq (c (e i))]
    have h4 (c : Fin T → Bool) : signSum e (insert i s) c ^ 4 =
        signSum e s c ^ 4 + 4*(signSum e s c ^ 3 * sign (c (e i))) +
          6*signSum e s c ^ 2 + 4*(signSum e s c * sign (c (e i))) + 1 := by
      rw [hsum]
      calc
        _ = signSum e s c ^ 4 + 4*(signSum e s c ^ 3 * sign (c (e i))) +
            6*signSum e s c ^ 2 * sign (c (e i)) ^ 2 +
            4*signSum e s c * sign (c (e i)) ^ 3 + sign (c (e i)) ^ 4 := by ring
        _ = _ := by rw [sign_sq, sign_cube, sign_four]; ring
    constructor
    · change coinAvg (fun c => signSum e (insert i s) c) = 0
      simp_rw [hsum, coinAvg_add, ih.1, h1]
      norm_num
    constructor
    · simp_rw [h2, coinAvg_add, coinAvg_const_mul, coinAvg_const, ih.2.1, hodd]
      simp only [card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      ring
    · simp_rw [h4, coinAvg_add, coinAvg_const_mul, coinAvg_const, ih.2.2, ih.2.1, hodd3, hodd]
      simp only [card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      ring

 theorem absolute_polynomial_bound (v a : ℝ) (ha : 0 < a) :
    3*v^2/(2*a) - v^4/(2*a^3) ≤ |v| := by
  have h := mul_nonneg (mul_nonneg (abs_nonneg v) (sq_nonneg (|v|-a)))
    (by positivity : 0 ≤ |v|+2*a)
  have hsq := sq_abs v
  have hfour : |v|^4 = v^4 := by
    calc
      _ = (|v|^2)^2 := by ring
      _ = (v^2)^2 := by rw [sq_abs]
      _ = _ := by ring
  have hsqmul := congrArg (fun x : ℝ => a^2*x) hsq
  have heq : (3*v^2/(2*a)-v^4/(2*a^3)) = (3*v^2*a^2-v^4)/(2*a^3) := by
    field_simp
  rw [heq]
  apply (div_le_iff₀ (show 0 < 2*a^3 by positivity)).2
  nlinarith only [h, hsqmul, hfour]

 theorem coinAvg_abs_sign_sum {T n : ℕ} (e : Fin n → Fin T)
    (he : Function.Injective e) (s : Finset (Fin n)) :
    Real.sqrt (s.card : ℝ) / 16 ≤
      coinAvg (fun c => |∑ i ∈ s, sign (c (e i))|) := by
  classical
  obtain ⟨_, hm2, hm4⟩ := sign_moments e he s
  by_cases hs : s.card = 0
  · have hz : s = ∅ := card_eq_zero.mp hs
    simp [hz, coinAvg_const]
  have hq : 0 < (s.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hroot := Real.sq_sqrt hq.le
  have hp : 0 < Real.sqrt (s.card : ℝ) := Real.sqrt_pos.2 hq
  let a := 2*Real.sqrt (s.card : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have h := coinAvg_mono
    (fun c => 3*signSum e s c^2/(2*a)-signSum e s c^4/(2*a^3))
    (fun c => |signSum e s c|)
    (fun c => absolute_polynomial_bound (signSum e s c) a ha)
  have havg : coinAvg (fun c => 3*signSum e s c^2/(2*a)-signSum e s c^4/(2*a^3)) =
      3*(s.card:ℝ)/(2*a)-(3*(s.card:ℝ)^2-2*(s.card:ℝ))/(2*a^3) := by
    simp only [div_eq_mul_inv, coinAvg_sub, coinAvg_mul_const, coinAvg_const_mul, hm2, hm4]
  rw [havg] at h
  have hformula : 3*(s.card:ℝ)/(2*a)-(3*(s.card:ℝ)^2-2*(s.card:ℝ))/(2*a^3) =
      9*Real.sqrt (s.card:ℝ)/16 + 1/(8*Real.sqrt (s.card:ℝ)) := by
    dsimp [a]
    set q := (s.card : ℝ)
    set r := Real.sqrt q
    have hr : r^2 = q := hroot
    have hrne : r ≠ 0 := hp.ne'
    rw [← hr]
    field_simp [hrne]
    ring
  rw [hformula] at h
  have hn : 0 ≤ 1/(8*Real.sqrt (s.card:ℝ)) := by positivity
  have hlower : Real.sqrt (s.card:ℝ)/16 ≤
      9*Real.sqrt (s.card:ℝ)/16 + 1/(8*Real.sqrt (s.card:ℝ)) := by linarith
  exact hlower.trans h

end PigeonholeProof
end

noncomputable section
open Finset PigeonholeDesign.Lower
namespace PigeonholeProof

 theorem sum_fin_pairs {N : ℕ} (f : Fin (2*N) → ℝ) :
    (∑ t, f t) = ∑ j : Fin N, (f ⟨2*j.val, by omega⟩ + f ⟨2*j.val+1, by omega⟩) := by
  let e : Fin N × Fin 2 ≃ Fin (2*N) :=
    { toFun := fun a => ⟨2*a.1.val+a.2.val, by omega⟩
      invFun := fun t => (⟨t.val/2, by omega⟩, ⟨t.val%2, by omega⟩)
      left_inv := by intro a; apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
      right_inv := by intro t; apply Fin.ext; dsimp; omega }
  have h := e.sum_comp f
  rw [Fintype.sum_prod_type] at h
  simpa [Fin.sum_univ_two, e] using h.symm

 theorem paired_even {K N : ℕ} (b : Breakpoints K) (label : Fin N → Fin K) (j : Fin N) :
    pairedX b label ⟨2*j.val, by omega⟩ = b.l (label j).castSucc := by
  simp [pairedX]

 theorem paired_odd {K N : ℕ} (b : Breakpoints K) (label : Fin N → Fin K) (j : Fin N) :
    pairedX b label ⟨2*j.val+1, by omega⟩ = midpoint b (label j) := by
  have hdiv : (2*j.val+1)/2=j.val := by omega
  have hmod : (2*j.val+1)%2=1 := by omega
  simp [pairedX, hdiv, hmod]

 theorem paired_cells {K N : ℕ} (b : Breakpoints K) (label : Fin N → Fin K)
    (j : ℕ) (hj : j < N) :
    PigeonholeDesign.Upper.cellOf (intervalHole b) (pairedX b label) (2*j+1) =
      PigeonholeDesign.Upper.cellOf (intervalHole b) (pairedX b label) (2*j) := by
  have h0 : 2*j<2*N := by omega
  have h1 : 2*j+1<2*N := by omega
  simp only [PigeonholeDesign.Upper.cellOf, dif_pos h0, dif_pos h1]
  rw [paired_even b label ⟨j,hj⟩, paired_odd b label ⟨j,hj⟩]
  rw [intervalHole_mem b _ _ (midpoint_bounds b _).1.le (midpoint_bounds b _).2,
    intervalHole_mem b _ _ le_rfl (b.strictMono (by simp))]

 theorem paired_assign_values {K N : ℕ} (b : Breakpoints K) (label : Fin N → Fin K)
    (coin : Fin (2*N) → Bool) (j : Fin N) :
    PigeonholeDesign.Upper.assign (intervalHole b) (pairedX b label) coin ⟨2*j.val, by omega⟩ =
      coin ⟨2*j.val, by omega⟩ ∧
    PigeonholeDesign.Upper.assign (intervalHole b) (pairedX b label) coin ⟨2*j.val+1, by omega⟩ =
      !(coin ⟨2*j.val, by omega⟩) := by
  let cell := PigeonholeDesign.Upper.cellOf (intervalHole b) (pairedX b label)
  let co := PigeonholeDesign.Upper.coinOf coin
  have hs := paired_prefix_step N j.val cell co j.isLt
    (fun k hk => paired_cells b label k (by omega))
  have h0 := prefix_getD (2*N) cell co (n:=2*j.val+2) (m:=2*N) (t:=2*j.val)
    (by omega) (by omega)
  have h1 := prefix_getD (2*N) cell co (n:=2*j.val+2) (m:=2*N) (t:=2*j.val+1)
    (by omega) (by omega)
  rw [hs] at h0 h1
  have hlen := run_length (2*N) cell co (2*j.val)
  simp [hlen] at h0 h1
  constructor
  · change (PigeonholeDesign.Upper.prefixAssign (2*N) cell co (2*N)).getD _ false = _
    simpa [co, PigeonholeDesign.Upper.coinOf, show 2*j.val<2*N by omega] using h0.symm
  · change (PigeonholeDesign.Upper.prefixAssign (2*N) cell co (2*N)).getD _ false = _
    simpa [co, PigeonholeDesign.Upper.coinOf, show 2*j.val<2*N by omega] using (congrArg Bool.not h1).symm

 theorem paired_run_cut {K N : ℕ} (b : Breakpoints K) (label : Fin N → Fin K)
    (coin : Fin (2*N) → Bool) (i : Fin K) :
    cut (pairedX b label) (assign (intervalHole b) (pairedX b label) coin) (b.l i.castSucc) =
      ∑ j ∈ univ.filter (fun j => label j = i), sign (coin ⟨2*j.val, by omega⟩) := by
  unfold cut
  rw [sum_fin_pairs, sum_filter]
  apply sum_congr rfl
  intro j _
  simp only [PigeonholeDesign.Lower.assign]
  rw [paired_even, paired_odd, (paired_assign_values b label coin j).1,
    (paired_assign_values b label coin j).2]
  by_cases he : label j=i
  · simp [he, not_le.mpr (midpoint_bounds b i).1]
  · rcases lt_or_gt_of_ne he with hl | hg
    · have hle : b.l (label j).succ ≤ b.l i.castSucc :=
        b.strictMono.monotone (show (label j).succ ≤ i.castSucc by exact hl)
      have hm : midpoint b (label j) ≤ b.l i.castSucc := (midpoint_bounds b _).2.le.trans hle
      have ha : b.l (label j).castSucc ≤ b.l i.castSucc := (midpoint_bounds b _).1.le.trans hm
      simp only [if_pos ha, if_pos hm, if_neg he]
      cases coin ⟨2*j.val, by omega⟩ <;> norm_num [sign]
    · have ha : b.l i.castSucc < b.l (label j).castSucc := b.strictMono hg
      have hm : b.l i.castSucc < midpoint b (label j) := ha.trans (midpoint_bounds b _).1
      simp [not_le.mpr ha, not_le.mpr hm, he]

end PigeonholeProof
end

noncomputable section
open Finset PigeonholeDesign.Lower
namespace PigeonholeProof

 theorem large_energy_instance {K : ℕ} (hK : 1 ≤ K) (b : Breakpoints K) (N : ℕ) :
    ∃ x : Fin (2*N) → ℝ, (∀ t, x t ∈ Set.Icc (0:ℝ) 1) ∧
      (Real.sqrt ((N:ℝ)*squareMass b)-1)/32 ≤
        PigeonholeDesign.Upper.phdExp (intervalHole b) x := by
  classical
  obtain ⟨label, hlabel⟩ := allocation_exists hK b N
  let x := pairedX b label
  have hcoord (t : Fin (2*N)) : x t = b.l (label ⟨t.val/2, by omega⟩).castSucc ∨
      x t = midpoint b (label ⟨t.val/2, by omega⟩) := by
    dsimp [x, pairedX]
    split_ifs <;> simp
  have hx (t : Fin (2*N)) : x t ∈ Set.Icc (0:ℝ) 1 := by
    rcases hcoord t with h | h
    · rw [h]; exact breakpoint_bounds b _
    · rw [h]
      exact ⟨(breakpoint_bounds b _).1.trans (midpoint_bounds b _).1.le,
        (midpoint_bounds b _).2.le.trans (breakpoint_bounds b _).2⟩
  have hord (i j : Fin K) (hij : i<j) : midpoint b i ≤ b.l j.castSucc :=
    (midpoint_bounds b i).2.le.trans (b.strictMono.monotone (show i.succ≤j.castSucc from hij))
  have hgap (t : Fin (2*N)) (i : Fin K) : x t ≤ b.l i.castSucc ∨ midpoint b i ≤ x t := by
    let j := label ⟨t.val/2, by omega⟩
    rcases lt_trichotomy j i with h | h | h
    · left
      have hu := hord j i h
      rcases hcoord t with ht | ht
      · rw [ht]; exact (midpoint_bounds b j).1.le.trans hu
      · rw [ht]; exact hu
    · subst i
      rcases hcoord t with ht | ht
      · exact Or.inl ht.le
      · exact Or.inr ht.ge
    · right
      have hu := hord i j h
      rcases hcoord t with ht | ht
      · rw [ht]; exact hu
      · rw [ht]; exact hu.trans (midpoint_bounds b j).1.le
  let e : Fin N → Fin (2*N) := fun j => ⟨2*j.val, by omega⟩
  have he : Function.Injective e := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp [e] at this
    omega
  have hpoint (coin : Fin (2*N) → Bool) :
      (∑ i, (len b i/2)*|∑ j ∈ univ.filter (fun j => label j=i), sign (coin (e j))|) ≤
        PigeonholeDesign.Upper.discrepancy x (assign (intervalHole b) x coin) := by
    have h := matching_gaps_lower x (assign (intervalHole b) x coin)
      (assign_balanced (even_two_mul N) (intervalHole b) x coin)
      (fun i => b.l i.castSucc) (midpoint b) (fun i => (midpoint_bounds b i).1.le) hord hgap
    have hc (i : Fin K) := paired_run_cut b label coin i
    simp only [x] at h
    simp_rw [hc] at h
    convert h using 1
    apply sum_congr rfl
    intro i _
    congr 1
    dsimp [midpoint, len]
    ring
  have havg := coinAvg_mono _ _ hpoint
  rw [coinAvg_sum] at havg
  simp_rw [coinAvg_const_mul] at havg
  have hm : (∑ i, (len b i/2)*(Real.sqrt ((univ.filter (fun j => label j=i)).card:ℝ)/16)) ≤
      ∑ i, (len b i/2)*coinAvg (fun coin => |∑ j ∈ univ.filter (fun j => label j=i), sign (coin (e j))|) := by
    apply sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (coinAvg_abs_sign_sum e he _) (by
      have := (lengths_properties hK b).1 i
      positivity)
  refine ⟨x, hx, ?_⟩
  change (Real.sqrt ((N:ℝ)*squareMass b)-1)/32 ≤
    coinAvg (fun coin => PigeonholeDesign.Upper.discrepancy x (assign (intervalHole b) x coin))
  have hs : (∑ i, (len b i/2)*(Real.sqrt ((univ.filter (fun j => label j=i)).card:ℝ)/16)) =
      (∑ i, len b i*Real.sqrt ((univ.filter (fun j => label j=i)).card:ℝ))/32 := by
    rw [sum_div]
    apply sum_congr rfl
    intro i _; ring
  rw [hs] at hm
  linarith

end PigeonholeProof
end

noncomputable section
open Finset PigeonholeDesign.Lower
namespace PigeonholeProof

 theorem spread_instance {K : ℕ} (hK : 1 ≤ K) (b : Breakpoints K)
    (N r : ℕ) (hr : r ≤ N) (hrS : (r : ℝ)*squareMass b < 1/4) :
    ∃ x : Fin (2*N) → ℝ, (∀ t, x t ∈ Set.Icc (0:ℝ) 1) ∧
      Real.sqrt (r:ℝ)/32 ≤ PigeonholeDesign.Upper.phdExp (intervalHole b) x := by
  classical
  obtain ⟨z, hz, hcell⟩ := left_representatives hK b r hrS
  let x := spreadX N r hr z
  have hx (t : Fin (2*N)) : x t ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [x, spreadX]
    split_ifs with h0 h1
    · norm_num
    · exact ⟨(hz _).1, (hz _).2.trans (by norm_num)⟩
    · norm_num
  have hg (t : Fin (2*N)) : x t ≤ 1/2 ∨ 1 ≤ x t := by
    dsimp [x, spreadX]
    split_ifs with h0 h1
    · left; norm_num
    · exact Or.inl (hz _).2
    · exact Or.inr le_rfl
  let e : Fin r → Fin (2*N) := fun i => ⟨2*(N-r)+i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    dsimp [e] at h
    omega
  have hm := coinAvg_abs_sign_sum e he univ
  simp only [card_univ, Fintype.card_fin] at hm
  have hpoint (coin : Fin (2*N) → Bool) :
      (1/2:ℝ)*|∑ i : Fin r, sign (coin (e i))| ≤
        PigeonholeDesign.Upper.discrepancy x (assign (intervalHole b) x coin) := by
    have h := matching_cut_lower x (assign (intervalHole b) x coin)
      (assign_balanced (by exact even_two_mul N) (intervalHole b) x coin)
      (1/2) 1 (by norm_num) hg
    have hc := spread_run_cut b hr z hz hcell coin
    change cut x (assign (intervalHole b) x coin) (1/2) = _ at hc
    rw [hc] at h
    norm_num only [show (1:ℝ)-1/2=1/2 by norm_num] at h
    exact h
  have havg := coinAvg_mono _ _ hpoint
  rw [coinAvg_const_mul] at havg
  refine ⟨x, hx, ?_⟩
  change Real.sqrt (r:ℝ)/32 ≤
    coinAvg (fun coin => PigeonholeDesign.Upper.discrepancy x (assign (intervalHole b) x coin))
  nlinarith only [hm, havg]

 theorem small_energy_instance {K N : ℕ} (hK : 1 ≤ K) (b : Breakpoints K)
    (hN : 2^24 ≤ 2*N)
    (hS : squareMass b < 1/(16*Real.sqrt (2*N:ℝ))) :
    ∃ x : Fin (2*N) → ℝ, (∀ t, x t ∈ Set.Icc (0:ℝ) 1) ∧
      (1/1024:ℝ)*(2*N:ℝ)^((1:ℝ)/4) ≤
        PigeonholeDesign.Upper.phdExp (intervalHole b) x := by
  let t : ℝ := 2*N
  have htbig : (2^24:ℝ) ≤ t := by
    dsimp [t]
    exact_mod_cast hN
  have ht : 0 ≤ t := by positivity
  have hsq := Real.sq_sqrt ht
  have hs0 := Real.sqrt_nonneg t
  have hs2 : 2 ≤ Real.sqrt t := by norm_num at htbig; nlinarith only [hsq, hs0, htbig]
  let r := Nat.floor (Real.sqrt t)
  have hrle : (r:ℝ) ≤ Real.sqrt t := Nat.floor_le hs0
  have hrlt : Real.sqrt t < (r:ℝ)+1 := Nat.lt_floor_add_one _
  have hrN : r ≤ N := by
    have h : (r:ℝ) ≤ (N:ℝ) := by dsimp [t] at hsq; nlinarith only [hrle, hs2, hsq]
    exact_mod_cast h
  have hS0 := (lengths_properties hK b).2.2.le
  have hspos : 0 < Real.sqrt t := lt_of_lt_of_le (by norm_num) hs2
  have hmul : Real.sqrt t*squareMass b < 1/16 := by
    have hd : 0 < 16*Real.sqrt t := by positivity
    have h := (lt_div_iff₀ hd).mp hS
    nlinarith only [h]
  have hrS : (r:ℝ)*squareMass b < 1/4 := by
    have h := mul_le_mul_of_nonneg_right hrle hS0
    linarith
  obtain ⟨x, hx, hbound⟩ := spread_instance hK b N r hrN hrS
  have hrhalf : Real.sqrt t/2 ≤ (r:ℝ) := by linarith
  have hrroot := Real.sq_sqrt (show 0 ≤ (r:ℝ) by positivity)
  have hrpos := Real.sqrt_nonneg (r:ℝ)
  let Q := t^((1:ℝ)/4)
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg ht _
  have hQsq : Q^2 = Real.sqrt t := by
    dsimp [Q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht, Real.sqrt_eq_rpow]
    norm_num
  have hcomp : Q ≤ 2*Real.sqrt (r:ℝ) := by
    nlinarith only [hrhalf, hrroot, hrpos, hQsq, hQ0]
  refine ⟨x, hx, ?_⟩
  change (1/1024:ℝ)*Q ≤ _
  nlinarith only [hcomp, hbound, hrpos]

end PigeonholeProof
end

namespace PigeonholeDesign.Lower

theorem lemma_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ (K : ℕ) (_hK : 1 ≤ K) (b : Breakpoints K), ∃ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
          c * (T : ℝ) ^ ((1 : ℝ) / 4) ≤ PigeonholeDesign.Upper.phdExp (intervalHole b) x := by
  refine ⟨1/1024, by norm_num, 2^24, ?_⟩
  intro T hT hEven K hK b
  obtain ⟨N, hN⟩ := hEven
  have hTN : T=2*N := by omega
  clear hN
  subst T
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  by_cases hS : 1/(16*Real.sqrt (2*N:ℝ)) ≤ PigeonholeProof.squareMass b
  · obtain ⟨x, hx, hb⟩ := PigeonholeProof.large_energy_instance hK b N
    refine ⟨x, hx, ?_⟩
    let t : ℝ := 2*N
    let Q : ℝ := t^((1:ℝ)/4)
    have ht0 : 0 ≤ t := by positivity
    have htbig : (2^24:ℝ) ≤ t := by dsimp [t]; exact_mod_cast hT
    have hs0 := Real.sqrt_nonneg t
    have hs2 := Real.sq_sqrt ht0
    have hslarge : 4096 ≤ Real.sqrt t := by norm_num at htbig; nlinarith only [htbig, hs2, hs0]
    have hspos : 0 < Real.sqrt t := by linarith
    have hQ0 : 0 ≤ Q := Real.rpow_nonneg ht0 _
    have hQ2 : Q^2=Real.sqrt t := by
      dsimp [Q]
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0, Real.sqrt_eq_rpow]
      norm_num
    have hQbig : 64 ≤ Q := by nlinarith only [hQ0, hQ2, hslarge]
    have hS0 := (PigeonholeProof.lengths_properties hK b).2.2.le
    have hm := (div_le_iff₀ (show 0 < 16*Real.sqrt t by positivity)).mp hS
    have hmul := mul_le_mul_of_nonneg_right hm hs0
    have heq := congrArg (fun a : ℝ => PigeonholeProof.squareMass b*a) hs2
    have hNS : Real.sqrt t/32 ≤ (N:ℝ)*PigeonholeProof.squareMass b := by
      dsimp [t] at heq
      nlinarith only [hmul, heq]
    have hR0 := Real.sqrt_nonneg ((N:ℝ)*PigeonholeProof.squareMass b)
    have hR2 := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hS0)
    have hRQ : Q/8 ≤ Real.sqrt ((N:ℝ)*PigeonholeProof.squareMass b) := by
      nlinarith only [hNS, hR0, hR2, hQ0, hQ2]
    change (1/1024:ℝ)*Q ≤ _
    nlinarith only [hRQ, hQbig, hb]
  · exact PigeonholeProof.small_energy_instance hK b hT (lt_of_not_ge hS)

end PigeonholeDesign.Lower

open PigeonholeDesign.Lower


theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ (K : ℕ) (_hK : 1 ≤ K) (b : Breakpoints K), ∃ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
          c * (T : ℝ) ^ ((1 : ℝ) / 4) ≤ PigeonholeDesign.Upper.phdExp (intervalHole b) x := by
  exact PigeonholeDesign.Lower.lemma_4
