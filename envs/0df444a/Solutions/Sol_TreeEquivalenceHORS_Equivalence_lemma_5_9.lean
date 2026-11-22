-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.lemma_5_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T18:49:11.439173+00:00
-- url     : https://prove2.me/submissions/9c58be66-e646-4458-a7c7-018b7ac02233

import Theorems.Thm_TreeEquivalenceHORS_Equivalence_binary_translation_correct
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_binary_encoding_reflects_tree_equality
import Definitions.Def_TreeEquivalenceHORS_Equivalence_BinaryOutput

namespace TreeEquivalenceHORS.Equivalence.SyntaxCode

def atom (n : ℕ) := Nat.pair 0 n
def cell (x y : ℕ) := Nat.pair (x+1) y
def tag (k args : ℕ) := cell (atom k) args
def bare (k : ℕ) := tag k (atom 0)
def unary (k n : ℕ) := tag k (cell (atom n) (atom 0))
def binary (k a b : ℕ) := tag k (cell a (cell b (atom 0)))

def first (n : ℕ) := n.unpair.1.pred
def rest (n : ℕ) := n.unpair.2
def tagNum (n : ℕ) := rest (first n)
def left (n : ℕ) := first (rest n)
def right (n : ℕ) := first (rest (rest n))

theorem pr_atom : Primrec atom := Primrec₂.natPair.comp (Primrec.const 0) Primrec.id
theorem pr_cell : Primrec₂ cell := Primrec₂.natPair.comp₂ (Primrec.succ.comp Primrec.fst).to₂ Primrec₂.right
theorem pr_tag : Primrec₂ tag := pr_cell.comp₂ (pr_atom.comp Primrec.fst).to₂ Primrec₂.right
theorem pr_unary (k : ℕ) : Primrec (unary k) :=
  pr_tag.comp (Primrec.const k) (pr_cell.comp pr_atom (Primrec.const _))
theorem pr_binary (k : ℕ) : Primrec₂ (binary k) :=
  (pr_tag.comp (Primrec.const k) (pr_cell.comp Primrec.fst (pr_cell.comp Primrec.snd (Primrec.const _)))).to₂

theorem pr_first : Primrec first := Primrec.pred.comp (Primrec.fst.comp Primrec.unpair)
theorem pr_rest : Primrec rest := Primrec.snd.comp Primrec.unpair
theorem pr_left : Primrec left := pr_first.comp pr_rest
theorem pr_right : Primrec right := pr_left.comp pr_rest
theorem pr_tagNum : Primrec tagNum := pr_rest.comp pr_first

def history (step : ℕ → List ℕ → ℕ) : ℕ → List ℕ :=
  Nat.rec [] fun n h => h ++ [step n h]

def evaluate (step : ℕ → List ℕ → ℕ) (n : ℕ) := step n (history step n)

private theorem tabulated (step : ℕ → List ℕ → ℕ) (n : ℕ) :
    history step n = (List.range n).map (evaluate step) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [history, List.range_succ, List.map_append, List.map_cons, List.map_nil]
                 exact congrArg (· ++ [evaluate step n]) ih

private theorem pr_evaluate (step : ℕ → List ℕ → ℕ) (p : Primrec₂ step) : Primrec (evaluate step) := by
  have h : Primrec (history step) := Primrec.nat_rec₁ [] (Primrec.list_concat.comp Primrec.snd p).to₂
  exact p.comp Primrec.id h

abbrev Args := ℕ × ℕ × ℕ × ℕ

def foldStep (base : ℕ) (op : Args → ℕ) (n : ℕ) (h : List ℕ) :=
  op (tagNum n, rest (left n), h.getD (left n) base, h.getD (right n) base)
def fold (base : ℕ) (op : Args → ℕ) := evaluate (foldStep base op)

theorem pr_fold (base : ℕ) (op : Args → ℕ) (p : Primrec op) : Primrec (fold base op) := by
  apply pr_evaluate
  have lookup (f : ℕ → ℕ) (pf : Primrec f) : Primrec fun z : ℕ × List ℕ => z.2.getD (f z.1) base := by
    simp only [List.getD_eq_getElem?_getD]
    exact Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd (pf.comp Primrec.fst)) (Primrec.const base)
  exact (p.comp ((pr_tagNum.comp Primrec.fst).pair
    (((pr_rest.comp pr_left).comp Primrec.fst).pair ((lookup _ pr_left).pair (lookup _ pr_right))))).to₂

private theorem getD_closed {P : ℕ → Prop} {xs : List ℕ} {i b : ℕ} (hb : P b) (h : ∀ x ∈ xs, P x) :
    P (xs.getD i b) := by
  rw [List.getD_eq_getElem?_getD]
  cases he : xs[i]? with
  | none => exact hb
  | some x => exact h x (List.mem_of_getElem? he)

theorem fold_invariant {P : ℕ → Prop} {base : ℕ} (hb : P base) {op : Args → ℕ}
    (hp : ∀ k n a b, P a → P b → P (op (k,n,a,b))) (n : ℕ) : P (fold base op n) := by
  have hist (n : ℕ) : ∀ x ∈ history (foldStep base op) n, P x := by
    induction n with
    | zero => simp [history]
    | succ n ih =>
      intro x h
      rcases List.mem_append.mp h with h | h
      · exact ih _ h
      · obtain rfl := List.mem_singleton.mp h
        apply hp <;> exact getD_closed hb ih
  apply hp <;> exact getD_closed hb (hist _)

theorem fold_binary (base : ℕ) (op : Args → ℕ) (k a b : ℕ) :
    fold base op (binary k a b) = op (k, rest a, fold base op a, fold base op b) := by
  have l : a < binary k a b := by
    have h₁ := Nat.left_le_pair (a+1) (cell b (atom 0))
    have h₂ := Nat.right_le_pair (atom k+1) (cell a (cell b (atom 0)))
    dsimp [binary,tag,cell] at *
    omega
  have r : b < binary k a b := by
    have h₁ := Nat.left_le_pair (b+1) (atom 0)
    have h₂ := Nat.right_le_pair (a+1) (cell b (atom 0))
    have h₃ := Nat.right_le_pair (atom k+1) (cell a (cell b (atom 0)))
    dsimp [binary,tag,cell] at *
    omega
  conv_lhs => unfold fold evaluate; rw [tabulated]
  simp [foldStep, tagNum, left, right, first, rest, binary, tag, cell, atom, List.getD_eq_getElem?_getD] at *
  simp_all [fold]

theorem fold_unary (base : ℕ) (op : Args → ℕ) (k n : ℕ) (h : ∀ x y, op (k,n,x,y) = op (k,n,base,base)) :
    fold base op (unary k n) = op (k,n,base,base) := by
  unfold fold evaluate foldStep
  simp [unary, tagNum, left, right, first, rest, tag, cell, atom, h]

theorem fold_bare (base : ℕ) (op : Args → ℕ) (k v : ℕ)
    (h : ∀ n x y, op (k,n,x,y) = v) : fold base op (bare k) = v := by
  unfold fold evaluate foldStep
  simp [bare, tagNum, left, right, first, rest, tag, cell, atom, h]

end TreeEquivalenceHORS.Equivalence.SyntaxCode


namespace TreeEquivalenceHORS.Equivalence
namespace SyntaxCode

def Exact (α : Type) [Encodable α] := ∀ n (x : α), Encodable.decode n = some x → Encodable.encode x = n
private theorem exactNat : Exact ℕ := fun _ _ h => Option.some.inj h.symm

private theorem exactEquiv {α : Type} (e : α ≃ ℕ) : @Exact α (Encodable.ofEquiv ℕ e) := by
  intro n a h
  change some (e.symm n) = some a at h
  exact Option.some.inj h ▸ e.apply_symm_apply n

private theorem exactLeft {α β : Type} [Encodable α] (f : β → α) (g : α → Option β) (h : ∀ x, g (f x) = some x)
    (hα : Exact α) (hg : ∀ x y, g x = some y → f y = x) : @Exact β (Encodable.ofLeftInjection f g h) := by
  intro n b hb
  obtain ⟨x,hx,hxb⟩ := Option.bind_eq_some_iff.mp hb
  change Encodable.encode (f b) = n
  rw [hg x b hxb, hα n x hx]

theorem exactTy : Exact Ty := by
  apply exactLeft
  · apply exactEquiv
  · intro x t
    induction t generalizing x <;> intro h <;> cases x with
    | nat => contradiction
    | cons tag fields =>
      cases tag with
      | cons => contradiction
      | nat k =>
        cases k with
        | zero =>
          cases fields with
          | cons => contradiction
          | nat z => cases z <;> first | contradiction | rfl | cases Option.some.inj h
        | succ k =>
          cases k with
          | succ => contradiction
          | zero =>
            cases fields with
            | nat => contradiction
            | cons a tail =>
              cases tail with
              | nat => contradiction
              | cons b tail =>
                cases tail with
                | cons => contradiction
                | nat z =>
                  cases z with
                  | succ => contradiction
                  | zero =>
                    conv at h => lhs; whnf
                    split at h <;> first | contradiction | skip
                    cases Option.some.inj h <;> (conv_lhs => whnf) <;> congr 3 <;> solve_by_elim

theorem exactTm : Exact Tm := by
  apply exactLeft
  · apply exactEquiv
  · intro x t
    induction t generalizing x <;> intro h <;> cases x with
    | nat => contradiction
    | cons tag fields =>
      cases tag with
      | cons => contradiction
      | nat k =>
        by_cases hsmall : k < 3
        · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
          all_goals
            cases fields with
            | nat => contradiction
            | cons field tail =>
              cases field with
              | cons => contradiction
              | nat i =>
                cases tail with
                | cons => contradiction
                | nat z =>
                  cases z with
                  | succ => contradiction
                  | zero => cases Option.some.inj h <;> rfl
        · by_cases hk : k = 3
          · subst k
            cases fields with
            | nat => contradiction
            | cons a tail =>
              cases tail with
              | nat => contradiction
              | cons b tail =>
                cases tail with
                | cons => contradiction
                | nat z =>
                  cases z with
                  | succ => contradiction
                  | zero =>
                    conv at h => lhs; whnf
                    split at h <;> first | contradiction | skip
                    cases Option.some.inj h <;> (conv_lhs => whnf) <;> congr 3 <;> solve_by_elim
          · obtain ⟨j,rfl⟩ : ∃ j, k = j+4 := ⟨k-4,by omega⟩
            contradiction

theorem exactList {α : Type} [Encodable α] (ha : Exact α) : Exact (List α) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs hd
    cases n with
    | zero =>
      change Encodable.decodeList 0 = some xs at hd
      rw [Encodable.decodeList] at hd
      exact Option.some.inj hd ▸ rfl
    | succ n =>
      change Encodable.decodeList (n+1) = some xs at hd
      rw [Encodable.decodeList] at hd
      dsimp only at hd
      cases hh : (Encodable.decode n.unpair.1 : Option α) <;>
        cases ht : (Encodable.decodeList n.unpair.2 : Option (List α)) <;> simp [hh,ht, Seq.seq] at hd
      subst xs
      rename_i x xs
      change (Nat.pair (Encodable.encode x) (Encodable.encode xs))+1 = n+1
      rw [ha _ _ hh, ih _ (Nat.lt_succ_of_le (Nat.unpair_right_le n)) _ ht, Nat.pair_unpair]

theorem exactHORS : Exact HORS := by
  apply exactLeft
  · apply exactEquiv
  · rintro x ⟨a,ts,rs,i⟩ h
    conv at h => lhs; whnf
    conv_lhs => whnf
    split at h <;> (try split at h) <;> try contradiction
    cases Option.some.inj h
    rename_i h₁ h₂ h₃ h₄
    simp [exactList exactNat _ _ h₁, exactList exactTy _ _ h₂, exactList exactTm _ _ h₃, exactNat _ _ h₄]

end SyntaxCode
end TreeEquivalenceHORS.Equivalence


namespace TreeEquivalenceHORS.Equivalence.SyntaxCode

theorem enc_o : Encodable.encode Ty.o = bare 0 := rfl
theorem enc_arr (a b : Ty) : Encodable.encode (a.arr b) = binary 1 (Encodable.encode a) (Encodable.encode b) := rfl
theorem enc_var (i : ℕ) : Encodable.encode (Tm.var i) = unary 0 i := rfl
theorem enc_nt (i : ℕ) : Encodable.encode (Tm.nt i) = unary 1 i := rfl
theorem enc_tm (i : ℕ) : Encodable.encode (Tm.tm i) = unary 2 i := rfl
theorem enc_app (a b : Tm) : Encodable.encode (a.app b) = binary 3 (Encodable.encode a) (Encodable.encode b) := rfl

def tyOp (x : Args) : ℕ := if x.1 = 0 then bare 0 else binary 1 x.2.2.1 x.2.2.2
def normTy := fold (bare 0) tyOp

theorem pr_normTy : Primrec normTy := pr_fold _ _ (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
  (Primrec.const _) ((pr_binary 1).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

theorem normTy_enc (t : Ty) : normTy (Encodable.encode t) = Encodable.encode t := by
  induction t with
  | o =>
    rw [enc_o]
    exact fold_bare (bare 0) tyOp 0 (bare 0) (fun _ _ _ => rfl)
  | arr a b ia ib =>
    rw [enc_arr, normTy, fold_binary]
    simp only [tyOp, Nat.one_ne_zero, ↓reduceIte]
    exact congrArg₂ (binary 1) ia ib

theorem normTy_range (n : ℕ) : ∃ t : Ty, Encodable.encode t = normTy n := by
  apply fold_invariant (P := fun n => ∃ t : Ty, Encodable.encode t = n) (hb := ⟨.o,rfl⟩)
  rintro k n a b ⟨x,rfl⟩ ⟨y,rfl⟩
  by_cases h : k = 0
  · exact ⟨.o, by simp [tyOp,h,enc_o]⟩
  · exact ⟨.arr x y, by simp [tyOp,h,enc_arr]⟩

def termOp (v n c : ℕ → ℕ) (x : Args) :=
  if x.1 = 0 then v x.2.1 else if x.1=1 then n x.2.1 else if x.1=2 then c x.2.1 else binary 3 x.2.2.1 x.2.2.2

private theorem pr_termOp {v n c : ℕ → ℕ} (hv : Primrec v) (hn : Primrec n) (hc : Primrec c) : Primrec (termOp v n c) :=
  have test (k : ℕ) : PrimrecPred (fun x : Args => x.1 = k) := Primrec.eq.comp Primrec.fst (Primrec.const _)
  have arg : Primrec (fun x : Args => x.2.1) := Primrec.fst.comp Primrec.snd
  have more : Primrec (fun x : Args => x.2.2) := Primrec.snd.comp Primrec.snd
  Primrec.ite (test 0) (hv.comp arg) (Primrec.ite (test 1) (hn.comp arg) (Primrec.ite (test 2) (hc.comp arg)
    ((pr_binary 3).comp (Primrec.fst.comp more) (Primrec.snd.comp more))))

def tmFold (v n c : ℕ → ℕ) := fold (unary 0 0) (termOp v n c)
theorem pr_tmFold {v n c : ℕ → ℕ} (hv : Primrec v) (hn : Primrec n) (hc : Primrec c) : Primrec (tmFold v n c) :=
  pr_fold _ _ (pr_termOp hv hn hc)

theorem tmFold_enc (v n c : ℕ → ℕ) (f : Tm → ℕ)
    (v₀ : ∀ i, v i = f (.var i)) (v₁ : ∀ i, n i = f (.nt i)) (v₂ : ∀ i, c i = f (.tm i))
    (va : ∀ x y, binary 3 (f x) (f y) = f (.app x y))
    (t : Tm) : tmFold v n c (Encodable.encode t) = f t := by
  induction t with
  | var i =>
    rw [enc_var, tmFold, fold_unary _ _ 0 i (by intros; rfl)]
    exact v₀ i
  | nt i =>
    rw [enc_nt, tmFold, fold_unary _ _ 1 i (by intros; rfl)]
    exact v₁ i
  | tm i =>
    rw [enc_tm, tmFold, fold_unary _ _ 2 i (by intros; rfl)]
    exact v₂ i
  | app t u it iu =>
    rw [enc_app, tmFold, fold_binary]
    simp only [termOp, Nat.reduceEqDiff, ↓reduceIte]
    change binary 3 (tmFold v n c _) (tmFold v n c _) = _
    rw [it, iu, va]

def normTm := tmFold (unary 0) (unary 1) (unary 2)
theorem pr_normTm : Primrec normTm := pr_tmFold (pr_unary _) (pr_unary _) (pr_unary _)
theorem normTm_enc (t : Tm) : normTm (Encodable.encode t) = Encodable.encode t :=
  tmFold_enc _ _ _ Encodable.encode (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) t

theorem normTm_range (n : ℕ) : ∃ t : Tm, Encodable.encode t = normTm n := by
  apply fold_invariant (P := fun n => ∃ t : Tm, Encodable.encode t = n) (hb := ⟨.var 0,rfl⟩)
  rintro k n a b ⟨x,rfl⟩ ⟨y,rfl⟩
  by_cases h₀ : k=0
  · exact ⟨.var n, by simp [termOp,h₀,enc_var]⟩
  by_cases h₁ : k=1
  · exact ⟨.nt n, by simp [termOp,h₁,enc_nt]⟩
  by_cases h₂ : k=2
  · exact ⟨.tm n, by simp [termOp,h₂,enc_tm]⟩
  exact ⟨.app x y, by simp [termOp,h₀,h₁,h₂,enc_app]⟩

end TreeEquivalenceHORS.Equivalence.SyntaxCode


namespace TreeEquivalenceHORS.Equivalence
open SyntaxCode

private abbrev coded {α : Type} [Encodable α] (exactly : Exact α) (norm : ℕ → ℕ) (hpr : Primrec norm)
    (fix : ∀ a : α, norm (Encodable.encode a) = Encodable.encode a)
    (ran : ∀ n, ∃ a : α, Encodable.encode a = norm n) : Primcodable α where
  prim := Primrec.nat_iff.mp <| (Primrec.ite (Primrec.eq.comp hpr Primrec.id) Primrec.succ
    (Primrec.const 0)).of_eq fun n => by
      change (if norm n = n then n+1 else 0) = _
      by_cases h : norm n = n
      · obtain ⟨a, ha⟩ := ran n
        have e := ha.trans h
        rw [if_pos h]
        conv_rhs => arg 1; rw [← e, Encodable.encodek]
        simp [e]
      · rw [if_neg h]
        cases hd : (Encodable.decode n : Option α) with
        | none => rfl
        | some a =>
          have he := exactly n a hd
          exact (h (by rw [← he,fix])).elim

local instance : Primcodable Ty := coded exactTy normTy pr_normTy normTy_enc normTy_range
local instance : Primcodable Tm := coded exactTm normTm pr_normTm normTm_enc normTm_range

private def record (a t r s : ℕ) := tag 0 (cell (atom a) (cell (atom t) (cell (atom r) (cell (atom s) (atom 0)))))
private theorem encode_record (G : HORS) : Encodable.encode G =
    record (Encodable.encode G.alphabet) (Encodable.encode G.nts) (Encodable.encode G.rules) G.start := by
  cases G
  rfl

private theorem encode_mk (a : List ℕ) (ts : List Ty) (rs : List Tm) (i : ℕ) :
    Encodable.encode (HORS.mk a ts rs i) = record (Encodable.encode a) (Encodable.encode ts) (Encodable.encode rs) i := rfl

private theorem prim_record {α : Type} [Primcodable α] {a t r s : α → ℕ}
    (ha : Primrec a) (ht : Primrec t) (hr : Primrec r) (hs : Primrec s) :
    Primrec fun x => record (a x) (t x) (r x) (s x) :=
  pr_tag.comp (Primrec.const 0) (pr_cell.comp (pr_atom.comp ha) (pr_cell.comp (pr_atom.comp ht)
    (pr_cell.comp (pr_atom.comp hr) (pr_cell.comp (pr_atom.comp hs) (Primrec.const _)))))

private def field (i : ℕ) (n : ℕ) := rest (left ((rest^[i]) n))
private theorem pr_field (i : ℕ) : Primrec (field i) := by
  have hi : Primrec (rest^[i]) := by
    induction i with
    | zero => exact Primrec.id
    | succ i ih => exact ih.comp pr_rest
  exact pr_rest.comp (pr_left.comp hi)

private def getList {α : Type} [Encodable α] (i n : ℕ) : List α := (Encodable.decode (field i n)).getD []
private theorem pr_getList {α : Type} [Primcodable α] (i : ℕ) : Primrec (@getList α _ i) :=
  Primrec.option_getD.comp (Primrec.decode.comp (pr_field i)) (Primrec.const [])

private def candidateHORS (n : ℕ) : HORS := ⟨getList 0 n, getList 1 n, getList 2 n, field 3 n⟩
private theorem candidateHORS_encode (G : HORS) : candidateHORS (Encodable.encode G) = G := by
  cases G
  simp [candidateHORS, encode_record, getList, field, Function.iterate_succ_apply, record, tag, cell,
    atom, left, first, rest, Encodable.encodek]

private theorem candidate_code (n : ℕ) : Encodable.encode (candidateHORS n) =
    record (Encodable.encode (getList (α := ℕ) 0 n)) (Encodable.encode (getList (α := Ty) 1 n))
      (Encodable.encode (getList (α := Tm) 2 n)) (field 3 n) := encode_mk _ _ _ _

private theorem pr_getCode {α : Type} [Primcodable α] (i : ℕ) :
    Primrec fun n => Encodable.encode (getList (α := α) i n) :=
  Primrec.encode.comp (pr_getList i)

private theorem pr_candidateHORS : Primrec fun n => Encodable.encode (candidateHORS n) := by
  simp only [candidate_code]
  exact prim_record (pr_getCode (α := ℕ) 0) (pr_getCode (α := Ty) 1) (pr_getCode (α := Tm) 2) (pr_field 3)

local instance : Primcodable HORS := coded exactHORS _ pr_candidateHORS
  (fun G => congrArg Encodable.encode (candidateHORS_encode G)) (fun n => ⟨candidateHORS n,rfl⟩)

private def transCode := tmFold (unary 0) (fun i => unary 1 (3+i)) (fun i => if i<3 then unary 1 i else unary 2 2)

private theorem pr_transCode : Primrec transCode := pr_tmFold (pr_unary 0)
  ((pr_unary 1).comp (Primrec.nat_add.comp (Primrec.const 3) Primrec.id))
  (Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const 3)) (pr_unary 1) (Primrec.const _))

private theorem transCode_eq (t : Tm) : transCode (Encodable.encode t) = Encodable.encode (binaryTerm t) := by
  apply tmFold_enc _ _ _ (fun t => Encodable.encode (binaryTerm t)) (fun _ => rfl) (fun _ => rfl) _ (fun _ _ => rfl)
  intro i
  by_cases h : i<3 <;> simp [binaryTerm,h,enc_nt,enc_tm]

private theorem pr_binaryTerm : Primrec binaryTerm := by
  have h := Primrec.option_getD.comp (Primrec.decode.comp (pr_transCode.comp (Primrec.encode (α := Tm))))
    (Primrec.const (.tm 0 : Tm))
  apply h.of_eq
  intro t
  change ((Encodable.decode (transCode (Encodable.encode t)) : Option Tm).getD _) = _
  rw [transCode_eq, Encodable.encodek]
  rfl

private theorem prim_nts : Primrec (HORS.nts) := by
  have eq (G : HORS) : getList 1 (Encodable.encode G) = G.nts := congrArg HORS.nts (candidateHORS_encode G)
  exact ((pr_getList (α := Ty) 1).comp Primrec.encode).of_eq eq

private theorem prim_rules : Primrec (HORS.rules) := by
  have eq (G : HORS) : getList 2 (Encodable.encode G) = G.rules := congrArg HORS.rules (candidateHORS_encode G)
  exact ((pr_getList (α := Tm) 2).comp Primrec.encode).of_eq eq

private theorem prim_start : Primrec (HORS.start) := by
  have eq (G : HORS) : field 3 (Encodable.encode G) = G.start := by
    rw [encode_record]
    simp [field, Function.iterate_succ_apply, record, tag, cell, atom, left, first, rest]
  exact ((pr_field 3).comp Primrec.encode).of_eq eq

private theorem binary_code (G : HORS) : Encodable.encode (binaryScheme G) =
    record (Encodable.encode sigma2) (Encodable.encode (sigma0.map termTy ++ G.nts))
      (Encodable.encode (binaryRules ++ G.rules.map binaryTerm)) (3+G.start) := encode_mk _ _ _ _

private theorem pr_binary_record : Primrec fun G : HORS => Encodable.encode (binaryScheme G) := by
  have hts : Primrec fun G : HORS => Encodable.encode ((sigma0.map termTy) ++ G.nts) :=
    Primrec.encode.comp (Primrec.list_append.comp (Primrec.const _) prim_nts)
  have hrs : Primrec fun G : HORS => Encodable.encode (binaryRules ++ G.rules.map binaryTerm) :=
    Primrec.encode.comp (Primrec.list_append.comp (Primrec.const _) (Primrec.list_map prim_rules (pr_binaryTerm.comp Primrec.snd).to₂))
  simp only [binary_code]
  exact prim_record (Primrec.const (Encodable.encode sigma2)) hts hrs (Primrec.nat_add.comp (Primrec.const 3) prim_start)

theorem computable_binary_translation :
    Computable (fun n : ℕ => Encodable.encode ((Encodable.decode n : Option HORS).map binaryScheme)) := by
  have h := Primrec.option_map (Primrec.decode (α := HORS)) (pr_binary_record.comp Primrec.snd).to₂
  refine (Primrec.encode.comp h).to_comp.of_eq fun n => ?_
  change Encodable.encode ((Encodable.decode n : Option HORS).map (fun G => Encodable.encode (binaryScheme G))) = _
  cases (Encodable.decode n : Option HORS) <;> simp

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution :
    ∃ f : HORS → HORS,
      Computable (fun n : ℕ => Encodable.encode ((Encodable.decode n : Option HORS).map f)) ∧
      (∀ G : HORS, G.Valid → G.alphabet = sigma0 → G.Prod →
        (f G).Valid ∧ (f G).alphabet = sigma2 ∧ (f G).Prod ∧ (f G).order ≤ max 1 G.order ∧
          (f G).BT = encAt G.BT ∧ (G.Safe → (f G).Safe)) ∧
      ∀ G H : HORS, G.Valid → H.Valid → G.alphabet = sigma0 → H.alphabet = sigma0 →
        G.Prod → H.Prod → ((f G).BT = (f H).BT ↔ G.BT = H.BT) := by
  refine ⟨binaryScheme, computable_binary_translation, binary_translation_correct, ?_⟩
  intro G H vg vh ag ah pg ph
  have eg := (binary_translation_correct G vg ag pg).2.2.2.2.1
  have eh := (binary_translation_correct H vh ah ph).2.2.2.2.1
  rw [eg, eh]
  exact binary_encoding_reflects_tree_equality G H vg vh ag ah pg ph
