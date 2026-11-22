-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.exact_prefix_algorithm
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T19:42:23.304887+00:00
-- url     : https://prove2.me/submissions/eb59a481-d792-440b-8402-3b57f6fd9c30

import Definitions.Def_TreeEquivalenceHORS_Equivalence_BinaryOutput
import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_6_1
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_finite_head_test_computable

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

abbrev syntaxTyPrimcodable : Primcodable Ty := coded exactTy normTy pr_normTy normTy_enc normTy_range
abbrev syntaxTmPrimcodable : Primcodable Tm := coded exactTm normTm pr_normTm normTm_enc normTm_range

attribute [local instance] syntaxTmPrimcodable

attribute [local instance] syntaxTyPrimcodable

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

abbrev syntaxHORSPrimcodable : Primcodable HORS := coded exactHORS _ pr_candidateHORS
  (fun G => congrArg Encodable.encode (candidateHORS_encode G)) (fun n => ⟨candidateHORS n,rfl⟩)

attribute [local instance] syntaxHORSPrimcodable

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

theorem prim_nts : Primrec (HORS.nts) := by
  have eq (G : HORS) : getList 1 (Encodable.encode G) = G.nts := congrArg HORS.nts (candidateHORS_encode G)
  exact ((pr_getList (α := Ty) 1).comp Primrec.encode).of_eq eq

theorem prim_rules : Primrec (HORS.rules) := by
  have eq (G : HORS) : getList 2 (Encodable.encode G) = G.rules := congrArg HORS.rules (candidateHORS_encode G)
  exact ((pr_getList (α := Tm) 2).comp Primrec.encode).of_eq eq

theorem prim_start : Primrec (HORS.start) := by
  have eq (G : HORS) : field 3 (Encodable.encode G) = G.start := by
    rw [encode_record]
    simp [field, Function.iterate_succ_apply, record, tag, cell, atom, left, first, rest]
  exact ((pr_field 3).comp Primrec.encode).of_eq eq

theorem prim_alphabet : Primrec HORS.alphabet :=
  ((pr_getList (α := ℕ) 0).comp Primrec.encode).of_eq
    (fun G => congrArg HORS.alphabet (candidateHORS_encode G))

theorem start_code_computable : ∃ start : ℕ → ℕ, Computable start ∧ ∀ G : HORS,
    start (Encodable.encode G) = Encodable.encode (Tm.nt G.start) :=
  ⟨fun n => unary 1 (field 3 n), ((pr_unary 1).comp (pr_field 3)).to_comp,
    fun G => by
      rw [enc_nt, encode_record]
      simp [field, Function.iterate_succ_apply, record, tag, cell, atom, left, first, rest]⟩

end TreeEquivalenceHORS.Equivalence
namespace TreeEquivalenceHORS.Equivalence.SyntaxCode

theorem pr_fold_parameter {α : Type} [Primcodable α] {op : α → Args → ℕ} (base : ℕ)
    (hop : Primrec₂ op) : Primrec₂ (fun a n => fold base (op a) n) := by
  let step (a : α) (n : ℕ) (h : List ℕ) := foldStep base (op a) n h
  have ps : Primrec (fun z : α × ℕ × List ℕ => step z.1 z.2.1 z.2.2) := by
    have num := Primrec.fst.comp (Primrec.snd (α := α) (β := ℕ × List ℕ))
    have hist := Primrec.snd.comp (Primrec.snd (α := α) (β := ℕ × List ℕ))
    have lookup (f : ℕ → ℕ) (pf : Primrec f) : Primrec fun z : α × ℕ × List ℕ => z.2.2.getD (f z.2.1) base := by
      simp only [List.getD_eq_getElem?_getD]
      exact Primrec.option_getD.comp (Primrec.list_getElem?.comp hist (pf.comp num)) (Primrec.const _)
    exact hop.comp Primrec.fst ((pr_tagNum.comp num).pair
      (((pr_rest.comp pr_left).comp num).pair ((lookup _ pr_left).pair (lookup _ pr_right))))
  have ph : Primrec₂ fun a n => history (step a) n :=
    Primrec.nat_rec (Primrec.const []) ((Primrec.list_concat.comp (Primrec.snd.comp Primrec.snd) ps).to₂)
  exact (ps.comp (Primrec.fst.pair (Primrec.snd.pair ph))).to₂

end TreeEquivalenceHORS.Equivalence.SyntaxCode

namespace TreeEquivalenceHORS.Equivalence
open SyntaxCode
attribute [local instance] syntaxTyPrimcodable syntaxTmPrimcodable syntaxHORSPrimcodable
namespace SyntaxAlgorithm

variable {α β : Type} [Primcodable α] [Primcodable β]
private def readVal (v : β) (n : ℕ) := (Encodable.decode n).getD v
private theorem prim_readVal (v : β) : Primrec (readVal v) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const v)

abbrev Node (β : Type) := ℕ × ℕ × β × β
private def codeOp (v : β) (op : α → Node β → β) (a : α) (z : Args) :=
  Encodable.encode (op a (z.1,z.2.1,readVal v z.2.2.1, readVal v z.2.2.2))

private def treeFold (v : β) (op : α → Node β → β) (a : α) (n : ℕ) :=
  readVal v (fold (Encodable.encode v) (codeOp v op a) n)

private theorem prim_treeFold (v : β) (op : α → Node β → β) (hop : Primrec₂ op) :
    Primrec₂ (treeFold v op) := by
  have po : Primrec₂ (codeOp v op) := by
    have z := Primrec.snd (α := α) (β := Args)
    have R := Primrec.snd.comp z
    have cs := Primrec.snd.comp R
    exact (Primrec.encode.comp (hop.comp Primrec.fst ((Primrec.fst.comp z).pair
      ((Primrec.fst.comp R).pair (((prim_readVal v).comp (Primrec.fst.comp cs)).pair
        ((prim_readVal v).comp (Primrec.snd.comp cs))))))).to₂
  exact ((prim_readVal v).comp (pr_fold_parameter _ po)).to₂

private theorem treeFold_binary (v : β) (op : α → Node β → β) (a : α) (k x y : ℕ) :
    treeFold v op a (binary k x y) =
      op a (k, rest x, treeFold v op a x, treeFold v op a y) := by
  simp only [treeFold, fold_binary, codeOp,readVal,Encodable.encodek,Option.getD_some]

private theorem treeFold_unary (v : β) (op : α → Node β → β) (a : α) (k n : ℕ)
    (h : ∀ x y, op a (k,n,x,y) = op a (k,n,v,v)) :
    treeFold v op a (unary k n) = op a (k,n,v,v) := by
  unfold treeFold
  rw [fold_unary]
  · simp [codeOp,readVal,Encodable.encodek]
  · intros
    simp [codeOp,readVal,Encodable.encodek,h]

private theorem treeFold_bare (v : β) (op : α → Node β → β) (a : α) (k : ℕ)
    (b : β) (h : ∀ n x y, op a (k,n,x,y) = b) : treeFold v op a (bare k) = b := by
  unfold treeFold
  rw [fold_bare _ _ _ (Encodable.encode b) (by intros; simp [codeOp,h])]
  simp [readVal, Encodable.encodek]

/-- Primitive recursion over types with a primitive-recursive binary operation. -/
theorem prim_ty_fold {f : Ty → β} (b : β) (op : β → β → β) (p : Primrec₂ op)
    (ho : f .o = b) (ha : ∀ σ τ, f (.arr σ τ) = op (f σ) (f τ)) : Primrec f := by
  let alg (_ : Unit) (z : Node β) := if z.1 = 0 then b else op z.2.2.1 z.2.2.2
  have pa : Primrec₂ alg := by
    have z := Primrec.snd (α := Unit) (β := Node β)
    have cs := Primrec.snd.comp (Primrec.snd.comp z)
    exact (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp z) (Primrec.const 0)) (Primrec.const b)
      (p.comp (Primrec.fst.comp cs) (Primrec.snd.comp cs))).to₂
  apply ((prim_treeFold b alg pa).comp (Primrec.const ()) Primrec.encode).of_eq
  intro t
  induction t with
  | o => rw [enc_o,treeFold_bare _ _ _ _ b (by intros; rfl),ho]
  | arr x y hx hy => rw [enc_arr,treeFold_binary]; simpa only [alg, Nat.one_ne_zero, if_false, hx,hy] using (ha x y).symm

/-- Primitive recursion over terms, with an additional fixed parameter. -/
theorem prim_tm_fold (v : β) {f : α → Tm → β} (leaf : ℕ → α → ℕ → β)
    (node : α → β × β → β) (pl : ∀ k, Primrec₂ (leaf k)) (pn : Primrec₂ node)
    (hv : ∀ a i, f a (.var i) = leaf 0 a i) (hn : ∀ a i, f a (.nt i) = leaf 1 a i)
    (ht : ∀ a i, f a (.tm i) = leaf 2 a i) (hap : ∀ a t u, f a (.app t u) = node a (f a t, f a u)) :
    Primrec₂ f := by
  let alg (a : α) (z : Node β) := if z.1=0 then leaf 0 a z.2.1 else
    if z.1=1 then leaf 1 a z.2.1 else if z.1=2 then leaf 2 a z.2.1 else node a z.2.2
  have pa : Primrec₂ alg := by
    have z := Primrec.snd (α := α) (β := Node β)
    have tag := Primrec.fst.comp z
    have test (k : ℕ) := Primrec.eq.comp tag (Primrec.const k)
    have num := Primrec.fst.comp (Primrec.snd.comp z)
    exact (Primrec.ite (test 0) ((pl 0).comp Primrec.fst num)
      (Primrec.ite (test 1) ((pl 1).comp Primrec.fst num)
        (Primrec.ite (test 2) ((pl 2).comp Primrec.fst num)
          (pn.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp z)))))).to₂
  apply ((prim_treeFold v alg pa).comp Primrec.fst (Primrec.encode.comp Primrec.snd)).to₂.of_eq
  intro a t
  induction t with
  | var i => rw [enc_var,treeFold_unary _ _ _ _ _ (by intros; rfl),hv]; rfl
  | nt i => rw [enc_nt,treeFold_unary _ _ _ _ _ (by intros; rfl),hn]; rfl
  | tm i => rw [enc_tm,treeFold_unary _ _ _ _ _ (by intros; rfl),ht]; rfl
  | app t u h₁ h₂ => rw [enc_app,treeFold_binary]; simpa only [alg, Nat.reduceEqDiff, if_false, h₁,h₂] using (hap a t u).symm

end SyntaxAlgorithm
end TreeEquivalenceHORS.Equivalence
namespace TreeEquivalenceHORS.Equivalence
attribute [local instance] syntaxTyPrimcodable syntaxTmPrimcodable syntaxHORSPrimcodable
namespace SyntaxAlgorithm
open SyntaxCode

theorem prim_arr : Primrec₂ Ty.arr := by
  have h := Primrec.option_getD.comp (Primrec.decode.comp
    ((pr_binary 1).comp ((Primrec.encode (α := Ty)).comp (Primrec.fst (β := Ty))) ((Primrec.encode (α := Ty)).comp Primrec.snd))) (Primrec.const Ty.o)
  exact h.to₂.of_eq fun x y => by
    change ((Encodable.decode (binary 1 (Encodable.encode x) (Encodable.encode y))) : Option Ty).getD .o = _
    rw [←enc_arr,Encodable.encodek]; rfl

private theorem prim_ord : Primrec Ty.ord :=
  prim_ty_fold 0 (fun a b => max (a+1) b) (Primrec.nat_max.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to₂
    rfl (fun _ _ => rfl)

theorem prim_args : Primrec Ty.args := by
  let f (t : Ty) := (t,t.args)
  let node (a b : Ty × List Ty) := (a.1.arr b.1,a.1 :: b.2)
  have h : Primrec f := prim_ty_fold (Ty.o,[]) node
    (((prim_arr.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂)
    rfl (fun _ _ => rfl)
  exact Primrec.snd.comp h

private def firstOrder : Ty → ℕ
  | .o => 0
  | .arr t _ => t.ord

private theorem prim_homog : Primrec Ty.homog := by
  let f (t : Ty) := (t.homog,t.ord,firstOrder t)
  let node (x y : Bool × ℕ × ℕ) :=
    (x.1 && y.1 && decide (y.2.2 ≤ x.2.1), max (x.2.1+1) y.2.1, x.2.1)
  have h : Primrec f := by
    apply prim_ty_fold (true,0,0) node
    · have ord₁ := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst (α := Bool × ℕ × ℕ) (β := Bool × ℕ × ℕ)))
      have ord₂ := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd (α := Bool × ℕ × ℕ) (β := Bool × ℕ × ℕ)))
      have first₂ := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd (α := Bool × ℕ × ℕ) (β := Bool × ℕ × ℕ)))
      exact ((Primrec.and.comp (Primrec.and.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.nat_le.comp first₂ ord₁).decide).pair
        ((Primrec.nat_max.comp (Primrec.succ.comp ord₁) ord₂).pair ord₁)).to₂
    · rfl
    · intro t u; cases u <;> simp [f,node,Ty.homog,Ty.ord,firstOrder]
  exact Primrec.fst.comp h

theorem prim_termTy : Primrec termTy := by
  apply (Primrec.nat_rec₁ Ty.o ((prim_arr.comp (Primrec.const .o) Primrec.snd).to₂)).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (Ty.arr .o) ih

private def applyType (p : Option Ty × Option Ty) : Option Ty :=
  match p with
  | (some (.arr σ τ), some σ') => if σ = σ' then some τ else none
  | _ => none

def tyView (t : Ty) : Option (Ty × Ty) := match t with
  | .o => none
  | .arr x y => some (x,y)

theorem prim_tyView : Primrec tyView := by
  let f (t : Ty) := (t,tyView t)
  let node (x y : Ty × Option (Ty × Ty)) := (x.1.arr y.1,some (x.1,y.1))
  have h : Primrec f := prim_ty_fold (Ty.o,none) node
    (((prim_arr.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.option_some.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))).to₂)
    rfl (fun _ _ => rfl)
  exact Primrec.snd.comp h

private theorem prim_applyType : Primrec applyType := by
  let v (p : Option Ty × Option Ty) := p.1.bind tyView
  have pv : Primrec v := Primrec.option_bind Primrec.fst (prim_tyView.comp Primrec.snd).to₂
  have h := Primrec.option_bind pv ((Primrec.ite
    (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)))
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)).to₂)
  apply h.of_eq
  rintro ⟨x,y⟩
  cases x with
  | none => rfl
  | some x => cases x <;> cases y <;> simp [v,tyView,applyType,eq_comm]

abbrev Context := HORS × List Ty
theorem prim_typeOf : Primrec₂ (fun (p : Context) t => p.1.typeOf p.2 t) := by
  let leaf (k : ℕ) (p : Context) (i : ℕ) := if k=0 then p.2[i]? else if k=1 then p.1.nts[i]? else (p.1.alphabet[i]?).map termTy
  have pl (k : ℕ) : Primrec₂ (leaf k) := by
    have g := Primrec.fst.comp (Primrec.fst (α := Context) (β := ℕ))
    by_cases h : k=0
    · simpa [leaf,h] using (Primrec.list_getElem?.comp (Primrec.snd.comp (Primrec.fst (α := Context) (β := ℕ))) Primrec.snd).to₂
    by_cases h' : k=1
    · simpa [leaf,h,h'] using (Primrec.list_getElem?.comp (prim_nts.comp g) Primrec.snd).to₂
    · simpa [leaf,h,h'] using ((Primrec.option_map₁ prim_termTy).comp
        (Primrec.list_getElem?.comp (prim_alphabet.comp g) Primrec.snd)).to₂
  exact prim_tm_fold none leaf (fun _ p => applyType p) pl (prim_applyType.comp Primrec.snd).to₂
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (by
      intro p t u
      simp only [HORS.typeOf]
      cases p.1.typeOf p.2 t with
      | none => rfl
      | some τ => cases τ <;> cases p.1.typeOf p.2 u <;> rfl)

theorem prim_all {α β : Type} [Primcodable α] [Primcodable β]
    {l : α → List β} {p : α → β → Bool} (hl : Primrec l) (hp : Primrec₂ p) :
    Primrec fun a => (l a).all (p a) := by
  apply (Primrec.list_foldr hl (Primrec.const true)
    ((Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂)).of_eq
  intro a
  induction l a with
  | nil => rfl
  | cons x xs ih => simp_all

private def acceptTy (o : Option Ty) := (o.map Ty.homog).getD false
private theorem prim_acceptTy : Primrec acceptTy :=
  Primrec.option_getD.comp (Primrec.option_map₁ prim_homog) (Primrec.const false)

private def guardVar (p : ℕ × List Ty) (i : ℕ) : Bool :=
  match p.2[i]? with
  | some τ => decide (p.1 ≤ τ.ord)
  | none => false
private theorem prim_guardVar : Primrec₂ guardVar := by
  have xs := Primrec.snd.comp (Primrec.fst (α := ℕ × List Ty) (β := ℕ))
  have m := Primrec.fst.comp (Primrec.fst (α := ℕ × List Ty) (β := ℕ))
  apply (Primrec.option_getD.comp (Primrec.option_map (Primrec.list_getElem?.comp xs Primrec.snd)
    ((Primrec.nat_le.comp (m.comp Primrec.fst) (prim_ord.comp Primrec.snd)).decide.to₂)) (Primrec.const false)).to₂.of_eq
  intro p i; cases h : p.2[i]? <;> simp [guardVar,h]

private def checkVars (p : List Ty × Option Ty × List ℕ) : Bool :=
  (p.2.1.map fun σ => p.2.2.all (guardVar (σ.ord,p.1))).getD false
private theorem prim_checkVars : Primrec checkVars := by
  have z := Primrec.fst (α := List Ty × Option Ty × List ℕ) (β := Ty)
  have xs := Primrec.snd.comp (Primrec.snd.comp z)
  have ctx := Primrec.fst.comp z
  have arg := (prim_ord.comp Primrec.snd).pair ctx
  exact Primrec.option_getD.comp (Primrec.option_map (Primrec.fst.comp Primrec.snd)
    (prim_all xs (prim_guardVar.comp (arg.comp Primrec.fst) Primrec.snd).to₂).to₂) (Primrec.const false)

private abbrev Data := Option Ty × List ℕ × Bool
private def info (a : Context) (t : Tm) : Data := (a.1.typeOf a.2 t,t.vars,a.1.safeTm a.2 t)
private def combine (a : Context) (c : Data × Data) : Data :=
  let τ := applyType (c.1.1,c.2.1)
  (τ,c.1.2.1 ++ c.2.2.1,acceptTy τ && c.1.2.2 && c.2.2.2 && checkVars (a.2,c.2.1,c.2.2.1))

private theorem prim_combine : Primrec₂ combine := by
  have c := Primrec.snd (α := Context) (β := Data × Data)
  have l := Primrec.fst.comp c
  have r := Primrec.snd.comp c
  have t := prim_applyType.comp ((Primrec.fst.comp l).pair (Primrec.fst.comp r))
  have vl := Primrec.fst.comp (Primrec.snd.comp l)
  have vr := Primrec.fst.comp (Primrec.snd.comp r)
  have ok := prim_checkVars.comp ((Primrec.snd.comp Primrec.fst).pair ((Primrec.fst.comp r).pair vr))
  exact (t.pair ((Primrec.list_append.comp vl vr).pair
    (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (prim_acceptTy.comp t) (Primrec.snd.comp (Primrec.snd.comp l)))
      (Primrec.snd.comp (Primrec.snd.comp r))) ok))).to₂

theorem prim_constructor (k : ℕ) (f : ℕ → Tm) (h : ∀ i, Encodable.encode (f i) = unary k i) :
    Primrec f := by
  apply (Primrec.option_getD.comp (Primrec.decode.comp (pr_unary k)) (Primrec.const (Tm.var 0))).of_eq
  intro i
  change ((Encodable.decode (unary k i)) : Option Tm).getD _ = _
  rw [←h,Encodable.encodek]; rfl

private theorem prim_safeTm : Primrec₂ (fun (a : Context) t => a.1.safeTm a.2 t) := by
  let leaf (k : ℕ) (a : Context) (i : ℕ) : Data :=
    let t := if k=0 then Tm.var i else if k=1 then Tm.nt i else Tm.tm i
    let τ := a.1.typeOf a.2 t
    (τ,if k=0 then [i] else [],acceptTy τ)
  have pl (k : ℕ) : Primrec₂ (leaf k) := by
    let encodeLeaf (i : ℕ) := if k=0 then Tm.var i else if k=1 then Tm.nt i else Tm.tm i
    have pt : Primrec encodeLeaf := by
      by_cases h : k=0
      · simpa [encodeLeaf,h] using prim_constructor 0 _ enc_var
      by_cases h' : k=1
      · simpa [encodeLeaf,h,h'] using prim_constructor 1 _ enc_nt
      · simpa [encodeLeaf,h,h'] using prim_constructor 2 _ enc_tm
    have ty := prim_typeOf.comp Primrec.fst (pt.comp Primrec.snd)
    have vs : Primrec fun z : Context × ℕ => if k=0 then [z.2] else [] := by
      by_cases h : k=0
      · simpa [h] using (Primrec.list_cons.comp (Primrec.snd (α := Context) (β := ℕ)) (Primrec.const []))
      · simpa [h] using (Primrec.const (α := Context × ℕ) ([] : List ℕ))
    exact (ty.pair (vs.pair (prim_acceptTy.comp ty))).to₂
  have pi : Primrec₂ info := by
    apply prim_tm_fold (none,[],false) leaf combine pl prim_combine
    · intro a n
      simp only [leaf,if_true,info,Tm.vars,HORS.safeTm,HORS.typeOf,acceptTy]
      cases a.2[n]? <;> rfl
    · intro a n
      simp only [leaf,Nat.one_ne_zero,if_false,if_true,info,Tm.vars,HORS.safeTm,HORS.typeOf,acceptTy]
      cases a.1.nts[n]? <;> rfl
    · intro a n
      simp only [leaf,Nat.reduceEqDiff,if_false,info,Tm.vars,HORS.safeTm,HORS.typeOf,acceptTy]
      cases a.1.alphabet[n]? <;> rfl
    · intro a t u
      simp only [combine,info,Tm.vars,HORS.safeTm,acceptTy,checkVars,HORS.typeOf]
      cases ht : a.1.typeOf a.2 t with
      | none => cases hu : a.1.typeOf a.2 u <;> simp [applyType,guardVar]
      | some τ =>
        cases τ <;> cases hu : a.1.typeOf a.2 u <;> simp [applyType,guardVar]
        all_goals split <;> simp_all
        all_goals try rfl
  exact (Primrec.snd.comp (Primrec.snd.comp pi)).to₂

private theorem groundTest : Primrec (fun o : Option Ty => o == some Ty.o) := by
  apply ((Primrec.eq.comp Primrec.id (Primrec.const (some Ty.o))).decide).of_eq
  intro x; apply Bool.eq_iff_iff.mpr; simp

private theorem implTest {α : Type} [Primcodable α] {p q : α → Prop} (hp : PrimrecPred p)
    (hq : PrimrecPred q) : PrimrecPred fun x => p x → q x :=
  (hp.not.or hq).of_eq (fun _ => by tauto)

private def ruleTest (safe : Bool) (G : HORS) (i : ℕ) : Bool :=
  ((G.nts[i]?).bind fun τ => (G.rules[i]?).map fun t => if safe then τ.homog && G.safeTm τ.args t
    else G.typeOf τ.args t == some Ty.o).getD false

private theorem prim_ruleTest (safe : Bool) : Primrec₂ (ruleTest safe) := by
  have g := Primrec.fst (α := HORS) (β := ℕ)
  have ts := Primrec.list_getElem?.comp (prim_nts.comp g) Primrec.snd
  have gg := g.comp (Primrec.fst (β := Ty))
  have rs := Primrec.list_getElem?.comp (prim_rules.comp gg) (Primrec.snd.comp Primrec.fst)
  have typ := Primrec.snd.comp (Primrec.fst (α := (HORS × ℕ) × Ty) (β := Tm))
  have ctx := (gg.comp Primrec.fst).pair (prim_args.comp typ)
  have safeBody := Primrec.and.comp (prim_homog.comp typ) (prim_safeTm.comp ctx Primrec.snd)
  have okBody := groundTest.comp (prim_typeOf.comp ctx Primrec.snd)
  cases safe
  · exact (Primrec.option_getD.comp (Primrec.option_bind ts (Primrec.option_map rs okBody.to₂).to₂) (Primrec.const false)).to₂
  · exact (Primrec.option_getD.comp (Primrec.option_bind ts (Primrec.option_map rs safeBody.to₂).to₂) (Primrec.const false)).to₂

private theorem prim_ruleOK : Primrec₂ HORS.ruleOK := by
  apply (prim_ruleTest false).of_eq
  intro G i
  cases ht : G.nts[i]? <;> cases hr : G.rules[i]? <;> simp [ruleTest,HORS.ruleOK,ht,hr]

private theorem prim_ruleSafe : Primrec₂ HORS.ruleSafe := by
  apply (prim_ruleTest true).of_eq
  intro G i
  cases ht : G.nts[i]? <;> cases hr : G.rules[i]? <;> simp [ruleTest,HORS.ruleSafe,ht,hr]

theorem prim_valid : Primrec HORS.valid := by
  have ln := Primrec.list_length.comp prim_nts
  have lr := Primrec.list_length.comp prim_rules
  exact Primrec.and.comp (Primrec.and.comp (Primrec.beq.comp lr ln)
    (groundTest.comp (Primrec.list_getElem?.comp prim_nts prim_start)))
    (prim_all (Primrec.list_range.comp ln) prim_ruleOK)

end SyntaxAlgorithm
end TreeEquivalenceHORS.Equivalence
namespace TreeEquivalenceHORS.Equivalence
theorem ofArgs_args (τ : Ty) : Ty.ofArgs τ.args = τ := by
  induction τ with
  | o => rfl
  | arr σ τ _ ih => simp [Ty.args, Ty.ofArgs, ih]

theorem args_ofArgs (l : List Ty) : (Ty.ofArgs l).args = l := by
  induction l <;> simp [Ty.ofArgs, Ty.args, *]

private theorem app_typed_inv {G : HORS} {ctx : List Ty} {t u : Tm} {τ : Ty}
    (h : G.typeOf ctx (t.app u) = some τ) :
    ∃ σ, G.typeOf ctx t = some (.arr σ τ) ∧ G.typeOf ctx u = some σ := by
  unfold HORS.typeOf at h
  split at h <;> simp_all

theorem spine_typed {G : HORS} {ctx : List Ty} (t : Tm) {τ : Ty}
    (h : G.typeOf ctx t = some τ) :
    ∃ tys, G.typeOf ctx t.spine.1 = some (Ty.ofArgs (tys ++ τ.args)) ∧
      t.spine.2.map (G.typeOf ctx) = tys.map some := by
  induction t generalizing τ with
  | var i | nt i | tm i => exact ⟨[], by simpa [ofArgs_args, Tm.spine] using h, rfl⟩
  | app t u ih _ =>
    obtain ⟨σ, ht, hu⟩ := app_typed_inv h
    obtain ⟨tys, hhead, hargs⟩ := ih ht
    exact ⟨tys ++ [σ], by simpa [Tm.spine, Ty.args] using hhead,
      by simp [Tm.spine, hargs, hu]⟩

theorem subst_typed {G : HORS} {ctx : List Ty} {args : List Tm}
    (htys : args.map (G.typeOf []) = ctx.map some) (t : Tm) {τ : Ty}
    (h : G.typeOf ctx t = some τ) : G.typeOf [] (t.subst args) = some τ := by
  induction t generalizing τ with
  | var i =>
    have hh := congrArg (fun l : List (Option Ty) => l[i]?) htys
    change ctx[i]? = some τ at h
    simp only [List.getElem?_map, h, Option.map_some] at hh
    cases ha : args[i]? with
    | none => simp [ha] at hh
    | some u => simpa [Tm.subst, List.getD_eq_getElem?_getD, ha] using Option.some.inj (by simpa [ha] using hh : some (G.typeOf [] u) = some (some τ))
  | nt i | tm i => exact h
  | app t u ih₁ ih₂ =>
    obtain ⟨σ, ht, hu⟩ := app_typed_inv h
    simp [Tm.subst, HORS.typeOf, ih₁ ht, ih₂ hu]

theorem step_typed {G : HORS} (hG : G.Valid) {t u : Tm}
    (ht : G.typeOf [] t = some .o) (hs : G.HeadStep t u) : G.typeOf [] u = some .o := by
  obtain ⟨tys, hhead, hargs⟩ := spine_typed t ht
  unfold HORS.HeadStep HORS.headStep at hs
  split at hs <;> try contradiction
  rename_i F args sp
  simp only [sp, HORS.typeOf, Ty.args, List.append_nil] at hhead
  simp only [sp] at hargs
  rw [hhead] at hs
  cases hr : G.rules[F]? with
  | none => simp [hr] at hs
  | some body =>
    simp only [hr, args_ofArgs] at hs
    split at hs <;> try contradiction
    obtain rfl := Option.some.inj hs
    apply subst_typed hargs
    have hi : F < G.nts.length := by simpa using (Option.isSome_iff_exists.mpr ⟨_, hhead⟩)
    simp only [HORS.Valid, HORS.valid, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hG
    simpa [HORS.ruleOK, hhead, hr, args_ofArgs] using hG.2 F hi

theorem headConv_typed {G : HORS} (hG : G.Valid) {t : Tm} (ht : G.typeOf [] t = some .o)
    {c : ℕ} {us : List Tm} (hc : G.HeadConv t c us) :
    G.alphabet[c]? = some us.length ∧ ∀ u ∈ us, G.typeOf [] u = some .o := by
  obtain ⟨v, hv, hsp⟩ := hc
  have htv : G.typeOf [] v = some .o := by
    clear hsp
    induction hv with
    | refl => exact ht
    | tail _ hs ih => exact step_typed hG ih hs
  obtain ⟨tys, hh, hu⟩ := spine_typed v htv
  simp only [hsp, HORS.typeOf, Ty.args, List.append_nil] at hh
  simp only [hsp] at hu
  cases he : G.alphabet[c]? with
  | none => simp [he] at hh
  | some r =>
    simp only [he, Option.map_some, Option.some.injEq] at hh
    have ha := congrArg Ty.args hh
    simp only [termTy, args_ofArgs] at ha
    subst tys
    have len := congrArg List.length hu
    simp only [List.length_map, List.length_replicate] at len
    refine ⟨by rw [len], fun u hm => ?_⟩
    have mem : G.typeOf [] u ∈ us.map (G.typeOf []) := List.mem_map_of_mem hm
    rw [hu] at mem
    simpa using (List.eq_of_mem_replicate (by simpa only [List.map_replicate] using mem))

theorem terminal_conv {G : HORS} {t : Tm} {c : ℕ} {args : List Tm}
    (head : t.spine = (.tm c, args)) (a : ℕ) (us : List Tm) :
    G.HeadConv t a us ↔ c = a ∧ args = us := by
  constructor
  · rintro ⟨t', hs, h⟩
    rcases hs.cases_head with rfl | ⟨v, step, _⟩
    · simpa [head] using h
    · simp [HORS.HeadStep, HORS.headStep, head] at step
  · rintro ⟨rfl, rfl⟩
    exact ⟨t, .refl, head⟩


theorem exposed_eq {t : Tm} {c : ℕ} {us : List Tm} :
    exposed t = some (c, us) ↔ t.spine = (.tm c, us) := by
  unfold exposed
  rcases t.spine with ⟨h, args⟩
  cases h <;> simp

theorem run_reaches (G : HORS) (t : Tm) (n : ℕ) :
    Relation.ReflTransGen G.HeadStep t (G.run n t) := by
  induction n generalizing t with
  | zero => exact .refl
  | succ n ih =>
    cases hs : G.headStep t with
    | none => simpa [HORS.run, hs] using (Relation.ReflTransGen.refl (r := G.HeadStep) (a := t))
    | some u => simpa [HORS.run, hs] using (ih u).head (show G.HeadStep t u from hs)

private theorem budget_of_steps {G : HORS} {t u : Tm} (h : Relation.ReflTransGen G.HeadStep t u) :
    ∃ n, G.run n t = u := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n+1, by simp only [HORS.run, show G.headStep _ = some _ from hs, hn]⟩

theorem headConv_unique {G : HORS} {t : Tm} {c a : ℕ} {us vs : List Tm}
    (hc : G.HeadConv t c us) (ha : G.HeadConv t a vs) : (c, us) = (a, vs) := by
  obtain ⟨u, hu, sp⟩ := hc
  induction hu using Relation.ReflTransGen.head_induction_on with
  | refl => exact Prod.ext (terminal_conv sp a vs |>.mp ha).1 (terminal_conv sp a vs |>.mp ha).2
  | head hs _ ih =>
    apply ih
    obtain ⟨v, hv, sv⟩ := ha
    rcases hv.cases_head with rfl | ⟨w, hw, tail⟩
    · simp [HORS.HeadStep, HORS.headStep, sv] at hs
    · exact ⟨v, Option.some.inj (hs.symm.trans hw) ▸ tail, sv⟩

theorem head_eq_some_iff {G : HORS} {t : Tm} {c : ℕ} {us : List Tm} :
    G.head t = some (c, us) ↔ G.HeadConv t c us := by
  classical
  unfold HORS.head
  split
  next hex =>
    constructor
    · exact fun h => ⟨_, run_reaches G t _, exposed_eq.mp h⟩
    · intro h
      obtain ⟨⟨a, vs⟩, hv⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hex)
      exact hv.trans (congrArg some (headConv_unique ⟨_, run_reaches G t _, exposed_eq.mp hv⟩ h))
  next hn =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨v, h, hv⟩
    obtain ⟨n, rfl⟩ := budget_of_steps h
    exact hn ⟨n, Option.isSome_iff_exists.mpr ⟨_, exposed_eq.mpr hv⟩⟩


end TreeEquivalenceHORS.Equivalence
namespace TreeEquivalenceHORS.Equivalence.OperationalAlgorithm
open SyntaxAlgorithm SyntaxCode
attribute [local instance] syntaxTyPrimcodable syntaxTmPrimcodable syntaxHORSPrimcodable

private theorem pr_appTerm : Primrec₂ Tm.app := by
  apply (Primrec.option_getD.comp (Primrec.decode.comp ((pr_binary 3).comp
    ((Primrec.encode (α := Tm)).comp (Primrec.fst (β := Tm))) ((Primrec.encode (α := Tm)).comp Primrec.snd)))
    (Primrec.const (Tm.tm 0))).to₂.of_eq
  intro x y
  change ((Encodable.decode (binary 3 (Encodable.encode x) (Encodable.encode y))) : Option Tm).getD _ = _
  rw [←enc_app,Encodable.encodek]; rfl

def baseTerm (k i : ℕ) := if k=0 then Tm.var i else if k=1 then Tm.nt i else Tm.tm i
private theorem pr_base (k : ℕ) : Primrec (baseTerm k) := by
  by_cases k0 : k=0
  · exact (prim_constructor 0 _ enc_var).of_eq (fun i => by simp [baseTerm,k0])
  by_cases k1 : k=1
  · exact (prim_constructor 1 _ enc_nt).of_eq (fun i => by simp [baseTerm,k0,k1])
  · exact (prim_constructor 2 _ enc_tm).of_eq (fun i => by simp [baseTerm,k0,k1])

private theorem pr_spine : Primrec Tm.spine := by
  let leaf (k : ℕ) (_ : Unit) (i : ℕ) := (baseTerm k i,baseTerm k i,([] : List Tm))
  let node (_ : Unit) (p : (Tm × Tm × List Tm) × (Tm × Tm × List Tm)) :=
    (p.1.1.app p.2.1,p.1.2.1,p.1.2.2 ++ [p.2.1])
  have pl (k) : Primrec₂ (leaf k) := ((pr_base k).comp Primrec.snd |>.pair
    (((pr_base k).comp Primrec.snd).pair (Primrec.const []))).to₂
  have pn : Primrec₂ node := by
    have l := Primrec.fst.comp (Primrec.snd (α := Unit) (β := (Tm × Tm × List Tm) × (Tm × Tm × List Tm)))
    have r := Primrec.snd.comp (Primrec.snd (α := Unit) (β := (Tm × Tm × List Tm) × (Tm × Tm × List Tm)))
    exact ((pr_appTerm.comp (Primrec.fst.comp l) (Primrec.fst.comp r)).pair
      ((Primrec.fst.comp (Primrec.snd.comp l)).pair
        (Primrec.list_concat.comp (Primrec.snd.comp (Primrec.snd.comp l)) (Primrec.fst.comp r)))).to₂
  have prod : Primrec₂ (fun (_ : Unit) (t : Tm) => (t,t.spine)) := prim_tm_fold (.tm 0,.tm 0,[])
    leaf node pl pn (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
  exact Primrec.snd.comp (prod.comp (Primrec.const ()) Primrec.id)

private theorem pr_subst : Primrec₂ Tm.subst := by
  let leaf (k : ℕ) (args : List Tm) (i : ℕ) := if k=0 then args.getD i (.var i) else baseTerm k i
  have pl (k) : Primrec₂ (leaf k) := by
    by_cases h : k=0
    · simpa [leaf,h,List.getD_eq_getElem?_getD] using (Primrec.option_getD.comp Primrec.list_getElem?
        ((prim_constructor 0 _ enc_var).comp (Primrec.snd (α := List Tm)))).to₂
    · simpa [leaf,h] using ((pr_base k).comp (Primrec.snd (α := List Tm))).to₂
  exact prim_tm_fold (.tm 0) leaf (fun _ p => p.1.app p.2) pl (pr_appTerm.comp
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

private def atomIndex (k : ℕ) (t : Tm) :=
  let n := Encodable.encode t
  if tagNum n = k then some (rest (left n)) else none
private theorem pr_atomIndex (k : ℕ) : Primrec (atomIndex k) :=
  Primrec.ite (Primrec.eq.comp (pr_tagNum.comp Primrec.encode) (Primrec.const k))
    (Primrec.option_some.comp (pr_rest.comp (pr_left.comp Primrec.encode))) (Primrec.const none)

def headStepAlg (G : HORS) (t : Tm) :=
  (atomIndex 1 t.spine.1).bind fun F => (G.nts[F]?).bind fun τ => (G.rules[F]?).bind fun b =>
    if t.spine.2.length = τ.args.length then some (b.subst t.spine.2) else none

theorem pr_headStep : Primrec₂ HORS.headStep := by
  have gs := Primrec.fst (α := HORS) (β := Tm)
  have as := Primrec.snd.comp (pr_spine.comp (Primrec.snd (α := HORS) (β := Tm)))
  have head := (pr_atomIndex 1).comp (Primrec.fst.comp (pr_spine.comp (Primrec.snd (α := HORS))))
  have tys := Primrec.list_getElem?.comp ((prim_nts.comp gs).comp Primrec.fst) Primrec.snd
  have bodies := Primrec.list_getElem?.comp (((prim_rules.comp gs).comp (Primrec.fst (β := ℕ))).comp (Primrec.fst (β := Ty)))
    (Primrec.snd.comp Primrec.fst)
  have ctx := as.comp ((Primrec.fst (β := ℕ)).comp ((Primrec.fst (β := Ty)).comp (Primrec.fst (β := Tm))))
  have accept := Primrec.eq.comp (Primrec.list_length.comp ctx)
    (Primrec.list_length.comp (prim_args.comp (Primrec.snd.comp Primrec.fst)))
  have pr : Primrec₂ headStepAlg := (Primrec.option_bind head (Primrec.option_bind tys (Primrec.option_bind bodies
    (Primrec.ite accept (Primrec.option_some.comp (pr_subst.comp ctx Primrec.snd)) (Primrec.const none)).to₂).to₂).to₂).to₂
  apply pr.of_eq
  intro G t
  unfold headStepAlg HORS.headStep
  rcases sp : t.spine with ⟨h,us⟩
  cases h <;> simp [sp,atomIndex,enc_var,enc_nt,enc_tm,enc_app,tagNum,first,rest,left,unary,binary,tag,cell,atom]
  split <;> simp_all

private def tick (G : HORS) (t : Tm) := (G.headStep t).getD t
private theorem run_eq (G : HORS) (t : Tm) (n : ℕ) : (tick G)^[n] t = G.run n t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases hs : G.headStep t with
    | none =>
      have fail : tick G t = t := by simp [tick,hs]
      simp [HORS.run,hs,fail,Function.iterate_fixed fail]
    | some u => simpa [tick,hs,HORS.run] using ih u

private theorem pr_run : Primrec₂ (fun (a : HORS × Tm) n => a.1.run n a.2) := by
  have step : Primrec₂ tick := (Primrec.option_getD.comp pr_headStep Primrec.snd).to₂
  apply (Primrec.nat_rec (Primrec.snd (α := HORS) (β := Tm)) (step.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro p n
  rw [←run_eq]
  induction n <;> simp [Function.iterate_succ_apply', *]

private theorem pr_exposed : Primrec exposed := by
  have hd := (pr_atomIndex 2).comp (Primrec.fst.comp pr_spine)
  apply (Primrec.option_map hd ((Primrec.snd.pair ((Primrec.snd.comp pr_spine).comp Primrec.fst)).to₂)).of_eq
  intro t
  unfold exposed
  rcases sp : t.spine with ⟨h,us⟩
  cases h <;> simp [sp,atomIndex,enc_var,enc_nt,enc_tm,enc_app,tagNum,first,rest,left,unary,binary,tag,cell,atom]

theorem pr_exposeAt : Primrec₂ (fun (p : HORS × Tm) n => p.1.exposeAt n p.2) :=
  (pr_exposed.comp pr_run).to₂

end TreeEquivalenceHORS.Equivalence.OperationalAlgorithm

namespace TreeEquivalenceHORS.Equivalence.OperationalAlgorithm
open SyntaxAlgorithm
attribute [local instance] syntaxTyPrimcodable syntaxTmPrimcodable syntaxHORSPrimcodable

private theorem search_computable {α β : Type} [Primcodable α] [Primcodable β] {spec : α → β}
    (search : α → ℕ → Option β) (hc : Computable₂ search) (total : ∀ x, ∃ n, search x n = some (spec x))
    (sound : ∀ x n y, search x n = some y → y = spec x) : Computable spec := by
  apply (Partrec.rfindOpt hc).of_eq_tot
  intro x
  have dom := Nat.rfindOpt_dom.mpr (show ∃ n y, y ∈ search x n from (total x).imp (fun n h => ⟨spec x,h⟩))
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp dom
  obtain ⟨n,hn⟩ := Nat.rfindOpt_spec hy
  exact sound x n y hn ▸ hy

private theorem budget {G : HORS} {t : Tm} {p : ℕ × List Tm} (h : G.head t = some p) :
    ∃ n, G.exposeAt n t = some p := by
  classical
  unfold HORS.head at h
  split at h
  next _ => exact ⟨_,h⟩
  next => contradiction

theorem effective_head (b : ℕ × ℕ → Bool) (cb : Computable b)
    (spec : ∀ (G : HORS) (t : Tm), G.Valid → G.typeOf [] t = some .o →
      (b (Encodable.encode G,Encodable.encode t) = true ↔ ∃ c us, G.HeadConv t c us)) :
    ∃ head : HORS × Tm → Option (ℕ × List Tm), Computable head ∧
      ∀ G t, G.Valid → G.typeOf [] t = some .o → head (G,t) = G.head t := by
  classical
  let ready (p : HORS × Tm) := p.1.valid && decide (p.1.typeOf [] p.2 = some Ty.o) && b (Encodable.encode p.1,Encodable.encode p.2)
  have rv : Computable ready := by
    have ty := prim_typeOf.comp (Primrec.fst.pair (Primrec.const ([] : List Ty))) (Primrec.snd (α := HORS) (β := Tm))
    exact Primrec.and.to_comp.comp ((Primrec.and.comp (prim_valid.comp Primrec.fst)
      (Primrec.eq.comp ty (Primrec.const (some Ty.o))).decide).to_comp)
      (cb.comp ((Primrec.encode.comp Primrec.fst).pair (Primrec.encode.comp Primrec.snd)).to_comp)
  let find (p : HORS × Tm) (n : ℕ) : Option (Option (ℕ × List Tm)) :=
    bif ready p then (p.1.exposeAt n p.2).map some else some none
  have cf : Computable₂ find := (Computable.cond (rv.comp Computable.fst)
    ((Primrec.option_map₁ Primrec.option_some).to_comp.comp pr_exposeAt.to_comp) (Computable.const (some none))).to₂
  let head (p : HORS × Tm) := if ready p then p.1.head p.2 else none
  have present (p : HORS × Tm) (h : ready p = true) : ∃ w, p.1.head p.2 = some w := by
    simp only [ready,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨c,us,conv⟩ := (spec _ _ h.1.1 h.1.2).mp h.2
    exact ⟨_,head_eq_some_iff.mpr conv⟩
  refine ⟨head, search_computable find cf ?_ ?_, ?_⟩
  · intro p
    cases h : ready p with
    | false => exact ⟨0,by simp [find,head,h]⟩
    | true =>
      obtain ⟨w,hw⟩ := present p h
      obtain ⟨n,hn⟩ := budget hw
      exact ⟨n,by simp [find,head,h,hn,hw]⟩
  · intro p n y hy
    cases h : ready p with
    | false => simpa [find,head,h] using (Option.some.inj (by simpa [find,h] using hy : some none = some y)).symm
    | true =>
      cases he : p.1.exposeAt n p.2 with
      | none => simp [find,h,he] at hy
      | some w =>
        obtain rfl := (by simpa [find,h,he] using hy : some w = y)
        obtain ⟨c,us⟩ := w
        have e := head_eq_some_iff.mpr (show p.1.HeadConv p.2 c us from ⟨_,run_reaches _ _ _,exposed_eq.mp he⟩)
        simp [head,h,e]
  · intro G t vg ht
    cases h : b (Encodable.encode G,Encodable.encode t) with
    | true => simp [head,ready,show G.valid=true from vg,ht,h]
    | false =>
      have em : G.head t = none := by
        cases he : G.head t with
        | none => rfl
        | some p =>
          obtain ⟨c,us⟩ := p
          have pos := (spec G t vg ht).mpr ⟨c,us,head_eq_some_iff.mp he⟩
          simp [h] at pos
      simp [head,ready,h,em]

end TreeEquivalenceHORS.Equivalence.OperationalAlgorithm

namespace TreeEquivalenceHORS.Equivalence.OperationalAlgorithm
open SyntaxAlgorithm SyntaxCode
attribute [local instance] syntaxTyPrimcodable syntaxTmPrimcodable syntaxHORSPrimcodable

private theorem cfold {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    (b : β) {l : α → List β} {s : α → γ} {f : α → γ × β → γ}
    (cl : Computable l) (cs : Computable s) (cf : Computable₂ f) :
    Computable fun a => (l a).foldl (fun acc x => f a (acc,x)) (s a) := by
  let step (a : α) (v : ℕ × γ) := f a (v.2,(l a).getD v.1 b)
  have stepC : Computable₂ step := by
    have elem := Primrec.list_getElem?.to_comp.comp (cl.comp Computable.fst)
      (Computable.fst.comp (Computable.snd (α := α) (β := ℕ × γ)))
    simp only [step,List.getD_eq_getElem?_getD]
    exact (cf.comp Computable.fst ((Computable.snd.comp Computable.snd).pair
      (Computable.option_getD elem (Computable.const b)))).to₂
  apply (Computable.nat_rec (Primrec.list_length.to_comp.comp cl) cs stepC).of_eq
  intro a
  have aux (i : ℕ) (hi : i ≤ (l a).length) :
      Nat.rec (s a) (fun j h => step a (j,h)) i = ((l a).take i).foldl (fun acc x => f a (acc,x)) (s a) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have h : i < (l a).length := by omega
      change step a (i,Nat.rec (s a) (fun j acc => step a (j,acc)) i) = _
      rw [ih h.le]
      simp only [step,List.take_succ_eq_append_getElem h,List.foldl_append,
        List.foldl_cons,List.foldl_nil,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
  simpa using aux _ le_rfl

private theorem cmap {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    (b : β) {l : α → List β} {f : α → β → γ} (cl : Computable l) (cf : Computable₂ f) :
    Computable fun a => (l a).map (f a) := by
  have act := Primrec.list_concat.to_comp.comp (Computable.fst.comp (Computable.snd (α := α) (β := List γ × β)))
    (cf.comp Computable.fst (Computable.snd.comp Computable.snd))
  apply (cfold b cl (Computable.const ([] : List γ)) act.to₂).of_eq
  intro a
  simp only [List.concat_eq_append]
  apply (List.foldl_append_eq_append (f := fun b => [f a b])).trans
  simp only [List.nil_append]
  induction l a <;> simp_all

private theorem pr_max : Primrec HORS.maxArity := Primrec.list_foldr prim_alphabet (Primrec.const 0)
  (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

private theorem pr_addrs : Primrec₂ addrs := by
  have op := Primrec.list_flatMap (Primrec.list_range.comp (Primrec.fst (β := ℕ × List (List ℕ))))
    (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  apply (Primrec.nat_rec (Primrec.const []) (Primrec.list_cons.comp (Primrec.const []) op).to₂).of_eq
  intro b n; induction n <;> simp [addrs, *]

abbrev Head := HORS × Tm → Option (ℕ × List Tm)

private def down (head : Head) (G : HORS) (p : Option Tm × ℕ) :=
  p.1.bind fun t => (head (G,t)).bind fun h => h.2[p.2]?

private theorem cdown {head : Head} (hc : Computable head) : Computable₂ (down head) := by
  have z := Computable.fst (α := HORS × (Option Tm × ℕ)) (β := Tm)
  have hh := hc.comp ((Computable.fst.comp z).pair Computable.snd)
  have i := Computable.snd.comp (Computable.snd.comp z)
  exact (Computable.option_bind (Computable.fst.comp Computable.snd) (Computable.option_bind hh
    (Primrec.list_getElem?.to_comp.comp (Computable.snd.comp Computable.snd) (i.comp Computable.fst)).to₂).to₂).to₂

private def label (head : Head) (G : HORS) (s : Option Tm) : ℕ :=
  (s.map (fun t => ((head (G,t)).map (fun p => Encodable.encode (Lab.term p.1))).getD (Encodable.encode Lab.bot))).getD
    (Encodable.encode Lab.absent)

private theorem clabel {head : Head} (hc : Computable head) : Computable₂ (label head) := by
  have cr : Primrec (fun n => Encodable.encode (Lab.term n)) := (pr_unary 0).of_eq (fun _ => rfl)
  have hh := hc.comp ((Computable.fst.comp (Computable.fst (α := HORS × Option Tm) (β := Tm))).pair Computable.snd)
  have val := Computable.option_getD (Computable.option_map hh
    ((cr.comp (Primrec.fst.comp Primrec.snd)).to_comp.to₂)) (Computable.const (Encodable.encode Lab.bot))
  exact (Computable.option_getD (Computable.option_map Computable.snd val.to₂) (Computable.const _)).to₂

private def readRaw (head : Head) (G : HORS) (t : Tm) (w : List ℕ) :=
  label head G (w.foldl (fun s i => down head G (s,i)) (some t))

private theorem cread {head : Head} (hc : Computable head) :
    Computable fun p : (HORS × Tm) × List ℕ => readRaw head p.1.1 p.1.2 p.2 := by
  have g := Computable.fst.comp (Computable.fst (α := HORS × Tm) (β := List ℕ))
  have t := Computable.snd.comp (Computable.fst (α := HORS × Tm) (β := List ℕ))
  have run := cfold 0 Computable.snd (Primrec.option_some.to_comp.comp t)
    ((cdown hc).comp (g.comp Computable.fst) Computable.snd).to₂
  exact (clabel hc).comp g run

private theorem read_spec {head : Head} (hs : ∀ G t, G.Valid → G.typeOf [] t = some .o → head (G,t) = G.head t)
    (G : HORS) (vg : G.Valid) (t : Tm) (ht : G.typeOf [] t = some .o) (w : List ℕ) :
    readRaw head G t w = Encodable.encode (G.BTat t w) := by
  have noTerm (w : List ℕ) : w.foldl (fun s i => down head G (s,i)) none = none := by
    induction w with
    | nil => rfl
    | cons i w ih => exact ih
  induction w generalizing t with
  | nil =>
    simp only [readRaw,List.foldl_nil,label,Option.map_some,Option.getD_some,HORS.BTat,hs G t vg ht]
    cases G.head t with
    | none => rfl
    | some h => cases h; rfl
  | cons i w ih =>
    simp only [readRaw,List.foldl_cons,down,Option.bind_some,hs G t vg ht,HORS.BTat]
    cases e : G.head t with
    | none => exact congrArg (label head G) (noTerm w)
    | some h =>
      obtain ⟨c,us⟩ := h
      simp only [Option.bind_some]
      by_cases hi : i < us.length
      · simp only [hi,dif_pos,List.getElem?_eq_getElem hi]
        exact ih _ ((headConv_typed vg ht (head_eq_some_iff.mp e)).2 _ (List.getElem_mem _))
      · simp only [dif_neg hi,List.getElem?_eq_none (by omega : us.length ≤ i)]
        exact congrArg (label head G) (noTerm w)

theorem prefixes_of_effective_head (head : Head) (hc : Computable head)
    (hs : ∀ G t, G.Valid → G.typeOf [] t = some .o → head (G,t) = G.head t) :
    ∃ f : ℕ × ℕ × ℕ → ℕ, Computable f ∧ ∀ (G : HORS) (t : Tm) (d : ℕ), G.Valid → G.typeOf [] t = some .o →
      f (Encodable.encode G, Encodable.encode t, d) = Encodable.encode (G.Pref t d) := by
  let g (z : ℕ × ℕ × ℕ) := (Encodable.decode z.1 : Option HORS).getD ⟨[],[],[],0⟩
  let t (z : ℕ × ℕ × ℕ) := (Encodable.decode z.2.1 : Option Tm).getD (.tm 0)
  have cg : Primrec g := Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const _)
  have ct : Primrec t := Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const _)
  have addresses := pr_addrs.comp (pr_max.comp cg) (Primrec.snd.comp Primrec.snd)
  have both := (cg.pair ct).to_comp
  have read := (cread hc).comp ((both.comp Computable.fst).pair (Computable.snd (β := List ℕ)))
  have mapC := cmap ([] : List ℕ) addresses.to_comp (Computable.snd.pair read).to₂
  refine ⟨_,Primrec.encode.to_comp.comp mapC,?_⟩
  intro G v d vg ht
  change Encodable.encode ((addrs (g _).maxArity d).map (fun w => (w,readRaw head (g _) (t _) w))) = _
  simp only [g,t,Encodable.encodek,Option.getD_some,read_spec hs G vg v ht,HORS.Pref]
  induction addrs G.maxArity d with
  | nil => rfl
  | cons w wr ih => simp [Encodable.encode_prod_val,ih]

end TreeEquivalenceHORS.Equivalence.OperationalAlgorithm


namespace TreeEquivalenceHORS.Equivalence


private theorem proved_here :
    ∃ f : ℕ × ℕ × ℕ → ℕ, Computable f ∧
      ∀ (G : HORS) (t : Tm) (d : ℕ), G.Valid → G.typeOf [] t = some .o →
        f (Encodable.encode G, Encodable.encode t, d) = Encodable.encode (G.Pref t d) := by
  obtain ⟨b,cb,spec⟩ := finite_head_test_computable
  obtain ⟨head,cHead,hHead⟩ := OperationalAlgorithm.effective_head b cb (fun G t vg ht =>
    (spec G t vg ht).trans (lemma_6_1 G vg t ht))
  exact OperationalAlgorithm.prefixes_of_effective_head head cHead hHead



end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution :
    ∃ f : ℕ × ℕ × ℕ → ℕ, Computable f ∧
      ∀ (G : HORS) (t : Tm) (d : ℕ), G.Valid → G.typeOf [] t = some .o →
        f (Encodable.encode G, Encodable.encode t, d) = Encodable.encode (G.Pref t d) := proved_here
