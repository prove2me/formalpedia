-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.finite_head_test_computable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T19:35:37.941973+00:00
-- url     : https://prove2.me/submissions/26690a0d-50d7-48ba-8091-0e201f716a24

import Definitions.Def_TreeEquivalenceHORS_Equivalence_BinaryOutput
import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

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

theorem prim_constructor (k : ℕ) (f : ℕ → Tm) (h : ∀ i, Encodable.encode (f i) = unary k i) :
    Primrec f := by
  apply (Primrec.option_getD.comp (Primrec.decode.comp (pr_unary k)) (Primrec.const (Tm.var 0))).of_eq
  intro i
  change ((Encodable.decode (unary k i)) : Option Tm).getD _ = _
  rw [←h,Encodable.encodek]; rfl

end SyntaxAlgorithm
end TreeEquivalenceHORS.Equivalence
namespace TreeEquivalenceHORS.Equivalence
namespace FiniteModel

def Below (σ : Ty) (x y : SVal) := leT σ x y = true
def Member (σ : Ty) (x : SVal) := x ∈ enum σ

theorem below_tabs (σ τ : Ty) (s t : List SVal) :
    Below (.arr σ τ) (.tab s) (.tab t) ↔ List.Forall₂ (Below τ) s t := by
  rw [List.forall₂_iff_zip]
  simp [Below,leT,List.all_eq_true,Prod.forall]

theorem below_antisymm (σ : Ty) {x y : SVal} (h : Below σ x y) (k : Below σ y x) : x = y := by
  induction σ generalizing x y with
  | o => cases x <;> cases y <;> simp_all [Below,leT]; rename_i x y; cases x <;> cases y <;> simp_all
  | arr σ τ _ ih =>
    cases x <;> cases y <;> try contradiction
    rename_i s t
    rw [below_tabs,List.forall₂_iff_get] at h k
    apply congrArg SVal.tab
    apply List.ext_get h.1
    intro i hi hj
    exact ih (h.2 i hi hj) (k.2 i hj hi)

theorem below_trans (σ : Ty) {x y z : SVal} (h : Below σ x y) (k : Below σ y z) : Below σ x z := by
  induction σ generalizing x y z with
  | o => cases x <;> cases y <;> cases z <;> try contradiction
         rename_i a b c; cases a <;> cases b <;> cases c <;> simp_all [Below,leT]
  | arr σ τ _ ih =>
    cases x <;> cases y <;> cases z <;> try contradiction
    rw [below_tabs,List.forall₂_iff_get] at h k ⊢
    refine ⟨h.1.trans k.1, fun i hi hj => ?_⟩
    have hm := h.1 ▸ hi
    exact ih (h.2 i hi hm) (k.2 i hm hj)

theorem mem_tuples {α : Type} (k : ℕ) (xs : List α) (ys : List α) :
    ys ∈ tuples k xs ↔ ys.length = k ∧ ∀ x ∈ ys, x ∈ xs := by
  induction k generalizing ys with
  | zero => cases ys <;> simp [tuples]
  | succ k ih =>
    cases ys with
    | nil => simp [tuples]
    | cons y ys =>
      simp [tuples,ih,and_assoc,and_left_comm,and_comm]

def TableOK (σ τ : Ty) (l : List SVal) : Prop :=
  l.length = (enum σ).length ∧ (∀ v ∈ l, Member τ v) ∧
    ∀ i < (enum σ).length, ∀ j < (enum σ).length,
      Below σ ((enum σ).getD i default) ((enum σ).getD j default) →
        Below τ (l.getD i default) (l.getD j default)

theorem mem_tab (σ τ : Ty) (l : List SVal) : Member (.arr σ τ) (.tab l) ↔ TableOK σ τ l := by
  have bit (a b : Bool) : (a = false ∨ b = true) ↔ (a = true → b = true) := by cases a <;> simp
  simp [Member,enum,TableOK,mem_tuples,Below,List.all_eq_true, Bool.or_eq_true, and_assoc,bit]

theorem below_refl (σ : Ty) {v : SVal} (hv : Member σ v) : Below σ v v := by
  induction σ generalizing v with
  | o =>
    simp [Member,enum] at hv
    rcases hv with rfl | rfl <;> rfl
  | arr σ τ _ ih =>
    cases v with
    | bit b => simp [Member,enum] at hv
    | tab l =>
      obtain ⟨_,mem,_⟩ := (mem_tab _ _ _).mp hv
      apply (below_tabs _ _ _ _).mpr
      apply List.forall₂_iff_get.mpr
      exact ⟨rfl, fun i h _ => ih (mem _ (List.get_mem _ _))⟩

def index (σ : Ty) (x : SVal) : ℕ :=
  (enum σ).findIdx fun y => leT σ x y && leT σ y x

theorem index_lt {σ : Ty} {x : SVal} (hx : Member σ x) : index σ x < (enum σ).length :=
  List.findIdx_lt_length_of_exists ⟨x,hx,by simp only [Bool.and_self]; exact below_refl σ hx⟩

theorem at_index {σ : Ty} {x : SVal} (hx : Member σ x) : (enum σ).getD (index σ x) default = x := by
  have ok := @List.findIdx_getElem _ (fun y => leT σ x y && leT σ y x) (enum σ) (index_lt hx)
  simp only [Bool.and_eq_true] at ok
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (index_lt hx), Option.getD_some]
  exact below_antisymm σ ok.2 ok.1

theorem mem_getD {σ : Ty} {i : ℕ} (h : i < (enum σ).length) : Member σ ((enum σ).getD i default) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
  exact List.getElem_mem h

def tabulate (σ : Ty) (f : SVal → SVal) : SVal := .tab ((enum σ).map f)

private theorem map_get {l : List SVal} (f : SVal → SVal) (i : ℕ) (hi : i < l.length) :
    (l.map f).getD i default = f (l.getD i default) := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]

theorem tabulate_lookup {σ : Ty} (f : SVal → SVal) {x : SVal} (hx : Member σ x) :
    appT σ (tabulate σ f) x = f x := by
  change ((enum σ).map f).getD (index σ x) default = _
  rw [map_get _ _ (index_lt hx),at_index hx]

theorem tabulate_mem (σ τ : Ty) (f : SVal → SVal)
    (typed : ∀ x, Member σ x → Member τ (f x))
    (mono : ∀ x y, Member σ x → Member σ y → Below σ x y → Below τ (f x) (f y)) :
    Member (.arr σ τ) (tabulate σ f) := by
  apply (mem_tab _ _ _).mpr
  refine ⟨by simp, ?_, ?_⟩
  · intro v hv
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    exact typed x hx
  · intro i hi j hj ord
    rw [map_get _ _ hi,map_get _ _ hj]
    exact mono _ _ (mem_getD hi) (mem_getD hj) ord

theorem tabulate_below (σ τ : Ty) {f g : SVal → SVal} (h : ∀ x, Member σ x → Below τ (f x) (g x)) :
    Below (.arr σ τ) (tabulate σ f) (tabulate σ g) := by
  apply (below_tabs _ _ _ _).mpr
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp,fun i hi _ => ?_⟩
  simpa using h ((enum σ)[i]'(by simpa using hi)) (List.getElem_mem _)

theorem app_mem {σ τ : Ty} {f x : SVal} (hf : Member (.arr σ τ) f) (hx : Member σ x) :
    Member τ (appT σ f x) := by
  cases f with
  | bit b => simp [Member,enum] at hf
  | tab l =>
    obtain ⟨len,hm,_⟩ := (mem_tab _ _ _).mp hf
    have hi : index σ x < l.length := len ▸ index_lt hx
    change Member τ (l.getD (index σ x) default)
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    exact hm _ (List.getElem_mem _)

theorem app_below {σ τ : Ty} {f g x y : SVal}
    (hf : Member (.arr σ τ) f) (hg : Member (.arr σ τ) g) (hx : Member σ x) (hy : Member σ y)
    (hfg : Below (.arr σ τ) f g) (hxy : Below σ x y) :
    Below τ (appT σ f x) (appT σ g y) := by
  cases f with
  | bit b => simp [Member,enum] at hf
  | tab l =>
    cases g with
    | bit b => simp [Member,enum] at hg
    | tab r =>
      obtain ⟨lr,_,mono⟩ := (mem_tab _ _ _).mp hg
      obtain ⟨ll,_⟩ := (mem_tab _ _ _).mp hf
      have h₁ := index_lt hx
      have h₂ := index_lt hy
      have z := mono _ h₁ _ h₂ (by simpa only [at_index hx,at_index hy] using hxy)
      apply below_trans τ _ z
      have ij := (List.forall₂_iff_get.mp ((below_tabs _ _ _ _).mp hfg)).2 (index σ x) (ll ▸ h₁) (lr ▸ h₁)
      change Below τ (l.getD (index σ x) default) (r.getD (index σ x) default)
      simpa only [List.get_eq_getElem, List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (ll ▸ h₁),
        List.getElem?_eq_getElem (lr ▸ h₁),Option.getD_some] using ij

theorem bot_mem (σ : Ty) : Member σ (botV σ) := by
  induction σ with
  | o => simp [Member,botV,enum]
  | arr σ τ _ h =>
    simpa [botV,tabulate] using tabulate_mem σ τ (fun _ => botV τ) (fun _ _ => h)
      (fun _ _ _ _ _ => below_refl τ h)

theorem one_mem (σ : Ty) : Member σ (oneV σ) := by
  induction σ with
  | o => simp [Member,oneV,enum]
  | arr σ τ _ h =>
    simpa [oneV,tabulate] using tabulate_mem σ τ (fun _ => oneV τ) (fun _ _ => h)
      (fun _ _ _ _ _ => below_refl τ h)

theorem bot_below (σ : Ty) {x : SVal} (hx : Member σ x) : Below σ (botV σ) x := by
  induction σ generalizing x with
  | o => simp [Member,enum] at hx; rcases hx with rfl | rfl <;> rfl
  | arr σ τ _ ih =>
    cases x with
    | bit b => simp [Member,enum] at hx
    | tab l =>
      obtain ⟨len,mem,_⟩ := (mem_tab _ _ _).mp hx
      apply (below_tabs _ _ _ _).mpr
      apply List.forall₂_iff_get.mpr
      refine ⟨by simp [len],fun i hi hj => ?_⟩
      simpa using ih (mem l[i] (List.getElem_mem hj))

end FiniteModel
end TreeEquivalenceHORS.Equivalence
namespace TreeEquivalenceHORS.Equivalence.FiniteModel

def Related (σ : Ty) (v w : SVal) := Member σ v ∧ Member σ w ∧ Below σ v w

structure Matches {α β : Type} [Inhabited α] [Inhabited β] (rel : Ty → α → β → Prop)
    (ts : List Ty) (a : List α) (b : List β) : Prop where
  left : a.length = ts.length
  right : b.length = ts.length
  atIdx : ∀ i σ, ts[i]? = some σ → rel σ (a.getD i default) (b.getD i default)

theorem matches_nil {α β : Type} [Inhabited α] [Inhabited β] (r : Ty → α → β → Prop) :
    Matches r [] [] [] := ⟨rfl,rfl,by simp⟩

theorem matches_snoc {α β : Type} [Inhabited α] [Inhabited β] {r : Ty → α → β → Prop}
    {ts : List Ty} {a : List α} {b : List β} {σ x y}
    (h : Matches r ts a b) (hr : r σ x y) : Matches r (ts ++ [σ]) (a ++ [x]) (b ++ [y]) := by
  refine ⟨by simp [h.left],by simp [h.right],?_⟩
  intro i τ ht
  by_cases hi : i < ts.length
  · rw [List.getElem?_append_left hi] at ht
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left (h.left ▸ hi),
      List.getElem?_append_left (h.right ▸ hi)] using h.atIdx i τ ht
  · have j : ts.length ≤ i := by omega
    rw [List.getElem?_append_right j] at ht
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (h.left ▸ j),
      List.getElem?_append_right (h.right ▸ j),h.left,h.right]
    cases hh : i-ts.length with
    | zero => simp [hh] at ht; subst τ; exact hr
    | succ k => simp [hh] at ht

abbrev Env := Matches Related

theorem Env.refl_left {ts a b} (h : Env ts a b) : Env ts a a :=
  ⟨h.left,h.left,fun i σ ht => by
    have v := (h.atIdx i σ ht).1
    exact ⟨v,v,below_refl σ v⟩⟩

theorem Env.refl_right {ts a b} (h : Env ts a b) : Env ts b b :=
  ⟨h.right,h.right,fun i σ ht => by
    have v := (h.atIdx i σ ht).2.1
    exact ⟨v,v,below_refl σ v⟩⟩

private theorem inv_app {G : HORS} {ctx : List Ty} {t u : Tm} {τ : Ty}
    (h : G.typeOf ctx (.app t u) = some τ) :
    ∃ σ, G.typeOf ctx t = some (.arr σ τ) ∧ G.typeOf ctx u = some σ := by
  simp only [HORS.typeOf] at h
  split at h <;> simp_all

theorem den_related {G : HORS} {ctx : List Ty} {η₁ η₂ ρ₁ ρ₂ : List SVal}
    (he : Env G.nts η₁ η₂) (hr : Env ctx ρ₁ ρ₂) (t : Tm) {τ : Ty}
    (ht : G.typeOf ctx t = some τ) :
    Related τ (G.den ctx η₁ ρ₁ t) (G.den ctx η₂ ρ₂ t) := by
  induction t generalizing τ with
  | var i => exact hr.atIdx i τ ht
  | nt i => exact he.atIdx i τ ht
  | tm c =>
    cases hc : G.alphabet[c]? with
    | none => simp [HORS.typeOf,hc] at ht
    | some r =>
      obtain rfl := (by simpa [HORS.typeOf,hc] using ht : termTy r = τ)
      simpa [HORS.den,hc] using (show Related (termTy r) (oneV (termTy r)) (oneV (termTy r)) from
        ⟨one_mem _,one_mem _,below_refl _ (one_mem _)⟩)
  | app t u it iu =>
    obtain ⟨σ,ht,hu⟩ := inv_app ht
    obtain ⟨l,r,lr⟩ := it ht
    obtain ⟨a,b,ab⟩ := iu hu
    simp only [HORS.den,hu]
    exact ⟨app_mem l a,app_mem r b,app_below l r a b lr ab⟩

theorem rule_related {G : HORS} {ctx : List Ty} {η₁ η₂ : List SVal} {body : Tm}
    (ht : G.typeOf ctx body = some .o) (he : Env G.nts η₁ η₂)
    (τ : Ty) (pre : List Ty) (hctx : ctx = pre ++ τ.args) {ρ₁ ρ₂ : List SVal}
    (hr : Env pre ρ₁ ρ₂) :
    Related τ (G.ruleTab ctx η₁ body τ ρ₁) (G.ruleTab ctx η₂ body τ ρ₂) := by
  induction τ generalizing pre η₁ η₂ ρ₁ ρ₂ with
  | o =>
    simp only [Ty.args,List.append_nil] at hctx
    subst ctx
    exact den_related he hr body ht
  | arr σ τ _ ih =>
    let left (x : SVal) := G.ruleTab ctx η₁ body τ (ρ₁ ++ [x])
    let right (x : SVal) := G.ruleTab ctx η₂ body τ (ρ₂ ++ [x])
    have ctx' : ctx = (pre ++ [σ]) ++ τ.args := by simpa [List.append_assoc,Ty.args] using hctx
    have cross {α β a b : List SVal} (e : Env G.nts α β) (r : Env pre a b) {x y : SVal} (xy : Related σ x y) :
        Related τ (G.ruleTab ctx α body τ (a ++ [x])) (G.ruleTab ctx β body τ (b ++ [y])) :=
      ih e _ ctx' (matches_snoc r xy)
    have self (x : SVal) (vx : Member σ x) : Related σ x x := ⟨vx,vx,below_refl σ vx⟩
    change Related (.arr σ τ) (tabulate σ left) (tabulate σ right)
    exact ⟨tabulate_mem σ τ left (fun x vx => (cross he hr (self x vx)).1)
      (fun _ _ vx vy xy => (cross he.refl_left hr.refl_left ⟨vx,vy,xy⟩).2.2),
      tabulate_mem σ τ right (fun x vx => (cross he hr (self x vx)).2.1)
      (fun _ _ vx vy xy => (cross he.refl_right hr.refl_right ⟨vx,vy,xy⟩).2.2),
      tabulate_below σ τ (fun x vx => (cross he hr (self x vx)).2.2)⟩

theorem rule_type {G : HORS} (v : G.Valid) (i : ℕ) (σ : Ty) (hi : G.nts[i]? = some σ) :
    G.typeOf σ.args (G.rules.getD i (.tm 0)) = some .o := by
  obtain ⟨hlt,_⟩ := List.getElem?_eq_some_iff.mp hi
  simp only [HORS.Valid,HORS.valid,Bool.and_eq_true,List.all_eq_true] at v
  have ok := v.2 i (List.mem_range.mpr hlt)
  cases hb : G.rules[i]? with
  | none => simp [HORS.ruleOK,hi,hb] at ok
  | some b => simpa [HORS.ruleOK,hi,hb,List.getD_eq_getElem?_getD] using ok

theorem phi_related {G : HORS} (v : G.Valid) {a b : List SVal} (h : Env G.nts a b) :
    Env G.nts (G.Phi a) (G.Phi b) := by
  refine ⟨by simp [HORS.Phi],by simp [HORS.Phi],?_⟩
  intro i σ hi
  obtain ⟨lt,eq⟩ := List.getElem?_eq_some_iff.mp hi
  have tab := rule_related (rule_type v i σ hi) h σ [] (by simp) (matches_nil Related)
  simpa [HORS.Phi,List.getD_eq_getElem?_getD,lt,hi,eq] using tab

theorem env_trans {ts a b c} (h : Env ts a b) (k : Env ts b c) : Env ts a c := by
  refine ⟨h.left,k.right,fun i σ hi => ?_⟩
  obtain ⟨va,_,le₁⟩ := h.atIdx i σ hi
  obtain ⟨_,vc,le₂⟩ := k.atIdx i σ hi
  exact ⟨va,vc,below_trans σ le₁ le₂⟩

theorem env_antisymm {ts a b} (h : Env ts a b) (k : Env ts b a) : a = b := by
  apply List.ext_get (h.left.trans h.right.symm)
  intro i ha hb
  have ht := h.left ▸ ha
  have hi := List.getElem?_eq_getElem ht
  have e := below_antisymm _ (h.atIdx i _ hi).2.2 (k.atIdx i _ hi).2.2
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb] using e

theorem initial_related (G : HORS) : Env G.nts G.eta0 G.eta0 := by
  refine ⟨by simp [HORS.eta0],by simp [HORS.eta0],fun i σ hi => ?_⟩
  simp [HORS.eta0,List.getD_eq_getElem?_getD,hi,Related,bot_mem,bot_below]

theorem initial_le {G : HORS} {a : List SVal} (h : Env G.nts a a) : Env G.nts G.eta0 a := by
  refine ⟨by simp [HORS.eta0],h.left,fun i σ hi => ?_⟩
  have hv := (h.atIdx i σ hi).1
  simpa [HORS.eta0,List.getD_eq_getElem?_getD,hi] using
    (show Related σ (botV σ) (a.getD i default) from ⟨bot_mem σ,hv,bot_below σ hv⟩)

def envs : List Ty → List (List SVal)
  | [] => [[]]
  | σ :: ts => (enum σ).flatMap fun x => (envs ts).map (x :: ·)

theorem envs_length (ts : List Ty) : (envs ts).length = (ts.map fun τ => (enum τ).length).prod := by
  induction ts with
  | nil => rfl
  | cons σ ts ih =>
    simp [envs, List.length_flatMap,ih]

theorem env_mem {ts e} (h : Env ts e e) : e ∈ envs ts := by
  induction ts generalizing e with
  | nil => have z := h.left; simp at z; simp [z,envs]
  | cons σ ts ih =>
    cases e with
    | nil => have z := h.left; simp at z
    | cons a e =>
      have head := (h.atIdx 0 σ (by simp)).1
      have tail : Env ts e e :=
        ⟨Nat.succ.inj h.left,Nat.succ.inj h.right,fun i τ hi => h.atIdx (i+1) τ hi⟩
      exact List.mem_flatMap.mpr ⟨a,head,List.mem_map.mpr ⟨e,ih tail,rfl⟩⟩

def stage (G : HORS) (n : ℕ) := G.Phi^[n] G.eta0

theorem stage_next (G : HORS) (n : ℕ) : stage G (n+1) = G.Phi (stage G n) := Function.iterate_succ_apply' _ _ _

theorem stage_related {G : HORS} (v : G.Valid) (n : ℕ) : Env G.nts (stage G n) (stage G (n+1)) := by
  induction n with
  | zero => exact initial_le (phi_related v (initial_related G))
  | succ n ih => simpa only [←stage_next] using phi_related v ih

end TreeEquivalenceHORS.Equivalence.FiniteModel
namespace TreeEquivalenceHORS.Equivalence
namespace NumericSemantics
open SyntaxCode SyntaxAlgorithm FiniteModel

def tableCode (xs : List ℕ) : ℕ := Encodable.encode xs + 2
def readTable (n : ℕ) : List ℕ := (Encodable.decode (n-2)).getD []

def raw : SVal → ℕ
  | .bit b => if b then 1 else 0
  | .tab xs => tableCode (xs.map raw)

@[simp] theorem raw_bit (b : Bool) : raw (.bit b) = (if b then 1 else 0) := by rw [raw]
@[simp] theorem raw_tab (xs : List SVal) : raw (.tab xs) = tableCode (xs.map raw) := by rw [raw]
@[simp] theorem read_table (l : List ℕ) : readTable (tableCode l) = l := by simp [readTable,tableCode,Encodable.encodek]

theorem pr_table : Primrec tableCode := Primrec.nat_add.comp Primrec.encode (Primrec.const 2)
theorem pr_readTable : Primrec readTable :=
  Primrec.option_getD.comp (Primrec.decode.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 2))) (Primrec.const [])

theorem getD_pr {α β : Type} [Primcodable α] [Primcodable β] {l : α → List β} {i : α → ℕ}
    (hl : Primrec l) (hi : Primrec i) (b : β) : Primrec (fun a => (l a).getD (i a) b) := by
  simp only [List.getD_eq_getElem?_getD]
  exact Primrec.option_getD.comp (Primrec.list_getElem?.comp hl hi) (Primrec.const b)

private theorem mem_lt_table (l : List ℕ) {v : ℕ} (hv : v ∈ l) : v < tableCode l := by
  have bound {l : List ℕ} (hv : v ∈ l) : v < Encodable.encode l := by
    induction l with
    | nil => simp at hv
    | cons a l ih =>
      rcases List.mem_cons.mp hv with rfl | h
      · simpa [Encodable.encode_list_cons] using Nat.lt_succ_of_le (Nat.left_le_pair v (Encodable.encode l))
      · exact (ih h).trans_le (by simpa using (Nat.right_le_pair a (Encodable.encode l)).trans (Nat.le_succ _))
  exact (bound hv).trans (by unfold tableCode; omega)

def cmpStep (n : ℕ) (hist : List ℕ) : ℕ :=
  let a := n.unpair.1
  let b := n.unpair.2
  let l := readTable a
  let r := readTable b
  let val := if a<2 then decide (a≤b) else l.length == r.length &&
    (List.range l.length).all fun i => hist.getD (Nat.pair (l.getD i 0) (r.getD i 0)) 0 == 1
  bif val then 1 else 0

private theorem pr_cmpStep : Primrec₂ cmpStep := by
  have p := Primrec.unpair.comp (Primrec.fst (α := ℕ) (β := List ℕ))
  have a := Primrec.fst.comp p
  have b := Primrec.snd.comp p
  have l := pr_readTable.comp a
  have r := pr_readTable.comp b
  have z := Primrec.fst (α := ℕ × List ℕ) (β := ℕ)
  have pos :=  Primrec₂.natPair.comp (getD_pr (l.comp z) Primrec.snd 0) (getD_pr (r.comp z) Primrec.snd 0)
  have good := Primrec.beq.comp (getD_pr (Primrec.snd.comp z) pos 0) (Primrec.const 1)
  have cmp := Primrec.and.comp (Primrec.beq.comp (Primrec.list_length.comp l) (Primrec.list_length.comp r))
    (prim_all (Primrec.list_range.comp (Primrec.list_length.comp l)) good.to₂)
  exact (Primrec.cond (Primrec.ite (Primrec.nat_lt.comp a (Primrec.const 2)) (Primrec.nat_le.comp a b).decide cmp)
    (Primrec.const 1) (Primrec.const 0)).to₂

def compareCode (x y : ℕ) := evaluate cmpStep (Nat.pair x y) == 1

theorem pr_cmp : Primrec₂ compareCode := by
  have h : Primrec (history cmpStep) := Primrec.nat_rec₁ [] (Primrec.list_concat.comp Primrec.snd pr_cmpStep).to₂
  exact (Primrec.beq.comp ((pr_cmpStep.comp Primrec.id h).comp Primrec₂.natPair) (Primrec.const 1)).to₂

private theorem history_eq (n : ℕ) : history cmpStep n = (List.range n).map (evaluate cmpStep) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history,List.range_succ,List.map_append,List.map_cons,List.map_nil]
    exact congrArg (· ++ [evaluate cmpStep n]) ih

private theorem lookup_cmp (x y n : ℕ) (h : Nat.pair x y < n) :
    ((history cmpStep n).getD (Nat.pair x y) 0 == 1) = compareCode x y := by
  simp [history_eq,compareCode,List.getD_eq_getElem?_getD,h]

theorem cmp_spec (σ : Ty) {x y : SVal} (hx : Member σ x) (hy : Member σ y) :
    compareCode (raw x) (raw y) = leT σ x y := by
  induction σ generalizing x y with
  | o =>
    simp [Member,enum] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [compareCode,evaluate,cmpStep,leT]
  | arr σ τ _ ih =>
    cases x with
    | bit => simp [Member,enum] at hx
    | tab l =>
      cases y with
      | bit => simp [Member,enum] at hy
      | tab r =>
        obtain ⟨ll,lmem,_⟩ := (mem_tab _ _ _).mp hx
        obtain ⟨rr,rmem,_⟩ := (mem_tab _ _ _).mp hy
        have lens : l.length = r.length := ll.trans rr.symm
        let a := tableCode (l.map raw)
        let b := tableCode (r.map raw)
        have large : ¬ a<2 := by dsimp [a,tableCode]; omega
        have atI (i : ℕ) (hi : i < l.length) :
            ((history cmpStep (Nat.pair a b)).getD (Nat.pair (raw l[i]) (raw (r[i]'(lens ▸ hi)))) 0 == 1) =
            leT τ l[i] (r[i]'(lens ▸ hi)) := by
          rw [lookup_cmp,ih (lmem _ (List.getElem_mem _)) (rmem _ (List.getElem_mem _))]
          exact (Nat.pair_lt_pair_left _ (mem_lt_table _ (List.mem_map_of_mem (f := raw) (List.getElem_mem hi)))).trans
            (Nat.pair_lt_pair_right _ (mem_lt_table _ (List.mem_map_of_mem (f := raw) (List.getElem_mem (lens ▸ hi)))))
        simp only [raw_tab]
        apply Bool.eq_iff_iff.mpr
        change (cmpStep (Nat.pair a b) (history cmpStep (Nat.pair a b)) == 1) = true ↔ _
        rw [show leT (.arr σ τ) (.tab l) (.tab r) = true ↔ _ from below_tabs σ τ l r,List.forall₂_iff_get]
        simp only [cmpStep,Nat.unpair_pair,large,if_false,show readTable a = l.map raw from read_table _,
          show readTable b = r.map raw from read_table _,List.length_map,show (l.length == r.length) = true by simp [lens],Bool.true_and]
        have truth (p : Bool) : ((bif p then 1 else 0 : ℕ) == 1) = true ↔ p = true := by cases p <;> decide
        rw [truth,List.all_eq_true]
        constructor
        · intro all'
          refine ⟨lens,fun i hi hj => ?_⟩
          have yes := all' i (List.mem_range.mpr hi)
          exact (atI i hi).symm.trans (by simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using yes)
        · rintro ⟨_,all'⟩ i h
          have hi := List.mem_range.mp h
          have hj : i < r.length := lens ▸ hi
          have z := (atI i hi).trans (all' i hi hj)
          simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using z

attribute [local instance] syntaxTyPrimcodable syntaxTmPrimcodable syntaxHORSPrimcodable

theorem pr_tuples {α : Type} [Primcodable α] :
    Primrec₂ (fun (l : List α) n => tuples n l) := by
  apply (Primrec.nat_rec (Primrec.const [[]]) (Primrec.list_flatMap Primrec.fst
    (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂).to₂).of_eq
  intro l n; induction n <;> simp [tuples, *]

theorem tuples_map {α β : Type} (f : α → β) (n : ℕ) (l : List α) :
    tuples n (l.map f) = (tuples n l).map (List.map f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tuples,ih,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]

def monotoneRow (ds row : List ℕ) : Bool :=
  (List.range ds.length).all fun i => (List.range ds.length).all fun j =>
    !compareCode (ds.getD i 0) (ds.getD j 0) || compareCode (row.getD i 0) (row.getD j 0)

theorem pr_monotone : Primrec₂ monotoneRow := by
  have ds := Primrec.fst (α := List ℕ) (β := List ℕ)
  have row := Primrec.snd (α := List ℕ) (β := List ℕ)
  have ran := Primrec.list_range.comp (Primrec.list_length.comp ds)
  have p := Primrec.fst (α := (List ℕ × List ℕ) × ℕ) (β := ℕ)
  have i := Primrec.snd.comp p
  have env := Primrec.fst.comp p
  have cmp (l : List ℕ × List ℕ → List ℕ) (c : Primrec l) :=
    pr_cmp.comp (getD_pr (c.comp env) i 0) (getD_pr (c.comp env) Primrec.snd 0)
  exact (prim_all ran (prim_all (ran.comp Primrec.fst)
    (Primrec.or.comp (Primrec.not.comp (cmp _ ds)) (cmp _ row)).to₂).to₂).to₂

def arrowEnum (ds ts : List ℕ) := ((tuples ds.length ts).filter (monotoneRow ds)).map tableCode

private theorem pr_arrowEnum : Primrec₂ arrowEnum := by
  have rs := (pr_tuples (α := ℕ)).comp (Primrec.snd (α := List ℕ)) (Primrec.list_length.comp Primrec.fst)
  have row := Primrec.listFilterMap rs (Primrec.to₂ (Primrec.cond
    (pr_monotone.comp (Primrec.fst.comp Primrec.fst) Primrec.snd) (Primrec.option_some.comp Primrec.snd) (Primrec.const none)))
  apply (Primrec.list_map row (pr_table.comp Primrec.snd).to₂).to₂.of_eq
  intro d t
  rw [arrowEnum,←List.filterMap_eq_filter]
  simp [Bool.cond_eq_ite,Option.guard]

def domain (σ : Ty) := (enum σ).map raw

private theorem map_get {α β : Type} (f : α → β) (l : List α) (i : ℕ) (hi : i < l.length)
    (a : α) (b : β) : (l.map f).getD i b = f (l.getD i a) := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]

theorem all_congr_mem {α : Type} (l : List α) {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [h x (by simp),ih (fun a ha => h a (.tail _ ha))]

private theorem domain_arr (σ τ : Ty) : domain (.arr σ τ) = arrowEnum (domain σ) (domain τ) := by
  unfold domain arrowEnum
  simp only [enum,List.map_map,Function.comp_def,raw_tab,List.length_map,tuples_map,
    List.filter_map,List.map_map,Function.comp_def]
  congr 1
  apply List.filter_congr
  intro l hl
  obtain ⟨len,ml⟩ := (mem_tuples _ _ _).mp hl
  unfold monotoneRow
  simp only [List.length_map]
  apply all_congr_mem
  intro i hi
  have hi := List.mem_range.mp hi
  apply all_congr_mem
  intro j hj
  have hj := List.mem_range.mp hj
  have v (n : ℕ) (h : n < l.length) : Member τ (l.getD n default) := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
    exact ml _ (List.getElem_mem _)
  simp only [map_get raw _ _ hi default,map_get raw _ _ hj default,
    map_get raw _ _ (len ▸ hi) default,map_get raw _ _ (len ▸ hj) default,
    cmp_spec σ (mem_getD hi) (mem_getD hj),cmp_spec τ (v _ (len ▸ hi)) (v _ (len ▸ hj))]

theorem pr_domain : Primrec domain := prim_ty_fold (domain .o) arrowEnum pr_arrowEnum rfl domain_arr

theorem pr_ty_with {β : Type} [Primcodable β] {f : Ty → β} (b : β)
    (g : (Ty × β) → (Ty × β) → β) (p : Primrec₂ g) (ho : f .o = b)
    (ha : ∀ σ τ, f (.arr σ τ) = g (σ,f σ) (τ,f τ)) : Primrec f := by
  have h : Primrec (fun t : Ty => (t,f t)) := prim_ty_fold (.o,b)
    (fun l r => (l.1.arr r.1,g l r)) ((prim_arr.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).pair p).to₂ (by simp [ho]) (by intros; simp [ha])
  exact Primrec.snd.comp h

private theorem pr_replicate {α : Type} [Primcodable α] : Primrec₂ (fun (n : ℕ) (x : α) => List.replicate n x) := by
  simpa using (Primrec.list_map (Primrec.list_range.comp (Primrec.fst (β := α))) (Primrec.snd.comp Primrec.fst).to₂).to₂

theorem pr_rawOne : Primrec (fun σ => raw (oneV σ)) := by
  apply pr_ty_with 1 (fun a b => tableCode (List.replicate (domain a.1).length b.2))
    (pr_table.comp (pr_replicate.comp (Primrec.list_length.comp (pr_domain.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd))).to₂
  · simp [oneV]
  · intro σ τ; simp [oneV,domain]

theorem pr_rawBot : Primrec (fun σ => raw (botV σ)) := by
  apply pr_ty_with 0 (fun a b => tableCode (List.replicate (domain a.1).length b.2))
    (pr_table.comp (pr_replicate.comp (Primrec.list_length.comp (pr_domain.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd))).to₂
  · simp [botV]
  · intro σ τ; simp [botV,domain]

def numericIndex (σ : Ty) (x : ℕ) := (domain σ).findIdx fun y => compareCode x y && compareCode y x

theorem pr_index : Primrec₂ numericIndex := by
  have x := Primrec.snd.comp (Primrec.fst (α := Ty × ℕ) (β := ℕ))
  exact (Primrec.list_findIdx (pr_domain.comp Primrec.fst)
    ((Primrec.and.comp (pr_cmp.comp x Primrec.snd) (pr_cmp.comp Primrec.snd x)).to₂)).to₂

private theorem find_congr {α : Type} (l : List α) {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.findIdx p = l.findIdx q := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.findIdx_cons,h x (by simp),ih (fun a ha => h a (.tail _ ha))]

theorem index_spec (σ : Ty) {x : SVal} (hx : Member σ x) : numericIndex σ (raw x) = index σ x := by
  simp only [numericIndex,domain,List.findIdx_map,index]
  exact find_congr _ (fun y hy => by simp only [Function.comp_apply,cmp_spec σ hx hy,cmp_spec σ hy hx])

def numericApp (z : Ty × ℕ × ℕ) := (readTable z.2.1).getD (numericIndex z.1 z.2.2) 0

theorem pr_app : Primrec numericApp := getD_pr (pr_readTable.comp (Primrec.fst.comp Primrec.snd))
  (pr_index.comp Primrec.fst (Primrec.snd.comp Primrec.snd)) 0

theorem app_spec {σ τ : Ty} {f x : SVal} (hf : Member (.arr σ τ) f) (hx : Member σ x) :
    numericApp (σ,raw f,raw x) = raw (appT σ f x) := by
  cases f with
  | bit b => simp [Member,enum] at hf
  | tab l =>
    obtain ⟨len,_,_⟩ := (mem_tab _ _ _).mp hf
    simp only [numericApp,raw_tab,read_table,index_spec σ hx]
    exact map_get raw l _ (len ▸ index_lt hx) default 0

end NumericSemantics
end TreeEquivalenceHORS.Equivalence
namespace TreeEquivalenceHORS.Equivalence.NumericSemantics
open SyntaxAlgorithm

def words : List (List ℕ) → List (List ℕ)
  | [] => [[]]
  | xs :: ds => xs.flatMap fun x => (words ds).map (x :: ·)

def layout : List (List ℕ) → List (ℕ × ℕ)
  | [] => []
  | xs :: ds => (1,xs.length) :: (layout ds).map fun (p,n) => (xs.length*p,n)

def scale (c : ℕ) (shape : List (ℕ × ℕ)) := shape.map fun (p,n) => (c*p,n)

def pack (cn : ℕ × ℕ) (a : List ℕ) :=
  (List.range cn.1).map fun i => tableCode ((a.drop (i*cn.2)).take cn.2)

def curried (f : List ℕ → ℕ) : List (List ℕ) → List ℕ → ℕ
  | [], pre => f pre
  | xs :: ds,pre => tableCode (xs.map (fun x => curried f ds (pre ++ [x])))

theorem pr_words : Primrec words := by
  apply (Primrec.list_foldr Primrec.id (Primrec.const [[]]) (Primrec.list_flatMap (Primrec.fst.comp Primrec.snd)
    (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂).to₂).of_eq
  intro ds; induction ds with
  | nil => rfl
  | cons d ds ih => dsimp at ih ⊢; simp [words,ih]

theorem pr_layout : Primrec layout := by
  have step : Primrec (fun z : List ℕ × List (ℕ × ℕ) => (1,z.1.length) :: z.2.map fun p => (z.1.length*p.1,p.2)) :=
    Primrec.list_cons.comp ((Primrec.const 1).pair (Primrec.list_length.comp Primrec.fst))
      (Primrec.list_map Primrec.snd ((Primrec.nat_mul.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)).to₂)
  apply (Primrec.list_foldr Primrec.id (Primrec.const []) (step.comp Primrec.snd).to₂).of_eq
  intro ds; induction ds with
  | nil => rfl
  | cons d ds ih => dsimp at ih ⊢; simp [layout,ih]

theorem pr_pack : Primrec₂ pack := by
  have z := Primrec.fst (α := (ℕ × ℕ) × List ℕ) (β := ℕ)
  have n := Primrec.snd.comp (Primrec.fst.comp z)
  have start := Primrec.nat_mul.comp Primrec.snd n
  exact (Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)) (pr_table.comp
    (Primrec.list_take.comp n (Primrec.list_drop.comp start (Primrec.snd.comp z)))).to₂).to₂

private theorem pack_flat (n : ℕ) (ls : List (List ℕ)) (lens : ∀ l ∈ ls, l.length = n) :
    pack (ls.length,n) ls.flatten = ls.map tableCode := by
  apply List.ext_getElem
  · simp [pack]
  · intro i hi hj
    have lt : i < ls.length := by simpa using hj
    simp only [pack,List.getElem_map,List.getElem_range]
    congr 1
    induction ls generalizing i with
    | nil => simp at lt
    | cons l ls ih =>
      have hl := lens l (by simp)
      have ht (v) (h : v ∈ ls) := lens v (.tail _ h)
      cases i with
      | zero => simp only [Nat.zero_mul,List.drop_zero,List.flatten_cons,List.getElem_cons_zero,←hl,List.take_append_of_le_length (Nat.le_refl _),List.take_length]
      | succ i =>
        simp only [List.flatten_cons, List.getElem_cons_succ,Nat.succ_mul]
        rw [show i*n+n=l.length+i*n by omega,List.drop_length_add_append]
        simpa [hl] using ih ht i (by simpa [pack] using (show i < ls.length from Nat.lt_of_succ_lt_succ lt))
          (by simpa using (show i < ls.length from Nat.lt_of_succ_lt_succ lt)) (Nat.lt_of_succ_lt_succ lt)

private theorem fold_layout (f : List ℕ → ℕ) (ds front : List (List ℕ)) :
    (scale front.length (layout ds)).foldr pack
      ((front.flatMap fun p => (words ds).map (p ++ ·)).map f) =
    front.map (curried f ds) := by
  induction ds generalizing front with
  | nil => simp [scale,layout,words,curried]
  | cons xs ds ih =>
    let next := front.flatMap fun p => xs.map fun x => p ++ [x]
    have len : next.length = front.length*xs.length := by simp [next,List.length_flatMap]
    have dims : scale front.length (layout (xs::ds)) = (front.length,xs.length) :: scale next.length (layout ds) := by
      simp [layout,scale,len,List.map_map,Function.comp_def,Nat.mul_assoc]
    have flatten : (front.flatMap fun p => (words (xs::ds)).map (p ++ ·)) =
        (next.flatMap fun p => (words ds).map (p ++ ·)) := by
      simp [words,next,List.map_flatMap,List.flatMap_assoc,List.flatMap_map,List.map_map,Function.comp_def,List.append_assoc]
    rw [dims,List.foldr_cons,flatten,ih]
    let rows := front.map fun p => xs.map fun x => curried f ds (p ++ [x])
    have count : rows.length = front.length := by simp [rows]
    have dataEq : next.map (curried f ds) = rows.flatten := by
      simp [next,rows,List.map_flatMap,List.map_map,Function.comp_def,List.flatMap_def]
    rw [dataEq,←count,pack_flat]
    · simp [rows,curried,List.map_map,Function.comp_def]
    · intro l hl; obtain ⟨p,_,rfl⟩ := List.mem_map.mp hl; simp

theorem prim_curried {α : Type} [Primcodable α] {f : α → List ℕ → ℕ} (pf : Primrec₂ f)
    {ds : α → List (List ℕ)} (pd : Primrec ds) : Primrec fun a => curried (f a) (ds a) [] := by
  have h := Primrec.list_foldr (pr_layout.comp pd) (Primrec.list_map (pr_words.comp pd) pf) (pr_pack.comp
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply (getD_pr h (Primrec.const 0) 0).of_eq
  intro a
  have e := fold_layout (f a) (ds a) [[]]
  simp [scale] at e
  change (List.foldr pack _ _).getD 0 0 = _
  rw [e]; rfl

end TreeEquivalenceHORS.Equivalence.NumericSemantics
namespace TreeEquivalenceHORS.Equivalence.NumericSemantics
open SyntaxAlgorithm SyntaxCode FiniteModel
attribute [local instance] syntaxTyPrimcodable syntaxTmPrimcodable syntaxHORSPrimcodable
abbrev DenInput := HORS × List Ty × List ℕ × List ℕ

def denRaw (G : HORS) (ctx : List Ty) (η ρ : List ℕ) : Tm → ℕ
  | .var i => ρ.getD i 0
  | .nt i => η.getD i 0
  | .tm c => ((G.alphabet[c]?).map (fun n => raw (oneV (termTy n)))).getD 0
  | .app t u => ((G.typeOf ctx u).map fun σ => numericApp (σ,denRaw G ctx η ρ t,denRaw G ctx η ρ u)).getD 0

theorem prim_tm_app : Primrec₂ Tm.app := by
  have h := Primrec.option_getD.comp (Primrec.decode.comp
    ((pr_binary 3).comp ((Primrec.encode (α := Tm)).comp (Primrec.fst (β := Tm))) ((Primrec.encode (α := Tm)).comp Primrec.snd))) (Primrec.const (Tm.tm 0))
  exact h.to₂.of_eq fun x y => by
    change ((Encodable.decode (binary 3 (Encodable.encode x) (Encodable.encode y))) : Option Tm).getD _ = _
    rw [←enc_app,Encodable.encodek]; rfl

theorem pr_denRaw : Primrec₂ (fun (a : DenInput) t => denRaw a.1 a.2.1 a.2.2.1 a.2.2.2 t) := by
  let leaf (k i : ℕ) := if k=0 then Tm.var i else if k=1 then Tm.nt i else Tm.tm i
  let leafVal (k : ℕ) (a : DenInput) (i : ℕ) := (leaf k i,denRaw a.1 a.2.1 a.2.2.1 a.2.2.2 (leaf k i))
  have pl (k : ℕ) : Primrec₂ (leafVal k) := by
    have a := Primrec.fst (α := DenInput) (β := ℕ)
    have ts := Primrec.snd.comp (Primrec.snd.comp a)
    by_cases k0 : k=0
    · simpa [leafVal,leaf,k0,denRaw] using (((prim_constructor 0 _ enc_var).comp Primrec.snd).pair
        (getD_pr (Primrec.snd.comp ts) Primrec.snd 0)).to₂
    by_cases k1 : k=1
    · simpa [leafVal,leaf,k0,k1,denRaw] using (((prim_constructor 1 _ enc_nt).comp Primrec.snd).pair
        (getD_pr (Primrec.fst.comp ts) Primrec.snd 0)).to₂
    · have tab := Primrec.list_getElem?.comp (prim_alphabet.comp (Primrec.fst.comp a)) Primrec.snd
      simpa [leafVal,leaf,k0,k1,denRaw] using (((prim_constructor 2 _ enc_tm).comp Primrec.snd).pair
        (Primrec.option_getD.comp ((Primrec.option_map₁ (pr_rawOne.comp prim_termTy)).comp tab) (Primrec.const 0))).to₂
  let combine (a : DenInput) (p : (Tm × ℕ) × (Tm × ℕ)) :=
    (p.1.1.app p.2.1, ((a.1.typeOf a.2.1 p.2.1).map fun σ => numericApp (σ,p.1.2,p.2.2)).getD 0)
  have pc : Primrec₂ combine := by
    have a := Primrec.fst (α := DenInput) (β := (Tm × ℕ) × (Tm × ℕ))
    have ctx := (Primrec.fst.comp a).pair (Primrec.fst.comp (Primrec.snd.comp a))
    have l := Primrec.fst.comp (Primrec.snd (α := DenInput) (β := (Tm × ℕ) × (Tm × ℕ)))
    have r := Primrec.snd.comp (Primrec.snd (α := DenInput) (β := (Tm × ℕ) × (Tm × ℕ)))
    have ty := prim_typeOf.comp ctx (Primrec.fst.comp r)
    have val := pr_app.comp (Primrec.snd.pair (((Primrec.snd.comp l).comp Primrec.fst).pair ((Primrec.snd.comp r).comp Primrec.fst)))
    exact ((prim_tm_app.comp (Primrec.fst.comp l) (Primrec.fst.comp r)).pair
      (Primrec.option_getD.comp (Primrec.option_map ty val.to₂) (Primrec.const 0))).to₂
  have pair : Primrec₂ (fun (a : DenInput) t => (t,denRaw a.1 a.2.1 a.2.2.1 a.2.2.2 t)) :=
    prim_tm_fold (.tm 0,0) leafVal combine pl pc (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
  exact (Primrec.snd.comp pair).to₂

theorem den_spec {G : HORS} {η ρ : List SVal} {ctx : List Ty} (ge : Env G.nts η η) (lo : Env ctx ρ ρ)
    (t : Tm) {τ : Ty} (ht : G.typeOf ctx t = some τ) :
    denRaw G ctx (η.map raw) (ρ.map raw) t = raw (G.den ctx η ρ t) := by
  induction t generalizing τ with
  | var i =>
    change ctx[i]? = some τ at ht
    have hi : i < ρ.length := lo.left ▸ (List.getElem?_eq_some_iff.mp ht).choose
    simp [denRaw,HORS.den,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
  | nt F =>
    change G.nts[F]? = some τ at ht
    have hi : F < η.length := ge.left ▸ (List.getElem?_eq_some_iff.mp ht).choose
    simp [denRaw,HORS.den,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
  | tm c =>
    cases h : G.alphabet[c]? with
    | none => simp [HORS.typeOf,h] at ht
    | some r => simp [denRaw,HORS.den,h]
  | app t u it iu =>
    obtain ⟨σ,ht,hu⟩ := (by unfold HORS.typeOf at ht; split at ht <;> simp_all :
      ∃ σ, G.typeOf ctx t = some (.arr σ τ) ∧ G.typeOf ctx u = some σ)
    simp [denRaw,HORS.den,hu,it ht,iu hu,app_spec (den_related ge lo t ht).1 (den_related ge lo u hu).1]

end TreeEquivalenceHORS.Equivalence.NumericSemantics
namespace TreeEquivalenceHORS.Equivalence.NumericSemantics
open SyntaxAlgorithm FiniteModel
attribute [local instance] syntaxTyPrimcodable syntaxTmPrimcodable syntaxHORSPrimcodable

abbrev RuleInput := HORS × Ty × Tm × List ℕ

def ruleRaw (p : RuleInput) :=
  curried (fun ρ => denRaw p.1 p.2.1.args p.2.2.2 ρ p.2.2.1) (p.2.1.args.map domain) []

theorem pr_ruleRaw : Primrec ruleRaw := by
  have ty := Primrec.fst.comp (Primrec.snd (α := HORS) (β := Ty × Tm × List ℕ))
  have args := prim_args.comp ty
  have d := Primrec.list_map args (pr_domain.comp Primrec.snd).to₂
  have z := Primrec.fst (α := RuleInput) (β := List ℕ)
  have ctx := (Primrec.fst.comp z).pair ((args.comp z).pair
    (((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp z).pair Primrec.snd))
  exact prim_curried (pr_denRaw.comp ctx ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp z)).to₂ d

private theorem curry_rule_spec {G : HORS} {ctx : List Ty} {body : Tm} {η : List SVal}
    (ge : Env G.nts η η) (typed : G.typeOf ctx body = some .o) (τ : Ty)
    (pre : List Ty) (hctx : ctx = pre ++ τ.args) (ρ : List SVal) (lo : Env pre ρ ρ) :
    curried (fun a => denRaw G ctx (η.map raw) a body) (τ.args.map domain) (ρ.map raw) =
    raw (G.ruleTab ctx η body τ ρ) := by
  induction τ generalizing pre ρ with
  | o => simp only [Ty.args,List.append_nil] at hctx; subst ctx; exact den_spec ge lo body typed
  | arr σ τ _ ih =>
    simp only [Ty.args,List.map_cons,curried,HORS.ruleTab,raw_tab,domain,List.map_map, Function.comp_def]
    apply congrArg tableCode
    apply List.map_congr_left
    intro x hx
    have m : Member σ x := hx
    have z := ih (pre ++ [σ]) (by simpa [Ty.args,List.append_assoc] using hctx) (ρ ++ [x])
      (matches_snoc lo (show Related σ x x from ⟨m,m,below_refl σ m⟩))
    simpa using z

def phiRaw (G : HORS) (η : List ℕ) :=
  (List.range G.nts.length).map fun i => ruleRaw (G,G.nts.getD i .o,G.rules.getD i (.tm 0),η)

theorem pr_phiRaw : Primrec₂ phiRaw := by
  have g := Primrec.fst (α := HORS) (β := List ℕ)
  have z := Primrec.fst (α := HORS × List ℕ) (β := ℕ)
  have t := getD_pr ((prim_nts.comp g).comp z) Primrec.snd Ty.o
  have r := getD_pr ((prim_rules.comp g).comp z) Primrec.snd (Tm.tm 0)
  exact (Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp (prim_nts.comp g)))
    (pr_ruleRaw.comp ((g.comp z).pair (t.pair (r.pair (Primrec.snd.comp z))))).to₂).to₂

theorem phi_spec {G : HORS} (vg : G.Valid) {η : List SVal} (ge : Env G.nts η η) :
    phiRaw G (η.map raw) = (G.Phi η).map raw := by
  simp only [phiRaw,HORS.Phi,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i hi
  have hlt := List.mem_range.mp hi
  have ht := List.getElem?_eq_getElem hlt
  simp only [List.getD_eq_getElem?_getD,ht,Option.getD_some,ruleRaw]
  exact curry_rule_spec ge (rule_type vg i _ ht) _ [] (by simp) [] (matches_nil _)

def sizeRaw (G : HORS) := (G.nts.map (fun τ => (domain τ).length)).prod

theorem pr_sizeRaw : Primrec sizeRaw := Primrec.list_foldr
  (Primrec.list_map prim_nts ((Primrec.list_length.comp pr_domain).comp Primrec.snd).to₂)
  (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

def bottomRaw (G : HORS) := G.nts.map (fun τ => raw (botV τ))
theorem pr_bottomRaw : Primrec bottomRaw := Primrec.list_map prim_nts (pr_rawBot.comp Primrec.snd).to₂

def finalRaw (G : HORS) := (phiRaw G)^[sizeRaw G] (bottomRaw G)
theorem pr_final : Primrec finalRaw := by
  apply (Primrec.nat_rec' pr_sizeRaw pr_bottomRaw (pr_phiRaw.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro G
  change Nat.rec _ _ (sizeRaw G) = (phiRaw G)^[sizeRaw G] _
  generalize sizeRaw G = k
  induction k with
  | zero => rfl
  | succ k ih => simpa [Function.iterate_succ_apply',ih]

theorem final_spec {G : HORS} (vg : G.Valid) : finalRaw G = G.etaStar.map raw := by
  have nEq : sizeRaw G = G.envCard := by simp [sizeRaw,HORS.envCard,domain]
  have aux (n : ℕ) : (phiRaw G)^[n] (bottomRaw G) = (stage G n).map raw := by
    induction n with
    | zero => simp [bottomRaw,stage,HORS.eta0,List.map_map,Function.comp_def]
    | succ n ih => rw [Function.iterate_succ_apply',stage_next,ih,phi_spec vg (stage_related vg n).refl_left]
  simpa [finalRaw,HORS.etaStar,stage,nEq] using aux (sizeRaw G)

theorem raw_true_iff (v : SVal) : raw v = 1 ↔ v = .bit true := by
  cases v with
  | bit b => cases b <;> simp
  | tab l => simp [tableCode]

end TreeEquivalenceHORS.Equivalence.NumericSemantics

namespace TreeEquivalenceHORS.Equivalence
open NumericSemantics FiniteModel
attribute [local instance] syntaxTyPrimcodable syntaxTmPrimcodable syntaxHORSPrimcodable


private theorem proved_here :
    ∃ b : ℕ × ℕ → Bool, Computable b ∧ ∀ (G : HORS) (t : Tm), G.Valid → G.typeOf [] t = some .o →
      (b (Encodable.encode G, Encodable.encode t) = true ↔ G.den [] G.etaStar [] t = .bit true) := by
  let scheme (z : ℕ × ℕ) := (Encodable.decode z.1 : Option HORS).getD ⟨[],[],[],0⟩
  let term (z : ℕ × ℕ) := (Encodable.decode z.2 : Option Tm).getD (.tm 0)
  have g : Primrec scheme := Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const _)
  have t : Primrec term := Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const _)
  have data := g.pair ((Primrec.const ([] : List Ty)).pair ((pr_final.comp g).pair (Primrec.const ([] : List ℕ))))
  refine ⟨fun z => denRaw (scheme z) [] (finalRaw (scheme z)) [] (term z) == 1,
    (Primrec.beq.comp (pr_denRaw.comp data t) (Primrec.const 1)).to_comp,?_⟩
  intro G t vg ht
  simp only [scheme,term,Encodable.encodek,Option.getD_some,beq_iff_eq,final_spec vg]
  exact (den_spec (stage_related vg G.envCard).refl_left (matches_nil _) t ht) ▸ raw_true_iff _


end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution :
    ∃ b : ℕ × ℕ → Bool, Computable b ∧ ∀ (G : HORS) (t : Tm), G.Valid → G.typeOf [] t = some .o →
      (b (Encodable.encode G, Encodable.encode t) = true ↔ G.den [] G.etaStar [] t = .bit true) := proved_here
