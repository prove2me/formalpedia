-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.theorem_5_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T18:11:38.083756+00:00
-- url     : https://prove2.me/submissions/99d9b71c-d969-4791-b6a7-ede6fdd9a715

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_1
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_2
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_7
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_halts_iff_compiled_observations

namespace TreeEquivalenceHORS.Equivalence

-- Derived encodings store constructor tags and fields as finite trees of naturals.
private def atom (n : ℕ) := Nat.pair 0 n
private def cell (x y : ℕ) := Nat.pair (x+1) y
private def tag (n args : ℕ) := cell (atom n) args

private theorem encode_incA : Encodable.encode Instr.incA = tag 0 (atom 0) := rfl
private theorem encode_incB : Encodable.encode Instr.incB = tag 1 (atom 0) := rfl
private theorem encode_decB (n : ℕ) : Encodable.encode (Instr.decB n) = tag 3 (cell (atom n) (atom 0)) := rfl
private theorem encode_decA (n : ℕ) : Encodable.encode (Instr.decA n) = tag 2 (cell (atom n) (atom 0)) := rfl

private def ExactCodes (α : Type) [Encodable α] : Prop :=
  ∀ n (a : α), Encodable.decode n = some a → Encodable.encode a = n

private theorem exactEquivNat {α : Type} (e : α ≃ ℕ) :
    @ExactCodes α (Encodable.ofEquiv ℕ e) := by
  intro n a h
  change (some (e.symm n)) = some a at h
  exact (Option.some.inj h) ▸ e.apply_symm_apply n

private theorem exactLeftInjection {α β : Type} [Encodable α]
    (f : β → α) (g : α → Option β) (h : ∀ x, g (f x) = some x)
    (hα : ExactCodes α) (hg : ∀ x y, g x = some y → f y = x) :
    @ExactCodes β (Encodable.ofLeftInjection f g h) := by
  intro n b hb
  change (Encodable.decode n).bind g = some b at hb
  obtain ⟨x, hx, hxb⟩ := Option.bind_eq_some_iff.mp hb
  change Encodable.encode (f b) = n
  rw [hg x b hxb, hα n x hx]

private theorem exactInstr : ExactCodes Instr := by
  apply exactLeftInjection
  · apply exactEquivNat
  · intro x y h
    conv at h => lhs; whnf
    split at h <;> simp_all <;> subst_vars <;> rfl

private def tagOf (n : ℕ) : ℕ := n.unpair.1.pred.unpair.2
private def argOf (n : ℕ) : ℕ := n.unpair.2.unpair.1.pred.unpair.2

private def candidate (n : ℕ) : Instr :=
  if tagOf n = 0 then .incA else if tagOf n = 1 then .incB else
    if tagOf n = 2 then .decA (argOf n) else .decB (argOf n)

private theorem candidate_encode (i : Instr) : candidate (Encodable.encode i) = i := by
  cases i <;> simp [candidate, tagOf, argOf, encode_incA, encode_incB, encode_decA, encode_decB, tag, cell, atom]

private theorem pr_atom : Primrec atom := Primrec₂.natPair.comp (Primrec.const 0) Primrec.id
private theorem pr_cell : Primrec₂ cell := Primrec₂.natPair.comp₂ (Primrec.succ.comp Primrec.fst).to₂ Primrec₂.right
private theorem pr_tag : Primrec₂ tag := pr_cell.comp₂ (pr_atom.comp Primrec.fst).to₂ Primrec₂.right

private theorem pr_tagOf : Primrec tagOf :=
  Primrec.snd.comp <| Primrec.unpair.comp <| Primrec.pred.comp <| Primrec.fst.comp Primrec.unpair
private theorem pr_argOf : Primrec argOf := pr_tagOf.comp (Primrec.snd.comp Primrec.unpair)

private theorem pr_candidate_code : Primrec fun n => Encodable.encode (candidate n) := by
  have dec (tagN : ℕ) : Primrec fun n => tag tagN (cell (atom (argOf n)) (atom 0)) :=
    pr_tag.comp (Primrec.const _) (pr_cell.comp (pr_atom.comp pr_argOf) (Primrec.const _))
  have test (k : ℕ) : PrimrecPred fun n => tagOf n = k := Primrec.eq.comp pr_tagOf (Primrec.const k)
  simp only [candidate, apply_ite Encodable.encode, encode_decA, encode_decB]
  exact Primrec.ite (test 0) (Primrec.const _) (Primrec.ite (test 1) (Primrec.const _)
    (Primrec.ite (test 2) (dec 2) (dec 3)))

private instance primInstr : Primcodable Instr where
  prim := Primrec.nat_iff.mp <| (Primrec.ite (Primrec.eq.comp pr_candidate_code Primrec.id)
    Primrec.succ (Primrec.const 0)).of_eq fun n => by
      simp only [id_eq]
      by_cases h : Encodable.encode (candidate n) = n
      · rw [if_pos h]
        conv_rhs => arg 1; rw [← h, Encodable.encodek]
        simp [h]
      · rw [if_neg h]
        cases hd : (Encodable.decode n : Option Instr) with
        | none => rfl
        | some i =>
          have he := exactInstr n i hd
          exact (h (by rw [← he, candidate_encode])).elim

private theorem pr_lookup : Primrec₂ Machine.lookup := by
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const none)
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))

private theorem pr_norm : Primrec₂ Machine.norm := by
  apply Primrec.ite _ Primrec.snd (Primrec.const 0)
  exact (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd).and
    (Primrec.nat_le.comp Primrec.snd (Primrec.list_length.comp Primrec.fst))

private theorem pr_iF : Primrec iF := Primrec.nat_add.comp (Primrec.const 13) Primrec.id

/-- The control templates use control index 2 for fallthrough and index 1 for the jump. -/
private def patchControl (fall jump : ℕ) : Tm → Tm
  | .nt k => .nt (if k = iF 2 then fall else if k = iF 1 then jump else k)
  | .app t u => .app (patchControl fall jump t) (patchControl fall jump u)
  | t => t

private theorem pr_patched {α : Type} [Primcodable α] (t : Tm) {fall jump : α → ℕ}
    (hf : Primrec fall) (hj : Primrec jump) :
    Primrec fun x => Encodable.encode (patchControl (fall x) (jump x) t) := by
  induction t with
  | var k => exact Primrec.const _
  | tm k => exact Primrec.const _
  | nt k =>
    have nt : Primrec fun i => Encodable.encode (Tm.nt i) := by
      change Primrec fun i => tag 1 (cell (atom i) (atom 0))
      exact pr_tag.comp (Primrec.const _) (pr_cell.comp pr_atom (Primrec.const _))
    by_cases h : k = iF 2
    · simpa only [patchControl, if_pos h] using nt.comp hf
    · by_cases h' : k = iF 1
      · simpa only [patchControl, if_neg h, if_pos h'] using nt.comp hj
      · simpa only [patchControl, if_neg h, if_neg h'] using
          (Primrec.const (α := α) (Encodable.encode (Tm.nt k)))
  | app t u ht hu =>
    exact pr_tag.comp (Primrec.const 3) (pr_cell.comp ht (pr_cell.comp hu (Primrec.const (atom 0))))

private def templateOf (ins : Instr) : Tm := ctrlBody .L [ins, .incA] 1

private theorem pr_ctrlBody (side : Side) :
    Primrec fun p : Machine × ℕ => Encodable.encode (ctrlBody side p.1 p.2) := by
  let op (p : Machine × ℕ) := (p.1.lookup p.2).map Encodable.encode
  let kind (p : Machine × ℕ) := ((op p).map tagOf).getD 4
  let fall (p : Machine × ℕ) := iF (p.1.norm (p.2 + 1))
  let jump (p : Machine × ℕ) := iF (p.1.norm (argOf ((op p).getD 0)))
  have hop : Primrec op := Primrec.option_map pr_lookup (Primrec.encode.comp Primrec.snd).to₂
  have hkind : Primrec kind := Primrec.option_getD.comp
    (Primrec.option_map hop (pr_tagOf.comp Primrec.snd).to₂) (Primrec.const 4)
  have hf : Primrec fall := pr_iF.comp (pr_norm.comp Primrec.fst (Primrec.succ.comp Primrec.snd))
  have hj : Primrec jump := pr_iF.comp (pr_norm.comp Primrec.fst
    (pr_argOf.comp (Primrec.option_getD.comp hop (Primrec.const 0))))
  have branch (a : Instr) := pr_patched (templateOf a) hf hj
  have test (k : ℕ) := Primrec.eq.comp hkind (Primrec.const k)
  let encHalt := Encodable.encode (ctrlBody side [] 0)
  apply (Primrec.ite (test 0) (branch .incA) (Primrec.ite (test 1) (branch .incB)
    (Primrec.ite (test 2) (branch (.decA 1)) (Primrec.ite (test 3) (branch (.decB 1))
      (Primrec.const encHalt))))).of_eq
  intro p
  cases h : p.1.lookup p.2 with
  | none => simp only [kind, op, h, ctrlBody, Option.map_none, Option.getD_none]; rfl
  | some ins =>
    cases ins <;> simp only [kind, fall, jump, op, ctrlBody, h, Option.map_some, Option.getD_some,
      encode_incA, encode_incB, encode_decA, encode_decB, tagOf, argOf, tag, cell, atom,
      Nat.unpair_pair, Nat.pred_succ] <;> rfl

private theorem pr_startBody : Primrec fun M : Machine => Encodable.encode (startBody M) := by
  have hj := pr_iF.comp (pr_norm.comp Primrec.id (Primrec.const 1))
  exact (pr_patched (startBody [.incA]) (Primrec.const 0) hj).of_eq (fun _ => rfl)

private theorem list_code {α : Type} [Encodable α] (l : List α) :
    Encodable.encode (l.map Encodable.encode) = Encodable.encode l := by
  induction l <;> simp [*]

private theorem pr_rules (side : Side) : Primrec fun M : Machine => Encodable.encode (compile side M).rules := by
  have hstates : Primrec fun M : Machine =>
      (List.range (M.length + 1)).map (fun i => Encodable.encode (ctrlBody side M i)) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length)) (pr_ctrlBody side).to₂
  have hstart := Primrec.list_cons.comp pr_startBody (Primrec.const [Encodable.encode kBody])
  have h := Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.const (arithRules.map Encodable.encode)) hstart) hstates
  refine (Primrec.encode.comp h).of_eq fun M => ?_
  rw [← list_code (compile side M).rules]
  simp [compile, List.map_append, List.map_map, Function.comp_def]

private theorem pr_types (side : Side) : Primrec fun M : Machine => Encodable.encode (compile side M).nts := by
  have rep : Primrec fun M : Machine => List.replicate (M.length + 1) (Encodable.encode tyF) := by
    simpa using (Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length (α := Instr))))
      (Primrec₂.const (Encodable.encode tyF)))
  have h := Primrec.list_append.comp (Primrec.const ((arithTys ++ [Ty.o,Ty.o]).map Encodable.encode)) rep
  refine (Primrec.encode.comp h).of_eq fun M => ?_
  rw [← list_code (compile side M).nts]
  simp [compile, List.map_append]

private theorem scheme_code (G : HORS) : Encodable.encode G =
    tag 0 (cell (atom (Encodable.encode G.alphabet)) (cell (atom (Encodable.encode G.nts))
      (cell (atom (Encodable.encode G.rules)) (cell (atom G.start) (atom 0))))) := by
  cases G
  rfl

private theorem pr_compile (side : Side) : Primrec fun M : Machine => Encodable.encode (compile side M) := by
  simp only [scheme_code]
  exact pr_tag.comp (Primrec.const 0) (pr_cell.comp (Primrec.const (atom (Encodable.encode sigma0)))
    (pr_cell.comp (pr_atom.comp (pr_types side)) (pr_cell.comp (pr_atom.comp (pr_rules side))
      (Primrec.const (cell (atom iS) (atom 0))))))

theorem computable_compiled_pair :
    Computable (fun n : ℕ => Encodable.encode
      ((Encodable.decode n : Option Machine).map fun M => (compile .L M, compile .R M))) := by
  have hp := Primrec₂.natPair.comp (pr_compile .L) (pr_compile .R)
  have h := Primrec.option_map (Primrec.decode (α := Machine)) (hp.comp Primrec.snd).to₂
  refine (Primrec.encode.comp h).to_comp.of_eq fun n => ?_
  cases hd : (Encodable.decode n : Option Machine) <;> simp [Encodable.encode_prod_val]

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution :
    Computable (fun n : ℕ => Encodable.encode
      ((Encodable.decode n : Option Machine).map fun M => (compile .L M, compile .R M))) ∧
    (∀ (M : Machine) (side : Side),
      (compile side M).Valid ∧ (compile side M).Safe ∧ (compile side M).Prod ∧
        (compile side M).alphabet = sigma0 ∧ (compile side M).order ≤ 4) ∧
    ∀ M : Machine, M.Halts ↔
      ∃ (w : List ℕ) (a b : ℕ), a < sigma0.length ∧ b < sigma0.length ∧ a ≠ b ∧
        (compile .L M).Obs (.nt (compile .L M).start) w a ∧
        (compile .R M).Obs (.nt (compile .R M).start) w b  := by
  exact ⟨computable_compiled_pair, fun M side =>
    ⟨(lemma_5_1 M side).1, lemma_5_2 M side, lemma_5_7 M side,
      (lemma_5_1 M side).2.1, (lemma_5_1 M side).2.2⟩, halts_iff_compiled_observations⟩

