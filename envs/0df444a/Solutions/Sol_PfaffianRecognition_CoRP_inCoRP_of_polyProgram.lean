-- Prove2me | solution 1 for PfaffianRecognition.CoRP.inCoRP_of_polyProgram
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:29:29.395063+00:00
-- url     : https://prove2.me/submissions/65ed71de-ddec-4e76-890f-a0eef7b72423

import Definitions.Def_PfaffianRecognition_Recognition_computation_model
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

namespace PfaffianRecognition.CoRP.BridgeAux
open HypergraphUnreliability.FPRAS

theorem fairProb_take (R D : ℕ) (P : List Bool → Prop) :
    fairProb (R + D) (fun ω => P ((tapeList ω).take R)) = fairProb R (fun ω => P (tapeList ω)) := by
  classical
  unfold fairProb
  have hc : (Finset.univ.filter (fun ω : Fin (R + D) → Bool => P ((tapeList ω).take R))).card
      = (Finset.univ.filter (fun ω : Fin R → Bool => P (tapeList ω))).card * 2 ^ D := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    have e : {ω : Fin (R + D) → Bool // P ((tapeList ω).take R)} ≃
        {ω : Fin R → Bool // P (tapeList ω)} × (Fin D → Bool) :=
      ((Fin.appendEquiv R D).symm.subtypeEquiv (fun ω => by
        have : ω = Fin.append ((Fin.appendEquiv R D).symm ω).1 ((Fin.appendEquiv R D).symm ω).2 := by
          exact ((Fin.appendEquiv R D).apply_symm_apply ω).symm
        conv_lhs => rw [this]
        simp [tapeList, List.ofFn_fin_append])).trans Equiv.prodSubtypeFstEquivSubtypeProd
    rw [Fintype.card_congr e, Fintype.card_prod]
    simp
  rw [hc]
  push_cast
  rw [pow_add]
  have : (2:ℝ) ^ D ≠ 0 := by positivity
  field_simp

end PfaffianRecognition.CoRP.BridgeAux

namespace PfaffianRecognition.CoRP.BridgeAux
open OAI.MetricKMedian.Binary

def unaryPow : ℕ → List Bool → List Bool
  | 0, _ => [true]
  | r + 1, w => (true :: true :: w).flatMap (fun _ => unaryPow r w)

theorem flatMap_const_replicate (l : List Bool) (n : ℕ) :
    l.flatMap (fun _ => List.replicate n true) = List.replicate (l.length * n) true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, ih, List.length_cons, ← List.replicate_add]
    congr 1; ring

theorem unaryPow_eq (r : ℕ) (w : List Bool) :
    unaryPow r w = List.replicate ((w.length + 2) ^ r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [unaryPow, ih, flatMap_const_replicate, List.length_cons, pow_succ]
    congr 1; ring

open Automatic in
theorem unaryPow_poly (r : ℕ) : Automatic.Poly (unaryPow r) := by
  induction r with
  | zero => exact Automatic.Poly.const _
  | succ r ih =>
    have h0 : Automatic.Poly (fun w : List Bool => true :: w) :=
      Automatic.Poly.comp (f := fun x : Bool × List Bool => x.1 :: x.2) (g := fun w => (true, w))
        Automatic.Poly.list_cons (Automatic.Poly.pair (Automatic.Poly.const true) Automatic.Poly.identity)
    have h1 : Automatic.Poly (fun w : List Bool => true :: true :: w) :=
      Automatic.Poly.comp (f := fun w : List Bool => true :: w) (g := fun w => true :: w) h0 h0
    have h2 : Automatic.Poly (fun x : List Bool × Bool => unaryPow r x.1) :=
      Automatic.Poly.comp ih Automatic.Poly.fst
    exact Automatic.Poly.list_flatMap (f := fun (w : List Bool) (_ : Bool) => unaryPow r w) h2 h1

noncomputable def unaryProg (r : ℕ) :
    PolyProgram id id (fun w : List Bool => List.replicate ((w.length + 2) ^ r) true) :=
  ((BooleanLists.packProgram.comp ((unaryPow_poly r).program.comp BooleanLists.unpackProgram))).congr _
    (fun w => by simp [unaryPow_eq])

noncomputable def preProg (r : ℕ) :
    PolyProgram id (encodePair id id)
      (fun w : List Bool => (List.replicate ((w.length + 2) ^ r) true, w)) :=
  (unaryProg r).fanout (PolyProgram.identity id)

end PfaffianRecognition.CoRP.BridgeAux

namespace PfaffianRecognition.CoRP.BridgeAux
open OAI.MetricKMedian.Binary Turing Function

inductive ML | read | copy | xfer deriving DecidableEq
instance : Fintype ML := ⟨{.read, .copy, .xfer}, by intro x; cases x <;> simp⟩

section
variable (P Q : Machine)

abbrev XK := P.K ⊕ (Q.K ⊕ Bool)
abbrev XL := P.Label ⊕ (Q.Label ⊕ ML)
abbrev XS := P.State × Q.State × Option Bool

abbrev coinK : XK P Q := .inr (.inr false)
abbrev bufK : XK P Q := .inr (.inr true)

def embP (t : List Bool) : Embedding P.K P.Label P.State (XK P Q) (XL P Q) (XS P Q) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x, v.2)
  state v := (v, Q.initial, none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim s (Sum.elim (fun _ => []) (fun b => if b then [] else t))
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j
    · simp only [update_apply, Sum.elim_inl, Sum.inl.injEq]
    · simp only [update_apply, Sum.elim_inr, reduceCtorEq, ite_false]
  label := Sum.inl
  halted := some (.inr (.inr .read))
  stop := .goto (fun _ => .inr (.inr .read))
  stop_spec _ _ := rfl

def embQ (t : List Bool) : Embedding Q.K Q.Label Q.State (XK P Q) (XL P Q) (XS P Q) where
  key k := .inr (.inl k)
  read v := v.2.1
  write v x := (v.1, x, v.2.2)
  state v := (P.initial, v, none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim (fun _ => []) (Sum.elim s (fun b => if b then [] else t))
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j | j
    · simp only [update_apply, Sum.elim_inl, reduceCtorEq, ite_false]
    · simp only [update_apply, Sum.elim_inr, Sum.elim_inl, Sum.inr.injEq, Sum.inl.injEq]
    · simp only [update_apply, Sum.elim_inr, Sum.inr.injEq, reduceCtorEq, if_false]
  label l := .inr (.inl l)
  halted := none
  stop := .halt
  stop_spec _ _ := rfl

def clean (v : XS P Q) : XS P Q := (v.1, v.2.1, none)

def readCode : TM2.Stmt (fun _ : XK P Q => Bool) (XL P Q) (XS P Q) :=
  .pop (.inl P.output) (fun v c => (v.1, v.2.1, c))
    (.branch (fun v => v.2.2.isSome)
      (.branch (fun v => v.2.2.getD false)
        (.pop (.inl P.output) (fun v _ => v)
          (.pop (coinK P Q) (fun v c => (v.1, v.2.1, c))
            (.push (bufK P Q) (fun _ => true)
              (.push (bufK P Q) (fun v => v.2.2.getD false)
                (.load (clean P Q) (.goto fun _ => .inr (.inr .read)))))))
        (.push (bufK P Q) (fun _ => false) (.load (clean P Q) (.goto fun _ => .inr (.inr .copy)))))
      (.load (clean P Q) (.goto fun _ => .inr (.inr .xfer))))

def copyCode : TM2.Stmt (fun _ : XK P Q => Bool) (XL P Q) (XS P Q) :=
  .pop (.inl P.output) (fun v c => (v.1, v.2.1, c))
    (.branch (fun v => v.2.2.isSome)
      (.push (bufK P Q) (fun v => v.2.2.getD false) (.load (clean P Q) (.goto fun _ => .inr (.inr .copy))))
      (.load (clean P Q) (.goto fun _ => .inr (.inr .xfer))))

def xferCode : TM2.Stmt (fun _ : XK P Q => Bool) (XL P Q) (XS P Q) :=
  .pop (bufK P Q) (fun v c => (v.1, v.2.1, c))
    (.branch (fun v => v.2.2.isSome)
      (.push (.inr (.inl Q.input)) (fun v => v.2.2.getD false)
        (.load (clean P Q) (.goto fun _ => .inr (.inr .xfer))))
      (.load (clean P Q) (.goto fun _ => .inr (.inl Q.main))))

def code : XL P Q → TM2.Stmt (fun _ : XK P Q => Bool) (XL P Q) (XS P Q)
  | .inl l => (embP P Q []).stmt (P.code l)
  | .inr (.inl l) => (embQ P Q []).stmt (Q.code l)
  | .inr (.inr .read) => readCode P Q
  | .inr (.inr .copy) => copyCode P Q
  | .inr (.inr .xfer) => xferCode P Q

abbrev X : Machine where
  K := XK P Q
  input := .inl P.input
  output := .inr (.inl Q.output)
  Label := XL P Q
  main := .inl P.main
  State := XS P Q
  initial := (P.initial, Q.initial, none)
  code := code P Q

theorem embP_stmt (t t' : List Bool) (q : TM2.Stmt (fun _ : P.K => Bool) P.Label P.State) :
    (embP P Q t).stmt q = (embP P Q t').stmt q := by
  induction q with
  | push k f q ih => simp only [Embedding.stmt, ih]; rfl
  | peek k f q ih => simp only [Embedding.stmt, ih]; rfl
  | pop k f q ih => simp only [Embedding.stmt, ih]; rfl
  | load f q ih => simp only [Embedding.stmt, ih]; rfl
  | branch f q r ihq ihr => simp only [Embedding.stmt, ihq, ihr]; rfl
  | goto f => rfl
  | halt => rfl

theorem embQ_stmt (t t' : List Bool) (q : TM2.Stmt (fun _ : Q.K => Bool) Q.Label Q.State) :
    (embQ P Q t).stmt q = (embQ P Q t').stmt q := by
  induction q with
  | push k f q ih => simp only [Embedding.stmt, ih]; rfl
  | peek k f q ih => simp only [Embedding.stmt, ih]; rfl
  | pop k f q ih => simp only [Embedding.stmt, ih]; rfl
  | load f q ih => simp only [Embedding.stmt, ih]; rfl
  | branch f q r ihq ihr => simp only [Embedding.stmt, ihq, ihr]; rfl
  | goto f => rfl
  | halt => rfl

theorem code_embP (t : List Bool) (l : P.Label) :
    (X P Q).code ((embP P Q t).label l) = (embP P Q t).stmt (P.code l) :=
  embP_stmt P Q [] t _

theorem code_embQ (t : List Bool) (l : Q.Label) :
    (X P Q).code ((embQ P Q t).label l) = (embQ P Q t).stmt (Q.code l) :=
  embQ_stmt P Q [] t _

def midStk (u t buf qin : List Bool) : XK P Q → List Bool
  | .inl k => if k = P.output then u else []
  | .inr (.inl k) => if k = Q.input then qin else []
  | .inr (.inr false) => t
  | .inr (.inr true) => buf

def midCfg (l : ML) (u t buf qin : List Bool) : (X P Q).Cfg :=
  ⟨some (.inr (.inr l)), (P.initial, Q.initial, none), midStk P Q u t buf qin⟩

theorem read_pair (c : Bool) (u t buf : List Bool) :
    (X P Q).step (midCfg P Q .read (true :: true :: u) (c :: t) buf []) =
      some (midCfg P Q .read u t (c :: true :: buf) []) := by
  show some (TM2.stepAux (readCode P Q) _ _) = _
  simp [readCode, TM2.stepAux, midStk, midCfg, clean]
  try (funext k; rcases k with k | k | _ | _ <;> simp [midStk, update_apply] <;> split_ifs <;> simp_all)

theorem read_false (u t buf : List Bool) :
    (X P Q).step (midCfg P Q .read (false :: u) t buf []) =
      some (midCfg P Q .copy u t (false :: buf) []) := by
  show some (TM2.stepAux (readCode P Q) _ _) = _
  simp [readCode, TM2.stepAux, midStk, midCfg, clean]
  try (funext k; rcases k with k | k | _ | _ <;> simp [midStk, update_apply] <;> split_ifs <;> simp_all)

theorem copy_cons (x : Bool) (u t buf : List Bool) :
    (X P Q).step (midCfg P Q .copy (x :: u) t buf []) =
      some (midCfg P Q .copy u t (x :: buf) []) := by
  show some (TM2.stepAux (copyCode P Q) _ _) = _
  simp [copyCode, TM2.stepAux, midStk, midCfg, clean]
  try (funext k; rcases k with k | k | _ | _ <;> simp [midStk, update_apply] <;> split_ifs <;> simp_all)

theorem copy_nil (t buf : List Bool) :
    (X P Q).step (midCfg P Q .copy [] t buf []) =
      some (midCfg P Q .xfer [] t buf []) := by
  show some (TM2.stepAux (copyCode P Q) _ _) = _
  simp [copyCode, TM2.stepAux, midStk, midCfg, clean]
  try (funext k; rcases k with k | k | _ | _ <;> simp [midStk, update_apply] <;> split_ifs <;> simp_all)

theorem xfer_cons (x : Bool) (t buf qin : List Bool) :
    (X P Q).step (midCfg P Q .xfer [] t (x :: buf) qin) =
      some (midCfg P Q .xfer [] t buf (x :: qin)) := by
  show some (TM2.stepAux (xferCode P Q) _ _) = _
  simp [xferCode, TM2.stepAux, midStk, midCfg, clean]
  try (funext k; rcases k with k | k | _ | _ <;> simp [midStk, update_apply] <;> split_ifs <;> simp_all)

theorem xfer_nil (t qin : List Bool) :
    (X P Q).step (midCfg P Q .xfer [] t [] qin) =
      some ((embQ P Q t).cfg (Q.initialCfg qin)) := by
  show some (TM2.stepAux (xferCode P Q) _ _) = _
  simp [xferCode, TM2.stepAux, midStk, midCfg, clean, Embedding.cfg, embQ, Machine.initialCfg]
  try (funext k; rcases k with k | k | _ | _ <;> simp [midStk, update_apply] <;> split_ifs <;> simp_all)

def rq : List Bool → List Bool
  | [] => []
  | c :: cs => rq cs ++ [c, true]

theorem quote_reverse (ρ : List Bool) : (quote ρ).reverse = false :: rq ρ := by
  induction ρ with
  | nil => rfl
  | cons c cs ih => simp [quote, rq, ih]

theorem read_run (w : List Bool) (ρ t buf : List Bool) :
    Trace (X P Q).step ρ.length
      (midCfg P Q .read (quote (List.replicate ρ.length true) ++ w) (ρ ++ t) buf [])
      (midCfg P Q .read (false :: w) t (rq ρ ++ buf) []) := by
  induction ρ generalizing buf with
  | nil => exact Trace.refl _
  | cons c cs ih =>
    have h := Trace.cons (read_pair P Q c _ _ buf) (ih (c :: true :: buf))
    simpa [List.replicate_succ, quote, rq] using h

theorem copy_run (u t buf : List Bool) :
    Trace (X P Q).step u.length (midCfg P Q .copy u t buf [])
      (midCfg P Q .copy [] t (u.reverse ++ buf) []) := by
  induction u generalizing buf with
  | nil => exact Trace.refl _
  | cons x u ih =>
    have h := Trace.cons (copy_cons P Q x u t buf) (ih (x :: buf))
    simpa using h

theorem xfer_run (t buf qin : List Bool) :
    Trace (X P Q).step buf.length (midCfg P Q .xfer [] t buf qin)
      (midCfg P Q .xfer [] t [] (buf.reverse ++ qin)) := by
  induction buf generalizing qin with
  | nil => exact Trace.refl _
  | cons x buf ih =>
    have h := Trace.cons (xfer_cons P Q x t buf qin) (ih (x :: qin))
    simpa using h

theorem mid_run (w ρ t : List Bool) :
    Trace (X P Q).step (ρ.length + 1 + w.length + 1 + (2 * ρ.length + 1 + w.length) + 1)
      (midCfg P Q .read (quote (List.replicate ρ.length true) ++ w) (ρ ++ t) [] [])
      ((embQ P Q t).cfg (Q.initialCfg (quote ρ ++ w))) := by
  have h1 := read_run P Q w ρ t []
  have h2 := Trace.cons (read_false P Q w t (rq ρ ++ [])) (copy_run P Q w t _)
  have h3 := Trace.cons (copy_nil P Q t (w.reverse ++ false :: (rq ρ ++ [])))
    (xfer_run P Q t (w.reverse ++ false :: (rq ρ ++ [])) [])
  have h4 := Trace.cons (xfer_nil P Q t (quote ρ ++ w)) (Trace.refl _)
  have hb : (w.reverse ++ false :: (rq ρ ++ [])) = (quote ρ ++ w).reverse := by
    simp [quote_reverse]
  rw [hb] at h3 h2
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse, List.length_append,
    quote_length] at h3
  have := ((h1.trans h2).trans h3).trans h4
  convert this using 1
  omega

theorem embP_final (tape u : List Bool) :
    (embP P Q tape).cfg (P.finalCfg u) = midCfg P Q .read u tape [] [] := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k; rcases k with k | k | _ | _ <;> simp [Embedding.cfg, embP, Machine.finalCfg, midStk, midCfg]

theorem full_run (w ρ t out : List Bool) {nP nQ : ℕ}
    (hP : Trace P.step nP (P.initialCfg w) (P.finalCfg (quote (List.replicate ρ.length true) ++ w)))
    (hQ : Trace Q.step nQ (Q.initialCfg (quote ρ ++ w)) (Q.finalCfg out)) :
    Trace (X P Q).step (nP + (ρ.length + 1 + w.length + 1 + (2 * ρ.length + 1 + w.length) + 1) + nQ)
      ((embP P Q (ρ ++ t)).cfg (P.initialCfg w)) ((embQ P Q t).cfg (Q.finalCfg out)) := by
  have h1 := (embP P Q (ρ ++ t)).trace P.code (X P Q).code (code_embP P Q _) hP
  have h3 := (embQ P Q t).trace Q.code (X P Q).code (code_embQ P Q _) hQ
  rw [embP_final] at h1
  exact (h1.trans (mid_run P Q w ρ t)).trans h3

theorem embP_coin (q : TM2.Stmt (fun _ : P.K => Bool) P.Label P.State) (v : XS P Q)
    (S : XK P Q → List Bool) :
    (TM2.stepAux ((embP P Q []).stmt q) v S).stk (coinK P Q) = S (coinK P Q) := by
  induction q generalizing v S with
  | push k f q ih => simp only [Embedding.stmt, TM2.stepAux, ih]; simp [embP]
  | peek k f q ih => simp only [Embedding.stmt, TM2.stepAux, ih]
  | pop k f q ih => simp only [Embedding.stmt, TM2.stepAux, ih]; simp [embP]
  | load f q ih => simp only [Embedding.stmt, TM2.stepAux, ih]
  | branch f q r ihq ihr =>
    simp only [Embedding.stmt, TM2.stepAux]
    cases f ((embP P Q []).read v) <;> simp [ihq, ihr]
  | goto f => rfl
  | halt => rfl

theorem embQ_coin (q : TM2.Stmt (fun _ : Q.K => Bool) Q.Label Q.State) (v : XS P Q)
    (S : XK P Q → List Bool) :
    (TM2.stepAux ((embQ P Q []).stmt q) v S).stk (coinK P Q) = S (coinK P Q) := by
  induction q generalizing v S with
  | push k f q ih => simp only [Embedding.stmt, TM2.stepAux, ih]; simp [embQ]
  | peek k f q ih => simp only [Embedding.stmt, TM2.stepAux, ih]
  | pop k f q ih => simp only [Embedding.stmt, TM2.stepAux, ih]; simp [embQ]
  | load f q ih => simp only [Embedding.stmt, TM2.stepAux, ih]
  | branch f q r ihq ihr =>
    simp only [Embedding.stmt, TM2.stepAux]
    cases f ((embQ P Q []).read v) <;> simp [ihq, ihr]
  | goto f => rfl
  | halt => rfl

theorem step_coin (a b : (X P Q).Cfg) (h : (X P Q).step a = some b) :
    (a.stk (coinK P Q)).length ≤ (b.stk (coinK P Q)).length + 1 := by
  rcases a with ⟨l, v, S⟩
  cases l with
  | none => cases h
  | some l =>
    have hb : b = TM2.stepAux ((X P Q).code l) v S := (Option.some.inj h).symm
    subst hb
    rcases l with l | l | l
    · show (S (coinK P Q)).length ≤ ((TM2.stepAux ((embP P Q []).stmt (P.code l)) v S).stk _).length + 1
      rw [embP_coin]; omega
    · show (S (coinK P Q)).length ≤ ((TM2.stepAux ((embQ P Q []).stmt (Q.code l)) v S).stk _).length + 1
      rw [embQ_coin]; omega
    · cases l
      · show (S (coinK P Q)).length ≤ ((TM2.stepAux (readCode P Q) v S).stk _).length + 1
        simp only [readCode, TM2.stepAux]
        cases h1 : (S (.inl P.output)).head? with
        | none => simp [h1, clean]
        | some x =>
          cases x
          · simp [h1, clean]
          · simp [h1, clean]; omega
      · show (S (coinK P Q)).length ≤ ((TM2.stepAux (copyCode P Q) v S).stk _).length + 1
        simp only [copyCode, TM2.stepAux]
        cases h1 : (S (.inl P.output)).head? <;> simp [h1, clean]
      · show (S (coinK P Q)).length ≤ ((TM2.stepAux (xferCode P Q) v S).stk _).length + 1
        simp only [xferCode, TM2.stepAux]
        cases h1 : (S (bufK P Q)).head? <;> simp [h1, clean]

end
end PfaffianRecognition.CoRP.BridgeAux

namespace PfaffianRecognition.CoRP.BridgeAux
open OAI.MetricKMedian.Binary Turing Function HypergraphUnreliability.FPRAS

section
variable (P Q : Machine)

def coinM : CoinMachine where
  tm := (X P Q).tm
  finiteAlphabet _ := inferInstanceAs (Finite Bool)
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  kCoin := coinK P Q
  coin_ne_input := by simp [Machine.tm]
  coin_ne_output := by simp [Machine.tm]
  coinAlphabet := Equiv.refl Bool

theorem coinM_init (w tape : List Bool) :
    (coinM P Q).initCfg w tape = (embP P Q tape).cfg (P.initialCfg w) := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    simp only [CoinMachine.initCfg]
    split_ifs with h0 hc
    · subst h0; simp [Embedding.cfg, embP, Machine.initialCfg, coinM, Machine.tm]; exact List.map_id _
    · subst hc; simp [Embedding.cfg, embP, Machine.initialCfg, coinM, Machine.tm]; exact List.map_id _
    · rcases k with k | k | _ | _
      · simp [coinM, Machine.tm] at h0
        simp [Embedding.cfg, embP, Machine.initialCfg, h0]; rfl
      · simp [Embedding.cfg, embP, Machine.initialCfg]; rfl
      · exact absurd rfl hc
      · simp [Embedding.cfg, embP, Machine.initialCfg]; rfl

theorem coinM_cfgAt (w tape : List Bool) (n : ℕ) :
    (coinM P Q).cfgAt w tape n = (flip bind (X P Q).step)^[n] (some ((embP P Q tape).cfg (P.initialCfg w))) := by
  rw [← coinM_init]; rfl

theorem coinM_coin (w tape : List Bool) (s : ℕ) (c : (coinM P Q).tm.Cfg)
    (h : (coinM P Q).cfgAt w tape s = some c) :
    tape.length ≤ (c.stk (coinM P Q).kCoin).length + s := by
  induction s generalizing c with
  | zero =>
    simp only [CoinMachine.cfgAt, Function.iterate_zero, id, Option.some.injEq] at h
    subst h
    rw [coinM_init]
    simp [Embedding.cfg, embP, coinM]; exact le_refl _
  | succ s ih =>
    have h' := h
    simp only [CoinMachine.cfgAt, Function.iterate_succ_apply'] at h'
    cases hs : (coinM P Q).cfgAt w tape s with
    | none =>
      simp only [CoinMachine.cfgAt] at hs
      rw [hs] at h'; cases h'
    | some c0 =>
      simp only [CoinMachine.cfgAt] at hs
      rw [hs] at h'
      have h1 := ih c0 (by simpa [CoinMachine.cfgAt] using hs)
      have h2 := step_coin P Q c0 c h'
      have := Nat.le_trans h1 (Nat.add_le_add_right h2 s)
      exact this.trans_eq (Nat.add_right_comm _ _ _)

end
end PfaffianRecognition.CoRP.BridgeAux

namespace PfaffianRecognition.CoRP.BridgeAux
open OAI.MetricKMedian.Binary Turing Function HypergraphUnreliability.FPRAS

theorem eval_le_pow (p : Polynomial ℕ) {m : ℕ} (hm : 1 ≤ m) :
    p.eval m ≤ p.eval 1 * m ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  simp only [one_pow, mul_one]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm (by simp at hi; omega))

theorem fairProb_mono (T : ℕ) (E F : (Fin T → Bool) → Prop) (h : ∀ ω, E ω → F ω) :
    fairProb T E ≤ fairProb T F := by
  classical
  unfold fairProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun ω => by simpa using h ω)

theorem fairProb_take' (B R : ℕ) (hRB : R ≤ B) (P : List Bool → Prop) :
    fairProb B (fun ω => P ((tapeList ω).take R)) = fairProb R (fun ω => P (tapeList ω)) := by
  obtain ⟨D, rfl⟩ := Nat.exists_eq_add_of_le hRB
  exact fairProb_take R D P

theorem runs (P Q : Machine) (A : List Bool × List Bool → Bool) (w tape : List Bool) (R B : ℕ)
    (hR : R ≤ tape.length) {nP nQ : ℕ}
    (hP : Trace P.step nP (P.initialCfg w) (P.finalCfg (quote (List.replicate R true) ++ w)))
    (hQ : Trace Q.step nQ (Q.initialCfg (quote (tape.take R) ++ w))
      (Q.finalCfg [A (tape.take R, w)]))
    (hB : nP + (R + 1 + w.length + 1 + (2 * R + 1 + w.length) + 1) + nQ ≤ B) :
    (coinM P Q).RunsWithin w tape B [A (tape.take R, w)] := by
  have hlen : (tape.take R).length = R := by simp; omega
  have hP' : Trace P.step nP (P.initialCfg w)
      (P.finalCfg (quote (List.replicate (tape.take R).length true) ++ w)) := by rw [hlen]; exact hP
  have ht := full_run P Q w (tape.take R) (tape.drop R) _ hP' hQ
  rw [List.take_append_drop, hlen] at ht
  refine ⟨_, (embQ P Q (tape.drop R)).cfg (Q.finalCfg [A (tape.take R, w)]), hB, ?_, rfl, ?_, ?_⟩
  · rw [coinM_cfgAt]; exact ht.iterate_eq
  · simp [Embedding.cfg, embQ, Machine.finalCfg, coinM, Machine.tm]; rfl
  · intro s' hs' c' hc'
    have := coinM_coin P Q w tape s' c' hc'
    omega

end PfaffianRecognition.CoRP.BridgeAux

namespace PfaffianRecognition.CoRP.BridgeAux
open OAI.MetricKMedian.Binary

theorem step_bound (T1 T2 : Polynomial ℕ) (r n sP sQ : ℕ) (hsP : sP ≤ T1.eval n)
    (hsQ : sQ ≤ T2.eval (2 * (n + 2) ^ r + 1 + n)) :
    sP + ((n + 2) ^ r + 1 + n + 1 + (2 * (n + 2) ^ r + 1 + n) + 1) + sQ ≤
      (T1.eval 1 + T2.eval 1 * 3 ^ T2.natDegree + 5) *
        (n + 2) ^ (T1.natDegree + (r + 1) * T2.natDegree + r + 1) := by
  set x := n + 2 with hx
  set K := T1.natDegree + (r + 1) * T2.natDegree + r + 1 with hK
  have hx1 : 1 ≤ x := by omega
  have h1 : T1.eval n ≤ T1.eval 1 * x ^ T1.natDegree :=
    (polynomial_eval_mono T1 (by omega : n ≤ x)).trans (eval_le_pow T1 hx1)
  have hxr : x ^ r ≤ x ^ (r + 1) := Nat.pow_le_pow_right hx1 (by omega)
  have hxr1 : x ≤ x ^ (r + 1) := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ (r + 1) := Nat.pow_le_pow_right hx1 (by omega)
  have hm : 2 * x ^ r + 1 + n ≤ 3 * x ^ (r + 1) := by omega
  have h2 : T2.eval (2 * x ^ r + 1 + n) ≤ T2.eval 1 * 3 ^ T2.natDegree * x ^ ((r + 1) * T2.natDegree) := by
    calc T2.eval (2 * x ^ r + 1 + n) ≤ T2.eval (3 * x ^ (r + 1)) := polynomial_eval_mono T2 hm
      _ ≤ T2.eval 1 * (3 * x ^ (r + 1)) ^ T2.natDegree :=
          eval_le_pow T2 (by have := Nat.one_le_pow (r+1) x hx1; omega)
      _ = T2.eval 1 * 3 ^ T2.natDegree * x ^ ((r + 1) * T2.natDegree) := by
          rw [mul_pow, ← pow_mul]; ring
  have p1 : x ^ T1.natDegree ≤ x ^ K := Nat.pow_le_pow_right hx1 (by omega)
  have p2 : x ^ ((r + 1) * T2.natDegree) ≤ x ^ K := Nat.pow_le_pow_right hx1 (by omega)
  have p3 : x ^ r ≤ x ^ K := Nat.pow_le_pow_right hx1 (by omega)
  have p4 : x ≤ x ^ K := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ K := Nat.pow_le_pow_right hx1 (by omega)
  calc sP + (x ^ r + 1 + n + 1 + (2 * x ^ r + 1 + n) + 1) + sQ
      ≤ T1.eval 1 * x ^ T1.natDegree + (3 * x ^ r + 2 * x) +
          T2.eval 1 * 3 ^ T2.natDegree * x ^ ((r + 1) * T2.natDegree) := by omega
    _ ≤ T1.eval 1 * x ^ K + (3 * x ^ K + 2 * x ^ K) + T2.eval 1 * 3 ^ T2.natDegree * x ^ K := by
          gcongr
    _ = (T1.eval 1 + T2.eval 1 * 3 ^ T2.natDegree + 5) * x ^ K := by ring

end PfaffianRecognition.CoRP.BridgeAux

namespace PfaffianRecognition.CoRP

open OAI.MetricKMedian.Binary in
theorem inCoRP_of_polyProgram_core (L : List Bool → Prop)
    (A : List Bool × List Bool → Bool)
    (hA : Nonempty (PolyProgram (encodePair id id) encodeBool A)) (r : ℕ)
    (hyes : ∀ w, L w → ∀ ρ : List Bool, ρ.length = (w.length + 2) ^ r → A (ρ, w) = true)
    (hno : ∀ w, ¬ L w → (1 / 2 : ℝ) ≤ HypergraphUnreliability.FPRAS.fairProb ((w.length + 2) ^ r)
        (fun ω => A (HypergraphUnreliability.FPRAS.tapeList ω, w) = false)) :
    PfaffianRecognition.Recognition.InCoRP L := by
  classical
  obtain ⟨PA⟩ := hA
  let Pre := BridgeAux.preProg r
  refine ⟨BridgeAux.coinM Pre.machine PA.machine,
    Pre.time.eval 1 + PA.time.eval 1 * 3 ^ PA.time.natDegree + 5,
    Pre.time.natDegree + (r + 1) * PA.time.natDegree + r + 1, by omega, ?_⟩
  intro w
  set C := Pre.time.eval 1 + PA.time.eval 1 * 3 ^ PA.time.natDegree + 5 with hC
  set k := Pre.time.natDegree + (r + 1) * PA.time.natDegree + r + 1 with hk
  set R := (w.length + 2) ^ r with hR
  have hRB : R ≤ C * (w.length + 2) ^ k := by
    have h1 : R ≤ (w.length + 2) ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (w.length + 2) ^ k ≤ C * (w.length + 2) ^ k := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have key : ∀ ω : Fin (C * (w.length + 2) ^ k) → Bool,
      (BridgeAux.coinM Pre.machine PA.machine).RunsWithin w
        (HypergraphUnreliability.FPRAS.tapeList ω) (C * (w.length + 2) ^ k)
        [A ((HypergraphUnreliability.FPRAS.tapeList ω).take R, w)] := by
    intro ω
    set tape := HypergraphUnreliability.FPRAS.tapeList ω
    have hlen : tape.length = C * (w.length + 2) ^ k := by simp [tape, HypergraphUnreliability.FPRAS.tapeList]
    let hPo := Pre.outputs w
    let hQo := PA.outputs (tape.take R, w)
    have tP := Trace.of_iterate hPo.evals_in_steps
    have tQ := Trace.of_iterate hQo.evals_in_steps
    have sP := hPo.steps_le_m
    have sQ := hQo.steps_le_m
    have hρ : (tape.take R).length = R := by simp; omega
    simp only [encodePair_length, id, hρ] at sP sQ
    apply BridgeAux.runs Pre.machine PA.machine A w tape R _ (by omega) tP tQ
    exact BridgeAux.step_bound Pre.time PA.time r w.length _ _ sP sQ
  refine ⟨fun ω => ⟨_, key ω⟩, fun hL ω => ?_, fun hL => ?_⟩
  · have := key ω
    rwa [hyes w hL _ (by simp [HypergraphUnreliability.FPRAS.tapeList]; omega)] at this
  · refine le_trans (hno w hL) ?_
    rw [← BridgeAux.fairProb_take' _ R hRB (fun ρ => A (ρ, w) = false)]
    apply BridgeAux.fairProb_mono
    intro ω hω
    have := key ω
    rwa [hω] at this

end PfaffianRecognition.CoRP


open OAI.MetricKMedian.Binary in
theorem solution (L : List Bool → Prop)
    (A : List Bool × List Bool → Bool)
    (hA : Nonempty (PolyProgram (encodePair id id) encodeBool A)) (r : ℕ)
    (hyes : ∀ w, L w → ∀ ρ : List Bool, ρ.length = (w.length + 2) ^ r → A (ρ, w) = true)
    (hno : ∀ w, ¬ L w → (1 / 2 : ℝ) ≤ HypergraphUnreliability.FPRAS.fairProb ((w.length + 2) ^ r)
        (fun ω => A (HypergraphUnreliability.FPRAS.tapeList ω, w) = false)) :
    PfaffianRecognition.Recognition.InCoRP L :=
  PfaffianRecognition.CoRP.inCoRP_of_polyProgram_core L A hA r hyes hno
