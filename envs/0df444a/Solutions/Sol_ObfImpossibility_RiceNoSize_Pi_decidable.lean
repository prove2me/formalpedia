-- Prove2me | solution 1 for ObfImpossibility.RiceNoSize.Pi_decidable
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-23T22:58:29.523825+00:00
-- url     : https://prove2.me/submissions/21019b62-d14a-4981-b5a3-fa082f2265ee

import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects

set_option maxHeartbeats 2000000

open ObfImpossibility.RiceNoSize Turing

namespace RiceDecider

abbrev RawCfg := ℕ × (List Bool × List Bool)
abbrev State := List ℕ × RawCfg

def table (M : Machine) : List ℕ :=
  (List.finRange (M.q + 1)).flatMap
    (fun s => [entryCode (M.δ s false), entryCode (M.δ s true)])

def decoded (d : ℕ) : ℕ × List ℕ :=
  (Encodable.decode (α := ℕ × List ℕ) d).getD (0, [])

def readEntry (p : State) : ℕ :=
  (p.1[2 * p.2.1 + (if p.2.2.2.headI then 1 else 0)]?).getD 0

def act (j : ℕ) (s : ℕ) (L R : List Bool) : RawCfg :=
  (s, if j = 0 then (L.tail, L.headI :: R)
      else if j = 1 then (R.headI :: L, R.tail)
      else (L, (j == 3) :: R.tail))

def step (p : State) : ℕ ⊕ State :=
  if readEntry p = 0 then Sum.inl ((p.2.2.2.takeWhile id).length)
  else Sum.inr (p.1,
    act (readEntry p - 1).unpair.2 (readEntry p - 1).unpair.1 p.2.2.1 p.2.2.2)

def run : State →. ℕ := PFun.fix (fun p => Part.some (step p))

def start (tab : List ℕ) (x : ℕ) : State := (tab, (0, ([], input x)))

def evaluate (tab : List ℕ) (x : ℕ) : Part ℕ := run (start tab x)

lemma decoded_desc (M : Machine) : decoded (desc M) = (M.q, table M) := by
  simp [decoded, desc, table]

lemma prim_decoded : Primrec decoded :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (0, []))

lemma prim_input : Primrec input := by
  have h : Primrec (fun n : ℕ => (List.range n).map (fun _ => true)) :=
    Primrec.list_map Primrec.list_range (Primrec.const true).to₂
  exact h.of_eq (fun n => by simp [input])

lemma prim_readEntry : Primrec readEntry := by
  have hi : Primrec (fun p : State =>
      2 * p.2.1 + (if p.2.2.2.headI then 1 else 0)) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd))
      (Primrec.ite (Primrec.eq.comp (Primrec.list_headI.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.snd))) (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0))
  exact Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst hi) (Primrec.const 0)

lemma prim_act : Primrec (fun p : (ℕ × ℕ) × (List Bool × List Bool) =>
    act p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hj : Primrec (fun p : (ℕ × ℕ) × (List Bool × List Bool) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun p : (ℕ × ℕ) × (List Bool × List Bool) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hL : Primrec (fun p : (ℕ × ℕ) × (List Bool × List Bool) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hR : Primrec (fun p : (ℕ × ℕ) × (List Bool × List Bool) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact hs.pair (Primrec.ite (Primrec.eq.comp hj (Primrec.const 0))
    ((Primrec.list_tail.comp hL).pair
      (Primrec.list_cons.comp (Primrec.list_headI.comp hL) hR))
    (Primrec.ite (Primrec.eq.comp hj (Primrec.const 1))
      ((Primrec.list_cons.comp (Primrec.list_headI.comp hR) hL).pair
        (Primrec.list_tail.comp hR))
      (hL.pair (Primrec.list_cons.comp
        (Primrec.beq.comp hj (Primrec.const 3)) (Primrec.list_tail.comp hR)))))

lemma prim_step : Primrec step := by
  have he : Primrec (fun p : State => (readEntry p - 1).unpair) :=
    Primrec.unpair.comp (Primrec.nat_sub.comp prim_readEntry (Primrec.const 1))
  exact Primrec.ite (Primrec.eq.comp prim_readEntry (Primrec.const 0))
    (Primrec.sumInl.comp (Primrec.list_length.comp
      ((Primrec.list_takeWhile Primrec.id).comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (Primrec.sumInr.comp (Primrec.fst.pair
      (prim_act.comp (((Primrec.snd.comp he).pair (Primrec.fst.comp he)).pair
        (Primrec.snd.comp Primrec.snd)))))

lemma partrec_run : Partrec run := Partrec.fix prim_step.to_comp

lemma prim_start : Primrec (fun p : List ℕ × ℕ => start p.1 p.2) :=
  Primrec.fst.pair ((Primrec.const 0).pair
    ((Primrec.const []).pair (prim_input.comp Primrec.snd)))

lemma partrec_evaluate : Partrec₂ evaluate :=
  (partrec_run.comp prim_start.to_comp).to₂

lemma get_pair_flatMap {α : Type} (f g : α → ℕ) (l : List α) (i : ℕ) (a : Bool) :
    (l.flatMap (fun s => [f s, g s]))[2 * i + (if a then 1 else 0)]? =
      l[i]?.map (fun s => if a then g s else f s) := by
  induction l generalizing i with
  | nil => simp
  | cons s l ih =>
    cases i with
    | zero => cases a <;> simp
    | succ i => cases a <;> simpa [Nat.mul_succ, Nat.add_assoc] using ih i

lemma readEntry_table (M : Machine) (s : Fin (M.q + 1)) (L R : List Bool) :
    readEntry (table M, (s.val, (L, R))) = entryCode (M.δ s R.headI) := by
  unfold readEntry table
  rw [get_pair_flatMap]
  have h : (List.finRange (M.q + 1))[s.val]? = some s := by
    rw [List.getElem?_eq_getElem (by simpa using s.isLt)]
    simp
  rw [h]
  cases R.headI <;> rfl

lemma step_table (M : Machine) (s : Fin (M.q + 1)) (L R : List Bool) :
    step (table M, (s.val, (L, R))) =
      match M.δ s R.headI with
      | none => Sum.inl ((R.takeWhile id).length)
      | some (s', a) => Sum.inr (table M,
          match a with
          | .move .left => (s'.val, (L.tail, L.headI :: R))
          | .move .right => (s'.val, (R.headI :: L, R.tail))
          | .write b => (s'.val, (L, b :: R.tail))) := by
  unfold step
  rw [readEntry_table]
  cases h : M.δ s R.headI with
  | none => rfl
  | some p =>
    rcases p with ⟨s', a⟩
    cases a with
    | move d => cases d <;> simp [entryCode, stmtCode, act]
    | write b => cases b <;> simp [entryCode, stmtCode, act]

def cfg (M : Machine) (s : Fin (M.q + 1)) (L R : List Bool) :
    TM0.Cfg Bool (Fin (M.q + 1)) :=
  ⟨s, Tape.mk' (ListBlank.mk L) (ListBlank.mk R)⟩

lemma run_from_eval (M : Machine) {b c : TM0.Cfg Bool (Fin (M.q + 1))}
    (h : b ∈ StateTransition.eval (TM0.step M.δ) c) :
    ∀ (s : Fin (M.q + 1)) (L R : List Bool), c = cfg M s L R →
      leadingOnes b.Tape.right₀ ∈ run (table M, (s.val, (L, R))) := by
  refine StateTransition.evalInduction (C := fun c =>
    ∀ (s : Fin (M.q + 1)) (L R : List Bool), c = cfg M s L R →
      leadingOnes b.Tape.right₀ ∈ run (table M, (s.val, (L, R)))) h ?_
  intro c hc ih s L R heq
  subst c
  cases hd : M.δ s R.headI with
  | none =>
    have hs : TM0.step M.δ (cfg M s L R) = none := by
      simp [TM0.step, cfg, hd]
    have hb : b = cfg M s L R := Part.mem_unique hc
      (StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hs⟩)
    apply PFun.mem_fix_iff.mpr
    left
    apply Part.mem_some_iff.mpr
    rw [step_table, hd]
    simp only [hb, cfg, Tape.mk'_right₀]
    rfl
  | some p =>
    rcases p with ⟨s', a⟩
    cases a with
    | move d =>
      cases d with
      | left =>
        have hs : TM0.step M.δ (cfg M s L R) =
            some (cfg M s' L.tail (L.headI :: R)) := by
          simp [TM0.step, cfg, hd, Tape.move_left_mk']
        apply PFun.mem_fix_iff.mpr
        refine Or.inr ⟨(table M, (s'.val, (L.tail, L.headI :: R))), ?_, ?_⟩
        · apply Part.mem_some_iff.mpr
          rw [step_table, hd]
        · exact ih _ hs s' L.tail (L.headI :: R) rfl
      | right =>
        have hs : TM0.step M.δ (cfg M s L R) =
            some (cfg M s' (R.headI :: L) R.tail) := by
          simp [TM0.step, cfg, hd, Tape.move_right_mk']
        apply PFun.mem_fix_iff.mpr
        refine Or.inr ⟨(table M, (s'.val, (R.headI :: L, R.tail))), ?_, ?_⟩
        · apply Part.mem_some_iff.mpr
          rw [step_table, hd]
        · exact ih _ hs s' (R.headI :: L) R.tail rfl
    | write a =>
      have hs : TM0.step M.δ (cfg M s L R) =
          some (cfg M s' L (a :: R.tail)) := by
        simp [TM0.step, cfg, hd, Tape.write_mk']
      apply PFun.mem_fix_iff.mpr
      refine Or.inr ⟨(table M, (s'.val, (L, a :: R.tail))), ?_, ?_⟩
      · apply Part.mem_some_iff.mpr
        rw [step_table, hd]
      · exact ih _ hs s' L (a :: R.tail) rfl

lemma evaluate_of_mem (M : Machine) (x y : ℕ) (hy : y ∈ fn M x) :
    evaluate (table M) x = Part.some y := by
  obtain ⟨w, hw, hwy⟩ := (Part.mem_map_iff leadingOnes).mp hy
  obtain ⟨b, hb, rfl⟩ :=
    (Part.mem_map_iff (fun c : TM0.Cfg Bool (Fin (M.q + 1)) => c.Tape.right₀)).mp hw
  apply Part.eq_some_iff.mpr
  rw [← hwy]
  exact run_from_eval M hb 0 [] (input x) rfl

def tally (tab : List ℕ) (n : ℕ) : Part ℕ :=
  n.rec (Part.some 0) fun k prev =>
    prev.bind fun a => (evaluate tab k).map (fun b => a + b)

lemma tally_zero (tab : List ℕ) : tally tab 0 = Part.some 0 := rfl

lemma tally_succ (tab : List ℕ) (n : ℕ) :
    tally tab (n + 1) = (tally tab n).bind
      (fun a => (evaluate tab n).map (fun b => a + b)) := rfl

lemma partrec_tally : Partrec₂ tally := by
  have hp : Primrec (fun p : (List ℕ × ℕ) × (ℕ × ℕ) => (p.1.1, p.2.1)) :=
    (Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)
  have he : Partrec (fun p : (List ℕ × ℕ) × (ℕ × ℕ) => evaluate p.1.1 p.2.1) :=
    Partrec.comp (f := fun p : List ℕ × ℕ => evaluate p.1 p.2)
      partrec_evaluate hp.to_comp
  have ha : Computable₂ (fun p : (List ℕ × ℕ) × (ℕ × ℕ) => fun v : ℕ => p.2.2 + v) :=
    (Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      Primrec.snd).to_comp.to₂
  exact (Partrec.nat_rec Computable.snd (Computable.const 0) (he.map ha).to₂).to₂

def decision (d : ℕ) : Part ℕ :=
  (tally (decoded d).2 ((decoded d).1 + 1)).map (fun v => if v = 0 then 0 else 1)

lemma partrec_decision : Partrec decision := by
  have hp : Primrec (fun d : ℕ => ((decoded d).2, (decoded d).1 + 1)) :=
    (Primrec.snd.comp prim_decoded).pair (Primrec.succ.comp (Primrec.fst.comp prim_decoded))
  have hf : Computable₂ (fun _ : ℕ => fun v : ℕ => if v = 0 then 0 else 1) :=
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      (Primrec.const 0) (Primrec.const 1)).to_comp.to₂
  exact (Partrec.comp (f := fun p : List ℕ × ℕ => tally p.1 p.2)
    partrec_tally hp.to_comp).map hf

lemma tally_total (M : Machine) (hM : AlwaysHalts M) (n : ℕ) :
    ∃ v : ℕ, tally (table M) n = Part.some v ∧
      (v = 0 ↔ ∀ x : ℕ, x < n → fn M x = Part.some 0) := by
  induction n with
  | zero => exact ⟨0, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha, ha0⟩ := ih
    let b := (fn M n).get (hM n)
    have hb : fn M n = Part.some b := Part.eq_some_iff.mpr ⟨hM n, rfl⟩
    have he := evaluate_of_mem M n b (Part.eq_some_iff.mp hb)
    refine ⟨a + b, ?_, ?_⟩
    · simp [tally_succ, ha, he]
    · rw [Nat.add_eq_zero_iff, ha0]
      constructor
      · rintro ⟨hprev, hb0⟩ x hx
        by_cases hxn : x < n
        · exact hprev x hxn
        · have hxn' : x = n := by omega
          subst x
          simpa [hb0] using hb
      · intro hzero
        refine ⟨fun x hx => hzero x (by omega), ?_⟩
        simpa using hb.symm.trans (hzero n (by omega))

end RiceDecider

theorem solution : ∃ T : Nat.Partrec.Code, Decides T PiY PiN := by
  obtain ⟨T, hT⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp RiceDecider.partrec_decision)
  refine ⟨T, ?_, ?_⟩
  · intro M hM
    obtain ⟨v, hv, hv0⟩ := RiceDecider.tally_total M hM.1 (size M)
    have hbound : KC (fn M) ≤ size M := Nat.sInf_le ⟨M, rfl, rfl⟩
    have hvne : v ≠ 0 := by
      intro hz
      obtain ⟨x, hx, hx1⟩ := hM.2
      have hx0 := (hv0.mp hz) x (lt_of_lt_of_le hx hbound)
      have heq : Part.some (1 : ℕ) = Part.some 0 := hx1.symm.trans hx0
      simp at heq
    rw [hT]
    simp only [RiceDecider.decision, RiceDecider.decoded_desc]
    change (RiceDecider.tally (RiceDecider.table M) (size M)).map _ = _
    rw [hv]
    simp [hvne]
  · intro M hM
    obtain ⟨v, hv, hv0⟩ := RiceDecider.tally_total M hM.1 (size M)
    have hz : v = 0 := hv0.mpr (fun x _ => hM.2 x)
    rw [hT]
    simp only [RiceDecider.decision, RiceDecider.decoded_desc]
    change (RiceDecider.tally (RiceDecider.table M) (size M)).map _ = _
    rw [hv]
    simp [hz]

#print axioms solution
