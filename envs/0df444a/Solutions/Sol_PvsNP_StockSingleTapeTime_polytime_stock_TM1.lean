-- Prove2me | solution 1 for PvsNP.StockSingleTapeTime.polytime_stock_TM1
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T02:44:40.284815+00:00
-- url     : https://prove2.me/submissions/a850e4d5-3df9-49c4-8b71-ff70c151e4e2

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PvsNP.StockSingleTapeTime

open Function Turing Turing.TM2to1

def Steps {A : Type*} (f : A → Option A) (n : ℕ) (a b : A) : Prop :=
  (fun x : Option A => x.bind f)^[n] (some a) = some b

theorem Steps.refl {A : Type*} (f : A → Option A) (a : A) : Steps f 0 a a := rfl

theorem Steps.one {A : Type*} {f : A → Option A} {a b : A} (h : f a = some b) :
    Steps f 1 a b := by simpa [Steps] using h

theorem Steps.trans {A : Type*} {f : A → Option A} {a b c : A} {m n : ℕ}
    (h : Steps f m a b) (g : Steps f n b c) : Steps f (m+n) a c := by
  unfold Steps at *
  rw [Nat.add_comm,iterate_add_apply,h,g]

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
variable [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ)

theorem go_scan {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n : ℕ) (H : n ≤ S.length) :
    Steps (TM1.step (tr M)) n
      ⟨some (Λ'.go k o q),v,Tape.mk' ∅ (addBottom L)⟩
      ⟨some (Λ'.go k o q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply (ih (le_of_lt H)).trans
    apply Steps.one
    rw [iterate_succ_apply']
    simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat, Tape.move_right_n_head,
      addBottom_nth_snd]
    rw [stk_nth_val _ hL, List.getElem?_eq_getElem]
    · rfl
    · rwa [List.length_reverse]

theorem return_scan (q : TM2.Stmt Γ Λ σ) (v : σ)
    (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    Steps (TM1.step (tr M)) n
      ⟨some (Λ'.ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (Λ'.ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have first : Steps (TM1.step (tr M)) 1
        ⟨some (Λ'.ret q),v,(Tape.move Dir.right)^[n+1] (Tape.mk' ∅ (addBottom L))⟩
        ⟨some (Λ'.ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      apply Steps.one
      simp only [TM1.step]
      rw [Option.some_inj, tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
        addBottom_nth_succ_fst, TM1.stepAux, iterate_succ', Function.comp_apply, Tape.move_right_left]
      rfl
    simpa only [Nat.add_comm 1 n] using first.trans ih


/-- One stack operation causes one outward move per old cell and one return
move per new cell, plus the two controller transitions. -/
theorem stack_operation_cost {k : K} {q : TM2.Stmt Γ Λ σ} {v : σ}
    {S : ∀ k, List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : ∀ j, L.map (proj j) = ListBlank.mk ((S j).map some).reverse)
    (op : StAct K Γ σ k) :
    let updated := Function.update S k (stWrite v (S k) op)
    ∃ L' : ListBlank (∀ j, Option (Γ j)),
      (∀ j, L'.map (proj j) = ListBlank.mk ((updated j).map some).reverse) ∧
      Steps (TM1.step (tr M)) ((S k).length+(updated k).length+2)
        (TM1.stepAux (trNormal (stRun op q)) v (Tape.mk' ∅ (addBottom L)))
        (TM1.stepAux (trNormal q) (stVar v (S k) op) (Tape.mk' ∅ (addBottom L'))) := by
  dsimp only
  obtain ⟨L',fit,operation⟩ := tr_respects_aux₂ (Λ := Λ) (q := TM1.Stmt.goto (fun _ _ => Λ'.ret q))
    (v := v) hL op
  refine ⟨L',fit,?_⟩
  let oldLength := (S k).length
  let newLength := (stWrite v (S k) op).length
  let out := (Tape.move Dir.right)^[oldLength] (Tape.mk' ∅ (addBottom L))
  let back := (Tape.move Dir.right)^[newLength] (Tape.mk' ∅ (addBottom L'))
  let newValue := stVar v (S k) op
  have start := go_scan M op q v (hL k) oldLength le_rfl
  have atTop : Steps (TM1.step (tr M)) 1 ⟨some (Λ'.go k op q),v,out⟩
      ⟨some (Λ'.ret q),newValue,back⟩ := by
    apply Steps.one
    simp only [TM1.step, tr, TM1.stepAux]
    have target : (out.head.2 k).isNone = true := by
      unfold out oldLength
      rw [Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd,
        stk_nth_val _ (hL k), List.getElem?_eq_none (le_of_eq List.length_reverse)]
      rfl
    rw [target,cond]
    simpa only [out,back,oldLength,newLength,newValue,TM1.stepAux,Function.update_self]
      using congrArg some operation
  have home := return_scan M q newValue L' newLength
  have done : Steps (TM1.step (tr M)) 1 ⟨some (Λ'.ret q),newValue,Tape.mk' ∅ (addBottom L')⟩
      (TM1.stepAux (trNormal q) newValue (Tape.mk' ∅ (addBottom L'))) := by
    apply Steps.one
    simp only [TM1.step, tr, TM1.stepAux, Tape.mk'_head, addBottom_head_fst, cond]
  rw [trNormal_run]
  simpa only [TM1.stepAux,Function.update_self,← Nat.add_assoc,Nat.add_right_comm oldLength 1 newLength]
    using ((start.trans atTop).trans home).trans done


/-- The greatest number of stack actions on a branch of one TM2 statement. -/
def stackOps : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ rest => stackOps rest + 1
  | .peek _ _ rest => stackOps rest + 1
  | .pop _ _ rest => stackOps rest + 1
  | .load _ rest => stackOps rest
  | .branch _ left right => max (stackOps left) (stackOps right)
  | .goto _ | .halt => 0

omit [DecidableEq K] in
private theorem stackOps_run {k : K} (op : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    stackOps (stRun op q) = stackOps q+1 := by cases op <;> rfl

private theorem update_stack_bound {k : K} (op : StAct K Γ σ k) (v : σ)
    (S : ∀ k, List (Γ k)) (B : ℕ) (fit : ∀ j, (S j).length ≤ B) :
    ∀ j, ((Function.update S k (stWrite v (S k) op)) j).length ≤ B+1 := by
  intro j
  by_cases atUpdate : j = k
  · subst j
    rw [Function.update_self]
    have bound := fit k
    cases op <;> simp only [stWrite,List.length_cons,List.length_tail] <;> omega
  · rw [Function.update_of_ne atUpdate]
    exact (fit j).trans (Nat.le_succ _)

/-- A single TM2 step adds at most one cell per selected stack operation. -/
theorem stepAux_stack_bound (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (B : ℕ) (fit : ∀ j, (S j).length ≤ B) :
    ∀ j, ((TM2.stepAux q v S).stk j).length ≤ B + stackOps q := by
  induction q using stmtStRec generalizing v S B with
  | run k op q ih =>
    rw [step_run,stackOps_run]
    intro j
    have bound := ih (stVar v (S k) op) (Function.update S k (stWrite v (S k) op))
      (B+1) (update_stack_bound op v S B fit) j
    exact bound.trans (by omega)
  | load a q ih => exact ih _ _ B fit
  | branch check left right ihL ihR =>
    rw [TM2.stepAux,stackOps]
    cases check v
    · exact fun j => (ihR v S B fit j).trans (Nat.add_le_add_left (le_max_right _ _) _)
    · exact fun j => (ihL v S B fit j).trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto => simpa [stackOps,TM2.stepAux] using fit
  | halt => simpa [stackOps,TM2.stepAux] using fit


def statementBudget (B actions : ℕ) : ℕ := actions*(2*(B+actions)+3)

private theorem statementBudget_mono {B B' actions actions' : ℕ}
    (space : B ≤ B') (ops : actions ≤ actions') :
    statementBudget B actions ≤ statementBudget B' actions' := by
  unfold statementBudget
  exact Nat.mul_le_mul ops (by omega)

/-- Quantitative lift of the stock translator's auxiliary statement semantics. -/
theorem counted_aux (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (L : ListBlank (∀ k, Option (Γ k))) (B : ℕ)
    (hL : ∀ j, L.map (proj j) = ListBlank.mk ((S j).map some).reverse)
    (fit : ∀ j, (S j).length ≤ B) :
    ∃ (n : ℕ) (b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ),
      TrCfg (TM2.stepAux q v S) b ∧
      Steps (TM1.step (tr M)) n (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) b ∧
      n ≤ statementBudget B (stackOps q) := by
  induction q using stmtStRec generalizing v S L B with
  | run k op q ih =>
    obtain ⟨L',hL',block⟩ := stack_operation_cost M (q := q) (v := v) hL op
    let updated := Function.update S k (stWrite v (S k) op)
    have fit' : ∀ j, (updated j).length ≤ B+1 := update_stack_bound op v S B fit
    obtain ⟨n,b,trCfg,suffix,late⟩ := ih (stVar v (S k) op) updated L' (B+1) hL' fit'
    rw [step_run,stackOps_run]
    refine ⟨(S k).length+(updated k).length+2+n,b,trCfg,block.trans suffix,?_⟩
    have part : (S k).length+(updated k).length+2 ≤ 2*B+3 := by have := fit k; have := fit' k; omega
    have full := Nat.add_le_add part late
    apply full.trans
    unfold statementBudget
    rw [show B+1+stackOps q = B+(stackOps q+1) by omega]
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  | load fn q ih => exact ih (fn v) S L B hL fit
  | branch check left right ihL ihR =>
    cases test : check v
    · obtain ⟨n,b,h₁,h₂,h₃⟩ := ihR v S L B hL fit
      exact ⟨n,b,by simpa [TM2.stepAux,test] using h₁,
        by simpa [trNormal,TM1.stepAux,test] using h₂,
        h₃.trans (statementBudget_mono le_rfl (le_max_right (stackOps left) (stackOps right)))⟩
    · obtain ⟨n,b,h₁,h₂,h₃⟩ := ihL v S L B hL fit
      exact ⟨n,b,by simpa [TM2.stepAux,test] using h₁,
        by simpa [trNormal,TM1.stepAux,test] using h₂,
        h₃.trans (statementBudget_mono le_rfl (le_max_left (stackOps left) (stackOps right)))⟩
  | goto => exact ⟨0,_,⟨L,hL⟩,Steps.refl _ _,Nat.zero_le _⟩
  | halt => exact ⟨0,_,⟨L,hL⟩,Steps.refl _ _,Nat.zero_le _⟩

/-- A successful source transition is simulated by at most one controller
step plus the stated budget. It also increases the maximal stack bound by
at most the maximum syntactic number of selected stack operations. -/
theorem counted_step {source source' : TM2.Cfg Γ Λ σ} {target}
    (matched : TrCfg source target) (transition : TM2.step M source = some source')
    (B D : ℕ) (fit : ∀ k, (source.stk k).length ≤ B) (ops : ∀ l, stackOps (M l) ≤ D) :
    ∃ n target', TrCfg source' target' ∧ Steps (TM1.step (tr M)) n target target' ∧
      n ≤ 1+statementBudget B D ∧ ∀ k, (source'.stk k).length ≤ B+D := by
  obtain @⟨q,v,S,L,hL⟩ := matched
  cases q with
  | none => simp [TM2.step] at transition
  | some l =>
    have same : TM2.stepAux (M l) v S = source' := Option.some.inj transition
    subst source'
    obtain ⟨n,b,bMatch,walk,cost⟩ := counted_aux M (M l) v S L B hL fit
    have enter : Steps (TM1.step (tr M)) 1 ⟨some (Λ'.normal l),v,Tape.mk' ∅ (addBottom L)⟩
        (TM1.stepAux (trNormal (M l)) v (Tape.mk' ∅ (addBottom L))) := Steps.one rfl
    refine ⟨1+n,b,bMatch,enter.trans walk,?_,?_⟩
    · exact Nat.add_le_add_left (cost.trans (statementBudget_mono le_rfl (ops l))) _
    · intro j
      exact (stepAux_stack_bound (M l) v S B fit j).trans (Nat.add_le_add_left (ops l) _)

theorem Steps.head_inv {A : Type*} {f : A → Option A} {a b : A} {n : ℕ}
    (h : Steps f (n+1) a b) : ∃ mid, f a = some mid ∧ Steps f n mid b := by
  unfold Steps at h
  rw [Function.iterate_succ_apply] at h
  change (fun x : Option A => x.bind f)^[n] (f a) = some b at h
  cases hx : f a with
  | none =>
    rw [hx, Function.iterate_fixed (show (none : Option A).bind f = none from rfl)] at h
    cases h
  | some mid => exact ⟨mid,rfl,by simpa only [Steps,hx] using h⟩

/-- An N-transition stock TM2 run is simulated by the stock single-tape TM1
within a quadratic bound for a fixed machine and initial maximal stack size. -/
theorem counted_run {source source' : TM2.Cfg Γ Λ σ} {target}
    (N B D : ℕ) (matched : TrCfg source target)
    (sourceRun : Steps (TM2.step M) N source source') (fit : ∀ k, (source.stk k).length ≤ B)
    (ops : ∀ l, stackOps (M l) ≤ D) :
    ∃ n target', TrCfg source' target' ∧ Steps (TM1.step (tr M)) n target target' ∧
      n ≤ N*(1+statementBudget (B+D*N) D) := by
  induction N generalizing source target B with
  | zero =>
    have same : source = source' := Option.some.inj sourceRun
    subst source'
    exact ⟨0,target,matched,Steps.refl _ _,Nat.zero_le _⟩
  | succ N ih =>
    obtain ⟨mid,first,rest⟩ := sourceRun.head_inv
    obtain ⟨firstCost,mid',midMatch,firstRun,firstBound,midSpace⟩ := counted_step M matched first B D fit ops
    obtain ⟨restCost,target',targetMatch,restRun,restBound⟩ := ih (B+D) midMatch rest midSpace
    refine ⟨firstCost+restCost,target',targetMatch,firstRun.trans restRun,?_⟩
    have firstBound' : firstCost ≤ 1+statementBudget (B+D*(N+1)) D :=
      firstBound.trans (Nat.add_le_add_left (statementBudget_mono (Nat.le_add_right B _) le_rfl) _)
    rw [show B+D+D*N = B+D*(N+1) by rw [Nat.mul_succ]; omega] at restBound
    calc
      _ ≤ (1+statementBudget (B+D*(N+1)) D) + N*(1+statementBudget (B+D*(N+1)) D) :=
        Nat.add_le_add firstBound' restBound
      _ = _ := by rw [Nat.succ_mul, Nat.add_comm]

variable [Inhabited Λ] [Inhabited σ]

/-- The quantitative simulation begins with the stock translated input. -/
theorem counted_run_init (k : K) (input : List (Γ k))
    {source' : TM2.Cfg Γ Λ σ} (N D : ℕ)
    (sourceRun : Steps (TM2.step M) N (TM2.init k input) source')
    (ops : ∀ l, stackOps (M l) ≤ D) :
    ∃ n target', TrCfg source' target' ∧
      Steps (TM1.step (tr M)) n (TM1.init (trInit k input)) target' ∧
      n ≤ N*(1+statementBudget (input.length+D*N) D) := by
  apply counted_run M N input.length D (trCfg_init k input) sourceRun _ ops
  intro j
  change ((Function.update (fun i : K => ([] : List (Γ i))) k input) j).length ≤ input.length
  by_cases atInput : j = k
  · subst j
    rw [Function.update_self]
  · rw [Function.update_of_ne atInput]
    exact Nat.zero_le _

omit [DecidableEq K] [Inhabited Λ] [Inhabited σ] in
/-- For finitely many source labels, the machine syntax supplies a uniform bound. -/
theorem exists_stackOps_bound [Fintype Λ] : ∃ D, ∀ l, stackOps (M l) ≤ D := by
  classical
  exact ⟨Finset.univ.sup (fun l => stackOps (M l)), fun l => Finset.le_sup (f := fun l => stackOps (M l)) (Finset.mem_univ l)⟩

/-- A stock translated run can be bounded using the public Mathlib step-time
interface, and the matching target configuration also halts. -/
theorem counted_halt_in_time (k : K) (input : List (Γ k))
    {source' : TM2.Cfg Γ Λ σ} (T D : ℕ)
    (sourceRun : StateTransition.EvalsToInTime (TM2.step M) (TM2.init k input) (some source') T)
    (halt : TM2.step M source' = none) (ops : ∀ l, stackOps (M l) ≤ D) :
    ∃ target', TrCfg source' target' ∧ TM1.step (tr M) target' = none ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr M)) (TM1.init (trInit k input))
        (some target') (T*(1+statementBudget (input.length+D*T) D))) := by
  obtain ⟨n,target',matched,run,bound⟩ := counted_run_init M k input sourceRun.steps D
    sourceRun.evals_in_steps ops
  have terminates := tr_respects M matched
  rw [halt] at terminates
  refine ⟨target',matched,terminates,⟨⟨⟨n,run⟩,bound.trans ?_⟩⟩⟩
  apply Nat.mul_le_mul sourceRun.steps_le_m
  apply Nat.add_le_add_left (statementBudget_mono ?_ le_rfl)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left D sourceRun.steps_le_m) _

set_option backward.isDefEq.respectTransparency false in
private theorem finTM2_init (tm : FinTM2) (input : List (tm.Γ tm.k₀)) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    initList tm input = TM2.init tm.k₀ input := by
  unfold initList TM2.init
  congr 1
  funext j
  by_cases hit : j = tm.k₀
  · subst j
    rw [dif_pos rfl, Function.update_self]
    rfl
  · rw [dif_neg hit, Function.update_of_ne hit]

/-- Any bundled polynomial-time TM2 algorithm has stock translated TM1 runs
with a polynomial step bound in the original encoding length. -/
theorem _root_.solution {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (alg : TM2ComputableInPolyTime ea eb f) :
    let tm := alg.tm
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ p : Polynomial ℕ, ∀ a, ∃ target',
      TrCfg (haltList tm ((eb (f a)).map alg.outputAlphabet.invFun)) target' ∧
      TM1.step (tr tm.m) target' = none ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr tm.m))
        (TM1.init (trInit tm.k₀ ((ea a).map alg.inputAlphabet.invFun))) (some target')
        (p.eval (ea a).length)) := by
  let tm := alg.tm
  let _ : Inhabited tm.Λ := ⟨tm.main⟩
  let _ : Fintype tm.Λ := tm.ΛFin
  obtain ⟨D,ops⟩ := exists_stackOps_bound tm.m
  refine ⟨alg.time * (1 + Polynomial.C D * (2 * (Polynomial.X + Polynomial.C D * alg.time + Polynomial.C D) + 3)), ?_⟩
  intro a
  have time := alg.outputsFun a
  change StateTransition.EvalsToInTime (TM2.step tm.m) (initList tm ((ea a).map alg.inputAlphabet.invFun))
    (some (haltList tm ((eb (f a)).map alg.outputAlphabet.invFun))) (alg.time.eval (ea a).length) at time
  rw [finTM2_init] at time
  simpa only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_one,Polynomial.eval_ofNat,List.length_map,statementBudget,Nat.add_assoc]
    using counted_halt_in_time tm.m tm.k₀ ((ea a).map alg.inputAlphabet.invFun) (alg.time.eval (ea a).length)
      D time rfl ops

end PvsNP.StockSingleTapeTime

#print axioms solution
