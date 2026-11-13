-- Prove2me | solution 1 for RemovingTrees.Main.tree_removal_polytime
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:16:11.721892+00:00
-- url     : https://prove2.me/submissions/00a13e0e-5d2d-4aa7-9cd0-c2f948f5c742

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT014
import Definitions.Def_RemovingTrees_Main_GraphModel
import Theorems.Thm_OAI_AlgorithmicThinTrees_GraphicHalf_Stack_sparsify_program_polynomial_explicit
import Theorems.Thm_OAI_AlgorithmicThinTrees_GraphicHalf_sparsification_correct_explicit

section
-- module Solutions.OAIQ241_TT.Compat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_NaturalPolynomial
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23

namespace NaturalPolynomial

theorem eval_mono (p : NaturalPolynomial) : Monotone p.eval := by
  intro x y hxy
  induction p with
  | constant c => exact le_rfl
  | «variable» => exact hxy
  | add p q hp hq => exact Nat.add_le_add hp hq
  | mul p q hp hq => exact Nat.mul_le_mul hp hq
  | power p k hp => exact Nat.pow_le_pow_left hp k

end NaturalPolynomial
end KS.W23

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedStackMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01.FixedStack
open KS.W29 (StackAction polynomialFuel)

end KS.W01.FixedStack

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RoutineLength
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.RoutineLength
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

lemma action_length (a : KS.W29.StackAction) (w : List Bool) :
    (a.apply w).length≤w.length+1 := by
  cases a <;> simp [KS.W29.StackAction.apply]; omega

lemma step_length (M : KS.W01.FixedStack.Machine) (s : KS.W01.FixedStack.Config M.stackCount M.states) (b : Bool)
    (j : Fin M.stackCount) : ((M.step s b).«stacks» j).length ≤ (s.«stacks» j).length+1 := by
  rcases s with ⟨control,tapes⟩
  cases control with
  | none => simp [KS.W01.FixedStack.Machine.step]
  | some c => exact action_length _ _

lemma run_length (M : KS.W01.FixedStack.Machine) (s : KS.W01.FixedStack.Config M.stackCount M.states) (bits : List Bool)
    (j : Fin M.stackCount) : ((M.run s bits).«stacks» j).length ≤ (s.«stacks» j).length+bits.length := by
  induction bits generalizing s with
  | nil => simp [KS.W01.FixedStack.Machine.run]
  | cons b bs ih =>
    have h := ih (M.step s b)
    have hs := step_length M s b j
    simp only [KS.W01.FixedStack.Machine.run,List.length_cons]
    omega

lemma output_length {k : ℕ} {P : Program k} {before after : Fin k → List Bool} {ticks : ℕ}
    (h : RunSpec P before after ticks) (j : Fin k) :
    (after j).length≤(before j).length+ticks := by
  have hr := run_length P.toMachine ⟨some P.initial,before⟩ (List.replicate ticks false) j
  rw [h _ (List.length_replicate ..)] at hr
  simpa using hr

end CurrentKS.RoutineLength

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoutine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

variable {α β γ δ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word} {ed : δ → Word}
  {f : α → β} {g : β → γ}

lemma Realizes.output_length (r : Realizes ea eb f) (x : α) :
    (eb (f x)).length≤(ea x).length+r.cost x := by
  have h := RoutineLength.output_length (r.routine.spec x) 0
  simpa only [io_zero] using h

lemma prodCode_length (p : α×β) : (prodCode ea eb p).length=2*(ea p.1).length+1+(eb p.2).length := by
  simp only [prodCode,PairRoutine.pair,List.length_append,KS.W01.length_frame]
lemma le_prodCode_left (p : α×β) : (ea p.1).length≤(prodCode ea eb p).length := by rw [prodCode_length];omega
lemma le_prodCode_right (p : α×β) : (eb p.2).length≤(prodCode ea eb p).length := by rw [prodCode_length];omega

instance poly_first (ea : α → Word) (eb : β → Word) : PolyTime (first ea eb) := by
  refine ⟨⟨6*X+5,?_⟩⟩
  intro p
  have h1 := le_prodCode_left (ea:=ea) (eb:=eb) p
  have h2 := le_prodCode_right (ea:=ea) (eb:=eb) p
  change 5*(ea p.1).length+(eb p.2).length+5≤6*(prodCode ea eb p).length+5
  omega
instance poly_second (ea : α → Word) (eb : β → Word) : PolyTime (second ea eb) := by
  refine ⟨⟨4*X+3,?_⟩⟩
  intro p
  have h1 := le_prodCode_left (ea:=ea) (eb:=eb) p
  change 4*(ea p.1).length+3≤4*(prodCode ea eb p).length+3
  omega
instance poly_then (r : Realizes ea eb f) (s : Realizes eb ec g) [PolyTime r] [PolyTime s] :
    PolyTime (r.then s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨p+q.comp (X+p),?_⟩⟩
  intro x
  have hl := r.output_length x
  have hs := (hq (f x)).trans (q.eval_mono (hl.trans (Nat.add_le_add_left (hp x) _)))
  have hh := Nat.add_le_add (hp x) hs
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_comp,NaturalPolynomial.eval_variable]
  exact hh
instance poly_both {g : α → γ} (r : Realizes ea eb f) (s : Realizes ea ec g) [PolyTime r] [PolyTime s] :
    PolyTime (r.both s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨16*X+13*p+q+15,?_⟩⟩
  intro x
  have hl := r.output_length x
  have h1 := hp x
  have h2 := hq x
  change PairRoutine.pairingTicks ea (fun x => eb (f x)) r.cost s.cost x≤
    16*(ea x).length+13*p.eval (ea x).length+q.eval (ea x).length+15
  simp only [PairRoutine.pairingTicks,KS.W01.length_frame]
  omega

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ListRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

variable {α β γ : Type*}

lemma fold_cons (xs ys : List α) : xs.foldl (fun acc x => x::acc) ys=xs.reverse++ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialLoops
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
attribute [-simp] _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word}

lemma len_listCode (ea : α → Word) (xs : List α) :
    (listCode ea xs).length=(xs.map (fun x => 2*(ea x).length+1)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listCode_cons,prodCode_length,List.map_cons,List.sum_cons,ih]
lemma sum_map_bound (xs : List α) (f : α → ℕ) (B : ℕ) (h : ∀ x∈xs,f x≤B) :
    (xs.map f).sum≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
lemma listCode_length_bound (xs : List α) (B : ℕ) (h : ∀ x∈xs,(ea x).length≤B) :
    (listCode ea xs).length≤xs.length*(2*B+1) := by
  rw [len_listCode]
  apply sum_map_bound
  intro x hx
  have := h x hx
  omega
lemma list_length_le_code (ea : α → Word) (xs : List α) : xs.length≤(listCode ea xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listCode_cons,prodCode_length,List.length_cons];omega
lemma mem_length_le_code (xs : List α) {x : α} (hx : x∈xs) :
    (ea x).length≤(listCode ea xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rw [listCode_cons,prodCode_length]
      dsimp only
      rcases hx with rfl|hx
      · omega
      · have := ih hx;omega
lemma listCode_reverse_length (ea : α → Word) (xs : List α) :
    (listCode ea xs.reverse).length=(listCode ea xs).length := by
  simp only [len_listCode,List.map_reverse,List.sum_reverse]

instance poly_map {f : α → β} (r : Realizes ea eb f) [PolyTime r] : PolyTime r.map := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  let Q := X+p
  refine ⟨⟨2*X+X*(3*X+p+6*Q+8)+X*(2*Q+1)+4,?_⟩⟩
  intro xs
  let L := (listCode ea xs).length
  have hn : xs.length≤L := list_length_le_code ea xs
  have ho : ∀ x∈xs,(eb (f x)).length≤L+p.eval L := by
    intro x hx
    have hl : (ea x).length≤L := mem_length_le_code xs hx
    exact (r.output_length x).trans (Nat.add_le_add hl ((hp x).trans (p.eval_mono hl)))
  have hs := sum_map_bound xs (fun x => FramedMapRoutine.bodyTicks ea (fun x => eb (f x)) r.cost x+1)
    (3*L+p.eval L+6*(L+p.eval L)+8) (by
      intro x hx
      have hl : (ea x).length≤L := mem_length_le_code xs hx
      have hc := (hp x).trans (p.eval_mono hl)
      have hout := ho x hx
      simp only [FramedMapRoutine.bodyTicks,KS.W01.length_frame]
      omega)
  have ht := listCode_length_bound (ea:=fun x => eb (f x)) xs (L+p.eval L) ho
  have hs' := hs.trans (Nat.mul_le_mul_right _ hn)
  have ht' := ht.trans (Nat.mul_le_mul_right _ hn)
  change FramedMapRoutine.ticks ea (fun x => eb (f x)) r.cost xs≤_
  simp only [FramedMapRoutine.ticks,FramedMapRoutine.scanTicks]
  change 2*L+2+((xs.map _).sum+1)+(listCode (fun x => eb (f x)) xs).length+1≤_
  change _≤2*L+L*(3*L+p.eval L+6*(L+p.eval L)+8)+L*(2*(L+p.eval L)+1)+4
  omega

lemma fold_scan_bound (F : α → β → α) (cost : α×β → ℕ) (s : α) (xs : List β) (S E C : ℕ)
    (hs : ∀ ys zs,xs=ys++zs → (ea (ys.foldl F s)).length≤S)
    (he : ∀ x∈xs,(eb x).length≤E)
    (hc : ∀ a x,(ea a).length≤S → (eb x).length≤E → cost (a,x)≤C) :
    FoldRoutine.scanTicks ea eb F cost s xs≤xs.length*(3*E+10*S+C+12)+1 := by
  induction xs generalizing s with
  | nil => simp [FoldRoutine.scanTicks]
  | cons x xs ih =>
      have h0 := hs [] (x::xs) rfl
      have h1 := hs [x] xs rfl
      have hx := he x (by simp)
      have hc0 := hc s x h0 hx
      have ht := ih (F s x) (by
        intro ys zs hz
        have h := hs (x::ys) zs (by simp only [List.cons_append];rw [hz])
        simpa only [List.foldl_cons] using h) (fun y hy => he y (by simp [hy]))
      simp only [FoldRoutine.scanTicks,FoldRoutine.bodyTicks,KS.W01.length_frame,List.length_cons,Nat.add_mul,Nat.one_mul]
      simp only [List.foldl_nil,List.foldl_cons] at h0 h1
      omega

instance poly_fold {f : α×β → α} (r : Realizes (prodCode ea eb) ea f) [PolyTime r] [FoldSize r] :
    PolyTime r.fold := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := FoldSize.bound (r:=r)
  refine ⟨⟨5*q+2*X+X*(3*X+10*q+p.comp (2*q+1+X)+12)+7,?_⟩⟩
  intro u
  let L := (prodCode ea (listCode eb) u).length
  let S := q.eval L
  have he : (listCode eb u.2).length≤L := le_prodCode_right u
  have hn := (list_length_le_code eb u.2).trans he
  have hs := hq u.1 u.2
  have h0 : (ea u.1).length≤S := hs [] u.2 rfl
  have hN : (ea (u.2.foldl (fun a b => f (a,b)) u.1)).length≤S := hs u.2 [] (by simp)
  have hc : ∀ a x,(ea a).length≤S → (eb x).length≤L → r.cost (a,x)≤p.eval (2*S+1+L) := by
    intro a x ha hx
    apply (hp (a,x)).trans (p.eval_mono ?_)
    rw [prodCode_length]
    dsimp only
    omega
  have hscan := fold_scan_bound (ea:=ea) (eb:=eb) (fun a b => f (a,b)) r.cost u.1 u.2 S L
    (p.eval (2*S+1+L)) hs (fun x hx => (mem_length_le_code u.2 hx).trans he) hc
  have hscan' := hscan.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  change FoldRoutine.ticks ea eb (fun a b => f (a,b)) r.cost u.1 u.2≤_
  simp only [FoldRoutine.ticks]
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
  change _≤5*S+2*L+L*(3*L+10*S+p.eval (2*S+1+L)+12)+7
  change _≤_ at hscan'
  change (FramedMapRoutine.tape eb u.2).length≤L at he
  omega

lemma iterate_ticks_bound {f : α → α} (r : Realizes ea ea f) (x : α) (n C : ℕ)
    (h : ∀ i,i<n → r.cost (f^[i] x)≤C) :
    IterateRoutine.loopTicks r.cost f n x≤n*(C+2)+1 := by
  induction n generalizing x with
  | zero => simp [IterateRoutine.loopTicks]
  | succ n ih =>
      have h0 := h 0 (by omega)
      have ht := ih (f x) (by
        intro i hi
        simpa only [←Function.iterate_succ_apply] using h (i+1) (by omega))
      simp only [Function.iterate_zero, id_eq] at h0
      simp only [IterateRoutine.loopTicks,Nat.add_mul,Nat.one_mul]
      omega
instance poly_iterate {f : α → α} (r : Realizes ea ea f) [PolyTime r] [IterateSize r] :
    PolyTime r.iterate := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := IterateSize.bound (r:=r)
  refine ⟨⟨3*X+X*(p.comp q+2)+3,?_⟩⟩
  intro u
  let L := (prodCode natCode ea u).length
  have hi : (ea u.2).length+u.1≤L := by simp only [L,prodCode_length,natCode,List.length_replicate];omega
  have hn : u.1≤L := by omega
  have ht := iterate_ticks_bound r u.2 u.1 (p.eval (q.eval L)) (by
    intro i hi'
    exact (hp _).trans (p.eval_mono ((hq u.2 i).trans (q.eval_mono (by omega)))))
  have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
  change 3*u.1+2+IterateRoutine.loopTicks r.cost f u.1 u.2≤3*L+L*(p.eval (q.eval L)+2)+3
  omega
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ArrayRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α γ : Type*}

lemma fold_length (xs : List α) (n : ℕ) : xs.foldl (fun k _ => k+1) n=n+xs.length := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_comm,Nat.add_left_comm]

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialLists
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma prefix_code_length (ea : α → Word) (xs ys zs : List α) (h : xs=ys++zs) :
    (listCode ea ys).length≤(listCode ea xs).length := by
  rw [h,listCode_append,List.length_append];omega
lemma prefix_length (xs ys zs : List α) (h : xs=ys++zs) : ys.length≤xs.length := by
  rw [h,List.length_append];omega

instance poly_appendList (ea : α → Word) : PolyTime (appendList ea) := by
  refine ⟨⟨5*X+4,?_⟩⟩
  intro p
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 5 (le_prodCode_left p)) 4
instance poly_reverseBody (ea : α → Word) : PolyTime (reverseBody ea) := by
  unfold reverseBody;infer_instance
instance size_reverseBody (ea : α → Word) : FoldSize (reverseBody ea) := by
  refine ⟨⟨X,?_⟩⟩
  intro s xs ys zs h
  rw [fold_cons,listCode_append,List.length_append,listCode_reverse_length]
  have hp := prefix_code_length ea xs ys zs h
  change _≤(prodCode (listCode ea) (listCode ea) (s,xs)).length
  rw [prodCode_length]
  try dsimp only
  omega
instance poly_reverseList (ea : α → Word) : PolyTime (reverseList ea) := by
  unfold reverseList;infer_instance

instance poly_mapCtxBody {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    PolyTime (mapCtxBody ec ea eb r) := by
  dsimp only [mapCtxBody]
  apply poly_both
instance size_mapCtxBody {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    FoldSize (mapCtxBody ec ea eb r) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  let U := 3*X+1+p.comp (3*X+1)
  refine ⟨⟨3*X+1+X*(2*U+1),?_⟩⟩
  intro s xs ys zs h
  rw [fold_mapCtx]
  let L := (prodCode (prodCode ec (listCode eb)) (listCode ea) (s,xs)).length
  have hc : (ec s.1).length≤L := (le_prodCode_left s).trans (le_prodCode_left (s,xs))
  have ha : (listCode eb s.2).length≤L := (le_prodCode_right s).trans (le_prodCode_left (s,xs))
  have he : (listCode ea ys).length≤L := (prefix_code_length ea xs ys zs h).trans (le_prodCode_right (s,xs))
  have hn : ys.length≤L := (list_length_le_code ea ys).trans he
  have ho : ∀ x∈ys,(eb (f (s.1,x))).length≤3*L+1+p.eval (3*L+1) := by
    intro x hx
    have hl : (prodCode ec ea (s.1,x)).length≤3*L+1 := by
      have he' := (mem_length_le_code ys hx).trans he
      simp only [prodCode_length]
      try dsimp only
      omega
    exact (r.output_length (s.1,x)).trans (Nat.add_le_add hl ((hp _).trans (p.eval_mono hl)))
  have hm := listCode_length_bound (ea:=fun x => eb (f (s.1,x))) ys (3*L+1+p.eval (3*L+1)) ho
  have hm' := hm.trans (Nat.mul_le_mul_right _ hn)
  have heq : listCode eb (ys.map (fun x => f (s.1,x)))=listCode (fun x => eb (f (s.1,x))) ys := by
    simp only [listCode,FramedMapRoutine.tape,List.flatMap_map]
  rw [prodCode_length]
  dsimp only
  rw [listCode_append,List.length_append,listCode_reverse_length,heq]
  change 2*(ec s.1).length+1+((listCode (fun x => eb (f (s.1,x))) ys).length+(listCode eb s.2).length)≤_
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp,U]
  change _≤3*L+1+L*(2*(3*L+1+p.eval (3*L+1))+1)
  omega
instance poly_mapCtx {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    PolyTime r.mapCtx := by
  unfold Realizes.mapCtx
  infer_instance

instance poly_natAdd : PolyTime natAdd := by
  refine ⟨⟨5*X+4,?_⟩⟩
  intro p
  have h := le_prodCode_left (ea:=natCode) (eb:=natCode) p
  simp only [natCode,List.length_replicate] at h
  change 5*p.1+4≤5*(prodCode natCode natCode p).length+4
  omega

instance poly_rangeStep : PolyTime rangeStepRealizes := by dsimp only [rangeStepRealizes];apply poly_both
lemma range_iterate_size (s : ℕ×List ℕ) (k : ℕ) :
    (rangeStep^[k] s).1=s.1+k ∧
    (listCode natCode (rangeStep^[k] s).2).length≤(listCode natCode s.2).length+k*(2*(s.1+k)+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change (rangeStep^[k] s).1+1=s.1+(k+1) ∧ _
      constructor
      · omega
      · change (listCode natCode ((rangeStep^[k] s).1::(rangeStep^[k] s).2)).length≤_
        rw [listCode_cons,prodCode_length]
        simp only [natCode,List.length_replicate]
        try dsimp only
        nlinarith [ih.2]
instance size_rangeStep : IterateSize rangeStepRealizes := by
  refine ⟨⟨10*(X+1)^2,?_⟩⟩
  intro s k
  have h := range_iterate_size s k
  simp only [prodCode_length,natCode,List.length_replicate]
  change 2*(rangeStep^[k] s).1+1+(listCode natCode (rangeStep^[k] s).2).length≤10*(2*s.1+1+(listCode natCode s.2).length+k+1)^2
  rw [h.1]
  nlinarith [h.2]
instance poly_range : PolyTime range := by unfold range;infer_instance

instance poly_lengthBody (ea : α → Word) : PolyTime ((first natCode ea).then natSucc) := by infer_instance
instance size_lengthBody (ea : α → Word) : FoldSize ((first natCode ea).then natSucc) := by
  refine ⟨⟨2*X,?_⟩⟩
  intro s xs ys zs h
  change (natCode (ys.foldl (fun k _ => k+1) s)).length≤_
  rw [fold_length]
  have hs := le_prodCode_left (ea:=natCode) (eb:=listCode ea) (s,xs)
  have hn := ((prefix_length xs ys zs h).trans (list_length_le_code ea xs)).trans (le_prodCode_right (ea:=natCode) (s,xs))
  simp only [natCode,List.length_replicate] at hs ⊢
  change s+ys.length≤2*(prodCode natCode (listCode ea) (s,xs)).length
  omega
instance poly_lengthList (ea : α → Word) : PolyTime (lengthList ea) := by unfold lengthList;infer_instance
instance poly_tabulate {f : γ×ℕ → α} (r : Realizes (prodCode ec natCode) ea f) [PolyTime r] :
    PolyTime r.tabulate := by unfold Realizes.tabulate;infer_instance

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialScalar
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_iterate _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_map _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

instance poly_ratOp (op : KS.W13.ExpressionMachine.BinaryOp) : PolyTime (ratOp op) := by
  refine ⟨⟨5*X+6000000*(X+1)^3+6,?_⟩⟩
  intro p
  have hl := RoutineLength.output_length (KS.W13.ExpressionMachine.binaryArithmetic_spec op p.1 p.2 [] []) 10
  have ht : (ratCode (op.eval p.1 p.2)).length≤KS.W13.ExpressionMachine.binaryBudget p.1 p.2 := by simpa [KS.W13.ExpressionMachine.registers] using hl
  have hi : (ratCode p.1).length+(ratCode p.2).length ≤ (prodCode ratCode ratCode p).length := by rw [prodCode_length];omega
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 3
  have ha := le_prodCode_left (ea:=ratCode) (eb:=ratCode) p
  change ArithmeticRoutine.ticks op p.1 p.2≤5*(prodCode ratCode ratCode p).length+6000000*((prodCode ratCode ratCode p).length+1)^3+6
  simp only [ArithmeticRoutine.ticks,ArithmeticRoutine.encode,KS.W13.ExpressionMachine.binaryBudget,KS.W01.ratLength] at ht ⊢
  simp only [ratCode] at *
  omega

instance poly_ratLE : PolyTime ratLE := by
  refine ⟨⟨5*X+2048*(X+1)^2+8,?_⟩⟩
  intro p
  have hi : (ratCode p.1).length+(ratCode p.2).length ≤ (prodCode ratCode ratCode p).length := by rw [prodCode_length];omega
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 2
  have ha := le_prodCode_left (ea:=ratCode) (eb:=ratCode) p
  change CompareRoutine.ticks p.1 p.2≤5*(prodCode ratCode ratCode p).length+2048*((prodCode ratCode ratCode p).length+1)^2+8
  simp only [CompareRoutine.ticks,CompareRoutine.encode,KS.W29.polynomialFuel,List.length_append]
  simp only [ratCode] at *
  omega

instance poly_ratFloor : PolyTime ratFloor := by
  refine ⟨⟨192*(X+1)^2+2,?_⟩⟩
  intro q
  have hl := RoutineLength.output_length (KS.W20.FloorRationalMachine.polynomial_spec q) 5
  have ht : (ratCode (⌊q⌋ : ℚ)).length≤64*((ratCode q).length+1)^2 := by
    simpa [KS.W20.FloorRationalMachine.state,KS.W19.SignedFloorMachine.«stacks»,KS.W29.polynomialFuel] using hl
  change FloorCleanRoutine.ticks q≤192*((ratCode q).length+1)^2+2
  simp only [FloorCleanRoutine.ticks,KS.W29.polynomialFuel,FloorCleanRoutine.encode]
  simp only [ratCode] at *
  omega

variable {α β : Type*} {ea : α → Word} {eb : β → Word}
instance poly_conditional {f g : α → β} (r : Realizes ea eb f) (s : Realizes ea eb g)
    [PolyTime r] [PolyTime s] : PolyTime (conditional r s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨p+q+6,?_⟩⟩
  intro x
  have hr := (hp x.2).trans (p.eval_mono (le_prodCode_right (ea:=boolCode) (eb:=ea) x))
  have hs := (hq x.2).trans (q.eval_mono (le_prodCode_right (ea:=boolCode) (eb:=ea) x))
  change 5+(if x.1 then r.cost x.2 else s.cost x.2)+1≤p.eval _+q.eval _+6
  split <;> omega
instance poly_ite {p : α → Bool} {f g : α → β} (b : Realizes ea boolCode p)
    (r : Realizes ea eb f) (s : Realizes ea eb g) [PolyTime b] [PolyTime r] [PolyTime s] : PolyTime (b.ite r s) := by unfold Realizes.ite; exact poly_then (b.both (identity ea)) (conditional r s)
instance poly_add {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.add s) := by unfold Realizes.add; exact poly_then (r.both s) (ratOp .add)
instance poly_sub {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.sub s) := by unfold Realizes.sub; exact poly_then (r.both s) (ratOp .sub)
instance poly_mul {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.mul s) := by unfold Realizes.mul; exact poly_then (r.both s) (ratOp .mul)
instance poly_div {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.div s) := by unfold Realizes.div; exact poly_then (r.both s) (ratOp .div)
instance poly_le {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.le s) := by unfold Realizes.le;infer_instance
instance poly_neg {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.neg := by unfold Realizes.neg;infer_instance
instance poly_abs {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.abs := by unfold Realizes.abs;infer_instance
instance poly_roundScalar : PolyTime roundScalar := by unfold roundScalar;infer_instance
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialArrays
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

instance poly_lookupStep (ea : α → Word) : PolyTime (lookupStepRealizes ea) := by
  dsimp only [lookupStepRealizes]
  apply poly_congr
lemma lookup_fold_size (ea : α → Word) (s : ℕ×α) (xs : List α) (K B : ℕ)
    (hk : s.1≤K) (ha : (ea s.2).length≤B) (hx : ∀x∈xs,(ea x).length≤B) :
    (xs.foldl (fun s x => lookupStep (s,x)) s).1≤K ∧
    (ea (xs.foldl (fun s x => lookupStep (s,x)) s).2).length≤B := by
  induction xs generalizing s with
  | nil => exact ⟨hk,ha⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      apply ih
      · dsimp only [lookupStep]
        split_ifs <;> (try dsimp only) <;> omega
      · dsimp only [lookupStep]
        split_ifs <;> try dsimp only
        · exact ha
        · exact hx x (by simp)
        · exact ha
      · intro y hy;exact hx y (by simp [hy])
instance size_lookupStep (ea : α → Word) : FoldSize (lookupStepRealizes ea) := by
  refine ⟨⟨3*X+1,?_⟩⟩
  intro s xs ys zs h
  let L := (prodCode (prodCode natCode ea) (listCode ea) (s,xs)).length
  have hk : s.1≤L := by
    have hl := (le_prodCode_left (ea:=natCode) (eb:=ea) s).trans (le_prodCode_left (eb:=listCode ea) (s,xs))
    simpa only [natCode,List.length_replicate] using hl
  have ha : (ea s.2).length≤L := (le_prodCode_right s).trans (le_prodCode_left (s,xs))
  have hy : (listCode ea ys).length≤L := (prefix_code_length ea xs ys zs h).trans (le_prodCode_right (s,xs))
  have ht := lookup_fold_size ea s ys L L hk ha (fun x hx => (mem_length_le_code ys hx).trans hy)
  change (prodCode natCode ea _).length≤3*L+1
  rw [prodCode_length]
  simp only [natCode,List.length_replicate]
  omega
instance poly_getD (ea : α → Word) (a : α) : PolyTime (getD ea a) := by unfold getD;infer_instance

instance poly_zipWith {f : α×β → γ} (r : Realizes (prodCode ea eb) ec f) (a : α) (b : β)
    [PolyTime r] : PolyTime (r.zipWith a b) := by unfold Realizes.zipWith;apply poly_then
instance poly_vectorAdd : PolyTime vectorAdd := by unfold vectorAdd;infer_instance
instance poly_vectorScaleBody : PolyTime vectorScaleBody := by unfold vectorScaleBody;exact poly_ratOp .mul
instance poly_vectorScale : PolyTime vectorScale := by unfold vectorScale;infer_instance
instance poly_matrixAdd : PolyTime matrixAdd := by unfold matrixAdd;infer_instance
instance poly_matrixScale : PolyTime matrixScale := by unfold matrixScale;infer_instance

lemma ratLength_natCast (n : ℕ) : KS.W01.ratLength (n : ℚ)≤4*n+11 := by
  apply (KS.W01.ratLength_le_of_parts (n : ℚ) n n ?_ ?_).trans (by omega)
  · simpa only [Rat.num_natCast,Int.natAbs_natCast] using (Nat.le_of_lt (Nat.lt_two_pow_self (n:=n)))
  · simpa only [Rat.den_natCast] using (Nat.one_le_two_pow (n:=n))
instance size_ratSucc : IterateSize ((identity ratCode).add (constant ratCode ratCode 1)) := by
  refine ⟨⟨20*X+60,?_⟩⟩
  intro q n
  change (ratCode ((fun x : ℚ => x+1)^[n] q)).length≤_
  rw [iterate_ratSucc]
  have h := KS.W01.ratLength_add_le q (n : ℚ)
  have hn := ratLength_natCast n
  change KS.W01.ratLength (q+(n : ℚ))≤20*(KS.W01.ratLength q+n)+60
  omega
instance poly_natToRat : PolyTime natToRat := by unfold natToRat;infer_instance
instance size_natMulStep : IterateSize ((first natCode natCode).both natAdd) := by
  refine ⟨⟨10*(X+1)^2,?_⟩⟩
  intro s n
  change (prodCode natCode natCode ((fun a : ℕ×ℕ => (a.1,a.1+a.2))^[n] s)).length≤_
  rcases s with ⟨k,z⟩
  rw [fold_natAdd]
  simp only [prodCode_length,natCode,List.length_replicate]
  change 2*k+1+(n*k+z)≤10*(2*k+1+z+n+1)^2
  nlinarith
instance poly_natMul : PolyTime natMul := by unfold natMul;infer_instance
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_iterate _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_map _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_natToRat _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratFloor _root_.OAI.CurrentKS.Realization.poly_ratLE _root_.OAI.CurrentKS.Realization.poly_ratOp _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundScalar _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_natMulStep _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {ι α β γ : Type*} {L f g : ι → ℕ}

lemma IsPoly.mono (hf : IsPoly L f) (h : ∀i,g i≤f i) : IsPoly L g := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun i => (h i).trans (hp i)⟩
lemma IsPoly.add (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i+g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,fun i => Nat.add_le_add (hp i) (hq i)⟩
lemma IsPoly.mul (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i*g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,fun i => Nat.mul_le_mul (hp i) (hq i)⟩
lemma isPoly_const (L : ι → ℕ) (c : ℕ) : IsPoly L (fun _ => c) := ⟨.constant c,fun _ => le_rfl⟩
lemma isPoly_self (L : ι → ℕ) : IsPoly L L := ⟨X,fun _ => le_rfl⟩
lemma IsPoly.eval (hf : IsPoly L f) (p : NaturalPolynomial) : IsPoly L (fun i => p.eval (f i)) := by
  obtain ⟨q,hq⟩ := hf
  exact ⟨p.comp q,fun i => by simpa only [NaturalPolynomial.eval_comp] using p.eval_mono (hq i)⟩
lemma IsPoly.reindex {κ : Type*} (hf : IsPoly L f) (a : κ → ι) : IsPoly (L ∘ a) (f ∘ a) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun i => hp (a i)⟩

variable {ea : α → Word} {eb : β → Word} {ec : γ → Word} {F : α → β} {G : β → γ}

lemma RunsPoly.of_poly (r : Realizes ea eb F) [PolyTime r] (a : ι → α)
    (h : IsPoly L (fun i => (ea (a i)).length)) : RunsPoly L r a := by
  refine ⟨h,?_⟩
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  exact (h.eval p).mono (fun i => hp (a i))
lemma RunsPoly.output {r : Realizes ea eb F} {a : ι → α} (h : RunsPoly L r a) :
    IsPoly L (fun i => (eb (F (a i))).length) := (h.input.add h.cost).mono (fun i => r.output_length (a i))
lemma RunsPoly.then {r : Realizes ea eb F} {s : Realizes eb ec G} {a : ι → α}
    (hr : RunsPoly L r a) (hs : RunsPoly L s (fun i => F (a i))) : RunsPoly L (r.then s) a :=
  ⟨hr.input,hr.cost.add hs.cost⟩
lemma RunsPoly.then_poly {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    (s : Realizes eb ec G) [PolyTime s] : RunsPoly L (r.then s) a :=
  hr.then (RunsPoly.of_poly s _ hr.output)
lemma RunsPoly.both {G : α → γ} {r : Realizes ea eb F} {s : Realizes ea ec G} {a : ι → α}
    (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.both s) a := by
  refine ⟨hr.input,?_⟩
  have h := (((((isPoly_const L 4).mul hr.input).add ((isPoly_const L 12).mul hr.output)).add hr.cost).add hs.cost).add (isPoly_const L 15)
  apply h.mono
  intro i
  change PairRoutine.pairingTicks ea (fun x => eb (F x)) r.cost s.cost (a i)≤_
  simp only [PairRoutine.pairingTicks,KS.W01.length_frame]
  omega
lemma RunsPoly.congr {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    {F' : α → β} (h : ∀x,F x=F' x) : RunsPoly L (r.congr h) a := by
  have he : F=F' := funext h
  subst F'
  exact hr
lemma RunsPoly.changeOutput {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    {δ : Type*} (ed : δ → Word) (g : α → δ) (h : ∀x,eb (F x)=ed (g x)) :
    RunsPoly L (r.changeOutput ed g h) a := ⟨hr.input,hr.cost⟩
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialBranchFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_iterate _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_map _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratLE _root_.OAI.CurrentKS.Realization.poly_ratOp _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundScalar _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_natMulStep _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_ratSucc _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}
lemma isPoly_dite {P : ι → Prop} [DecidablePred P] {f : (i : ι) → P i → ℕ}
    {g : (i : ι) → ¬P i → ℕ}
    (hf : IsPoly (fun i : {i // P i} => L i.val) (fun i => f i.val i.property))
    (hg : IsPoly (fun i : {i // ¬P i} => L i.val) (fun i => g i.val i.property)) :
    IsPoly L (fun i => if h : P i then f i h else g i h) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  refine ⟨p+q,?_⟩
  intro i
  by_cases h : P i
  · simp only [dite_eq_left h]
    exact (hp ⟨i,h⟩).trans (Nat.le_add_right _ _)
  · simp only [dite_eq_right h]
    exact (hq ⟨i,h⟩).trans (Nat.le_add_left _ _)

lemma RunsPoly.ite_on {P : α → Bool} {F G : α → β} {b : Realizes ea boolCode P}
    {r : Realizes ea eb F} {s : Realizes ea eb G} {a : ι → α}
    (hb : RunsPoly L b a)
    (hc : IsPoly L (fun i => if P (a i) then r.cost (a i) else s.cost (a i))) :
    RunsPoly L (b.ite r s) a := by
  unfold Realizes.ite
  have ht := hb.both (RunsPoly.of_poly (identity ea) a hb.input)
  apply ht.then
  refine ⟨ht.output,?_⟩
  have h := ((isPoly_const L 5).add hc).add (isPoly_const L 1)
  simp only [Nat.add_assoc] at h ⊢
  exact h

lemma RunsPoly.dite_on {P : α → Prop} [DecidablePred P]
    {F : {a // P a} → β} {G : {a // ¬P a} → β}
    {b : Realizes ea boolCode (fun a => decide (P a))}
    {r : Realizes (fun a : {a // P a} => ea a.val) eb F}
    {s : Realizes (fun a : {a // ¬P a} => ea a.val) eb G} {a : ι → α}
    (hb : RunsPoly L b a)
    (hc : IsPoly L (fun i => if h : P (a i) then r.cost ⟨a i,h⟩ else s.cost ⟨a i,h⟩)) :
    RunsPoly L (b.dite r s) a := by
  unfold Realizes.dite
  have ht := (hb.both (RunsPoly.of_poly (identity ea) a hb.input)).changeOutput
    (fun x => prodCode boolCode ea (decide (P x),x)) id (fun _ => rfl)
  apply ht.then
  refine ⟨ht.output,?_⟩
  have h := ((isPoly_const L 5).add hc).add (isPoly_const L 1)
  simp only [Nat.add_assoc] at h ⊢
  exact h
lemma RunsPoly.dite_families {P : α → Prop} [DecidablePred P]
    {F : {a // P a} → β} {G : {a // ¬P a} → β}
    {b : Realizes ea boolCode (fun a => decide (P a))}
    {r : Realizes (fun a : {a // P a} => ea a.val) eb F}
    {s : Realizes (fun a : {a // ¬P a} => ea a.val) eb G} {a : ι → α}
    (hb : RunsPoly L b a)
    (hr : RunsPoly (fun i : {i // P (a i)} => L i.val) r (fun i => ⟨a i.val,i.property⟩))
    (hs : RunsPoly (fun i : {i // ¬P (a i)} => L i.val) s (fun i => ⟨a i.val,i.property⟩)) :
    RunsPoly L (b.dite r s) a := hb.dite_on (isPoly_dite hr.cost hs.cost)
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCoordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*} {ea : α → Word}
local instance coordinates_natLE : PolyTime natLE := by unfold natLE;infer_instance

local instance coordinates_natEq_ra5a355_1 : PolyTime natEq := by unfold natEq;infer_instance
local instance coordinates_matrixEntry_ra5a355_1 : PolyTime matrixEntry := by unfold matrixEntry;infer_instance
local instance coordinates_matrixTabulate_ra5a355_1 {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime r.matrixTabulate := by unfold Realizes.matrixTabulate;apply poly_then
local instance coordinates_identityEntry_ra5a355_1 : PolyTime identityEntry := by unfold identityEntry;infer_instance
local instance coordinates_identityMatrix_ra5a355_1 : PolyTime identityMatrix := by unfold identityMatrix;apply poly_then
local instance coordinates_fromBlocks_ra5a355_1 : PolyTime fromBlocks := by unfold fromBlocks;apply poly_then
instance poly_natLT : PolyTime natLT := by unfold natLT;infer_instance
instance poly_scaleMatrix {f : α → ℚ} {g : α → MatrixData}
    (r : Realizes ea ratCode f) (s : Realizes ea matrixCode g) [PolyTime r] [PolyTime s] :
    PolyTime (r.scaleMatrix s) := by unfold Realizes.scaleMatrix;apply poly_then
instance poly_negateMatrix : PolyTime negateMatrix := by unfold negateMatrix;infer_instance
instance poly_singletonList (ea : α → Word) : PolyTime (singletonList ea) := by unfold singletonList;apply poly_then
instance poly_replicateList (ea : α → Word) : PolyTime (replicateList ea) := by unfold replicateList;infer_instance
instance poly_blockScalar : PolyTime blockScalar := by unfold blockScalar;apply poly_then
instance poly_withLevel : PolyTime withLevel := by unfold withLevel;apply poly_both
instance poly_matrixSub : PolyTime matrixSub := by
  unfold matrixSub
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_both
  · exact poly_matrixAdd
instance poly_zeroRect : PolyTime zeroRect := by unfold zeroRect;apply poly_then
instance poly_vdD : PolyTime vdD := by unfold vdD;infer_instance
instance poly_vdRest : PolyTime vdRest := by unfold vdRest;infer_instance
instance poly_vdAtoms : PolyTime vdAtoms := by unfold vdAtoms;infer_instance
instance poly_vdParams : PolyTime vdParams := by unfold vdParams;infer_instance
instance poly_vdX : PolyTime vdX := by unfold vdX;infer_instance
instance poly_vdTheta : PolyTime vdTheta := by unfold vdTheta;infer_instance
instance poly_vdEps : PolyTime vdEps := by unfold vdEps;infer_instance
instance poly_realDimension : PolyTime realDimension := by unfold realDimension;infer_instance
instance poly_valueDimension : PolyTime valueDimension := by unfold valueDimension;infer_instance
instance poly_coordinateIndexRealizes (b : Bool) : PolyTime (coordinateIndexRealizes b) := by unfold coordinateIndexRealizes;first | infer_instance | apply poly_then
instance poly_coordinateEntry (b : Bool) : PolyTime (coordinateEntry b) := by unfold coordinateEntry;infer_instance

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialMatrixFold
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_accumMatrix : PolyTime accumMatrixRealizes := by
  unfold accumMatrixRealizes
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_both
  · exact poly_matrixAdd

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoots
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize

instance poly_ratNumBinary : PolyTime ratNumBinary := by unfold ratNumBinary;infer_instance
instance poly_unframeNat : PolyTime unframeNat := by unfold unframeNat;apply poly_reindex
instance poly_ratDenBinary : PolyTime ratDenBinary := by unfold ratDenBinary;apply poly_then
instance poly_ratDenSize : PolyTime ratDenSize := by unfold ratDenSize;infer_instance

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialStored
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma flatten_code_le (ea : α → Word) (xs : List (List α)) :
    (listCode ea xs.flatten).length≤(listCode (listCode ea) xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatten_cons,listCode_append,List.length_append,listCode_cons,prodCode_length]
      omega
instance size_appendList (ea : α → Word) : FoldSize (appendList ea) := by
  refine ⟨⟨2*X,?_⟩⟩
  intro s xs ys zs h
  rw [fold_append_flatten,listCode_append,List.length_append]
  have hs := le_prodCode_left (ea:=listCode ea) (eb:=listCode (listCode ea)) (s,xs)
  have hy := (flatten_code_le ea ys).trans ((prefix_code_length (listCode ea) xs ys zs h).trans (le_prodCode_right (ea:=listCode ea) (s,xs)))
  change _≤2*(prodCode (listCode ea) (listCode (listCode ea)) (s,xs)).length
  dsimp only at hs hy
  omega
instance poly_flattenList (ea : α → Word) : PolyTime (flattenList ea) := by unfold flattenList;infer_instance
instance poly_joinList (ea : α → Word) : PolyTime (joinList ea) := by unfold joinList;infer_instance
instance poly_singleton (ea : α → Word) : PolyTime (singleton ea) := by unfold singleton;apply poly_then
instance poly_filterCtx {p : γ×α → Bool} (r : Realizes (prodCode ec ea) boolCode p) [PolyTime r] :
    PolyTime r.filterCtx := by unfold Realizes.filterCtx;infer_instance

instance poly_natToBinary : PolyTime natToBinary := by unfold natToBinary;infer_instance

instance poly_natLE : PolyTime natLE := by unfold natLE;infer_instance
instance poly_natEq : PolyTime natEq := by unfold natEq;infer_instance
instance poly_matrixEntry : PolyTime matrixEntry := by unfold matrixEntry;infer_instance
instance poly_matrixTabulate {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime r.matrixTabulate := by unfold Realizes.matrixTabulate;apply poly_then
instance poly_identityEntry : PolyTime identityEntry := by unfold identityEntry;infer_instance
instance poly_identityMatrix : PolyTime identityMatrix := by unfold identityMatrix;apply poly_then
instance poly_transposeMatrix : PolyTime transposeMatrix := by unfold transposeMatrix;apply poly_then
instance poly_fromBlocks : PolyTime fromBlocks := by unfold fromBlocks;apply poly_then
instance poly_tabulateFin {n : α → ℕ} {f : (Σ a,Fin (n a)) → β}
    (r : Realizes (finFamilyCode ea n) eb f) (rn : Realizes ea natCode n) [PolyTime r] [PolyTime rn] :
    PolyTime (r.tabulateFin rn) := by unfold Realizes.tabulateFin;infer_instance
instance poly_familyFirst {n : α → ℕ} : PolyTime (familyFirst (ea:=ea) (n:=n)) := by unfold familyFirst;apply poly_reindex
instance poly_familyIndex {n : α → ℕ} : PolyTime (familyIndex (ea:=ea) (n:=n)) := by unfold familyIndex;apply poly_reindex

instance poly_pow {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] (k : ℕ) : PolyTime (r.pow k) := by
  induction k with
  | zero => unfold Realizes.pow;infer_instance
  | succ k ih => unfold Realizes.pow;infer_instance
instance poly_min {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.min s) := by unfold Realizes.min;infer_instance
instance poly_max {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.max s) := by unfold Realizes.max;infer_instance
instance poly_inv {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.inv := by unfold Realizes.inv;infer_instance
instance poly_lt {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.lt s) := by unfold Realizes.lt;infer_instance
instance poly_eq {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.eq s) := by unfold Realizes.eq;infer_instance

instance poly_better (ea : α → Word) : PolyTime (better ea) := by unfold better;infer_instance

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCurvature
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

instance poly_vectorNeg : PolyTime vectorNeg := by unfold vectorNeg;apply poly_map
instance poly_vectorDivide : PolyTime vectorDivide := by unfold vectorDivide;apply poly_mapCtx
instance poly_intCeil : PolyTime intCeil := by unfold intCeil;apply poly_congr
instance poly_nearest : PolyTime nearest := by unfold nearest;apply poly_congr
instance poly_nearestMesh : PolyTime nearestMesh := by unfold nearestMesh;apply poly_mul
instance poly_roundMesh : PolyTime roundMesh := by unfold roundMesh;apply poly_mapCtx
instance poly_cuN : PolyTime cuN := by unfold cuN;apply poly_then
instance poly_cuRest : PolyTime cuRest := by unfold cuRest;apply poly_then
instance poly_cuH : PolyTime cuH := by unfold cuH;apply poly_then
instance poly_cuScalars : PolyTime cuScalars := by unfold cuScalars;apply poly_then
instance poly_cuA : PolyTime cuA := by unfold cuA;apply poly_then
instance poly_cuMore : PolyTime cuMore := by unfold cuMore;apply poly_then
instance poly_cuM : PolyTime cuM := by unfold cuM;apply poly_then
instance poly_cuLast : PolyTime cuLast := by unfold cuLast;apply poly_then
instance poly_cuS : PolyTime cuS := by unfold cuS;apply poly_then
instance poly_cuRho : PolyTime cuRho := by unfold cuRho;apply poly_then
instance poly_cuShift : PolyTime cuShift := by unfold cuShift;apply poly_changeOutput
instance poly_updateVector : PolyTime updateVector := by unfold updateVector;apply poly_congr
instance poly_endpointEntry : PolyTime endpointEntry := by unfold endpointEntry;apply poly_then
instance poly_endpointCandidates : PolyTime endpointCandidates := by unfold endpointCandidates;apply poly_congr
instance poly_freezeScalar : PolyTime freezeScalar := by unfold freezeScalar;apply poly_congr
instance poly_freezeVector : PolyTime freezeVector := by unfold freezeVector;apply poly_mapCtx
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialSchedule
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_saD : PolyTime saD := by unfold saD;infer_instance
instance poly_saRest : PolyTime saRest := by unfold saRest;infer_instance
instance poly_saN : PolyTime saN := by unfold saN;apply poly_then
instance poly_saScalars : PolyTime saScalars := by unfold saScalars;apply poly_then
instance poly_saNu : PolyTime saNu := by unfold saNu;apply poly_then
instance poly_saLam : PolyTime saLam := by unfold saLam;apply poly_then
instance poly_saEpsilon : PolyTime saEpsilon := by unfold saEpsilon;apply poly_div
instance poly_saSigma : PolyTime saSigma := by unfold saSigma;apply poly_div
instance poly_movementBudget : PolyTime movementBudget := by unfold movementBudget;apply poly_max
instance poly_saThreshold : PolyTime saThreshold := by unfold saThreshold;apply poly_div
instance poly_saCoarse : PolyTime saCoarse := by unfold saCoarse;apply poly_add
instance poly_saCurve2 : PolyTime saCurve2 := by unfold saCurve2;apply poly_mul
instance poly_saCurve3 : PolyTime saCurve3 := by unfold saCurve3;apply poly_mul
instance poly_saBudget : PolyTime saBudget := by unfold saBudget;apply poly_add
instance poly_saStep : PolyTime saStep := by unfold saStep;apply poly_min
instance poly_saStencil : PolyTime saStencil := by unfold saStencil;apply poly_min
instance poly_saMesh : PolyTime saMesh := by unfold saMesh;apply poly_div
instance poly_parameters_singleton : PolyTime parameters.singletonRat := by unfold parameters.singletonRat;apply poly_then
instance poly_parameters : PolyTime parameters := by unfold parameters;apply poly_changeOutput
instance poly_parameterField (i : ℕ) : PolyTime (parameterField i) := by
  unfold parameterField
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · apply poly_reindex
  · infer_instance
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceBasics
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_activeIndices : PolyTime activeIndices := by unfold activeIndices;apply poly_then
instance poly_fD : PolyTime fD := by unfold fD;apply poly_then
instance poly_fRest : PolyTime fRest := by unfold fRest;apply poly_then
instance poly_fAtoms : PolyTime fAtoms := by unfold fAtoms;apply poly_then
instance poly_fArgs : PolyTime fArgs := by unfold fArgs;apply poly_then
instance poly_fBase : PolyTime fBase := by unfold fBase;apply poly_then
instance poly_fScalars : PolyTime fScalars := by unfold fScalars;apply poly_then
instance poly_fNu : PolyTime fNu := by unfold fNu;apply poly_then
instance poly_fLam : PolyTime fLam := by unfold fLam;apply poly_then
instance poly_fIndices : PolyTime fIndices := by unfold fIndices;apply poly_congr
instance poly_fN : PolyTime fN := by unfold fN;apply poly_congr
instance poly_fSchedule : PolyTime fSchedule := by unfold fSchedule;apply poly_then
instance poly_gather : PolyTime gather := by unfold gather;apply poly_mapCtx
instance poly_fState : PolyTime fState := by unfold fState;apply poly_congr
instance poly_fpP : PolyTime fpP := by unfold fpP;apply poly_then
instance poly_fpY : PolyTime fpY := by unfold fpY;apply poly_then
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoundedStep
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize
open scoped BigOperators

instance poly_statePencil : PolyTime statePencil := by unfold statePencil;apply poly_then
instance poly_stateParameters : PolyTime stateParameters := by unfold stateParameters;apply poly_then
instance poly_stateY : PolyTime stateY := by unfold stateY;apply poly_then
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialSearch
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_searchPencil : PolyTime searchPencil := by unfold searchPencil;apply poly_then
instance poly_searchParameters : PolyTime searchParameters := by unfold searchParameters;apply poly_then
instance poly_searchY : PolyTime searchY := by unfold searchY;apply poly_then
instance poly_searchDim : PolyTime searchDim := by unfold searchDim;infer_instance
instance poly_searchStep : PolyTime searchStepRealizes := by unfold searchStepRealizes;apply poly_div
instance poly_searchMesh : PolyTime searchMeshRealizes := by unfold searchMeshRealizes;apply poly_div
instance poly_searchInit : PolyTime searchInit := by unfold searchInit;apply poly_changeOutput

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialOptimize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_optB : PolyTime optB := by unfold optB;apply poly_then
instance poly_optF : PolyTime optF := by unfold optF;apply poly_then
instance poly_optScalars : PolyTime optScalars := by unfold optScalars;apply poly_then
instance poly_optDelta : PolyTime optDelta := by unfold optDelta;apply poly_then
instance poly_optRest : PolyTime optRest := by unfold optRest;apply poly_then
instance poly_optRadius : PolyTime optRadius := by unfold optRadius;apply poly_both
instance poly_optUpper : PolyTime optUpper := by unfold optUpper;apply poly_then
instance poly_optLevel : PolyTime optLevel := by unfold optLevel;apply poly_add
instance poly_optLevelPencil : PolyTime optLevelPencil := by unfold optLevelPencil;apply poly_congr
instance poly_osP : PolyTime osP := by unfold osP;apply poly_then
instance poly_osK : PolyTime osK := by unfold osK;apply poly_then
instance poly_osY : PolyTime osY := by unfold osY;apply poly_then
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialValueQuery
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_veP : PolyTime veP := by unfold veP;infer_instance
instance poly_veY : PolyTime veY := by unfold veY;infer_instance
instance poly_veD : PolyTime veD := by unfold veD;apply poly_then
instance poly_veN : PolyTime veN := by unfold veN;apply poly_then
instance poly_veEye : PolyTime veEye := by unfold veEye;apply poly_then
instance poly_veEps : PolyTime veEps := by unfold veEps;apply poly_then
instance poly_veTime : PolyTime veTime := by unfold veTime;apply poly_then
instance poly_tinyMatrix : PolyTime tinyMatrix := by unfold tinyMatrix;apply poly_then
instance poly_vqData : PolyTime vqData := by unfold vqData;apply poly_then
instance poly_vqDelta : PolyTime vqDelta := by unfold vqDelta;apply poly_then
instance poly_valueLipschitz : PolyTime valueLipschitz := by unfold valueLipschitz;apply poly_mul
instance poly_valueOuterRadius : PolyTime valueOuterRadius := by unfold valueOuterRadius;apply poly_mul
instance poly_valueInnerRadius : PolyTime valueInnerRadius := by unfold valueInnerRadius;apply poly_div
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialPotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

instance poly_ppD : PolyTime ppD := by unfold ppD;apply poly_then
instance poly_ppRest : PolyTime ppRest := by unfold ppRest;apply poly_then
instance poly_ppAtoms : PolyTime ppAtoms := by unfold ppAtoms;apply poly_then
instance poly_ppArgs : PolyTime ppArgs := by unfold ppArgs;apply poly_then
instance poly_ppX : PolyTime ppX := by unfold ppX;apply poly_then
instance poly_ppScalars : PolyTime ppScalars := by unfold ppScalars;apply poly_then
instance poly_ppNu : PolyTime ppNu := by unfold ppNu;apply poly_then
instance poly_ppLam : PolyTime ppLam := by unfold ppLam;apply poly_then
instance poly_ppError : PolyTime ppError := by unfold ppError;apply poly_then
instance poly_ppN : PolyTime ppN := by unfold ppN;apply poly_congr
instance poly_ppRootTolerance : PolyTime ppRootTolerance := by unfold ppRootTolerance;apply poly_div
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialStencil
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ}
instance poly_fiP : PolyTime fiP := by unfold fiP;apply poly_familyFirst
instance poly_fiI : PolyTime fiI := by unfold fiI;apply poly_familyIndex
instance poly_fdS : PolyTime fdS := by unfold fdS;apply poly_familyFirst
instance poly_fdP : PolyTime fdP := by unfold fdP;apply poly_then
instance poly_fdI : PolyTime fdI := by unfold fdI;apply poly_then
instance poly_fdJ : PolyTime fdJ := by unfold fdJ;apply poly_familyIndex
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceChoice
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι : Type*} {L : ι → ℕ}
instance poly_vectorSub : PolyTime vectorSub := by unfold vectorSub;apply poly_zipWith
instance poly_curvatureCandidates : PolyTime curvatureCandidates := by unfold curvatureCandidates;apply poly_congr
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceFuel
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_packFace {α : Type*} {ea : α → Word} {f : α → FaceParams}
    {g : (a : α) → Fin (f a).N → ℚ}
    (p : Realizes ea faceCode f) (y : Realizes ea vectorCode (fun a => List.ofFn (g a)))
    [PolyTime p] [PolyTime y] : PolyTime (packFace p y) := by
  unfold packFace;apply poly_changeOutput
instance poly_faceStart : PolyTime faceStart := by
  unfold faceStart
  refine @poly_packFace _ _ _ _ _ _ ?_ ?_
  · exact poly_identity _
  · apply poly_congr
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialIterateFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_better _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eq _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_familyFirst _root_.OAI.CurrentKS.Realization.poly_familyIndex _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_filterCtx _root_.OAI.CurrentKS.Realization.poly_flattenList _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_fromBlocks _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_identityEntry _root_.OAI.CurrentKS.Realization.poly_identityMatrix _root_.OAI.CurrentKS.Realization.poly_inv _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_joinList _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_lt _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixEntry _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixTabulate _root_.OAI.CurrentKS.Realization.poly_max _root_.OAI.CurrentKS.Realization.poly_min _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natEq _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natLE _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_natToBinary _root_.OAI.CurrentKS.Realization.poly_natToRat _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_pow _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratLE _root_.OAI.CurrentKS.Realization.poly_ratOp _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_roundScalar _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_singleton _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_tabulateFin _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_appendList _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_natMulStep _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ} {ea : α → Word} {f : α → α}
lemma runsPoly_iterate (r : Realizes ea ea f) (a : ι → ℕ×α)
    (ha : IsPoly L (fun i => (prodCode natCode ea (a i)).length))
    (hc : ∃p : NaturalPolynomial,∀i j,j<(a i).1 → r.cost (f^[j] (a i).2)≤p.eval (L i)) :
    RunsPoly L r.iterate a := by
  obtain ⟨p,hp⟩ := ha
  obtain ⟨q,hq⟩ := hc
  refine ⟨⟨p,hp⟩,⟨3*p+p*(q+2)+3,?_⟩⟩
  intro i
  have hn : (a i).1≤p.eval (L i) := by
    have h := hp i
    simp only [prodCode_length,natCode,List.length_replicate] at h
    omega
  have ht := iterate_ticks_bound r (a i).2 (a i).1 (q.eval (L i)) (hq i)
  have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  change 3*(a i).1+2+IterateRoutine.loopTicks r.cost f (a i).1 (a i).2≤
    3*p.eval (L i)+p.eval (L i)*(q.eval (L i)+2)+3
  omega
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialOriginalFields
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_originalD : PolyTime originalD := by unfold originalD;apply poly_then
instance poly_originalRecords : PolyTime originalRecords := by unfold originalRecords;apply poly_then
instance poly_originalN : PolyTime originalN := by unfold originalN;apply poly_congr
instance poly_recordEntry (imag : Bool) : PolyTime (recordEntry imag) := by unfold recordEntry;apply poly_then
instance poly_recordCoordinate : PolyTime recordCoordinate := by unfold recordCoordinate;apply poly_congr
instance poly_recordCoordinates : PolyTime recordCoordinates := by unfold recordCoordinates;apply poly_then
instance poly_originalRecord : PolyTime originalRecord := by unfold originalRecord;apply poly_congr
instance poly_nonzeroIndices : PolyTime nonzeroIndices := by unfold nonzeroIndices;apply poly_congr
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialVariance
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_mgN : PolyTime mgN := by unfold mgN;apply poly_then
instance poly_mgRest : PolyTime mgRest := by unfold mgRest;apply poly_then
instance poly_mgM : PolyTime mgM := by unfold mgM;apply poly_then
instance poly_mgDen : PolyTime mgDen := by unfold mgDen;apply poly_then
instance poly_mgShift : PolyTime mgShift := by unfold mgShift;apply poly_changeOutput
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_MachineAdapter
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.ArchivedMachine
open KS.W01.FixedStack

end CurrentKS.ArchivedMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OriginalMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS
open Realization CleanRoutine

end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_BasePacking
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Hermitian.instFiniteDimensionalRealSubtypeMatMemSubmoduleH
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uI2

section

noncomputable section
open Finset Submodule
namespace StrongThinTree.Packing

variable {E : Type uE} {I : Type uI} {V : Type uV} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_mono (v : E → V) {s t : Finset E} (h : s ⊆ t) : span v s ≤ span v t :=
  Submodule.span_mono (Set.image_mono h)

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma span_insert (v : E → V) (s : Finset E) (e : E) :
    span v (insert e s) = Submodule.span ℝ (insert (v e) (v '' (s : Set E))) := by
  simp only [span, coe_insert, Set.image_insert_eq]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma indep_rank (v : E → V) {s : Finset E} (hs : LinearIndepOn ℝ v s) :
    Module.finrank ℝ (span v s) = s.card := by
  have heq : Set.range (fun e : (s : Set E) => v e) = v '' (s : Set E) := by
    ext x; simp
  have h := finrank_span_eq_card hs.linearIndependent
  change Module.finrank ℝ (Submodule.span ℝ (Set.range (fun e : (s : Set E) => v e))) = _ at h
  rw [heq] at h
  simpa using h

omit [Fintype E] [FiniteDimensional ℝ V] in

lemma support_exchange (v : E → V) {s : Finset E}
    (hs : LinearIndepOn ℝ v s) {x : V} {l : E →₀ ℝ}
    (hl : l ∈ Finsupp.supported ℝ ℝ (s : Set E))
    (hx : Finsupp.linearCombination ℝ v l = x) {f : E} (hf : f ∈ l.support) :
    x ∉ span v (s.erase f) := by
  intro h
  obtain ⟨l', hl', hx'⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp h
  have hl's : l' ∈ Finsupp.supported ℝ ℝ (s : Set E) := by
    rw [Finsupp.mem_supported] at hl' ⊢
    exact hl'.trans (Finset.erase_subset _ _)
  have heq : l = l' := (linearIndepOn_iffₛ.mp hs) l hl l' hl's (hx.trans hx'.symm)
  have hz : l' f = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have := ((Finsupp.mem_supported ℝ l').mp hl') hmem
    simp at this
  exact (Finsupp.mem_support_iff.mp hf) (heq ▸ hz)

omit [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma valid_empty (v : E → V) : Valid v (fun _ : I => ∅) := by
  constructor
  · intro i; simp
  · intro i j h; simp

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma valid_update {v : E → V} (F : State v I) (i : I) (s : Finset E)
    (hs : LinearIndepOn ℝ v (s : Set E))
    (hd : ∀ j, j ≠ i → Disjoint s (F.1 j)) : Valid v (Function.update F.1 i s) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j; simpa using hs
    · simpa [Function.update_of_ne h] using F.2.1 j
  · intro j k hjk
    by_cases hj : j = i
    · subst j
      simpa [Function.update_of_ne (Ne.symm hjk)] using hd k (Ne.symm hjk)
    · by_cases hk : k = i
      · subst k
        simpa [Function.update_of_ne hj] using (hd j hj).symm
      · simpa [Function.update_of_ne hj, Function.update_of_ne hk] using F.2.2 hjk

omit [Fintype E] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma disjoint_insert_unused {v : E → V} (F : State v I) {i : I} {s : Finset E}
    (hs : s ⊆ F.1 i) {e : E} (he : unused F e) :
    ∀ j, j ≠ i → Disjoint (insert e s) (F.1 j) := by
  intro j hj
  rw [Finset.disjoint_insert_left]
  exact ⟨he j, (F.2.2 (Ne.symm hj)).mono_left hs⟩

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma cost_update {v : E → V} (F : State v I) {i : I} {s : Finset E}
    (h : Valid v (Function.update F.1 i s)) :
    cost (⟨Function.update F.1 i s, h⟩ : State v I) + (F.1 i).card = cost F + s.card := by
  unfold cost
  have hsum := Finset.sum_update_of_mem (Finset.mem_univ i) (fun j => (F.1 j).card) s.card
  have heq : (fun j => ((Function.update F.1 i s) j).card) =
      Function.update (fun j => (F.1 j).card) i s.card := by
    ext j; by_cases hj : j = i <;> simp [hj, Function.update_of_ne]
  rw [heq]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ : Finset I) _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  have he : ∑ j ∈ Finset.univ.erase i,
      Function.update (fun j => (F.1 j).card) i s.card j =
      ∑ j ∈ Finset.univ.erase i, (F.1 j).card := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  rw [he]
  omega

omit [DecidableEq E] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma exists_maximal_state (v : E → V) :
    ∃ F : State v I, ∀ F' : State v I, cost F' ≤ cost F := by
  classical
  let : Fintype (State v I) := Fintype.ofFinite _
  have hne : (Finset.univ : Finset (State v I)).Nonempty :=
    ⟨⟨fun _ => ∅, valid_empty v⟩, Finset.mem_univ _⟩
  obtain ⟨F, _, hF⟩ := Finset.exists_max_image (Finset.univ : Finset (State v I)) cost hne
  exact ⟨F, fun F' => hF F' (Finset.mem_univ _)⟩

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma maximal_unused_mem_span {v : E → V} {F : State v I}
    (hF : ∀ F' : State v I, cost F' ≤ cost F) {e : E} (he : unused F e) (i : I) :
    v e ∈ span v (F.1 i) := by
  by_contra h
  have hs : LinearIndepOn ℝ v (insert e (F.1 i) : Finset E) := by
    simpa only [Finset.coe_insert] using (F.2.1 i).insert h
  have hv := valid_update F i _ hs (disjoint_insert_unused F (Subset.refl _) he)
  have hc := cost_update F hv
  have hu := hF ⟨_, hv⟩
  rw [Finset.card_insert_of_notMem (he i)] at hc
  omega

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma unused_after_exchange {v : E → V} {F F' : State v I} {i : I} {e f : E}
    (he : unused F e) (hf : f ∈ F.1 i)
    (h : F'.1 = Function.update F.1 i (insert e ((F.1 i).erase f))) : unused F' f := by
  intro j
  rw [h]
  by_cases hj : j = i
  · subst j
    have hfe : f ≠ e := by rintro rfl; exact he i hf
    simp [hfe]
  · rw [Function.update_of_ne hj]
    exact fun hfj => Finset.disjoint_left.mp (F.2.2 (Ne.symm hj)) hf hfj

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma Move.cost_eq {v : E → V} {F F' : State v I} (h : Move F F') : cost F' = cost F := by
  obtain ⟨i, e, f, he, hf, heq⟩ := h
  have hv : Valid v (Function.update F.1 i (insert e ((F.1 i).erase f))) := heq ▸ F'.2
  have hc := cost_update F hv
  have hsame : (⟨_, hv⟩ : State v I) = F' := Subtype.ext heq.symm
  rw [hsame, Finset.card_insert_of_notMem (fun hh => he i (Finset.mem_erase.mp hh).2),
    Finset.card_erase_of_mem hf] at hc
  have hfpos := Finset.card_pos.mpr ⟨f, hf⟩
  omega

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma reachable_cost_eq {v : E → V} {F F' : State v I}
    (h : Relation.ReflTransGen Move F F') : cost F' = cost F := by
  induction h with
  | refl => rfl
  | @tail F' F'' hr hm ih => exact hm.cost_eq.trans ih

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma reachable_maximal {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (h : Relation.ReflTransGen Move F F') : ∀ G : State v I, cost G ≤ cost F' := by
  intro G
  rw [reachable_cost_eq h]
  exact hF G

omit [FiniteDimensional ℝ V] in
lemma mem_recycled {v : E → V} {F : State v I} {e : E} :
    e ∈ recycled F ↔ ∃ F', Relation.ReflTransGen Move F F' ∧ unused F' e := by
  classical
  simp [recycled]

omit [FiniteDimensional ℝ V] in
lemma unused_span_recycled {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') {e : E} (he : unused F' e) (i : I) :
    v e ∈ span v (F'.1 i ∩ recycled F) := by
  have hsp := maximal_unused_mem_span (reachable_maximal hF hr) he i
  obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp hsp
  apply (Finsupp.mem_span_image_iff_linearCombination ℝ).mpr
  refine ⟨l, ?_, hle⟩
  rw [Finsupp.mem_supported]
  intro f hf
  have hfi : f ∈ F'.1 i := (Finsupp.mem_supported ℝ l).mp hl hf
  refine Finset.mem_inter.mpr ⟨hfi, mem_recycled.mpr ?_⟩
  have hex := support_exchange v (F'.2.1 i) hl hle hf
  have hs : LinearIndepOn ℝ v (insert e ((F'.1 i).erase f) : Finset E) := by
    simpa only [Finset.coe_insert] using
      ((F'.2.1 i).mono (Finset.erase_subset _ _)).insert hex
  have hv := valid_update F' i _ hs
    (disjoint_insert_unused F' (Finset.erase_subset _ _) he)
  let F'' : State v I := ⟨_, hv⟩
  have hm : Move F' F'' := ⟨i, e, f, he, hfi, rfl⟩
  exact ⟨F'', hr.tail hm, unused_after_exchange he hfi rfl⟩

omit [FiniteDimensional ℝ V] in
lemma move_span_recycled_eq {v : E → V} {F F' F'' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') (hm : Move F' F'') (j : I) :
    span v (F''.1 j ∩ recycled F) = span v (F'.1 j ∩ recycled F) := by
  obtain ⟨i, e, f, he, hf, hup⟩ := hm
  by_cases hji : j = i
  · subst j
    have heU : v e ∈ span v (F'.1 i ∩ recycled F) := unused_span_recycled hF hr he i
    have hfU : v f ∈ span v (F''.1 i ∩ recycled F) :=
      unused_span_recycled hF (hr.tail ⟨i, e, f, he, hf, hup⟩)
        (unused_after_exchange he hf hup) i
    apply le_antisymm
    · apply (span_le_iff v).mpr
      intro g hg
      have hgU := (Finset.mem_inter.mp hg).2
      have hg' := (Finset.mem_inter.mp hg).1
      rw [hup, Function.update_self] at hg'
      rcases Finset.mem_insert.mp hg' with rfl | hg'
      · exact heU
      · exact mem_span_self v (Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hg').2, hgU⟩)
    · apply (span_le_iff v).mpr
      intro g hg
      by_cases hgf : g = f
      · subst g; exact hfU
      · apply mem_span_self v
        apply Finset.mem_inter.mpr
        refine ⟨?_, (Finset.mem_inter.mp hg).2⟩
        rw [hup, Function.update_self]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hgf, (Finset.mem_inter.mp hg).1⟩)
  · rw [hup, Function.update_of_ne hji]

omit [FiniteDimensional ℝ V] in
lemma reachable_span_recycled_eq {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') (i : I) :
    span v (F'.1 i ∩ recycled F) = span v (F.1 i ∩ recycled F) := by
  induction hr with
  | refl => rfl
  | @tail F' F'' hr hm ih => exact (move_span_recycled_eq hF hr hm i).trans ih

omit [FiniteDimensional ℝ V] in

lemma span_recycled_eq {v : E → V} {F : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F) (i : I) :
    span v (recycled F) = span v (F.1 i ∩ recycled F) := by
  apply le_antisymm
  · apply (span_le_iff v).mpr
    intro e he
    obtain ⟨F', hr, he'⟩ := mem_recycled.mp he
    rw [← reachable_span_recycled_eq hF hr i]
    exact unused_span_recycled hF hr he' i
  · exact span_mono v Finset.inter_subset_right

omit [FiniteDimensional ℝ V] in
lemma cost_decomposition {v : E → V} {F : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F) :
    cost F = (Finset.univ \ recycled F).card +
      Fintype.card I * Module.finrank ℝ (span v (recycled F)) := by
  classical
  have hcover : Finset.univ \ recycled F =
      Finset.univ.biUnion (fun i => F.1 i \ recycled F) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro he
      have hused : ∃ i, e ∈ F.1 i := by
        by_contra h
        have hu : unused F e := by simpa only [unused, not_exists] using h
        exact he (mem_recycled.mpr ⟨F, Relation.ReflTransGen.refl, hu⟩)
      obtain ⟨i, hi⟩ := hused
      exact ⟨i, hi, he⟩
    · rintro ⟨i, hi, he⟩; exact he
  have hdisj : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => F.1 i \ recycled F) := by
    intro i _ j _ hij
    exact (F.2.2 hij).mono Finset.sdiff_subset Finset.sdiff_subset
  have hrank (i : I) : (F.1 i ∩ recycled F).card =
      Module.finrank ℝ (span v (recycled F)) := by
    rw [span_recycled_eq hF i]
    exact (indep_rank v ((F.2.1 i).mono Finset.inter_subset_left)).symm
  rw [hcover, Finset.card_biUnion hdisj]
  calc
    cost F = ∑ i, ((F.1 i \ recycled F).card + (F.1 i ∩ recycled F).card) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.card_sdiff_add_card_inter _ _).symm
    _ = (∑ i, (F.1 i \ recycled F).card) +
        Fintype.card I * Module.finrank ℝ (span v (recycled F)) := by
      simp_rw [hrank, Finset.sum_add_distrib]
      simp

theorem vector_base_packing (v : E → V)
    (hcut : ∀ U : Finset E,
      Fintype.card I * Module.finrank ℝ (span v Finset.univ) ≤
        (Finset.univ \ U).card + Fintype.card I * Module.finrank ℝ (span v U)) :
    ∃ F : State v I, ∀ i, span v (F.1 i) = span v Finset.univ := by
  obtain ⟨F, hF⟩ := exists_maximal_state (I := I) v
  have hle (i : I) : (F.1 i).card ≤ Module.finrank ℝ (span v Finset.univ) := by
    rw [← indep_rank v (F.2.1 i)]
    exact Submodule.finrank_mono (span_mono v (Finset.subset_univ _))
  have htotal : cost F = Fintype.card I * Module.finrank ℝ (span v Finset.univ) := by
    apply le_antisymm
    · calc
        cost F ≤ ∑ _i : I, Module.finrank ℝ (span v Finset.univ) :=
          Finset.sum_le_sum fun i _ => hle i
        _ = _ := by simp
    · rw [cost_decomposition hF]
      exact hcut (recycled F)
  have hcards (i : I) : (F.1 i).card = Module.finrank ℝ (span v Finset.univ) := by
    apply (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset I)) => hle i)).mp ?_ i
      (Finset.mem_univ i)
    simpa [cost] using htotal
  refine ⟨F, fun i => ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq (span_mono v (Finset.subset_univ _))
  rw [indep_rank v (F.2.1 i), hcards]

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma masked_span (v : E → V) (T U : Finset E) :
    span (fun e => if e ∈ T then v e else 0) U = span v (U ∩ T) := by
  classical
  apply le_antisymm
  · apply (span_le_iff _).mpr
    intro e he
    by_cases heT : e ∈ T
    · simp only [ite_eq_left heT]
      exact mem_span_self v (Finset.mem_inter.mpr ⟨he, heT⟩)
    · simp [heT]
  · apply (span_le_iff _).mpr
    intro e he
    have hm := mem_span_self (fun e => if e ∈ T then v e else 0) (Finset.mem_inter.mp he).1
    simpa only [ite_eq_left (Finset.mem_inter.mp he).2] using hm

theorem vector_base_packing_on (v : E → V) (T : Finset E)
    (hcut : ∀ U : Finset E, U ⊆ T →
      Fintype.card I * Module.finrank ℝ (span v T) ≤
        (T \ U).card + Fintype.card I * Module.finrank ℝ (span v U)) :
    ∃ F : I → Finset E, Valid v F ∧ ∀ i, F i ⊆ T ∧ span v (F i) = span v T := by
  classical
  let w : E → V := fun e => if e ∈ T then v e else 0
  have hcrit : ∀ U : Finset E, Fintype.card I * Module.finrank ℝ (span w Finset.univ) ≤
      (Finset.univ \ U).card + Fintype.card I * Module.finrank ℝ (span w U) := by
    intro U
    have hw (A : Finset E) : span w A = span v (A ∩ T) := masked_span v T A
    rw [hw, hw, Finset.univ_inter]
    have h := hcut (U ∩ T) Finset.inter_subset_right
    apply h.trans
    apply Nat.add_le_add_right
    apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ, true_and] at he ⊢
    tauto
  obtain ⟨F, hF⟩ := vector_base_packing (I := I) w hcrit
  have hsub (i : I) : F.1 i ⊆ T := by
    intro e he
    have hz := (F.2.1 i).ne_zero he
    by_contra h
    exact hz (by simp [w, h])
  refine ⟨F.1, ⟨?_, F.2.2⟩, fun i => ⟨hsub i, ?_⟩⟩
  · intro i
    apply (F.2.1 i).congr
    intro e he
    simp [w, hsub i he]
  · have heq := hF i
    simpa only [w, masked_span, Finset.inter_eq_left.mpr (hsub i), Finset.univ_inter] using heq

end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

lemma rep_same (T : Finset (Fin m)) (u : Fin n) : G.Same T (G.rep T u) u :=
  Quotient.mk_out (s := G.components T) u

lemma rep_eq_iff (T : Finset (Fin m)) (u v : Fin n) : G.rep T u = G.rep T v ↔ G.Same T u v := by
  constructor
  · intro h
    exact G.same_trans (G.same_symm (G.rep_same T u)) (h ▸ G.rep_same T v)
  · intro h
    exact congrArg Quotient.out (Quotient.sound h)

lemma rep_idempotent (T : Finset (Fin m)) (u : Fin n) : G.rep T (G.rep T u) = G.rep T u :=
  (G.rep_eq_iff T _ _).mpr (G.rep_same T u)

lemma rep_endpoints {T : Finset (Fin m)} {e : Fin m} (he : e ∈ T) :
    G.rep T (G.left e) = G.rep T (G.right e) :=
  (G.rep_eq_iff T _ _).mpr (G.same_endpoints he)

lemma repDifference_mem (T : Finset (Fin m)) (u : Fin n) : G.repDifference T u ∈ G.edgeSpan T :=
  G.same_symm (G.rep_same T u)

lemma repDifference_independent (T : Finset (Fin m)) :
    LinearIndependent ℝ (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u) := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun u => LinearMap.proj u.1)
  · intro u v huv
    have huv' : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    have hru : u.1 ≠ G.rep T v.1 := by
      intro h
      have := G.rep_idempotent T v.1
      rw [← h] at this
      exact u.2 this
    simp [repDifference, point, huv', hru]
  · intro u
    simp [repDifference, point, (Ne.symm u.2)]

lemma edgeSpan_eq_repSpan (T : Finset (Fin m)) :
    G.edgeSpan T = Submodule.span ℝ
      (Set.range (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u)) := by
  classical
  apply le_antisymm
  · apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    have hdiff (u : Fin n) : G.repDifference T u ∈ Submodule.span ℝ
        (Set.range (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u)) := by
      by_cases hu : G.rep T u = u
      · simp [repDifference, hu]
      · exact Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩
    have h := (Submodule.span ℝ _).sub_mem (hdiff (G.left e)) (hdiff (G.right e))
    have heq : G.repDifference T (G.left e) - G.repDifference T (G.right e) = G.incidence e := by
      dsimp [repDifference, incidence]
      rw [G.rep_endpoints he]
      abel
    rwa [heq] at h
  · apply Submodule.span_le.mpr
    rintro x ⟨u, rfl⟩
    exact G.repDifference_mem T u

theorem incidence_rank (T : Finset (Fin m)) :
    Module.finrank ℝ (G.edgeSpan T) = n - G.componentCount T := by
  classical
  rw [G.edgeSpan_eq_repSpan, finrank_span_eq_card (G.repDifference_independent T),
    Fintype.card_subtype_compl]
  have heq : Finset.univ.image (G.rep T) = Finset.univ.filter (fun u => G.rep T u = u) := by
    ext u
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨v, rfl⟩
      exact G.rep_idempotent T v
    · intro hu
      exact ⟨u, hu⟩
  simp only [componentCount, heq, Fintype.card_fin, Fintype.card_subtype]

lemma connected_of_span_eq {T U : Finset (Fin m)}
    (h : G.edgeSpan T = G.edgeSpan U) (hT : G.Connected T) : G.Connected U := by
  rw [G.connected_iff_same] at hT ⊢
  intro u v
  change point u - point v ∈ G.edgeSpan U
  rw [← h]
  exact hT u v

theorem spanningTree_iff_independent (T : Finset (Fin m)) :
    G.SpanningTree T ↔ G.Connected T ∧ LinearIndepOn ℝ G.incidence (T : Set (Fin m)) := by
  constructor
  · rintro ⟨hconn, hmin⟩
    refine ⟨hconn, linearIndepOn_iff_notMem_span.mpr ?_⟩
    intro e he hdep
    have hd : G.incidence e ∈ G.edgeSpan (T.erase e) := by
      simpa only [edgeSpan, Packing.span, Finset.coe_erase] using hdep
    have heq : G.edgeSpan T = G.edgeSpan (T.erase e) := by
      calc
        G.edgeSpan T = G.edgeSpan (insert e (T.erase e)) := by rw [Finset.insert_erase he]
        _ = G.edgeSpan (T.erase e) := by
          change Packing.span G.incidence (insert e (T.erase e)) = _
          rw [Packing.span_insert, Submodule.span_insert_eq_span hd]
    exact hmin e he (G.connected_of_span_eq heq hconn)
  · rintro ⟨hconn, hind⟩
    refine ⟨hconn, fun e he hdel => ?_⟩
    have hnot := linearIndepOn_iff_notMem_span.mp hind e he
    apply hnot
    have hsame := (G.connected_iff_same (T.erase e)).mp hdel (G.left e) (G.right e)
    simpa only [Same, incidence, edgeSpan, Packing.span, Finset.coe_erase] using hsame

lemma componentCount_pos (hn : 0 < n) (T : Finset (Fin m)) : 0 < G.componentCount T := by
  apply Finset.card_pos.mpr
  exact ⟨G.rep T ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩

lemma componentCount_le (T : Finset (Fin m)) : G.componentCount T ≤ n := by
  exact (Finset.card_image_le).trans_eq (Finset.card_univ.trans (Fintype.card_fin n))

lemma connected_componentCount {T : Finset (Fin m)} (hn : 0 < n) (hc : G.Connected T) :
    G.componentCount T = 1 := by
  apply Finset.card_eq_one.mpr
  let u : Fin n := ⟨0, hn⟩
  refine ⟨G.rep T u, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_singleton.mpr ((G.rep_eq_iff T w u).mpr ((G.connected_iff_same T).mp hc w u))
  · intro hv
    have hv' := Finset.mem_singleton.mp hv
    subst v
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

lemma connected_rank {T : Finset (Fin m)} (hn : 0 < n) (hc : G.Connected T) :
    Module.finrank ℝ (G.edgeSpan T) = n - 1 := by
  rw [G.incidence_rank, G.connected_componentCount hn hc]

lemma connected_of_componentCount_eq_one {T : Finset (Fin m)}
    (hc : G.componentCount T = 1) : G.Connected T := by
  rw [G.connected_iff_same]
  have ⟨v, hv⟩ := Finset.card_eq_one.mp hc
  intro a b
  have ha : G.rep T a ∈ Finset.univ.image (G.rep T) :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hb : G.rep T b ∈ Finset.univ.image (G.rep T) :=
    Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  rw [hv, Finset.mem_singleton] at ha hb
  exact (G.rep_eq_iff T a b).mp (ha.trans hb.symm)

lemma crossing_components_subset (T U : Finset (Fin m)) :
    G.crossing T (G.rep U) ⊆ T \ U := by
  intro e he
  obtain ⟨heT, hec⟩ := Finset.mem_filter.mp he
  exact Finset.mem_sdiff.mpr ⟨heT, fun heU => hec (G.rep_endpoints heU)⟩

lemma crossing_components_self (T : Finset (Fin m)) : G.crossing T (G.rep T) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  have := G.crossing_components_subset T T he
  simp at this

theorem partition_criterion_sufficient (T : Finset (Fin m)) {r : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hp : ∀ p : Fin n → Fin n, r * (partitionSize p - 1) ≤ (G.crossing T p).card) :
    G.TreePackable T r := by
  have hc : G.Connected T := by
    have h := hp (G.rep T)
    rw [G.crossing_components_self, Finset.card_empty] at h
    change r * (G.componentCount T - 1) ≤ 0 at h
    have hpos := G.componentCount_pos hn T
    have hz : G.componentCount T - 1 = 0 := by nlinarith
    exact G.connected_of_componentCount_eq_one (by omega)
  have hcrit : ∀ U : Finset (Fin m), U ⊆ T →
      Fintype.card (Fin r) * Module.finrank ℝ (Packing.span G.incidence T) ≤
        (T \ U).card + Fintype.card (Fin r) * Module.finrank ℝ (Packing.span G.incidence U) := by
    intro U hUT
    change Fintype.card (Fin r) * Module.finrank ℝ (G.edgeSpan T) ≤
      (T \ U).card + Fintype.card (Fin r) * Module.finrank ℝ (G.edgeSpan U)
    rw [Fintype.card_fin, G.connected_rank hn hc, G.incidence_rank]
    have hpart := hp (G.rep U)
    have hcross := Finset.card_le_card (G.crossing_components_subset T U)
    have hcp := G.componentCount_pos hn U
    have hcle := G.componentCount_le U
    change r * (G.componentCount U - 1) ≤ (G.crossing T (G.rep U)).card at hpart
    have hnid : n - 1 = (G.componentCount U - 1) + (n - G.componentCount U) := by omega
    rw [hnid, Nat.mul_add]
    exact Nat.add_le_add_right (hpart.trans hcross) _
  obtain ⟨F, hv, hF⟩ := Packing.vector_base_packing_on G.incidence T hcrit
  refine ⟨F, fun i => ?_, hv.2⟩
  refine ⟨(hF i).1, (G.spanningTree_iff_independent (F i)).mpr ⟨?_, hv.1 i⟩⟩
  exact G.connected_of_span_eq (hF i).2.symm hc

lemma sum_partition_cuts (T : Finset (Fin m)) (p : Fin n → Fin n) :
    (∑ c ∈ Finset.univ.image p, (G.cut T (Finset.univ.filter (p · = c))).card) =
      2 * (G.crossing T p).card := by
  classical
  simp only [cut, crossing, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_comm]
  calc
    _ = ∑ e ∈ T, if p (G.left e) ≠ p (G.right e) then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases h : p (G.left e) = p (G.right e)
      · simp [h]
      · rw [ite_eq_left h]
        have hl : p (G.left e) ∈ Finset.univ.image p := Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
        have hr : p (G.right e) ∈ Finset.univ.image p := Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
        rw [Finset.sum_eq_add (p (G.left e)) (p (G.right e)) h]
        · simp [h, Ne.symm h]
        · intro c hc hh
          simp [Ne.symm hh.1, Ne.symm hh.2]
        · exact fun hh => (hh hl).elim
        · exact fun hh => (hh hr).elim
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; split_ifs <;> omega

lemma partition_fiber_proper (p : Fin n → Fin n) (hp : 1 < partitionSize p) (c : Fin n) :
    Finset.univ.filter (p · = c) ≠ Finset.univ := by
  intro h
  have him : Finset.univ.image p ⊆ {c} := by
    intro d hd
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hd
    have hv' : v ∈ Finset.univ.filter (p · = c) := by rw [h]; exact Finset.mem_univ v
    simpa using hv'
  have : partitionSize p ≤ 1 := by simpa [partitionSize] using Finset.card_le_card him
  omega

theorem edgeConnected_treePackable {r : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hc : G.EdgeConnected (2 * r)) : G.TreePackable Finset.univ r := by
  apply G.partition_criterion_sufficient _ hr hn
  intro p
  by_cases hp : partitionSize p ≤ 1
  · have : partitionSize p - 1 = 0 := by omega
    simp [this]
  have hp' : 1 < partitionSize p := by omega
  have hsum : (∑ c ∈ Finset.univ.image p, 2 * r) ≤
      ∑ c ∈ Finset.univ.image p, (G.cut Finset.univ (Finset.univ.filter (p · = c))).card := by
    apply Finset.sum_le_sum
    intro c hc'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc'
    exact hc _ ⟨v, by simp⟩ (partition_fiber_proper p hp' _)
  rw [G.sum_partition_cuts] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  change partitionSize p * (2 * r) ≤ _ at hsum
  have : r * partitionSize p ≤ (G.crossing Finset.univ p).card := by nlinarith
  exact (Nat.mul_le_mul_left r (Nat.sub_le _ _)).trans this

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_BinaryArithmetic
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable

instance poly_binaryToRat : PolyTime binaryToRat := by unfold binaryToRat;infer_instance

instance poly_binaryDiv (d : ℕ) : PolyTime (binaryDiv d) := by unfold binaryDiv;infer_instance

instance poly_binaryMod (d : ℕ) : PolyTime (binaryMod d) := by unfold binaryMod;infer_instance

instance poly_binaryModUnary (d : ℕ) [hd : Fact (0<d)] : PolyTime (binaryModUnary d) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=binaryMod d)
  refine ⟨⟨5*p+4*X+NaturalPolynomial.constant (6*d+4),?_⟩⟩
  intro n
  have ho := (binaryMod d).output_length n
  have hn := Nat.mod_lt n hd.out
  have hh := hp n
  change (binaryMod d).cost n+(6*(n%d)+4*(binaryNatCode (n%d)).length+4)≤_
  change (binaryMod d).cost n+(6*(n%d)+4*(binaryNatCode (n%d)).length+4)≤
    5*p.eval (binaryNatCode n).length+4*(binaryNatCode n).length+(6*d+4)
  omega

instance poly_ratDenRat : PolyTime ratDenRat := by unfold ratDenRat;infer_instance

instance poly_scalarProductBinary : PolyTime scalarProductBinary := by
  unfold scalarProductBinary;infer_instance

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_UnaryArithmetic
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable

instance poly_natSub : PolyTime natSub := by unfold natSub;infer_instance

instance poly_natDivBinary : PolyTime natDivBinary := by unfold natDivBinary;infer_instance

instance poly_natDiv : PolyTime natDiv := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=natDivBinary)
  refine ⟨⟨5*p+10*X+4,?_⟩⟩
  intro a
  have hc := hp a
  have ho := natDivBinary.output_length a
  have hn := Nat.div_le_self a.1 a.2
  have hl := le_prodCode_left (ea:=natCode) (eb:=natCode) a
  simp only [natCode,List.length_replicate] at hl
  change natDivBinary.cost a+(6*(a.1/a.2)+4*(binaryNatCode (a.1/a.2)).length+4)≤
    5*p.eval (prodCode natCode natCode a).length+10*(prodCode natCode natCode a).length+4
  omega

instance poly_natMod : PolyTime natMod := by unfold natMod;infer_instance

variable {α : Type*} {ea : α → Word} {f g : α → ℕ}
instance instPolyTimeNatNadd {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nadd s) := by unfold Realizes.nadd;infer_instance
instance instPolyTimeNatNmul {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nmul s) := by unfold Realizes.nmul;infer_instance
instance instPolyTimeNatNsub {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nsub s) := by unfold Realizes.nsub;infer_instance
instance instPolyTimeNatNdiv {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.ndiv s) := by unfold Realizes.ndiv;infer_instance
instance instPolyTimeNatNmod {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nmod s) := by unfold Realizes.nmod;infer_instance
instance instPolyTimeBoolNeqOfNat {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.neq s) := by unfold Realizes.neq;infer_instance
instance instPolyTimeBoolNltOfNat {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nlt s) := by unfold Realizes.nlt;infer_instance

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_PartitionRank
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uE2 uV2

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

lemma connectedOn_mono_span {A : Finset (Fin n)} {F T : Finset (Fin m)}
    (h : G.edgeSpan F ≤ G.edgeSpan T) (hc : G.ConnectedOn A F) : G.ConnectedOn A T := by
  intro u hu v hv
  exact h (hc u hu v hv)

lemma independent_spanning_subset (F : Finset (Fin m)) :
    ∃ T ⊆ F, LinearIndepOn ℝ G.incidence (T : Set (Fin m)) ∧ G.edgeSpan T = G.edgeSpan F := by
  classical
  let h : LinearIndepOn ℝ G.incidence (∅ : Set (Fin m)) := linearIndepOn_empty ℝ G.incidence
  let U := h.extend (Set.empty_subset (F : Set (Fin m)))
  refine ⟨U.toFinset, ?_, ?_, ?_⟩
  · intro e he
    exact h.extend_subset (Set.empty_subset (F : Set (Fin m))) (Set.mem_toFinset.mp he)
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.empty_subset (F : Set (Fin m)))
  · simpa only [edgeSpan, Packing.span, Set.coe_toFinset] using
      h.span_image_extend_eq_span_image (Set.empty_subset (F : Set (Fin m)))

lemma packableOn_iff_trees (F : Finset (Fin m)) (q : ℕ) (A : Finset (Fin n)) :
    G.PackableOn F q A ↔ ∃ T : Fin q → Finset (Fin m),
      (∀ i, T i ⊆ F ∧ G.TreeOn A (T i)) ∧
      ∀ ⦃i j⦄, i ≠ j → Disjoint (T i) (T j) := by
  classical
  constructor
  · rintro ⟨T, hT, hd⟩
    choose U hU hi hs using fun i => G.independent_spanning_subset (T i)
    refine ⟨U, fun i => ⟨?_, ?_, ?_, hi i⟩, fun i j hij =>
      disjoint_of_subset_left (hU i) (disjoint_of_subset_right (hU j) (hd hij))⟩
    · exact (hU i).trans ((hT i).1.trans (filter_subset _ _))
    · intro e he
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ((hT i).1 (hU i he))).2⟩
    · exact G.connectedOn_mono_span (le_of_eq (hs i).symm) (hT i).2
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨?_, (hT i).2.2.1⟩, hd⟩
    intro e he
    exact mem_filter.mpr ⟨(hT i).1 he, (mem_filter.mp ((hT i).2.1 he)).2⟩

lemma connectedOn_univ (T : Finset (Fin m)) : G.ConnectedOn univ T ↔ G.Connected T := by
  rw [G.connected_iff_same]
  simp only [ConnectedOn, mem_univ, forall_const]

lemma packableOn_univ (F : Finset (Fin m)) (q : ℕ) :
    G.PackableOn F q univ ↔ G.TreePackable F q := by
  rw [G.packableOn_iff_trees]
  constructor
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨(hT i).1, ?_⟩, hd⟩
    exact (G.spanningTree_iff_independent _).mpr
      ⟨(G.connectedOn_univ _).mp (hT i).2.2.1, (hT i).2.2.2⟩
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨(hT i).1, ?_, ?_, ?_⟩, hd⟩
    · simp [internal]
    · exact (G.connectedOn_univ _).mpr (hT i).2.1
    · exact ((G.spanningTree_iff_independent _).mp (hT i).2).2

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_PartitionHierarchy
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

lemma connectedOn_cut {A S : Finset (Fin n)} {T : Finset (Fin m)}
    (hc : G.ConnectedOn A T) (hS : S.Nonempty) (hSA : S ⊂ A) : (G.cut T S).Nonempty := by
  classical
  by_contra hcut
  have hempty : G.cut T S=∅ := not_nonempty_iff_eq_empty.mp hcut
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑u ∈ S, LinearMap.proj u
  have hker : G.edgeSpan T ≤ LinearMap.ker f := by
    apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    have hiff : G.left e ∈ S ↔ G.right e ∈ S := by
      have hh : ¬((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.right e ∈ S ∧ G.left e ∉ S)) := by
        intro h
        have hm : e ∈ G.cut T S := mem_filter.mpr ⟨he,h⟩
        simp [hempty] at hm
      tauto
    change f (G.incidence e)=0
    rw [incidence,map_sub]
    change (∑u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.left e)) -
      (∑u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.right e))=0
    simp only [sumOn_point,hiff,sub_self]
  obtain ⟨u,hu⟩ := hS
  have hv : (A \ S).Nonempty := sdiff_nonempty.mpr (not_subset.mpr (by
    by_contra h
    push Not at h
    exact (not_ssubset_of_subset h) hSA))
  obtain ⟨v,hv⟩ := hv
  obtain ⟨hvA,hvS⟩ := mem_sdiff.mp hv
  have hz := hker (hc u (hSA.subset hu) v hvA)
  change f (point u-point v)=0 at hz
  rw [map_sub] at hz
  change (∑w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point u) -
    (∑w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v)=0 at hz
  simp [sumOn_point,hu,hvS] at hz

lemma packableOn_edgeConnectedReal {F : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (hp : G.PackableOn F q A) : G.EdgeConnectedReal A q := by
  classical
  obtain ⟨T,hT,hd⟩ := hp
  intro S hS hSA
  have hne (i : Fin q) := G.connectedOn_cut (hT i).2 hS hSA
  have hdis : (↑(univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint (fun i => G.cut (T i) S) := by
    intro i _ j _ hij
    exact disjoint_of_subset_left (filter_subset _ _) (disjoint_of_subset_right (filter_subset _ _) (hd hij))
  have hsub : univ.biUnion (fun i : Fin q => G.cut (T i) S) ⊆ G.cut (G.inducedEdges A) S := by
    apply biUnion_subset.mpr
    intro i _ e he
    obtain ⟨het,hes⟩ := mem_filter.mp he
    have hh := (mem_filter.mp ((hT i).1 het)).2
    exact mem_filter.mpr ⟨(G.mem_inducedEdges A e).mpr hh,hes⟩
  have hh := card_le_card hsub
  rw [card_biUnion hdis] at hh
  have hl : q ≤ ∑i : Fin q, (G.cut (T i) S).card := by
    simpa using sum_le_sum (s := (univ : Finset (Fin q))) (f := fun _ => 1)
      (g := fun i => (G.cut (T i) S).card) (fun i _ => card_pos.mpr (hne i))
  exact_mod_cast hl.trans hh

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ExtractionCriterion
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset Matrix
open scoped MatrixOrder
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma treePackable_edgeConnected {r : ℕ} (hp : G.TreePackable univ r) : G.EdgeConnected r := by
  have hh := G.packableOn_edgeConnectedReal ((G.packableOn_univ univ r).mpr hp)
  intro S hS hS'
  have hs : S ⊂ (univ : Finset (Fin n)) := Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,hS'⟩
  have hc := hh S hS hs
  have hi : G.inducedEdges univ = univ := by ext e; simp [mem_inducedEdges]
  rw [hi] at hc
  exact_mod_cast hc

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNeqOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNltOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeNatNadd _root_.OAI.CurrentKS.Realization.instPolyTimeNatNdiv _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmod _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmul _root_.OAI.CurrentKS.Realization.instPolyTimeNatNsub _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_binaryDiv _root_.OAI.CurrentKS.Realization.poly_binaryMod _root_.OAI.CurrentKS.Realization.poly_binaryModUnary _root_.OAI.CurrentKS.Realization.poly_binaryToRat _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natDiv _root_.OAI.CurrentKS.Realization.poly_natDivBinary _root_.OAI.CurrentKS.Realization.poly_natMod _root_.OAI.CurrentKS.Realization.poly_natSub _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenRat _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scalarProductBinary _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization realization. -/

section


namespace AlgorithmicThinTrees.Normalization.Stack
open CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open Matrix
instance poly_numColumns : PolyTime numColumns := by
  unfold numColumns
  apply poly_congr

instance poly_outer : PolyTime outer := by
  unfold outer
  infer_instance
instance poly_column : PolyTime column := by unfold column; apply poly_congr
instance poly_scale : PolyTime scale := by unfold scale; infer_instance

instance poly_updated : PolyTime updated := by unfold updated; apply poly_congr

instance poly_initial : PolyTime initial := by unfold initial; infer_instance

instance poly_unaryPow (k : ℕ) : PolyTime (unaryPow k) := by
  induction k with
  | zero => unfold unaryPow; apply poly_congr
  | succ k ih => unfold unaryPow; infer_instance

instance poly_multiplierProgram : PolyTime multiplierProgram := by
  unfold multiplierProgram; apply poly_sub

instance poly_fixedStep : PolyTime fixedStep := by unfold fixedStep; apply poly_changeOutput

instance poly_lengthProgram : PolyTime lengthProgram := by unfold lengthProgram; apply poly_then

end AlgorithmicThinTrees.Normalization.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_MatrixRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_column _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_fixedStep _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_initial _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_lengthProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_multiplierProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_numColumns _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_outer _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_scale _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_unaryPow _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_updated _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNeqOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNltOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeNatNadd _root_.OAI.CurrentKS.Realization.instPolyTimeNatNdiv _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmod _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmul _root_.OAI.CurrentKS.Realization.instPolyTimeNatNsub _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_binaryDiv _root_.OAI.CurrentKS.Realization.poly_binaryMod _root_.OAI.CurrentKS.Realization.poly_binaryModUnary _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binaryToRat _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natDiv _root_.OAI.CurrentKS.Realization.poly_natDivBinary _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_natMod _root_.OAI.CurrentKS.Realization.poly_natSub _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenRat _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scalarProductBinary _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix realization. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}

instance poly_schurEntry : PolyTime schurEntry := by unfold schurEntry; apply poly_sub

instance poly_schur : PolyTime schur := by unfold schur; apply poly_changeOutput

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_SchurHistory
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNeqOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNltOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeNatNadd _root_.OAI.CurrentKS.Realization.instPolyTimeNatNdiv _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmod _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmul _root_.OAI.CurrentKS.Realization.instPolyTimeNatNsub _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_binaryDiv _root_.OAI.CurrentKS.Realization.poly_binaryMod _root_.OAI.CurrentKS.Realization.poly_binaryModUnary _root_.OAI.CurrentKS.Realization.poly_binaryToRat _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natDiv _root_.OAI.CurrentKS.Realization.poly_natDivBinary _root_.OAI.CurrentKS.Realization.poly_natMod _root_.OAI.CurrentKS.Realization.poly_natSub _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenRat _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scalarProductBinary _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Schur history. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

instance poly_schurNext : PolyTime schurNext := by unfold schurNext; infer_instance

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_FiniteFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite families. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_dite {α β : Type*} {ea : α → Word} {eb : β → Word}
    {P : α → Prop} [DecidablePred P]
    {f : {a // P a} → β} {g : {a // ¬P a} → β}
    (test : Realizes ea boolCode (fun a => decide (P a)))
    (r : Realizes (fun a : {a // P a} => ea a.val) eb f)
    (s : Realizes (fun a : {a // ¬P a} => ea a.val) eb g)
    [PolyTime test] [PolyTime r] [PolyTime s] : PolyTime (test.dite r s) := by
  refine ⟨?_⟩
  exact (RunsPoly.dite_families
    (RunsPoly.of_poly test id (isPoly_self (fun a => (ea a).length)))
    (RunsPoly.of_poly r id (isPoly_self (fun a : {a // P a} => (ea a.val).length)))
    (RunsPoly.of_poly s id (isPoly_self (fun a : {a // ¬P a} => (ea a.val).length)))).cost

variable {α β : Type*} {ea : α → Word} {eb : β → Word}
variable {I J : α → Type*} {n m : α → ℕ}

instance poly_indexedFirst (e : (a : α) → I a ≃ Fin (n a)) :
    PolyTime (indexedFirst (ea:=ea) e) := by unfold indexedFirst;apply poly_reindex
instance poly_indexedIndex (e : (a : α) → I a ≃ Fin (n a)) :
    PolyTime (indexedIndex (ea:=ea) e) := by unfold indexedIndex;apply poly_reindex

instance poly_tabulateIndexed {e : (a : α) → I a ≃ Fin (n a)} {f : (Σ a,I a) → β}
    (r : Realizes (indexedCode ea e) eb f) (rn : Realizes ea natCode n)
    [PolyTime r] [PolyTime rn] : PolyTime (r.tabulateIndexed rn) := by
  unfold Realizes.tabulateIndexed
  refine @poly_tabulateFin _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_reindex
  · infer_instance

instance poly_indexedSumTest (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rn : Realizes ea natCode n) [PolyTime rn] :
    PolyTime (indexedSumTest e e' rn) := by unfold indexedSumTest;infer_instance

instance poly_indexedSumRight (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rn : Realizes ea natCode n) [PolyTime rn] :
    PolyTime (indexedSumRight e e' rn) := by unfold indexedSumRight;infer_instance

instance poly_sumCases {e : (a : α) → I a ≃ Fin (n a)}
    {e' : (a : α) → J a ≃ Fin (m a)} {f : (Σ a,I a) → β} {g : (Σ a,J a) → β}
    (r : Realizes (indexedCode ea e) eb f) (s : Realizes (indexedCode ea e') eb g)
    (rn : Realizes ea natCode n) [PolyTime r] [PolyTime s] [PolyTime rn] :
    PolyTime (r.sumCases s rn) := by unfold Realizes.sumCases;infer_instance

instance poly_splitProduct (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) [PolyTime rm] :
    PolyTime (splitProduct e e' rm) := by unfold splitProduct;infer_instance

instance poly_indexedProductLeft (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) [PolyTime rm] :
    PolyTime (indexedProductLeft e e' rm) := by unfold indexedProductLeft;infer_instance

instance poly_indexedProductRight (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) [PolyTime rm] :
    PolyTime (indexedProductRight e e' rm) := by unfold indexedProductRight;apply poly_changeOutput

instance poly_not {P : α → Prop} [DecidablePred P]
    (r : Realizes ea boolCode (fun a => decide (P a))) [PolyTime r] : PolyTime r.not := by
  unfold Realizes.not;infer_instance

instance poly_and {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (r : Realizes ea boolCode (fun a => decide (P a)))
    (s : Realizes ea boolCode (fun a => decide (Q a))) [PolyTime r] [PolyTime s] : PolyTime (r.and s) := by
  unfold Realizes.and;infer_instance

instance poly_finEq {n : α → ℕ} {f g : (a : α) → Fin (n a)}
    (r : Realizes ea natCode (fun a => (f a).val))
    (s : Realizes ea natCode (fun a => (g a).val)) [PolyTime r] [PolyTime s] :
    PolyTime (r.finEq s) := by unfold Realizes.finEq;infer_instance
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GraphRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_and _root_.OAI.CurrentKS.Realization.poly_dite _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_finEq _root_.OAI.CurrentKS.Realization.poly_indexedFirst _root_.OAI.CurrentKS.Realization.poly_indexedIndex _root_.OAI.CurrentKS.Realization.poly_indexedProductLeft _root_.OAI.CurrentKS.Realization.poly_indexedProductRight _root_.OAI.CurrentKS.Realization.poly_indexedSumRight _root_.OAI.CurrentKS.Realization.poly_indexedSumTest _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_not _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_splitProduct _root_.OAI.CurrentKS.Realization.poly_sumCases _root_.OAI.CurrentKS.Realization.poly_tabulateIndexed _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graph realization. -/

section

namespace AlgorithmicThinTrees.GraphStack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.MetricTests.RationalStep
open scoped BigOperators

instance poly_numEdges : PolyTime numEdges := by unfold numEdges;apply poly_congr

instance poly_edgeLeft : PolyTime edgeLeft := by unfold edgeLeft;apply poly_congr
instance poly_edgeRight : PolyTime edgeRight := by unfold edgeRight;apply poly_congr

instance poly_constantMatrix : PolyTime constantMatrix := by unfold constantMatrix;infer_instance

instance poly_projection : PolyTime projection := by unfold projection;infer_instance

end AlgorithmicThinTrees.GraphStack

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix
open scoped BigOperators

instance poly_dimensionProgram : PolyTime dimensionProgram := by
  unfold dimensionProgram Realizes.nadd
  apply poly_then

instance poly_rawEntry : PolyTime rawEntry := by unfold rawEntry;infer_instance

instance poly_raw : PolyTime raw := by unfold raw;infer_instance

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_Parameters
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_and _root_.OAI.CurrentKS.Realization.poly_dite _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_finEq _root_.OAI.CurrentKS.Realization.poly_indexedFirst _root_.OAI.CurrentKS.Realization.poly_indexedIndex _root_.OAI.CurrentKS.Realization.poly_indexedProductLeft _root_.OAI.CurrentKS.Realization.poly_indexedProductRight _root_.OAI.CurrentKS.Realization.poly_indexedSumRight _root_.OAI.CurrentKS.Realization.poly_indexedSumTest _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_not _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_splitProduct _root_.OAI.CurrentKS.Realization.poly_sumCases _root_.OAI.CurrentKS.Realization.poly_tabulateIndexed _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pencil parameters. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

private instance poly_paramsGraph : PolyTime paramsGraph := by
  unfold paramsGraph
  apply poly_then

private instance poly_paramsN : PolyTime paramsN := by
  unfold paramsN
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · unfold numVertices
    apply poly_then

private instance poly_paramsM : PolyTime paramsM := by
  unfold paramsM
  apply poly_then

instance poly_paramsField (k : ℕ) : PolyTime (paramsField k) := by unfold paramsField;apply poly_then
private instance poly_pointParams : PolyTime pointParams := by
  unfold pointParams
  apply poly_then

instance poly_pointParser : PolyTime pointParser := by
  have : PolyTime paramsDim := by unfold paramsDim; apply poly_then
  unfold pointParser
  apply poly_changeOutput

variable {α : Type*} {ea : α → Word} {p : α → Point}
instance poly_coordinate (rp : Realizes ea pointCode p)
    (i : (a : α) → Fin (dimension (p a).p.graph.n (p a).p.graph.m))
    (ri : Realizes ea natCode (fun a => (i a).val)) [PolyTime rp] [PolyTime ri] :
    PolyTime (coordinate rp i ri) := by unfold coordinate;apply poly_congr

instance poly_rawPoint : PolyTime rawPoint := by
  have : PolyTime pointN := by unfold pointN; apply poly_then
  have : PolyTime pointM := by unfold pointM; apply poly_then
  unfold rawPoint
  apply poly_changeOutput
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_PointPrograms
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Point programs. -/

section

namespace CurrentKS.Realization
open CleanRoutine
variable {α β : Type*} {ea : α → Word} {eb : β → Word}
instance poly_cons {f : α → β} {g : α → List β}
    (r : Realizes ea eb f) (s : Realizes ea (listCode eb) g) [PolyTime r] [PolyTime s] :
    PolyTime (r.cons s) := by unfold Realizes.cons;infer_instance

instance poly_select3 {i : α → Fin 3} (ri : Realizes ea natCode (fun a => (i a).val))
    {f g h : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g)
    (t : Realizes ea ratCode h) [PolyTime ri] [PolyTime r] [PolyTime s] [PolyTime t] :
    PolyTime (select3 ri r s t) := by unfold select3;apply poly_congr

instance poly_select7 {i : α → Fin 7} (ri : Realizes ea natCode (fun a => (i a).val))
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : α → ℚ}
    (r₀ : Realizes ea ratCode f₀) (r₁ : Realizes ea ratCode f₁) (r₂ : Realizes ea ratCode f₂)
    (r₃ : Realizes ea ratCode f₃) (r₄ : Realizes ea ratCode f₄) (r₅ : Realizes ea ratCode f₅)
    (r₆ : Realizes ea ratCode f₆) [PolyTime ri] [PolyTime r₀] [PolyTime r₁] [PolyTime r₂]
    [PolyTime r₃] [PolyTime r₄] [PolyTime r₅] [PolyTime r₆] :
    PolyTime (select7 ri r₀ r₁ r₂ r₃ r₄ r₅ r₆) := by unfold select7;apply poly_congr
end CurrentKS.Realization

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators
variable {α : Type*} {ea : α → Word} {a : α → Point}

instance poly_storedU (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val))
    [PolyTime r] [PolyTime re] : PolyTime (storedU r e re) := by unfold storedU;apply poly_congr

instance poly_graphEdge (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val))
    [PolyTime r] [PolyTime re] : PolyTime (graphEdge r e re) := by unfold graphEdge;apply poly_changeOutput

instance poly_tripleDistinct : PolyTime tripleDistinct := by
  have : PolyTime tripleI := by infer_instance
  have : PolyTime tripleJ := by infer_instance
  have : PolyTime tripleK := by infer_instance
  unfold tripleDistinct
  refine @poly_and _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · refine @poly_and _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · apply poly_not

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_BoolPrograms
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bool programs. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
variable {α : Type*} {ea : α → Word}

instance poly_or {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (r : Realizes ea boolCode (fun a => decide (P a)))
    (s : Realizes ea boolCode (fun a => decide (Q a))) [PolyTime r] [PolyTime s] : PolyTime (r.or s) := by
  unfold Realizes.or;infer_instance

instance poly_anyTrue : PolyTime anyTrue := by unfold anyTrue;infer_instance

instance poly_allTrue : PolyTime allTrue := by unfold allTrue;infer_instance

variable {n : α → ℕ} {P : (a : α) → Fin (n a) → Prop} [∀a,DecidablePred (P a)]
instance poly_existsFin
    (r : Realizes (finFamilyCode ea n) boolCode (fun p => decide (P p.1 p.2)))
    (rn : Realizes ea natCode n) [PolyTime r] [PolyTime rn] : PolyTime (r.existsFin rn) := by
  unfold Realizes.existsFin;infer_instance

instance poly_forallFin
    (r : Realizes (finFamilyCode ea n) boolCode (fun p => decide (P p.1 p.2)))
    (rn : Realizes ea natCode n) [PolyTime r] [PolyTime rn] : PolyTime (r.forallFin rn) := by
  unfold Realizes.forallFin;infer_instance

lemma bools_length (bs : List Bool) : (boolsCode bs).length=3*bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change (listCode boolCode (b::bs)).length=_
    rw [listCode_cons,prodCode_length]
    change 2*1+1+(boolsCode bs).length=3*(bs.length+1)
    rw [ih];omega

lemma bools_ofFn_length {n : ℕ} (f : Fin n → Bool) :
    (boolsCode (List.ofFn f)).length=3*n := by rw [bools_length,List.length_ofFn]

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_ScalarRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_constantMatrix _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeLeft _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeRight _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_numEdges _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_projection _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_coordinate _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_dimensionProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsField _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParser _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_raw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawEntry _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawPoint _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_storedU _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_tripleDistinct _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_column _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_fixedStep _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_initial _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_lengthProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_multiplierProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_numColumns _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_outer _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_scale _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_unaryPow _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_updated _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNeqOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNltOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeNatNadd _root_.OAI.CurrentKS.Realization.instPolyTimeNatNdiv _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmod _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmul _root_.OAI.CurrentKS.Realization.instPolyTimeNatNsub _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_allTrue _root_.OAI.CurrentKS.Realization.poly_and _root_.OAI.CurrentKS.Realization.poly_anyTrue _root_.OAI.CurrentKS.Realization.poly_cons _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_dite _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_existsFin _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_finEq _root_.OAI.CurrentKS.Realization.poly_forallFin _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_indexedFirst _root_.OAI.CurrentKS.Realization.poly_indexedIndex _root_.OAI.CurrentKS.Realization.poly_indexedProductLeft _root_.OAI.CurrentKS.Realization.poly_indexedProductRight _root_.OAI.CurrentKS.Realization.poly_indexedSumRight _root_.OAI.CurrentKS.Realization.poly_indexedSumTest _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natDiv _root_.OAI.CurrentKS.Realization.poly_natDivBinary _root_.OAI.CurrentKS.Realization.poly_natMod _root_.OAI.CurrentKS.Realization.poly_natSub _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_not _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_or _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_schur _root_.OAI.CurrentKS.Realization.poly_schurEntry _root_.OAI.CurrentKS.Realization.poly_schurNext _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_select3 _root_.OAI.CurrentKS.Realization.poly_select7 _root_.OAI.CurrentKS.Realization.poly_splitProduct _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_sumCases _root_.OAI.CurrentKS.Realization.poly_tabulateIndexed _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsM _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsN _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 AlgorithmicThinTrees.RationalGram
instance poly_squareScan : PolyTime squareScan := by
  let : Fact (0<4) := ⟨by decide⟩
  unfold squareScan
  apply poly_both

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_UnaryRoot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_constantMatrix _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeLeft _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeRight _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_numEdges _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_projection _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_coordinate _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_dimensionProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsField _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParser _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_raw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawEntry _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawPoint _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_storedU _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_tripleDistinct _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNeqOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNltOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeNatNadd _root_.OAI.CurrentKS.Realization.instPolyTimeNatNdiv _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmod _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmul _root_.OAI.CurrentKS.Realization.instPolyTimeNatNsub _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_allTrue _root_.OAI.CurrentKS.Realization.poly_and _root_.OAI.CurrentKS.Realization.poly_anyTrue _root_.OAI.CurrentKS.Realization.poly_binaryDiv _root_.OAI.CurrentKS.Realization.poly_binaryMod _root_.OAI.CurrentKS.Realization.poly_binaryModUnary _root_.OAI.CurrentKS.Realization.poly_binaryToRat _root_.OAI.CurrentKS.Realization.poly_cons _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_dite _root_.OAI.CurrentKS.Realization.poly_existsFin _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_finEq _root_.OAI.CurrentKS.Realization.poly_forallFin _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_indexedFirst _root_.OAI.CurrentKS.Realization.poly_indexedIndex _root_.OAI.CurrentKS.Realization.poly_indexedProductLeft _root_.OAI.CurrentKS.Realization.poly_indexedProductRight _root_.OAI.CurrentKS.Realization.poly_indexedSumRight _root_.OAI.CurrentKS.Realization.poly_indexedSumTest _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natDiv _root_.OAI.CurrentKS.Realization.poly_natDivBinary _root_.OAI.CurrentKS.Realization.poly_natMod _root_.OAI.CurrentKS.Realization.poly_natSub _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_not _root_.OAI.CurrentKS.Realization.poly_or _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenRat _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scalarProductBinary _root_.OAI.CurrentKS.Realization.poly_schur _root_.OAI.CurrentKS.Realization.poly_schurEntry _root_.OAI.CurrentKS.Realization.poly_schurNext _root_.OAI.CurrentKS.Realization.poly_select3 _root_.OAI.CurrentKS.Realization.poly_select7 _root_.OAI.CurrentKS.Realization.poly_splitProduct _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_sumCases _root_.OAI.CurrentKS.Realization.poly_tabulateIndexed _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsM _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsN _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary root. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable

instance poly_unaryRootStep (d : ℕ) : PolyTime (unaryRootStepProgram d) := by
  unfold unaryRootStepProgram
  apply poly_congr

instance size_unaryRootStep (d : ℕ) : IterateSize (unaryRootStepProgram d) := by
  refine ⟨⟨X,?_⟩⟩
  intro a k
  have h := unaryRootStep_iterate_bound d k a
  change (rootCode ((unaryRootStep d)^[k] a)).length≤(rootCode a).length+k
  simp only [rootCode,prodCode_length,natCode,List.length_replicate,h.1]
  omega

instance poly_unaryRoot (d : ℕ) (hd : d≠0) : PolyTime (unaryRoot d hd) := by
  unfold unaryRoot;infer_instance
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation start. -/

section

namespace AlgorithmicThinTrees.MetricTests
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma packing_connected (H : MultiGraph n m) {r : ℕ} (hr : 0 < r)
    (hp : H.TreePackable univ r) : H.Connected univ := by
  intro S hS hS'
  apply card_pos.mp
  exact hr.trans_le (H.treePackable_edgeConnected hp S hS hS')

end AlgorithmicThinTrees.MetricTests

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_BlockAssembly
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_constantMatrix _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeLeft _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeRight _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_numEdges _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_projection _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_coordinate _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_dimensionProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsField _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParser _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_raw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawEntry _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawPoint _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_storedU _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_tripleDistinct _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_allTrue _root_.OAI.CurrentKS.Realization.poly_and _root_.OAI.CurrentKS.Realization.poly_anyTrue _root_.OAI.CurrentKS.Realization.poly_cons _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_dite _root_.OAI.CurrentKS.Realization.poly_existsFin _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_finEq _root_.OAI.CurrentKS.Realization.poly_forallFin _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_indexedFirst _root_.OAI.CurrentKS.Realization.poly_indexedIndex _root_.OAI.CurrentKS.Realization.poly_indexedProductLeft _root_.OAI.CurrentKS.Realization.poly_indexedProductRight _root_.OAI.CurrentKS.Realization.poly_indexedSumRight _root_.OAI.CurrentKS.Realization.poly_indexedSumTest _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_not _root_.OAI.CurrentKS.Realization.poly_or _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_select3 _root_.OAI.CurrentKS.Realization.poly_select7 _root_.OAI.CurrentKS.Realization.poly_splitProduct _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_sumCases _root_.OAI.CurrentKS.Realization.poly_tabulateIndexed _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsM _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsN _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block assembly. -/

section

namespace CurrentKS.Realization
open CleanRoutine Matrix KS.W23

instance poly_stK : PolyTime stK := by unfold stK;infer_instance
instance poly_stCut : PolyTime stCut := by unfold stCut;infer_instance

instance poly_stitchedMatrixEntry : PolyTime stitchedMatrixEntry := by
  have : PolyTime stI := by infer_instance
  have : PolyTime stJ := by infer_instance
  have : PolyTime stMatrices := by infer_instance
  unfold stitchedMatrixEntry;infer_instance

instance poly_stitchProgramEntry : PolyTime stitchProgramEntry := by
  have : PolyTime stI := by infer_instance
  have : PolyTime stJ := by infer_instance
  have : PolyTime stScalars := by infer_instance
  unfold stitchProgramEntry;infer_instance

instance poly_stitchProgram : PolyTime stitchProgram := by
  unfold stitchProgram
  apply poly_then

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_allTrue _root_.OAI.CurrentKS.Realization.poly_anyTrue _root_.OAI.CurrentKS.Realization.poly_existsFin _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_forallFin _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_or _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pencil realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack

instance poly_matrixCount : PolyTime matrixCount := by unfold matrixCount;infer_instance
instance poly_scalarCount : PolyTime scalarCount := by unfold scalarCount;infer_instance

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_SearchRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_allTrue _root_.OAI.CurrentKS.Realization.poly_anyTrue _root_.OAI.CurrentKS.Realization.poly_existsFin _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_forallFin _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_or _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Search realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

instance poly_graphRadius : PolyTime graphRadius := by unfold graphRadius;infer_instance

instance poly_graphBound : PolyTime graphBound := by
  unfold graphBound
  refine @poly_mul _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · refine @poly_add _ _ _ _ _ _ ?_ ?_
    · apply poly_then
    · infer_instance

instance poly_graphZeros : PolyTime graphZeros := by unfold graphZeros;infer_instance

instance poly_gridStep : PolyTime gridStep := by unfold gridStep;infer_instance

instance poly_gridMesh : PolyTime gridMesh := by unfold gridMesh;infer_instance

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_allTrue _root_.OAI.CurrentKS.Realization.poly_anyTrue _root_.OAI.CurrentKS.Realization.poly_existsFin _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_forallFin _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_or _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

private instance poly_graphBaseline : PolyTime graphBaseline := by
  unfold graphBaseline
  apply poly_div

private instance poly_graphStep : PolyTime graphStep := by
  unfold graphStep
  apply poly_div

instance poly_graphError : PolyTime graphError := by unfold graphError;infer_instance

instance poly_gainProgram : PolyTime gainProgram := by unfold gainProgram; apply poly_div

instance poly_clockProgram : PolyTime clockProgram := by
  unfold clockProgram Realizes.nmul
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · apply poly_then
  · infer_instance

private instance poly_loopGraph : PolyTime loopGraph := by
  unfold loopGraph
  apply poly_then

private instance poly_loopCount : PolyTime loopCount := by
  unfold loopCount
  apply poly_then

private instance poly_loopScale : PolyTime loopScale := by
  unfold loopScale
  apply poly_then

private instance poly_loopQuality : PolyTime loopQuality := by
  unfold loopQuality
  apply poly_then

private instance poly_loopTarget : PolyTime loopTarget := by
  unfold loopTarget
  apply poly_sub

instance poly_loopParams : PolyTime loopParams := by unfold loopParams; apply poly_changeOutput

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_BitBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_allTrue _root_.OAI.CurrentKS.Realization.poly_anyTrue _root_.OAI.CurrentKS.Realization.poly_existsFin _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_forallFin _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_or _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation bit bound. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

instance poly_meshRaw : PolyTime meshRaw := by
  have hg : PolyTime meshGraph := by unfold meshGraph; apply poly_then
  have hv : PolyTime meshVector := by unfold meshVector; apply poly_then
  unfold meshRaw
  apply poly_changeOutput

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_InverseRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_constantMatrix _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeLeft _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeRight _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_numEdges _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_projection _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_clockProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_coordinate _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_dimensionProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gainProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphBound _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphError _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphRadius _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphZeros _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gridMesh _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gridStep _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_matrixCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshRaw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsField _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParser _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_raw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawEntry _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawPoint _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_storedU _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_tripleDistinct _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNeqOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNltOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeNatNadd _root_.OAI.CurrentKS.Realization.instPolyTimeNatNdiv _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmod _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmul _root_.OAI.CurrentKS.Realization.instPolyTimeNatNsub _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_allTrue _root_.OAI.CurrentKS.Realization.poly_and _root_.OAI.CurrentKS.Realization.poly_anyTrue _root_.OAI.CurrentKS.Realization.poly_binaryDiv _root_.OAI.CurrentKS.Realization.poly_binaryMod _root_.OAI.CurrentKS.Realization.poly_binaryModUnary _root_.OAI.CurrentKS.Realization.poly_binaryToRat _root_.OAI.CurrentKS.Realization.poly_cons _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_dite _root_.OAI.CurrentKS.Realization.poly_existsFin _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_finEq _root_.OAI.CurrentKS.Realization.poly_forallFin _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_indexedFirst _root_.OAI.CurrentKS.Realization.poly_indexedIndex _root_.OAI.CurrentKS.Realization.poly_indexedProductLeft _root_.OAI.CurrentKS.Realization.poly_indexedProductRight _root_.OAI.CurrentKS.Realization.poly_indexedSumRight _root_.OAI.CurrentKS.Realization.poly_indexedSumTest _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natDiv _root_.OAI.CurrentKS.Realization.poly_natDivBinary _root_.OAI.CurrentKS.Realization.poly_natMod _root_.OAI.CurrentKS.Realization.poly_natSub _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_not _root_.OAI.CurrentKS.Realization.poly_or _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenRat _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scalarProductBinary _root_.OAI.CurrentKS.Realization.poly_select3 _root_.OAI.CurrentKS.Realization.poly_select7 _root_.OAI.CurrentKS.Realization.poly_splitProduct _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_stCut _root_.OAI.CurrentKS.Realization.poly_stK _root_.OAI.CurrentKS.Realization.poly_stitchProgram _root_.OAI.CurrentKS.Realization.poly_stitchProgramEntry _root_.OAI.CurrentKS.Realization.poly_stitchedMatrixEntry _root_.OAI.CurrentKS.Realization.poly_sumCases _root_.OAI.CurrentKS.Realization.poly_tabulateIndexed _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphBaseline _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphStep _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopQuality _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopScale _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopTarget _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsM _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsN _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

instance poly_solveRhs : PolyTime solveRhs := by unfold solveRhs;infer_instance

instance poly_solveTopRow : PolyTime solveTopRow := by unfold solveTopRow;infer_instance

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_GramRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_clockProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gainProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphBound _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphError _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphRadius _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphZeros _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gridMesh _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gridStep _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_matrixCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshRaw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarCount _root_.OAI.CurrentKS.Realization.poly_allTrue _root_.OAI.CurrentKS.Realization.poly_anyTrue _root_.OAI.CurrentKS.Realization.poly_existsFin _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_forallFin _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_or _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_stCut _root_.OAI.CurrentKS.Realization.poly_stK _root_.OAI.CurrentKS.Realization.poly_stitchProgram _root_.OAI.CurrentKS.Realization.poly_stitchProgramEntry _root_.OAI.CurrentKS.Realization.poly_stitchedMatrixEntry _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphBaseline _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphStep _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopQuality _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopScale _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopTarget _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix AlgorithmicThinTrees

instance poly_firstColumn : PolyTime firstColumn := by unfold firstColumn;infer_instance

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_clockProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gainProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphBound _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphError _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphRadius _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphZeros _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gridMesh _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gridStep _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_matrixCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshRaw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarCount _root_.OAI.CurrentKS.Realization.poly_allTrue _root_.OAI.CurrentKS.Realization.poly_anyTrue _root_.OAI.CurrentKS.Realization.poly_existsFin _root_.OAI.CurrentKS.Realization.poly_forallFin _root_.OAI.CurrentKS.Realization.poly_or _root_.OAI.CurrentKS.Realization.poly_stCut _root_.OAI.CurrentKS.Realization.poly_stK _root_.OAI.CurrentKS.Realization.poly_stitchProgram _root_.OAI.CurrentKS.Realization.poly_stitchProgramEntry _root_.OAI.CurrentKS.Realization.poly_stitchedMatrixEntry _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphBaseline _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphStep _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopQuality _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopScale _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopTarget _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signing realization. -/

section

namespace AlgorithmicThinTrees.Signing.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix

private instance poly_frameDim : PolyTime frameDim := by
  unfold frameDim
  apply poly_then

private instance poly_frameRows : PolyTime frameRows := by
  unfold frameRows
  apply poly_then

instance poly_complexField : PolyTime complexField := by unfold complexField;infer_instance

instance poly_outerFields : PolyTime outerFields := by unfold outerFields;infer_instance

instance poly_signerInput : PolyTime signerInput := by
  unfold signerInput
  apply poly_changeOutput

instance poly_stack : PolyTime stack := by
  have : PolyTime pairLeft := by unfold pairLeft; apply poly_then
  have : PolyTime pairRight := by unfold pairRight; apply poly_then
  unfold stack
  apply poly_changeOutput

end AlgorithmicThinTrees.Signing.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GreedyTree
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Greedy tree. -/

section

namespace AlgorithmicThinTrees.GreedyTree
open Finset StrongThinTree StrongThinTree.MultiGraph
variable {n m : ℕ}

lemma connected_mono (G : MultiGraph n m) {A B : Finset (Fin m)} (h : A ⊆ B)
    (hc : G.Connected A) : G.Connected B := by
  intro S hS hS'
  exact (hc S hS hS').mono (filter_subset_filter _ h)

lemma eraseIf_subset (G : MultiGraph n m) (A : Finset (Fin m)) (e : Fin m) :
    eraseIf G A e ⊆ A := by
  unfold eraseIf
  split_ifs <;> simp only [erase_subset,Subset.refl]

lemma eraseIf_connected (G : MultiGraph n m) (A : Finset (Fin m)) (hc : G.Connected A)
    (e : Fin m) : G.Connected (eraseIf G A e) := by
  unfold eraseIf
  split_ifs with hh
  · exact (connected_correct G (A.erase e)).mp hh
  · exact hc

lemma deletePass_correct (G : MultiGraph n m) (es : List (Fin m))
    (A : Finset (Fin m)) (hc : G.Connected A) :
    deletePass G A es ⊆ A ∧ G.Connected (deletePass G A es) ∧
      ∀e ∈ es, e ∈ deletePass G A es → ¬G.Connected ((deletePass G A es).erase e) := by
  induction es generalizing A with
  | nil => exact ⟨subset_rfl,hc,by simp⟩
  | cons e es ih =>
    rw [deletePass,List.foldl_cons]
    change deletePass G (eraseIf G A e) es ⊆ A ∧ _
    obtain ⟨hsub,hconn,hmin⟩ := ih (eraseIf G A e) (eraseIf_connected G A hc e)
    refine ⟨hsub.trans (eraseIf_subset G A e),hconn,?_⟩
    intro f hf hmem hcon
    rcases List.mem_cons.mp hf with rfl|hf
    · have heA : f ∈ eraseIf G A f := hsub hmem
      have hbad : connected G (A.erase f)≠true := by
        intro he
        simp only [eraseIf,he,ite_true, if_true,mem_erase,ne_eq,not_true_eq_false,false_and] at heA
      apply hbad
      apply (connected_correct G (A.erase f)).mpr
      exact connected_mono G (erase_subset_erase _ (hsub.trans (eraseIf_subset G A f))) hcon
    · exact hmin f hf hmem hcon

theorem tree_correct (G : MultiGraph n m) (hc : G.Connected univ) : G.SpanningTree (tree G) := by
  obtain ⟨_,hconn,hmin⟩ := deletePass_correct G (List.finRange m) univ hc
  refine ⟨hconn,?_⟩
  intro e he
  exact hmin e (List.mem_finRange _) he

end AlgorithmicThinTrees.GreedyTree
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_IterationBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace StrongThinTree

lemma errorU_nonneg (r : ℕ) : 0 ≤ errorU r := Real.rpow_nonneg (Nat.cast_nonneg _) _
lemma errorU_le_one {r : ℕ} (hr : 1 ≤ r) : errorU r ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hr) (by norm_num)

lemma errorU_halving {r s : ℕ} (hs : 0 < s) (hrs : (s:ℝ) ≤ (r:ℝ)/2) :
    (2:ℝ)^(1/16:ℝ)*errorU r ≤ errorU s := by
  have hsR : (0:ℝ) < s := Nat.cast_pos.mpr hs
  have hrR : (0:ℝ) < r := by linarith
  have hh := Real.rpow_le_rpow_of_nonpos hsR hrs (by norm_num : (-1/16:ℝ) ≤ 0)
  rw [Real.div_rpow hrR.le (by norm_num)] at hh
  have hi : (2:ℝ)^(-1/16:ℝ)=((2:ℝ)^(1/16:ℝ))⁻¹ := by
    rw [show (-1/16:ℝ)=-(1/16:ℝ) by ring,Real.rpow_neg (by norm_num)]
  simpa only [hi,div_inv_eq_mul,mul_comm,errorU] using hh

end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_allTrue _root_.OAI.CurrentKS.Realization.poly_anyTrue _root_.OAI.CurrentKS.Realization.poly_existsFin _root_.OAI.CurrentKS.Realization.poly_forallFin _root_.OAI.CurrentKS.Realization.poly_or _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparsification realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_ratNatFloorBinary : PolyTime ratNatFloorBinary := by
  unfold ratNatFloorBinary;infer_instance

lemma runsPoly_binaryToNat {ι : Type*} {L : ι → ℕ} (a : ι → ℕ)
    (ha : IsPoly L (fun i => (binaryNatCode (a i)).length)) (hn : IsPoly L a) :
    RunsPoly L binaryToNat a := by
  refine ⟨ha,?_⟩
  exact (((isPoly_const L 6).mul hn).add ((isPoly_const L 4).mul ha)).add (isPoly_const L 4)

end CurrentKS.Realization

namespace AlgorithmicThinTrees.GraphicHalf.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree Finset
open MetricTests MetricTests.RationalStep Normalization GraphStack
open MetricTests.RationalStep.Stack

instance poly_problemD : PolyTime problemD := by unfold problemD; apply poly_congr

instance poly_edgeGraphInput : PolyTime edgeGraphInput := by unfold edgeGraphInput; apply poly_changeOutput

instance poly_maskEdgeInput : PolyTime maskEdgeInput := by unfold maskEdgeInput; apply poly_changeOutput

end AlgorithmicThinTrees.GraphicHalf.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GreedyRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Greedy realization. -/

section

namespace AlgorithmicThinTrees.GreedyTree.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Finset StrongThinTree
open GraphStack
local notation "X" => NaturalPolynomial.variable

private instance poly_subgraphN : PolyTime subgraphN := by
  unfold subgraphN
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · unfold numVertices
    apply poly_then

lemma subgraph_length (s : Subgraph) :
    (subgraphCode s).length=2*(graphCode s.graph).length+1+3*s.graph.m := by
  simp only [subgraphCode,prodCode_length,Subgraph.bits,bools_ofFn_length]

instance poly_selected : PolyTime selected := by unfold selected; apply poly_congr

private instance poly_reachN : PolyTime reachN := by
  unfold reachN
  apply poly_then

instance poly_reached : PolyTime reached := by unfold reached; apply poly_congr

instance poly_arcSubedge : PolyTime arcSubedge := by unfold arcSubedge; apply poly_changeOutput

instance poly_arcEdge : PolyTime arcEdge := by unfold arcEdge; apply poly_changeOutput
instance poly_leftReached : PolyTime leftReached := by unfold leftReached; apply poly_congr
instance poly_rightReached : PolyTime rightReached := by unfold rightReached; apply poly_congr

instance poly_incident : PolyTime incident := by unfold incident;infer_instance

instance poly_expands : PolyTime expands := by unfold expands; apply poly_congr

instance poly_next : PolyTime next := by unfold next; apply poly_changeOutput

lemma next_length (s : ReachState) : (reachCode s.next).length=(reachCode s).length := by
  simp only [reachCode,prodCode_length,ReachState.bits,bools_ofFn_length]
  rfl
instance size_next : IterateSize next := by
  refine ⟨⟨X,?_⟩⟩
  intro s k
  have he : (reachCode (ReachState.next^[k] s)).length=(reachCode s).length := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply',next_length,ih]
  change (reachCode (ReachState.next^[k] s)).length ≤ (reachCode s).length+k
  rw [he];omega

instance poly_initBit : PolyTime initBit := by unfold initBit;infer_instance

instance poly_start : PolyTime start := by unfold start; apply poly_changeOutput

instance poly_walk : PolyTime walk := by unfold walk; apply poly_then

instance poly_reachedAll : PolyTime reachedAll := by unfold reachedAll; apply poly_congr

instance poly_connectedProgram : PolyTime connectedProgram := by unfold connectedProgram;infer_instance

instance poly_eraseSubedge : PolyTime eraseSubedge := by unfold eraseSubedge; apply poly_changeOutput

instance poly_eraseBit : PolyTime eraseBit := by unfold eraseBit;infer_instance

instance poly_eraseProgram : PolyTime eraseProgram := by unfold eraseProgram;infer_instance

instance poly_deleteProgram : PolyTime deleteProgram := by unfold deleteProgram; apply poly_ite

lemma deleteAt_graph (s : Subgraph) (i : ℕ) : (deleteAt (s,i)).graph=s.graph := by
  unfold deleteAt;split_ifs <;> rfl
lemma folded_graph (s : Subgraph) (xs : List ℕ) :
    (xs.foldl (fun s i => deleteAt (s,i)) s).graph=s.graph := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih => rw [List.foldl_cons,ih,deleteAt_graph]

instance size_deleteProgram : FoldSize deleteProgram := by
  refine ⟨⟨X,?_⟩⟩
  intro s xs ys zs he
  change (subgraphCode (ys.foldl (fun s i => deleteAt (s,i)) s)).length≤_
  rw [subgraph_length,folded_graph,←subgraph_length]
  change (subgraphCode s).length ≤ (prodCode subgraphCode (listCode natCode) (s,xs)).length
  exact le_prodCode_left (ea:=subgraphCode) (eb:=listCode natCode) (s,xs)

instance poly_whole : PolyTime whole := by unfold whole;infer_instance

instance poly_treeProgram : PolyTime treeProgram := by unfold treeProgram; apply poly_congr

end AlgorithmicThinTrees.GreedyTree.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_BoundaryCases
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.copiesEquiv_apply _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary cases. -/

section

namespace AlgorithmicThinTrees
open StrongThinTree Finset

end AlgorithmicThinTrees
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_BinaryReduction
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.copiesEquiv_apply _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binary reduction. -/

section

namespace AlgorithmicThinTrees
open StrongThinTree Finset

namespace BinaryInput

lemma reduced_multiplicity_le (x : BinaryInput) (hk : 0 < x.k) (i : Fin x.p) :
    x.reduced.multiplicity i ≤ 2 * x.n ^ 2 := by
  change 2 * x.n ^ 2 * min (x.multiplicity i) x.k / x.k ≤ _
  have h := Nat.div_le_div_right (c := x.k) (Nat.mul_le_mul_left (2 * x.n ^ 2)
    (min_le_right (x.multiplicity i) x.k))
  simpa [Nat.ne_of_gt hk] using h

end BinaryInput
end AlgorithmicThinTrees

namespace StrongThinTree.MultiGraph
open Finset

end StrongThinTree.MultiGraph

namespace AlgorithmicThinTrees.BinaryInput
open StrongThinTree Finset

end AlgorithmicThinTrees.BinaryInput

namespace AlgorithmicThinTrees
open StrongThinTree Finset

lemma framed_nat_length_pos (v : ℕ) : 0 < (CurrentKS.encodeNat v).length := by
  unfold CurrentKS.encodeNat
  cases Computability.encodeNat v <;> simp [CurrentKS.frame]

lemma record_count_le_bits (records : List (List Bool))
    (h : ∀ bits ∈ records, 0 < bits.length) : records.length ≤ records.flatten.length := by
  induction records with
  | nil => simp
  | cons bits records ih =>
    have hb := h bits (List.mem_cons_self ..)
    have hr := ih (fun bs hbs => h bs (List.mem_cons_of_mem _ hbs))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

namespace BinaryInput

lemma vertices_le_twice_records (x : BinaryInput) (hn : 2 ≤ x.n) (hk : 0 < x.k)
    (hc : x.graph.EdgeConnected x.k) : x.n ≤ 2 * x.p := by
  classical
  let L : Finset (Fin x.n) := univ.image x.left
  let R : Finset (Fin x.n) := univ.image x.right
  have hcover : univ ⊆ L ∪ R := by
    intro v _
    have hproper : ({v} : Finset (Fin x.n)) ≠ univ := by
      intro he
      have hcard := congrArg Finset.card he
      simp only [card_singleton, card_univ, Fintype.card_fin] at hcard
      omega
    have hcut := hc {v} (singleton_nonempty v) hproper
    obtain ⟨e, he⟩ := card_pos.mp (lt_of_lt_of_le hk hcut)
    have hcross := (mem_filter.mp he).2
    change (x.left (x.edgeEquiv.symm e).1 ∈ {v} ∧
        x.right (x.edgeEquiv.symm e).1 ∉ {v}) ∨
      (x.right (x.edgeEquiv.symm e).1 ∈ {v} ∧
        x.left (x.edgeEquiv.symm e).1 ∉ {v}) at hcross
    rcases hcross with h | h
    · exact mem_union_left R (mem_image.mpr
        ⟨(x.edgeEquiv.symm e).1, mem_univ _, mem_singleton.mp h.1⟩)
    · exact mem_union_right L (mem_image.mpr
        ⟨(x.edgeEquiv.symm e).1, mem_univ _, mem_singleton.mp h.1⟩)
  have hL : L.card ≤ x.p := by simpa [L] using card_image_le (f := x.left) (s := univ)
  have hR : R.card ≤ x.p := by simpa [R] using card_image_le (f := x.right) (s := univ)
  have hcard := (card_le_card hcover).trans (card_union_le L R)
  simp only [card_univ, Fintype.card_fin] at hcard
  omega

lemma records_le_encoding (x : BinaryInput) : x.p ≤ x.encode.length := by
  let records := List.ofFn (fun i : Fin x.p =>
    CurrentKS.encodeNat (x.left i).val ++ CurrentKS.encodeNat (x.right i).val ++
      CurrentKS.encodeNat (x.multiplicity i))
  have h := record_count_le_bits records (by
    intro bits hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    have h := framed_nat_length_pos (x.left i).val
    simp only [List.length_append]
    omega)
  simp only [records, List.length_ofFn] at h
  unfold encode
  simp only [List.length_append]
  omega

end BinaryInput
end AlgorithmicThinTrees
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_CanonicalExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical expansion. -/

section

namespace AlgorithmicThinTrees.BinaryInput
open StrongThinTree Finset

end AlgorithmicThinTrees.BinaryInput
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputArrays
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input arrays. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack

instance poly_field (i : ℕ) : PolyTime (field i) := by unfold field;infer_instance

instance poly_eNBinary : PolyTime eNBinary := by unfold eNBinary;apply poly_congr
instance poly_eMBinary : PolyTime eMBinary := by unfold eMBinary;apply poly_congr
instance poly_eKBinary : PolyTime eKBinary := by unfold eKBinary;apply poly_congr
instance poly_bNBinary : PolyTime bNBinary := by unfold bNBinary;apply poly_congr
instance poly_bPBinary : PolyTime bPBinary := by unfold bPBinary;apply poly_congr
instance poly_bKBinary : PolyTime bKBinary := by unfold bKBinary;apply poly_congr

lemma explicit_records_le (x : ExplicitInput) : x.m ≤ x.encode.length := by
  have h := record_count_le_bits (List.ofFn fun i : Fin x.m =>
    CurrentKS.encodeNat (x.graph.left i).val ++ CurrentKS.encodeNat (x.graph.right i).val) (by
      intro bits hb
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
      have hh := framed_nat_length_pos (x.graph.left i).val
      simp only [List.length_append];omega)
  simp only [List.length_ofFn] at h
  simp only [ExplicitInput.encode,List.length_append]
  omega

lemma graph_dimensions {n m k : ℕ} (G : MultiGraph n m) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hc : G.EdgeConnected k) : k ≤ m ∧ n ≤ 2*m := by
  classical
  have hsingle (v : Fin n) : ({v} : Finset (Fin n)) ≠ univ := by
    intro he
    have he := congrArg Finset.card he
    simp only [card_singleton,card_univ,Fintype.card_fin] at he
    omega
  have hcard (S : Finset (Fin n)) : (G.cut univ S).card ≤ m := by
    have hh : G.cut univ S ⊆ univ := filter_subset _ _
    simpa only [card_univ,Fintype.card_fin] using card_le_card hh
  refine ⟨(hc {⟨0,by omega⟩} (singleton_nonempty _) (hsingle _)).trans (hcard _),?_⟩
  have hcover : univ ⊆ univ.image G.left ∪ univ.image G.right := by
    intro v _
    obtain ⟨e,he⟩ := card_pos.mp (lt_of_lt_of_le (by omega : 0<k)
      (hc {v} (singleton_nonempty _) (hsingle v)))
    rcases (mem_filter.mp he).2 with h | h
    · exact mem_union_left _ (mem_image.mpr ⟨e,mem_univ _,mem_singleton.mp h.1⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨e,mem_univ _,mem_singleton.mp h.1⟩)
  have h := (card_le_card hcover).trans (card_union_le _ _)
  have hl := card_image_le (s:=univ) (f:=G.left)
  have hr := card_image_le (s:=univ) (f:=G.right)
  simp only [card_univ,Fintype.card_fin] at *
  omega

lemma eM_bound (x : E) : x.val.m ≤ (eCode x).length := explicit_records_le _
lemma eN_bound (x : E) : x.val.n ≤ 2*(eCode x).length := by
  have h := (graph_dimensions x.val.graph x.property.1 x.property.2.1 x.property.2.2).2
  have h' := eM_bound x
  omega
lemma eK_bound (x : E) : x.val.k ≤ (eCode x).length :=
  (graph_dimensions x.val.graph x.property.1 x.property.2.1 x.property.2.2).1.trans (eM_bound x)
lemma bP_bound (x : B) : x.val.p ≤ (bCode x).length := x.val.records_le_encoding
lemma bN_bound (x : B) : x.val.n ≤ 2*(bCode x).length := by
  have h := x.val.vertices_le_twice_records x.property.1 x.property.2.1 x.property.2.2
  have h' := bP_bound x
  omega

lemma poly_bounded_binary {α : Type*} {ea : α → Word} {f : α → ℕ}
    (r : Realizes ea binaryNatCode f) [PolyTime r]
    (hf : IsPoly (fun a => (ea a).length) f) : PolyTime (r.then binaryToNat) := by
  have h := RunsPoly.of_poly r id (isPoly_self (fun a => (ea a).length))
  exact ⟨(h.then (runsPoly_binaryToNat f h.output hf)).cost⟩

instance poly_eN : PolyTime eN := by
  apply poly_bounded_binary
  exact ((isPoly_const _ 2).mul (isPoly_self _)).mono eN_bound
instance poly_eM : PolyTime eM := by
  apply poly_bounded_binary
  exact (isPoly_self _).mono eM_bound
instance poly_eK : PolyTime eK := by
  apply poly_bounded_binary
  exact (isPoly_self _).mono eK_bound
instance poly_bN : PolyTime bN := by
  apply poly_bounded_binary
  exact ((isPoly_const _ 2).mul (isPoly_self _)).mono bN_bound
instance poly_bP : PolyTime bP := by
  apply poly_bounded_binary
  exact (isPoly_self _).mono bP_bound

instance poly_eEndpointBinary (right : Bool) : PolyTime (eEndpointBinary right) := by
  unfold eEndpointBinary;infer_instance

instance poly_eEndpoint (right : Bool) : PolyTime (eEndpoint right) := by
  apply poly_bounded_binary
  apply ((isPoly_const _ 2).mul (isPoly_self _)).mono
  intro x
  have hv := eN_bound x.1
  have hl : (eCode x.1).length ≤ (eEdgeCode x).length :=
    le_prodCode_left (ea:=eCode) (eb:=natCode) (x.1,x.2.val)
  have h1 := (x.1.val.graph.left x.2).isLt
  have h2 := (x.1.val.graph.right x.2).isLt
  cases right <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

instance poly_bRecordBinary (j : Fin 3) : PolyTime (bRecordBinary j) := by
  unfold bRecordBinary;apply poly_congr

instance poly_bEndpointBinary (right : Bool) : PolyTime (bEndpointBinary right) := by
  unfold bEndpointBinary;infer_instance

instance poly_bEndpoint (right : Bool) : PolyTime (bEndpoint right) := by
  apply poly_bounded_binary
  apply ((isPoly_const _ 2).mul (isPoly_self _)).mono
  intro x
  have hv := bN_bound x.1
  have hl : (bCode x.1).length ≤ (bRecCode x).length :=
    le_prodCode_left (ea:=bCode) (eb:=natCode) (x.1,x.2.val)
  have h1 := (x.1.val.left x.2).isLt
  have h2 := (x.1.val.right x.2).isLt
  cases right <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputExpansion
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input expansion. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack GraphStack

instance poly_ePrepare : PolyTime ePrepare := by unfold ePrepare;infer_instance

instance poly_bMultiplicityRat : PolyTime bMultiplicityRat := by unfold bMultiplicityRat;apply poly_congr

instance poly_bCountBinary : PolyTime bCountBinary := by unfold bCountBinary;infer_instance

instance poly_bCount : PolyTime bCount := by
  apply poly_bounded_binary
  refine ⟨8*NaturalPolynomial.variable^2,?_⟩
  intro x
  have hv := bN_bound x.1
  have hl : (bCode x.1).length ≤ (bRecCode x).length :=
    le_prodCode_left (ea:=bCode) (eb:=natCode) (x.1,x.2.val)
  have hc := x.1.val.reduced_multiplicity_le x.1.property.2.1 x.2
  have hn : x.1.val.n ≤ 2*(bRecCode x).length := by omega
  have hn2 := Nat.pow_le_pow_left hn 2
  change x.1.val.reduced.multiplicity x.2 ≤ 8*(bRecCode x).length^2
  nlinarith

instance poly_bEndpointBlock (right : Bool) : PolyTime (bEndpointBlock right) := by
  unfold bEndpointBlock;infer_instance

instance poly_bLefts : PolyTime bLefts := by unfold bLefts;infer_instance
instance poly_bRights : PolyTime bRights := by unfold bRights;infer_instance
instance poly_bRecords : PolyTime bRecords := by unfold bRecords;infer_instance

instance poly_bPrepare : PolyTime bPrepare := by unfold bPrepare;infer_instance

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_OrderedGraph
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_incident _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_leftReached _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_rightReached _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bLefts _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRights _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eEndpoint _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eEndpointBinary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered graph. -/

section

namespace AlgorithmicThinTrees.OrderedGraph
open Finset StrongThinTree StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

lemma lift_univ (F : Finset (Fin m)) : liftEdges F univ=F := by
  ext e
  simp only [liftEdges,mem_map,mem_univ,true_and]
  exact ⟨fun ⟨i,hi⟩ => hi ▸ embedding_mem F i, embedding_surj F⟩
lemma lift_lower (F T : Finset (Fin m)) (hT : T ⊆ F) : liftEdges F (lowerEdges F T)=T := by
  ext e
  simp only [liftEdges,lowerEdges,mem_map,mem_preimage]
  refine ⟨fun ⟨i,hi,hie⟩ => hie ▸ hi,fun he => ?_⟩
  obtain ⟨i,rfl⟩ := embedding_surj F (hT he)
  exact ⟨i,he,rfl⟩
lemma restrict_cut (F : Finset (Fin m)) (T : Finset (Fin F.card)) (S : Finset (Fin n)) :
    liftEdges F ((restrict G F).cut T S)=G.cut (liftEdges F T) S := by
  ext e
  simp only [liftEdges,cut,mem_map,mem_filter]
  constructor
  · rintro ⟨i,⟨hi,hc⟩,rfl⟩
    exact ⟨⟨i,hi,rfl⟩,hc⟩
  · rintro ⟨⟨i,hi,rfl⟩,hc⟩
    exact ⟨i,⟨hi,hc⟩,rfl⟩
lemma restrict_cut_card (F : Finset (Fin m)) (T : Finset (Fin F.card)) (S : Finset (Fin n)) :
    ((restrict G F).cut T S).card=(G.cut (liftEdges F T) S).card := by
  rw [←restrict_cut G]
  exact (card_map _).symm
lemma restrict_connected (F : Finset (Fin m)) (T : Finset (Fin F.card)) :
    (restrict G F).Connected T ↔ G.Connected (liftEdges F T) := by
  unfold Connected
  constructor <;> intro h S hS hS'
  · rw [←restrict_cut G]
    exact map_nonempty.mpr (h S hS hS')
  · apply (map_nonempty (f := edgeEmbedding F)).mp
    change (liftEdges F ((restrict G F).cut T S)).Nonempty
    rw [restrict_cut G]
    exact h S hS hS'
lemma restrict_spanningTree (F : Finset (Fin m)) (T : Finset (Fin F.card)) :
    (restrict G F).SpanningTree T ↔ G.SpanningTree (liftEdges F T) := by
  constructor
  · rintro ⟨hc,hmin⟩
    refine ⟨(restrict_connected G F T).mp hc,?_⟩
    intro e he hh
    obtain ⟨i,hi,rfl⟩ := mem_map.mp he
    apply hmin i hi
    apply (restrict_connected G F (T.erase i)).mpr
    simpa only [liftEdges,map_erase] using hh
  · rintro ⟨hc,hmin⟩
    refine ⟨(restrict_connected G F T).mpr hc,?_⟩
    intro e he hh
    apply hmin (edgeEmbedding F e) (mem_map.mpr ⟨e,he,rfl⟩)
    have hh' := (restrict_connected G F (T.erase e)).mp hh
    simpa only [liftEdges,map_erase] using hh'
lemma restrict_packable (F : Finset (Fin m)) {r : ℕ} (h : G.TreePackable F r) :
    (restrict G F).TreePackable univ r := by
  obtain ⟨T,hT,hd⟩ := h
  refine ⟨fun i => lowerEdges F (T i),fun i => ⟨subset_univ _,?_⟩,?_⟩
  · apply (restrict_spanningTree G F _).mpr
    rw [lift_lower F (T i) (hT i).1]
    exact (hT i).2
  · intro i j hij
    exact disjoint_preimage (hd hij)
end AlgorithmicThinTrees.OrderedGraph
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_SelectionRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_arcEdge _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_arcSubedge _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_connectedProgram _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_deleteProgram _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_eraseBit _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_eraseProgram _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_eraseSubedge _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_expands _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_incident _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_initBit _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_leftReached _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_next _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reached _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachedAll _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_rightReached _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_selected _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_start _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_treeProgram _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_walk _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_whole _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bCount _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bCountBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bEndpoint _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bEndpointBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bEndpointBlock _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bKBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bLefts _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bMultiplicityRat _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bN _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bNBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bP _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bPBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bPrepare _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRecordBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRecords _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRights _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eEndpoint _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eEndpointBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eK _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eKBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eM _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eMBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eN _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eNBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_ePrepare _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_field _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachN _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphN _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Finset
open AlgorithmicThinTrees.OrderedGraph

variable {α : Type*}

instance poly_maskEntry (ea : α → Word) : PolyTime (maskEntry ea) := by unfold maskEntry;infer_instance

instance poly_maskArray (ea : α → Word) (z : α) : PolyTime (maskArray ea z) := by
  unfold maskArray;infer_instance

lemma selected_sublist {m : ℕ} (A : Finset (Fin m)) (f : Fin m → α) :
    (List.ofFn (fun i => f (edgeEmbedding A i))).Sublist (List.ofFn f) := by
  change (List.ofFn (f ∘ edgeEmbedding A)).Sublist (List.ofFn f)
  rw [←List.map_ofFn,←sorted_selected,List.ofFn_eq_map (f:=f)]
  exact List.Sublist.map f (List.filter_sublist)

lemma listCode_sublist_le {ea : α → Word} {xs ys : List α} (h : xs.Sublist ys) :
    (listCode ea xs).length≤(listCode ea ys).length := by
  rw [len_listCode,len_listCode]
  exact (h.map (fun x => 2*(ea x).length+1)).sum_le_sum (fun _ _ => Nat.zero_le _)

lemma listCode_selected_le {m : ℕ} (ea : α → Word) (A : Finset (Fin m)) (f : Fin m → α) :
    (listCode ea (List.ofFn (fun i => f (edgeEmbedding A i)))).length≤
      (listCode ea (List.ofFn f)).length := listCode_sublist_le (selected_sublist A f)

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Iteration
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeLeft _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeRight _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_incident _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_leftReached _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_rightReached _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bLefts _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRights _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eEndpoint _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eEndpointBinary _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset
namespace StrongThinTree.MultiGraph

lemma cut_card_le_full {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m))
    (S : Finset (Fin n)) : (G.cut T S).card ≤ (G.cut univ S).card := by
  exact card_le_card (filter_subset_filter _ (subset_univ T))

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_IterationPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration potential. -/

section

noncomputable section
namespace AlgorithmicThinTrees.Iteration
open StrongThinTree

lemma lossB_pos : 0 < lossB := by
  unfold lossB
  exact div_pos (by norm_num) (sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num)))
lemma potential_pos (r : ℕ) : 0 < potential r := Real.exp_pos _
lemma potential_one_le {r : ℕ} (hr : 1 ≤ r) : 1 ≤ potential r := by
  exact Real.one_le_exp (mul_nonneg lossB_pos.le (sub_nonneg.mpr (errorU_le_one hr)))
lemma potential_le (r : ℕ) : potential r ≤ Real.exp lossB := by
  apply Real.exp_le_exp.mpr
  have := mul_nonneg lossB_pos.le (errorU_nonneg r)
  nlinarith

lemma potential_step {r s : ℕ} (hs : 0 < s) (hrs : (s:ℝ) ≤ (r:ℝ)/2) :
    (1+80*errorU r)*potential s ≤ potential r := by
  have hd : 0 < (2:ℝ)^(1/16:ℝ)-1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hm := mul_le_mul_of_nonneg_left (errorU_halving hs hrs) lossB_pos.le
  have hB : lossB*((2:ℝ)^(1/16:ℝ)-1)=80 := by
    unfold lossB
    exact div_mul_cancel₀ _ (ne_of_gt hd)
  have hdiff : 80*errorU r ≤ lossB*(errorU s-errorU r) := by
    have hBu := congrArg (fun x : ℝ => x*errorU r) hB
    nlinarith
  have he : 1+80*errorU r ≤ Real.exp (80*errorU r) := by
    simpa only [add_comm] using Real.add_one_le_exp (80*errorU r)
  calc
    _ ≤ Real.exp (80*errorU r)*potential s :=
      mul_le_mul_of_nonneg_right he (potential_pos s).le
    _ = Real.exp (80*errorU r+lossB*(1-errorU s)) := by
      rw [potential,Real.exp_add]
    _ ≤ potential r := by
      apply Real.exp_le_exp.mpr
      linarith

lemma coefficient_step {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hhalf : (s:ℝ) ≤ (r:ℝ)/2)
    (hratio : (1/2+3*GraphicHalf.halfError r)*(r:ℝ) ≤ (1+80*errorU r)*s) :
    potential s/(s:ℝ)*(1/2+3*GraphicHalf.halfError r) ≤ potential r/(r:ℝ) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hsR hrR).mpr
  have hp := potential_step hs hhalf
  have hm := mul_le_mul_of_nonneg_left hratio (potential_pos s).le
  have hp' := mul_le_mul_of_nonneg_right hp hsR.le
  nlinarith

end AlgorithmicThinTrees.Iteration
end

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_RationalIteration
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_incident _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_leftReached _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_rightReached _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_treeProgram _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bCount _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bCountBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bEndpoint _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bEndpointBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bEndpointBlock _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bKBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bLefts _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bMultiplicityRat _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bN _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bNBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bP _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bPBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRecordBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRecords _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRights _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eEndpoint _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eEndpointBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eK _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eKBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eM _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eMBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eN _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eNBinary
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational iteration. -/

section

namespace AlgorithmicThinTrees.Iteration
open Finset StrongThinTree StrongThinTree.MultiGraph GraphicHalf
open MetricTests MetricTests.RationalStep

lemma iterate_bound {R : ℕ} (hR : 4 ≤ R) (hround : RoundBound R) (fuel r d m : ℕ)
    (G : MultiGraph (d+1) m) (hr : 1 ≤ r) (hfuel : r ≤ fuel)
    (hn : 2 ≤ d+1) (hp : G.TreePackable univ r) :
    G.SpanningTree (iterate R fuel r d m G) ∧
      ∀S : Finset (Fin (d+1)), ((G.cut (iterate R fuel r d m G) S).card:ℝ) ≤
        R*(potential r/(r:ℝ))*(G.cut univ S).card := by
  induction fuel generalizing r m with
  | zero => omega
  | succ fuel ih =>
    have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hRR : (0:ℝ) < R := by exact_mod_cast (show 0 < R by omega)
    by_cases hlarge : R ≤ r
    · obtain ⟨_,hhalf,hpos,hpack,hcut,hratio⟩ := hround r hlarge d m G hn hp
      have hlt : nextCount r < r := by
        exact_mod_cast (show (nextCount r:ℝ)<(r:ℝ) by linarith only [hhalf,hrR])
      have ih' := ih (nextCount r) (sparsify G r).card (OrderedGraph.restrict G (sparsify G r))
        hpos (by omega) (OrderedGraph.restrict_packable G _ hpack)
      rw [iterate,ite_eq_left hlarge]
      refine ⟨(OrderedGraph.restrict_spanningTree G _ _).mp ih'.1,?_⟩
      intro S
      have ht := ih'.2 S
      rw [OrderedGraph.restrict_cut_card,OrderedGraph.restrict_cut_card,OrderedGraph.lift_univ] at ht
      have hcoef : 0 ≤ R*(potential (nextCount r)/(nextCount r:ℝ)) := by
        exact mul_nonneg hRR.le (div_nonneg (potential_pos _).le (Nat.cast_nonneg _))
      calc
        _ ≤ R*(potential (nextCount r)/(nextCount r:ℝ))*(G.cut (sparsify G r) S).card := ht
        _ ≤ R*(potential (nextCount r)/(nextCount r:ℝ))*
            ((1/2+3*halfError r)*(G.cut univ S).card) :=
          mul_le_mul_of_nonneg_left (hcut S) hcoef
        _ = R*(potential (nextCount r)/(nextCount r:ℝ)*(1/2+3*halfError r))*
            (G.cut univ S).card := by ring
        _ ≤ R*(potential r/(r:ℝ))*(G.cut univ S).card :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (coefficient_step (by omega) hpos hhalf hratio) hRR.le)
            (Nat.cast_nonneg _)
    · rw [iterate,ite_eq_right hlarge]
      refine ⟨GreedyTree.tree_correct G (packing_connected G (by omega) hp),?_⟩
      intro S
      have hrleR : (r:ℝ) ≤ R := by exact_mod_cast (show r ≤ R by omega)
      have hcoef : 1 ≤ R*(potential r/(r:ℝ)) := by
        rw [←mul_div_assoc]
        apply (le_div_iff₀ hrR).mpr
        have hh := mul_le_mul_of_nonneg_left (potential_one_le hr) hRR.le
        nlinarith only [hh,hrleR]
      have hc : ((G.cut (GreedyTree.tree G) S).card:ℝ) ≤ (G.cut univ S).card := by
        exact_mod_cast G.cut_card_le_full (GreedyTree.tree G) S
      exact hc.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) hcoef)

lemma initialCount_pos (k : ℕ) : 1 ≤ initialCount k := le_max_left _ _
lemma initialCount_lower (k : ℕ) : k ≤ 3*initialCount k := by
  unfold initialCount
  omega

lemma initial_packable {n m k : ℕ} (G : MultiGraph n m) (hn : 0 < n) (hk : 1 ≤ k)
    (hc : G.EdgeConnected k) : G.TreePackable univ (initialCount k) := by
  by_cases hk2 : 2 ≤ k
  · have hr : 0 < k/2 := Nat.div_pos hk2 (by norm_num)
    have he : initialCount k=k/2 := max_eq_right hr
    rw [he]
    apply G.edgeConnected_treePackable hr hn
    intro S hS hS'
    exact (show 2*(k/2) ≤ k by omega).trans (hc S hS hS')
  · have hconn : G.Connected univ := by
      intro S hS hS'
      apply card_pos.mp
      exact hk.trans (hc S hS hS')
    have he : initialCount k=1 := by unfold initialCount; omega
    rw [he]
    refine ⟨fun _ => GreedyTree.tree G,fun _ => ⟨subset_univ _,GreedyTree.tree_correct G hconn⟩,?_⟩
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

end AlgorithmicThinTrees.Iteration
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_IterationRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bCount _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bCountBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bEndpoint _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bEndpointBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bEndpointBlock _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bKBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bLefts _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bMultiplicityRat _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bN _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bNBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bP _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bPBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bPrepare _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRecordBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRecords _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRights _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eEndpoint _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eEndpointBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eK _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eKBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eM _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eMBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eN _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eNBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_ePrepare _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_field _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_wordHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration realization. -/

section

namespace AlgorithmicThinTrees.Iteration.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 StrongThinTree Finset
open GraphStack GraphicHalf GraphicHalf.Stack MetricTests.RationalStep MetricTests.RationalStep.Stack OrderedGraph

lemma nextCount_le (r : ℕ) : nextCount r ≤ r := by
  unfold nextCount
  apply (Nat.floor_mono (show (1-16*countError r)*(r:ℚ)/2 ≤ (r:ℚ) from ?_)).trans_eq
    (Nat.floor_natCast r)
  have : 0 ≤ countError r := by unfold countError; positivity
  have : 0 ≤ countError r*(r:ℚ) := mul_nonneg this (Nat.cast_nonneg _)
  nlinarith

instance poly_nextCountBinary : PolyTime nextCountBinary := by
  unfold nextCountBinary
  apply poly_then

instance poly_nextCountProgram : PolyTime nextCountProgram := by
  apply PolyTime.mk
  have hb := RunsPoly.of_poly nextCountBinary id (isPoly_self (fun r => (natCode r).length))
  have hn : IsPoly (fun r => (natCode r).length) nextCount :=
    (isPoly_self (fun r => (natCode r).length)).mono (fun r => by
      simpa only [natCode,List.length_replicate] using nextCount_le r)
  exact (hb.then (runsPoly_binaryToNat _ hb.output hn)).cost

private instance poly_problem : PolyTime problem := by
  unfold problem
  apply poly_then

private instance poly_labels : PolyTime labels := by
  unfold labels
  apply poly_then

private instance poly_graph : PolyTime graph := by
  unfold graph
  apply poly_then

private instance poly_count : PolyTime count := by
  unfold count
  apply poly_then

instance poly_selectState : PolyTime selectState := by
  unfold selectState
  dsimp only
  refine @poly_changeOutput _ _ _ _ _ _ _ _ _ _ ?_
  refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_ <;> infer_instance

instance poly_large (R : ℕ) : PolyTime (large R) := by unfold large;apply poly_then

instance poly_finish : PolyTime finish := by unfold finish;apply poly_congr

lemma restrict_length (s : State) (A : Finset (Fin s.problem.m)) :
    (stateCode (s.restrict A)).length≤(stateCode s).length := by
  have hl := listCode_selected_le natCode A (fun e => (s.problem.G.left e).val)
  have hr := listCode_selected_le natCode A (fun e => (s.problem.G.right e).val)
  have hlabels := listCode_selected_le natCode A s.labels
  have hn := nextCount_le s.problem.r
  simp only [stateCode,State.restrict,problemCode,extractionInputCode,Problem.graph,graphCode,
    graphDataCode,Graph.data,prodCode_length,natCode,List.length_replicate,
    OrderedGraph.restrict,indicesCode] at *
  omega
lemma step_length (R : ℕ) (s : State) : (stateCode (step R s)).length≤(stateCode s).length := by
  unfold step
  split
  · exact restrict_length _ _
  · rfl
lemma orbit_length (R t : ℕ) (s : State) :
    (stateCode ((step R)^[t] s)).length≤(stateCode s).length := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply'];exact (step_length _ _).trans ih

lemma orbit_packed {R : ℕ} (_hR : 4 ≤ R) (hb : RoundBound R) (s : State)
    (hn : 2 ≤ s.problem.d+1) (hp : s.problem.G.TreePackable univ s.problem.r)
    (t : ℕ) :
    2 ≤ ((step R)^[t] s).problem.d+1 ∧
      ((step R)^[t] s).problem.G.TreePackable univ ((step R)^[t] s).problem.r := by
  induction t with
  | zero => exact ⟨hn,hp⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    by_cases hh : R ≤ ((step R)^[t] s).problem.r
    · rw [step,ite_eq_left hh]
      exact ⟨ih.1,OrderedGraph.restrict_packable _ _
        (hb _ hh _ _ _ ih.1 ih.2).2.2.2.1⟩
    · rw [step,ite_eq_right hh];exact ih

lemma runsPoly_step {R T : ℕ} (hTR : T ≤ R)
    (htime : ∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
      IsPoly L (fun i => (problemCode (a i)).length) →
      (∀i,T ≤ (a i).r ∧ 2 ≤ (a i).d+1 ∧ (a i).G.TreePackable univ (a i).r) →
      RunsPoly L sparsifyProgram a)
    {ι : Type} {L : ι → ℕ} (a : ι → State)
    (ha : IsPoly L (fun i => (stateCode (a i)).length))
    (hp : ∀i,2 ≤ (a i).problem.d+1 ∧ (a i).problem.G.TreePackable univ (a i).problem.r) :
    RunsPoly L (stepProgram R) a := by
  unfold stepProgram
  apply RunsPoly.congr
  apply RunsPoly.ite_on (RunsPoly.of_poly _ a ha)
  have hh : IsPoly (fun i : {i // R ≤ (a i).problem.r} => L i.val)
      (fun i => halveProgram.cost (a i.val)) := by
    have hi := RunsPoly.of_poly problem (fun i : {i // R ≤ (a i).problem.r} => a i.val)
      (ha.reindex Subtype.val)
    have hs := htime (fun i : {i // R ≤ (a i).problem.r} => (a i.val).problem) hi.output
      (fun i => ⟨hTR.trans i.property,(hp i.val).1,(hp i.val).2⟩)
    have hh := (RunsPoly.of_poly (identity stateCode)
      (fun i : {i // R ≤ (a i).problem.r} => a i.val) (ha.reindex Subtype.val)).both
        (hi.then hs)
    have hz : RunsPoly (fun i : {i // R ≤ (a i).problem.r} => L i.val)
        halveProgram (fun i => a i.val) := by
      unfold halveProgram;apply RunsPoly.congr;exact hh.then_poly selectState
    exact hz.cost
  have hl := (RunsPoly.of_poly (identity stateCode)
    (fun i : {i // ¬R ≤ (a i).problem.r} => a i.val) (ha.reindex Subtype.val)).cost
  have hz := isPoly_dite (L:=L) (P:=fun i => R ≤ (a i).problem.r)
    (f:=fun i _ => halveProgram.cost (a i))
    (g:=fun i _ => (identity stateCode).cost (a i)) hh hl
  convert hz using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  simp only [decide_eq_true_eq]
  split_ifs <;> rfl

lemma runsPoly_run {R T : ℕ} (hR : 4 ≤ R) (hb : RoundBound R) (hTR : T ≤ R)
    (htime : ∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
      IsPoly L (fun i => (problemCode (a i)).length) →
      (∀i,T ≤ (a i).r ∧ 2 ≤ (a i).d+1 ∧ (a i).G.TreePackable univ (a i).r) →
      RunsPoly L sparsifyProgram a)
    {ι : Type} {L : ι → ℕ} (a : ι → ℕ×State)
    (ha : IsPoly L (fun i => (prodCode natCode stateCode (a i)).length))
    (hp : ∀i,2 ≤ (a i).2.problem.d+1 ∧
      (a i).2.problem.G.TreePackable univ (a i).2.problem.r) : RunsPoly L (run R) a := by
  have hi : IsPoly L (fun i => (stateCode (a i).2).length) :=
    ha.mono (fun i => le_prodCode_right (ea:=natCode) (eb:=stateCode) (a i))
  have hs := runsPoly_step hTR htime (fun p : ι×ℕ => (step R)^[p.2] (a p.1).2)
    ((hi.reindex Prod.fst).mono (fun p => orbit_length R p.2 (a p.1).2))
    (fun p => orbit_packed hR hb (a p.1).2 (hp p.1).1 (hp p.1).2 p.2)
  apply (runsPoly_iterate _ a ha ?_).then_poly finish
  obtain ⟨q,hq⟩ := hs.cost
  exact ⟨q,fun i j _ => hq (i,j)⟩

end AlgorithmicThinTrees.Iteration.Stack

namespace AlgorithmicThinTrees.Iteration.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 StrongThinTree Finset
open GraphStack GraphicHalf GraphicHalf.Stack MetricTests.RationalStep OrderedGraph

instance poly_initialCountProgram : PolyTime initialCountProgram := by
  unfold initialCountProgram;infer_instance

instance poly_startProgram : PolyTime startProgram := by unfold startProgram;infer_instance

lemma runsPoly_tree {R T : ℕ} (hR : 4 ≤ R) (hb : RoundBound R) (hTR : T ≤ R)
    (htime : ∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
      IsPoly L (fun i => (problemCode (a i)).length) →
      (∀i,T ≤ (a i).r ∧ 2 ≤ (a i).d+1 ∧ (a i).G.TreePackable univ (a i).r) →
      RunsPoly L sparsifyProgram a)
    {ι : Type} {L : ι → ℕ} (a : ι → Problem)
    (ha : IsPoly L (fun i => (problemCode (a i)).length))
    (hp : ∀i,2 ≤ (a i).d+1 ∧ 1 ≤ (a i).r ∧ (a i).G.EdgeConnected (a i).r) :
    RunsPoly L (treeProgram R) a := by
  have hs := RunsPoly.of_poly startProgram a ha
  unfold treeProgram
  apply RunsPoly.congr
  apply hs.then
  apply runsPoly_run hR hb hTR htime _ hs.output
  intro i
  exact ⟨(hp i).1,initial_packable _ (by omega) (hp i).2.1 (hp i).2.2⟩

end AlgorithmicThinTrees.Iteration.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputOutput
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_wordHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input output. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack GraphStack OrderedGraph Iteration.Stack
open MetricTests.RationalStep.Stack

instance poly_lookupPair : PolyTime lookupPair := by unfold lookupPair;infer_instance

instance poly_pairsOutput : PolyTime pairsOutput := by unfold pairsOutput;infer_instance

variable {R : ℕ} {C : ℝ}
variable (hC : 0 < C)
variable (hcorrect : ∀p : Problem,2 ≤ p.d+1 → 1 ≤ p.r → p.G.EdgeConnected p.r →
  ThinTree C p.r p.G (Iteration.tree R p.r p.G))

variable (htime : ∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
  IsPoly L (fun i => (problemCode (a i)).length) →
  (∀i,2 ≤ (a i).d+1 ∧ 1 ≤ (a i).r ∧ (a i).G.EdgeConnected (a i).r) →
  RunsPoly L (treeProgram R) a)

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputDispatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input dispatch. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack

instance poly_goodN : PolyTime goodN := by unfold goodN;infer_instance

instance poly_singletonTest : PolyTime singletonTest := by unfold singletonTest;infer_instance

variable {R : ℕ} {C : ℝ}
variable (hC : 0<C)
variable (hcorrect : ∀p : Problem,2≤p.d+1 → 1≤p.r → p.G.EdgeConnected p.r →
  ThinTree C p.r p.G (Iteration.tree R p.r p.G))

variable (htime : ∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
  IsPoly L (fun i => (problemCode (a i)).length) →
  (∀i,2 ≤ (a i).d+1 ∧ 1 ≤ (a i).r ∧ (a i).G.EdgeConnected (a i).r) →
  RunsPoly L (Iteration.Stack.treeProgram R) a)

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_ExplicitAlgorithm
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bCount _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bCountBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bEndpoint _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bEndpointBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bEndpointBlock _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bKBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bLefts _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bMultiplicityRat _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bN _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bNBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bP _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bPBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bPrepare _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRecordBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRecords _root_.OAI.AlgorithmicThinTrees.InputStack.poly_bRights _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eEndpoint _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eEndpointBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eK _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eKBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eM _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eMBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eN _root_.OAI.AlgorithmicThinTrees.InputStack.poly_eNBinary _root_.OAI.AlgorithmicThinTrees.InputStack.poly_ePrepare _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_lookupPair _root_.OAI.AlgorithmicThinTrees.InputStack.poly_pairsOutput _root_.OAI.AlgorithmicThinTrees.InputStack.poly_singletonTest _root_.OAI.CurrentKS.Realization.poly_wordHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit algorithm. -/

section

namespace AlgorithmicThinTrees.Iteration
open StrongThinTree Finset GraphicHalf MetricTests.RationalStep
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack Stack

lemma tree_bound {R : ℕ} (hR : 4 ≤ R) (hb : RoundBound R)
    (d m k : ℕ) (G : MultiGraph (d+1) m) (hn : 2 ≤ d+1) (hk : 1 ≤ k)
    (hc : G.EdgeConnected k) :
    G.SpanningTree (tree R k G) ∧ ∀S : Finset (Fin (d+1)),
      ((G.cut (tree R k G) S).card:ℝ) ≤
        (3*R*Real.exp lossB)/(k:ℝ)*(G.cut univ S).card := by
  have hRR : (0:ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  obtain ⟨hT,hthin⟩ := iterate_bound hR hb (initialCount k) (initialCount k) d m G
    (initialCount_pos k) le_rfl hn (initial_packable G (by omega) hk hc)
  refine ⟨hT,fun S => (hthin S).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  have hrR : (0:ℝ) < initialCount k := by exact_mod_cast initialCount_pos k
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ hrR hkR).mpr
  have hrk : (k:ℝ) ≤ 3*(initialCount k:ℝ) := by exact_mod_cast initialCount_lower k
  have hx := mul_le_mul_of_nonneg_left (potential_le (initialCount k)) hRR.le
  have hm := mul_le_mul_of_nonneg_left hrk (mul_pos hRR (Real.exp_pos lossB)).le
  have hl := mul_le_mul_of_nonneg_right hx hkR.le
  nlinarith only [hm,hl]

theorem explicit_program_q339 :
    (∀p : Problem,2 ≤ p.d+1 → 1 ≤ p.r → p.G.EdgeConnected p.r →
      ThinTree (3*((2^2048:ℕ):ℝ)*Real.exp lossB) p.r p.G (tree (2^2048) p.r p.G)) ∧
    (∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
      IsPoly L (fun i => (problemCode (a i)).length) →
      (∀i,2 ≤ (a i).d+1 ∧ 1 ≤ (a i).r ∧ (a i).G.EdgeConnected (a i).r) →
      RunsPoly L (treeProgram (2^2048)) a) := by
  have hb := sparsification_correct_explicit
  have hR' : 4 ≤ 2^2048 := Nat.pow_le_pow_right (n:=2) (by norm_num) (by norm_num : 2 ≤ 2048)
  have hb' : RoundBound (2^2048) := fun r hr => hb r hr
  refine ⟨?_,?_⟩
  · intro p hn hk hc
    have h := tree_bound hR' hb' p.d p.m p.r p.G hn hk hc
    exact ⟨h.1,fun S _ _ => h.2 S⟩
  · exact fun a ha hp => runsPoly_tree hR' hb' le_rfl (fun a ha hp => sparsify_program_polynomial_explicit a ha hp) a ha hp

end AlgorithmicThinTrees.Iteration
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_AlgorithmicMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algorithmic main. -/

section

namespace CurrentKS.Realization
open CleanRoutine
variable {α : Type*} {ea : α → Word} {f : α → Word}

end CurrentKS.Realization

namespace AlgorithmicThinTrees.InputStack
open CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack

end AlgorithmicThinTrees.InputStack

namespace AlgorithmicThinTrees
open CurrentKS.Realization KS.W23


end AlgorithmicThinTrees
end

end OAI
end



set_option autoImplicit false

/-! Infrastructure copied from OpenAI's thin-tree solution (piece_top.lean). -/

section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace KS.W23
namespace NaturalPolynomial
theorem eval_mono_q339 (p : NaturalPolynomial) : Monotone p.eval := by
  intro x y hxy
  induction p with
  | constant c => exact le_rfl
  | «variable» => exact hxy
  | add p q hp hq => exact Nat.add_le_add hp hq
  | mul p q hp hq => exact Nat.mul_le_mul hp hq
  | power p k hp => exact Nat.pow_le_pow_left hp k
end NaturalPolynomial
end KS.W23
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace KS.W01.FixedStack
open KS.W29 (StackAction polynomialFuel)
theorem tableIndex_val_q339 {k q : ℕ} (s : Fin q) (h : Fin k → Fin 3) (b : Bool) :
    (tableIndex s h b).val = (3 ^ k * 2) * s.val +
      2 * headsCode k h + KS.W29.bitCode b := by
  change (coinFin b).val + 2 * (headFin h).val + (3 ^ k * 2) * s.val = _
  cases b <;> simp [coinFin, headFin, KS.W29.bitCode] <;> omega
end KS.W01.FixedStack
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace CurrentKS.RoutineLength
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
lemma action_length_q339 (a : KS.W29.StackAction) (w : List Bool) :
    (a.apply w).length≤w.length+1 := by
  cases a <;> simp [KS.W29.StackAction.apply]; omega
lemma step_length_q339 (M : KS.W01.FixedStack.Machine) (s : KS.W01.FixedStack.Config M.stackCount M.states) (b : Bool)
    (j : Fin M.stackCount) : ((M.step s b).«stacks» j).length ≤ (s.«stacks» j).length+1 := by
  rcases s with ⟨control,tapes⟩
  cases control with
  | none => simp [KS.W01.FixedStack.Machine.step]
  | some c => exact action_length_q339 _ _
lemma run_length_q339 (M : KS.W01.FixedStack.Machine) (s : KS.W01.FixedStack.Config M.stackCount M.states) (bits : List Bool)
    (j : Fin M.stackCount) : ((M.run s bits).«stacks» j).length ≤ (s.«stacks» j).length+bits.length := by
  induction bits generalizing s with
  | nil => simp [KS.W01.FixedStack.Machine.run]
  | cons b bs ih =>
    have h := ih (M.step s b)
    have hs := step_length_q339 M s b j
    simp only [KS.W01.FixedStack.Machine.run,List.length_cons]
    omega
lemma output_length_q339 {k : ℕ} {P : Program k} {before after : Fin k → List Bool} {ticks : ℕ}
    (h : RunSpec P before after ticks) (j : Fin k) :
    (after j).length≤(before j).length+ticks := by
  have hr := run_length_q339 P.toMachine ⟨some P.initial,before⟩ (List.replicate ticks false) j
  rw [h _ (List.length_replicate ..)] at hr
  simpa using hr
end CurrentKS.RoutineLength
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable
variable {α β γ δ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word} {ed : δ → Word}
  {f : α → β} {g : β → γ}
lemma Realizes.output_length_q339 (r : Realizes ea eb f) (x : α) :
    (eb (f x)).length≤(ea x).length+r.cost x := by
  have h := RoutineLength.output_length_q339 (r.routine.spec x) 0
  simpa only [io_zero] using h
lemma prodCode_length_q339 (p : α×β) : (prodCode ea eb p).length=2*(ea p.1).length+1+(eb p.2).length := by
  simp only [prodCode,PairRoutine.pair,List.length_append,KS.W01.length_frame]
lemma le_prodCode_left_q339 (p : α×β) : (ea p.1).length≤(prodCode ea eb p).length := by rw [prodCode_length_q339];omega
lemma le_prodCode_right_q339 (p : α×β) : (eb p.2).length≤(prodCode ea eb p).length := by rw [prodCode_length_q339];omega
instance poly_first_q339 (ea : α → Word) (eb : β → Word) : PolyTime (first ea eb) := by
  refine ⟨⟨6*X+5,?_⟩⟩
  intro p
  have h1 := le_prodCode_left_q339 (ea:=ea) (eb:=eb) p
  have h2 := le_prodCode_right_q339 (ea:=ea) (eb:=eb) p
  change 5*(ea p.1).length+(eb p.2).length+5≤6*(prodCode ea eb p).length+5
  omega
instance poly_second_q339 (ea : α → Word) (eb : β → Word) : PolyTime (second ea eb) := by
  refine ⟨⟨4*X+3,?_⟩⟩
  intro p
  have h1 := le_prodCode_left_q339 (ea:=ea) (eb:=eb) p
  change 4*(ea p.1).length+3≤4*(prodCode ea eb p).length+3
  omega
instance poly_then_q339 (r : Realizes ea eb f) (s : Realizes eb ec g) [PolyTime r] [PolyTime s] :
    PolyTime (r.then s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨p+q.comp (X+p),?_⟩⟩
  intro x
  have hl := r.output_length_q339 x
  have hs := (hq (f x)).trans (q.eval_mono_q339 (hl.trans (Nat.add_le_add_left (hp x) _)))
  have hh := Nat.add_le_add (hp x) hs
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_comp,NaturalPolynomial.eval_variable]
  exact hh
instance poly_both_q339 {g : α → γ} (r : Realizes ea eb f) (s : Realizes ea ec g) [PolyTime r] [PolyTime s] :
    PolyTime (r.both s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨16*X+13*p+q+15,?_⟩⟩
  intro x
  have hl := r.output_length_q339 x
  have h1 := hp x
  have h2 := hq x
  change PairRoutine.pairingTicks ea (fun x => eb (f x)) r.cost s.cost x≤
    16*(ea x).length+13*p.eval (ea x).length+q.eval (ea x).length+15
  simp only [PairRoutine.pairingTicks,KS.W01.length_frame]
  omega
end CurrentKS.Realization
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
namespace CurrentKS.Realization
open CleanRoutine
variable {α β γ : Type*}
lemma fold_cons_q339 (xs ys : List α) : xs.foldl (fun acc x => x::acc) ys=xs.reverse++ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]
end CurrentKS.Realization
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word}
lemma len_listCode_q339 (ea : α → Word) (xs : List α) :
    (listCode ea xs).length=(xs.map (fun x => 2*(ea x).length+1)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listCode_cons,prodCode_length_q339,List.map_cons,List.sum_cons,ih]
lemma sum_map_bound_q339 (xs : List α) (f : α → ℕ) (B : ℕ) (h : ∀ x∈xs,f x≤B) :
    (xs.map f).sum≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
lemma listCode_length_bound_q339 (xs : List α) (B : ℕ) (h : ∀ x∈xs,(ea x).length≤B) :
    (listCode ea xs).length≤xs.length*(2*B+1) := by
  rw [len_listCode_q339]
  apply sum_map_bound_q339
  intro x hx
  have := h x hx
  omega
lemma list_length_le_code_q339 (ea : α → Word) (xs : List α) : xs.length≤(listCode ea xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listCode_cons,prodCode_length_q339,List.length_cons];omega
lemma mem_length_le_code_q339 (xs : List α) {x : α} (hx : x∈xs) :
    (ea x).length≤(listCode ea xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rw [listCode_cons,prodCode_length_q339]
      dsimp only
      rcases hx with rfl|hx
      · omega
      · have := ih hx;omega
lemma listCode_reverse_length_q339 (ea : α → Word) (xs : List α) :
    (listCode ea xs.reverse).length=(listCode ea xs).length := by
  simp only [len_listCode_q339,List.map_reverse,List.sum_reverse]
instance poly_map_q339 {f : α → β} (r : Realizes ea eb f) [PolyTime r] : PolyTime r.map := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  let Q := X+p
  refine ⟨⟨2*X+X*(3*X+p+6*Q+8)+X*(2*Q+1)+4,?_⟩⟩
  intro xs
  let L := (listCode ea xs).length
  have hn : xs.length≤L := list_length_le_code_q339 ea xs
  have ho : ∀ x∈xs,(eb (f x)).length≤L+p.eval L := by
    intro x hx
    have hl : (ea x).length≤L := mem_length_le_code_q339 xs hx
    exact (r.output_length_q339 x).trans (Nat.add_le_add hl ((hp x).trans (p.eval_mono_q339 hl)))
  have hs := sum_map_bound_q339 xs (fun x => FramedMapRoutine.bodyTicks ea (fun x => eb (f x)) r.cost x+1)
    (3*L+p.eval L+6*(L+p.eval L)+8) (by
      intro x hx
      have hl : (ea x).length≤L := mem_length_le_code_q339 xs hx
      have hc := (hp x).trans (p.eval_mono_q339 hl)
      have hout := ho x hx
      simp only [FramedMapRoutine.bodyTicks,KS.W01.length_frame]
      omega)
  have ht := listCode_length_bound_q339 (ea:=fun x => eb (f x)) xs (L+p.eval L) ho
  have hs' := hs.trans (Nat.mul_le_mul_right _ hn)
  have ht' := ht.trans (Nat.mul_le_mul_right _ hn)
  change FramedMapRoutine.ticks ea (fun x => eb (f x)) r.cost xs≤_
  simp only [FramedMapRoutine.ticks,FramedMapRoutine.scanTicks]
  change 2*L+2+((xs.map _).sum+1)+(listCode (fun x => eb (f x)) xs).length+1≤_
  change _≤2*L+L*(3*L+p.eval L+6*(L+p.eval L)+8)+L*(2*(L+p.eval L)+1)+4
  omega
lemma fold_scan_bound_q339 (F : α → β → α) (cost : α×β → ℕ) (s : α) (xs : List β) (S E C : ℕ)
    (hs : ∀ ys zs,xs=ys++zs → (ea (ys.foldl F s)).length≤S)
    (he : ∀ x∈xs,(eb x).length≤E)
    (hc : ∀ a x,(ea a).length≤S → (eb x).length≤E → cost (a,x)≤C) :
    FoldRoutine.scanTicks ea eb F cost s xs≤xs.length*(3*E+10*S+C+12)+1 := by
  induction xs generalizing s with
  | nil => simp [FoldRoutine.scanTicks]
  | cons x xs ih =>
      have h0 := hs [] (x::xs) rfl
      have h1 := hs [x] xs rfl
      have hx := he x (by simp)
      have hc0 := hc s x h0 hx
      have ht := ih (F s x) (by
        intro ys zs hz
        have h := hs (x::ys) zs (by simp only [List.cons_append];rw [hz])
        simpa only [List.foldl_cons] using h) (fun y hy => he y (by simp [hy]))
      simp only [FoldRoutine.scanTicks,FoldRoutine.bodyTicks,KS.W01.length_frame,List.length_cons,Nat.add_mul,Nat.one_mul]
      simp only [List.foldl_nil,List.foldl_cons] at h0 h1
      omega
instance poly_fold_q339 {f : α×β → α} (r : Realizes (prodCode ea eb) ea f) [PolyTime r] [FoldSize r] :
    PolyTime r.fold := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := FoldSize.bound (r:=r)
  refine ⟨⟨5*q+2*X+X*(3*X+10*q+p.comp (2*q+1+X)+12)+7,?_⟩⟩
  intro u
  let L := (prodCode ea (listCode eb) u).length
  let S := q.eval L
  have he : (listCode eb u.2).length≤L := le_prodCode_right_q339 u
  have hn := (list_length_le_code_q339 eb u.2).trans he
  have hs := hq u.1 u.2
  have h0 : (ea u.1).length≤S := hs [] u.2 rfl
  have hN : (ea (u.2.foldl (fun a b => f (a,b)) u.1)).length≤S := hs u.2 [] (by simp)
  have hc : ∀ a x,(ea a).length≤S → (eb x).length≤L → r.cost (a,x)≤p.eval (2*S+1+L) := by
    intro a x ha hx
    apply (hp (a,x)).trans (p.eval_mono_q339 ?_)
    rw [prodCode_length_q339]
    dsimp only
    omega
  have hscan := fold_scan_bound_q339 (ea:=ea) (eb:=eb) (fun a b => f (a,b)) r.cost u.1 u.2 S L
    (p.eval (2*S+1+L)) hs (fun x hx => (mem_length_le_code_q339 u.2 hx).trans he) hc
  have hscan' := hscan.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  change FoldRoutine.ticks ea eb (fun a b => f (a,b)) r.cost u.1 u.2≤_
  simp only [FoldRoutine.ticks]
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
  change _≤5*S+2*L+L*(3*L+10*S+p.eval (2*S+1+L)+12)+7
  change _≤_ at hscan'
  change (FramedMapRoutine.tape eb u.2).length≤L at he
  omega
lemma iterate_ticks_bound_q339 {f : α → α} (r : Realizes ea ea f) (x : α) (n C : ℕ)
    (h : ∀ i,i<n → r.cost (f^[i] x)≤C) :
    IterateRoutine.loopTicks r.cost f n x≤n*(C+2)+1 := by
  induction n generalizing x with
  | zero => simp [IterateRoutine.loopTicks]
  | succ n ih =>
      have h0 := h 0 (by omega)
      have ht := ih (f x) (by
        intro i hi
        simpa only [←Function.iterate_succ_apply] using h (i+1) (by omega))
      simp only [Function.iterate_zero, id_eq] at h0
      simp only [IterateRoutine.loopTicks,Nat.add_mul,Nat.one_mul]
      omega
instance poly_iterate_q339 {f : α → α} (r : Realizes ea ea f) [PolyTime r] [IterateSize r] :
    PolyTime r.iterate := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := IterateSize.bound (r:=r)
  refine ⟨⟨3*X+X*(p.comp q+2)+3,?_⟩⟩
  intro u
  let L := (prodCode natCode ea u).length
  have hi : (ea u.2).length+u.1≤L := by simp only [L,prodCode_length_q339,natCode,List.length_replicate];omega
  have hn : u.1≤L := by omega
  have ht := iterate_ticks_bound_q339 r u.2 u.1 (p.eval (q.eval L)) (by
    intro i hi'
    exact (hp _).trans (p.eval_mono_q339 ((hq u.2 i).trans (q.eval_mono_q339 (by omega)))))
  have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
  change 3*u.1+2+IterateRoutine.loopTicks r.cost f u.1 u.2≤3*L+L*(p.eval (q.eval L)+2)+3
  omega
end CurrentKS.Realization
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace CurrentKS.Realization
open CleanRoutine
variable {α γ : Type*}
lemma fold_length_q339 (xs : List α) (n : ℕ) : xs.foldl (fun k _ => k+1) n=n+xs.length := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_comm,Nat.add_left_comm]
end CurrentKS.Realization
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
lemma prefix_code_length_q339 (ea : α → Word) (xs ys zs : List α) (h : xs=ys++zs) :
    (listCode ea ys).length≤(listCode ea xs).length := by
  rw [h,listCode_append,List.length_append];omega
lemma prefix_length_q339 (xs ys zs : List α) (h : xs=ys++zs) : ys.length≤xs.length := by
  rw [h,List.length_append];omega
instance poly_appendList_q339 (ea : α → Word) : PolyTime (appendList ea) := by
  refine ⟨⟨5*X+4,?_⟩⟩
  intro p
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 5 (le_prodCode_left_q339 p)) 4
instance poly_reverseBody_q339 (ea : α → Word) : PolyTime (reverseBody ea) := by
  unfold reverseBody;infer_instance
instance size_reverseBody_q339 (ea : α → Word) : FoldSize (reverseBody ea) := by
  refine ⟨⟨X,?_⟩⟩
  intro s xs ys zs h
  rw [fold_cons_q339,listCode_append,List.length_append,listCode_reverse_length_q339]
  have hp := prefix_code_length_q339 ea xs ys zs h
  change _≤(prodCode (listCode ea) (listCode ea) (s,xs)).length
  rw [prodCode_length_q339]
  try dsimp only
  omega
instance poly_reverseList_q339 (ea : α → Word) : PolyTime (reverseList ea) := by
  unfold reverseList;infer_instance
instance poly_mapCtxBody_q339 {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    PolyTime (mapCtxBody ec ea eb r) := by
  dsimp only [mapCtxBody]
  apply poly_both_q339
instance size_mapCtxBody_q339 {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    FoldSize (mapCtxBody ec ea eb r) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  let U := 3*X+1+p.comp (3*X+1)
  refine ⟨⟨3*X+1+X*(2*U+1),?_⟩⟩
  intro s xs ys zs h
  rw [fold_mapCtx]
  let L := (prodCode (prodCode ec (listCode eb)) (listCode ea) (s,xs)).length
  have hc : (ec s.1).length≤L := (le_prodCode_left_q339 s).trans (le_prodCode_left_q339 (s,xs))
  have ha : (listCode eb s.2).length≤L := (le_prodCode_right_q339 s).trans (le_prodCode_left_q339 (s,xs))
  have he : (listCode ea ys).length≤L := (prefix_code_length_q339 ea xs ys zs h).trans (le_prodCode_right_q339 (s,xs))
  have hn : ys.length≤L := (list_length_le_code_q339 ea ys).trans he
  have ho : ∀ x∈ys,(eb (f (s.1,x))).length≤3*L+1+p.eval (3*L+1) := by
    intro x hx
    have hl : (prodCode ec ea (s.1,x)).length≤3*L+1 := by
      have he' := (mem_length_le_code_q339 ys hx).trans he
      simp only [prodCode_length_q339]
      try dsimp only
      omega
    exact (r.output_length_q339 (s.1,x)).trans (Nat.add_le_add hl ((hp _).trans (p.eval_mono_q339 hl)))
  have hm := listCode_length_bound_q339 (ea:=fun x => eb (f (s.1,x))) ys (3*L+1+p.eval (3*L+1)) ho
  have hm' := hm.trans (Nat.mul_le_mul_right _ hn)
  have heq : listCode eb (ys.map (fun x => f (s.1,x)))=listCode (fun x => eb (f (s.1,x))) ys := by
    simp only [listCode,FramedMapRoutine.tape,List.flatMap_map]
  rw [prodCode_length_q339]
  dsimp only
  rw [listCode_append,List.length_append,listCode_reverse_length_q339,heq]
  change 2*(ec s.1).length+1+((listCode (fun x => eb (f (s.1,x))) ys).length+(listCode eb s.2).length)≤_
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp,U]
  change _≤3*L+1+L*(2*(3*L+1+p.eval (3*L+1))+1)
  omega
instance poly_mapCtx_q339 {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    PolyTime r.mapCtx := by
  unfold Realizes.mapCtx
  infer_instance
instance poly_natAdd_q339 : PolyTime natAdd := by
  refine ⟨⟨5*X+4,?_⟩⟩
  intro p
  have h := le_prodCode_left_q339 (ea:=natCode) (eb:=natCode) p
  simp only [natCode,List.length_replicate] at h
  change 5*p.1+4≤5*(prodCode natCode natCode p).length+4
  omega
instance poly_rangeStep_q339 : PolyTime rangeStepRealizes := by dsimp only [rangeStepRealizes];apply poly_both_q339
lemma range_iterate_size_q339 (s : ℕ×List ℕ) (k : ℕ) :
    (rangeStep^[k] s).1=s.1+k ∧
    (listCode natCode (rangeStep^[k] s).2).length≤(listCode natCode s.2).length+k*(2*(s.1+k)+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change (rangeStep^[k] s).1+1=s.1+(k+1) ∧ _
      constructor
      · omega
      · change (listCode natCode ((rangeStep^[k] s).1::(rangeStep^[k] s).2)).length≤_
        rw [listCode_cons,prodCode_length_q339]
        simp only [natCode,List.length_replicate]
        try dsimp only
        nlinarith [ih.2]
instance size_rangeStep_q339 : IterateSize rangeStepRealizes := by
  refine ⟨⟨10*(X+1)^2,?_⟩⟩
  intro s k
  have h := range_iterate_size_q339 s k
  simp only [prodCode_length_q339,natCode,List.length_replicate]
  change 2*(rangeStep^[k] s).1+1+(listCode natCode (rangeStep^[k] s).2).length≤10*(2*s.1+1+(listCode natCode s.2).length+k+1)^2
  rw [h.1]
  nlinarith [h.2]
instance poly_range_q339 : PolyTime range := by unfold range;infer_instance
instance poly_lengthBody_q339 (ea : α → Word) : PolyTime ((first natCode ea).then natSucc) := by infer_instance
instance size_lengthBody_q339 (ea : α → Word) : FoldSize ((first natCode ea).then natSucc) := by
  refine ⟨⟨2*X,?_⟩⟩
  intro s xs ys zs h
  change (natCode (ys.foldl (fun k _ => k+1) s)).length≤_
  rw [fold_length_q339]
  have hs := le_prodCode_left_q339 (ea:=natCode) (eb:=listCode ea) (s,xs)
  have hn := ((prefix_length_q339 xs ys zs h).trans (list_length_le_code_q339 ea xs)).trans (le_prodCode_right_q339 (ea:=natCode) (s,xs))
  simp only [natCode,List.length_replicate] at hs ⊢
  change s+ys.length≤2*(prodCode natCode (listCode ea) (s,xs)).length
  omega
instance poly_lengthList_q339 (ea : α → Word) : PolyTime (lengthList ea) := by unfold lengthList;infer_instance
instance poly_tabulate_q339 {f : γ×ℕ → α} (r : Realizes (prodCode ec natCode) ea f) [PolyTime r] :
    PolyTime r.tabulate := by unfold Realizes.tabulate;infer_instance
end CurrentKS.Realization
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable
instance poly_ratOp_q339 (op : KS.W13.ExpressionMachine.BinaryOp) : PolyTime (ratOp op) := by
  refine ⟨⟨5*X+6000000*(X+1)^3+6,?_⟩⟩
  intro p
  have hl := RoutineLength.output_length_q339 (KS.W13.ExpressionMachine.binaryArithmetic_spec op p.1 p.2 [] []) 10
  have ht : (ratCode (op.eval p.1 p.2)).length≤KS.W13.ExpressionMachine.binaryBudget p.1 p.2 := by simpa [KS.W13.ExpressionMachine.registers] using hl
  have hi : (ratCode p.1).length+(ratCode p.2).length ≤ (prodCode ratCode ratCode p).length := by rw [prodCode_length_q339];omega
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 3
  have ha := le_prodCode_left_q339 (ea:=ratCode) (eb:=ratCode) p
  change ArithmeticRoutine.ticks op p.1 p.2≤5*(prodCode ratCode ratCode p).length+6000000*((prodCode ratCode ratCode p).length+1)^3+6
  simp only [ArithmeticRoutine.ticks,ArithmeticRoutine.encode,KS.W13.ExpressionMachine.binaryBudget,KS.W01.ratLength] at ht ⊢
  simp only [ratCode] at *
  omega
instance poly_ratLE_q339 : PolyTime ratLE := by
  refine ⟨⟨5*X+2048*(X+1)^2+8,?_⟩⟩
  intro p
  have hi : (ratCode p.1).length+(ratCode p.2).length ≤ (prodCode ratCode ratCode p).length := by rw [prodCode_length_q339];omega
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 2
  have ha := le_prodCode_left_q339 (ea:=ratCode) (eb:=ratCode) p
  change CompareRoutine.ticks p.1 p.2≤5*(prodCode ratCode ratCode p).length+2048*((prodCode ratCode ratCode p).length+1)^2+8
  simp only [CompareRoutine.ticks,CompareRoutine.encode,KS.W29.polynomialFuel,List.length_append]
  simp only [ratCode] at *
  omega
variable {α β : Type*} {ea : α → Word} {eb : β → Word}
instance poly_conditional_q339 {f g : α → β} (r : Realizes ea eb f) (s : Realizes ea eb g)
    [PolyTime r] [PolyTime s] : PolyTime (conditional r s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨p+q+6,?_⟩⟩
  intro x
  have hr := (hp x.2).trans (p.eval_mono_q339 (le_prodCode_right_q339 (ea:=boolCode) (eb:=ea) x))
  have hs := (hq x.2).trans (q.eval_mono_q339 (le_prodCode_right_q339 (ea:=boolCode) (eb:=ea) x))
  change 5+(if x.1 then r.cost x.2 else s.cost x.2)+1≤p.eval _+q.eval _+6
  split <;> omega
instance poly_ite_q339 {p : α → Bool} {f g : α → β} (b : Realizes ea boolCode p)
    (r : Realizes ea eb f) (s : Realizes ea eb g) [PolyTime b] [PolyTime r] [PolyTime s] : PolyTime (b.ite r s) := by unfold Realizes.ite; exact poly_then_q339 (b.both (identity ea)) (conditional r s)
instance poly_add_q339 {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.add s) := by unfold Realizes.add; exact poly_then_q339 (r.both s) (ratOp .add)
instance poly_le_q339 {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.le s) := by unfold Realizes.le;infer_instance
end CurrentKS.Realization
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
instance poly_lookupStep_q339 (ea : α → Word) : PolyTime (lookupStepRealizes ea) := by
  dsimp only [lookupStepRealizes]
  apply poly_congr
lemma lookup_fold_size_q339 (ea : α → Word) (s : ℕ×α) (xs : List α) (K B : ℕ)
    (hk : s.1≤K) (ha : (ea s.2).length≤B) (hx : ∀x∈xs,(ea x).length≤B) :
    (xs.foldl (fun s x => lookupStep (s,x)) s).1≤K ∧
    (ea (xs.foldl (fun s x => lookupStep (s,x)) s).2).length≤B := by
  induction xs generalizing s with
  | nil => exact ⟨hk,ha⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      apply ih
      · dsimp only [lookupStep]
        split_ifs <;> (try dsimp only) <;> omega
      · dsimp only [lookupStep]
        split_ifs <;> try dsimp only
        · exact ha
        · exact hx x (by simp)
        · exact ha
      · intro y hy;exact hx y (by simp [hy])
instance size_lookupStep_q339 (ea : α → Word) : FoldSize (lookupStepRealizes ea) := by
  refine ⟨⟨3*X+1,?_⟩⟩
  intro s xs ys zs h
  let L := (prodCode (prodCode natCode ea) (listCode ea) (s,xs)).length
  have hk : s.1≤L := by
    have hl := (le_prodCode_left_q339 (ea:=natCode) (eb:=ea) s).trans (le_prodCode_left_q339 (eb:=listCode ea) (s,xs))
    simpa only [natCode,List.length_replicate] using hl
  have ha : (ea s.2).length≤L := (le_prodCode_right_q339 s).trans (le_prodCode_left_q339 (s,xs))
  have hy : (listCode ea ys).length≤L := (prefix_code_length_q339 ea xs ys zs h).trans (le_prodCode_right_q339 (s,xs))
  have ht := lookup_fold_size_q339 ea s ys L L hk ha (fun x hx => (mem_length_le_code_q339 ys hx).trans hy)
  change (prodCode natCode ea _).length≤3*L+1
  rw [prodCode_length_q339]
  simp only [natCode,List.length_replicate]
  omega
instance poly_getD_q339 (ea : α → Word) (a : α) : PolyTime (getD ea a) := by unfold getD;infer_instance
instance poly_zipWith_q339 {f : α×β → γ} (r : Realizes (prodCode ea eb) ec f) (a : α) (b : β)
    [PolyTime r] : PolyTime (r.zipWith a b) := by unfold Realizes.zipWith;apply poly_then_q339
lemma ratLength_natCast_q339 (n : ℕ) : KS.W01.ratLength (n : ℚ)≤4*n+11 := by
  apply (KS.W01.ratLength_le_of_parts (n : ℚ) n n ?_ ?_).trans (by omega)
  · simpa only [Rat.num_natCast,Int.natAbs_natCast] using (Nat.le_of_lt (Nat.lt_two_pow_self (n:=n)))
  · simpa only [Rat.den_natCast] using (Nat.one_le_two_pow (n:=n))
instance size_ratSucc_q339 : IterateSize ((identity ratCode).add (constant ratCode ratCode 1)) := by
  refine ⟨⟨20*X+60,?_⟩⟩
  intro q n
  change (ratCode ((fun x : ℚ => x+1)^[n] q)).length≤_
  rw [iterate_ratSucc]
  have h := KS.W01.ratLength_add_le q (n : ℚ)
  have hn := ratLength_natCast_q339 n
  change KS.W01.ratLength (q+(n : ℚ))≤20*(KS.W01.ratLength q+n)+60
  omega
instance poly_natToRat_q339 : PolyTime natToRat := by unfold natToRat;infer_instance
instance size_natMulStep_q339 : IterateSize ((first natCode natCode).both natAdd) := by
  refine ⟨⟨10*(X+1)^2,?_⟩⟩
  intro s n
  change (prodCode natCode natCode ((fun a : ℕ×ℕ => (a.1,a.1+a.2))^[n] s)).length≤_
  rcases s with ⟨k,z⟩
  rw [fold_natAdd]
  simp only [prodCode_length_q339,natCode,List.length_replicate]
  change 2*k+1+(n*k+z)≤10*(2*k+1+z+n+1)^2
  nlinarith
instance poly_natMul_q339 : PolyTime natMul := by unfold natMul;infer_instance
end CurrentKS.Realization
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable
variable {ι α β γ : Type*} {L f g : ι → ℕ}
lemma IsPoly.mono_q339 (hf : IsPoly L f) (h : ∀i,g i≤f i) : IsPoly L g := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun i => (h i).trans (hp i)⟩
lemma IsPoly.add_q339 (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i+g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,fun i => Nat.add_le_add (hp i) (hq i)⟩
lemma IsPoly.mul_q339 (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i*g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,fun i => Nat.mul_le_mul (hp i) (hq i)⟩
lemma isPoly_const_q339 (L : ι → ℕ) (c : ℕ) : IsPoly L (fun _ => c) := ⟨.constant c,fun _ => le_rfl⟩
lemma isPoly_self_q339 (L : ι → ℕ) : IsPoly L L := ⟨X,fun _ => le_rfl⟩
lemma IsPoly.eval_q339 (hf : IsPoly L f) (p : NaturalPolynomial) : IsPoly L (fun i => p.eval (f i)) := by
  obtain ⟨q,hq⟩ := hf
  exact ⟨p.comp q,fun i => by simpa only [NaturalPolynomial.eval_comp] using p.eval_mono_q339 (hq i)⟩
variable {ea : α → Word} {eb : β → Word} {ec : γ → Word} {F : α → β} {G : β → γ}
lemma RunsPoly.of_poly_q339 (r : Realizes ea eb F) [PolyTime r] (a : ι → α)
    (h : IsPoly L (fun i => (ea (a i)).length)) : RunsPoly L r a := by
  refine ⟨h,?_⟩
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  exact (h.eval_q339 p).mono_q339 (fun i => hp (a i))
lemma RunsPoly.output_q339 {r : Realizes ea eb F} {a : ι → α} (h : RunsPoly L r a) :
    IsPoly L (fun i => (eb (F (a i))).length) := (h.input.add_q339 h.cost).mono_q339 (fun i => r.output_length_q339 (a i))
lemma RunsPoly.then_q339 {r : Realizes ea eb F} {s : Realizes eb ec G} {a : ι → α}
    (hr : RunsPoly L r a) (hs : RunsPoly L s (fun i => F (a i))) : RunsPoly L (r.then s) a :=
  ⟨hr.input,hr.cost.add_q339 hs.cost⟩
lemma RunsPoly.then_poly_q339 {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    (s : Realizes eb ec G) [PolyTime s] : RunsPoly L (r.then s) a :=
  hr.then_q339 (RunsPoly.of_poly_q339 s _ hr.output_q339)
lemma RunsPoly.both_q339 {G : α → γ} {r : Realizes ea eb F} {s : Realizes ea ec G} {a : ι → α}
    (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.both s) a := by
  refine ⟨hr.input,?_⟩
  have h := (((((isPoly_const_q339 L 4).mul_q339 hr.input).add_q339 ((isPoly_const_q339 L 12).mul_q339 hr.output_q339)).add_q339 hr.cost).add_q339 hs.cost).add_q339 (isPoly_const_q339 L 15)
  apply h.mono_q339
  intro i
  change PairRoutine.pairingTicks ea (fun x => eb (F x)) r.cost s.cost (a i)≤_
  simp only [PairRoutine.pairingTicks,KS.W01.length_frame]
  omega
lemma RunsPoly.changeOutput_q339 {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    {δ : Type*} (ed : δ → Word) (g : α → δ) (h : ∀x,eb (F x)=ed (g x)) :
    RunsPoly L (r.changeOutput ed g h) a := ⟨hr.input,hr.cost⟩
end CurrentKS.Realization
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
lemma flatten_code_le_q339 (ea : α → Word) (xs : List (List α)) :
    (listCode ea xs.flatten).length≤(listCode (listCode ea) xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatten_cons,listCode_append,List.length_append,listCode_cons,prodCode_length_q339]
      omega
instance size_appendList_q339 (ea : α → Word) : FoldSize (appendList ea) := by
  refine ⟨⟨2*X,?_⟩⟩
  intro s xs ys zs h
  rw [fold_append_flatten,listCode_append,List.length_append]
  have hs := le_prodCode_left_q339 (ea:=listCode ea) (eb:=listCode (listCode ea)) (s,xs)
  have hy := (flatten_code_le_q339 ea ys).trans ((prefix_code_length_q339 (listCode ea) xs ys zs h).trans (le_prodCode_right_q339 (ea:=listCode ea) (s,xs)))
  change _≤2*(prodCode (listCode ea) (listCode (listCode ea)) (s,xs)).length
  dsimp only at hs hy
  omega
instance poly_joinList_q339 (ea : α → Word) : PolyTime (joinList ea) := by unfold joinList;infer_instance
instance poly_singleton_q339 (ea : α → Word) : PolyTime (singleton ea) := by unfold singleton;apply poly_then_q339
instance poly_natToBinary_q339 : PolyTime natToBinary := by unfold natToBinary;infer_instance
instance poly_natLE_q339 : PolyTime natLE := by unfold natLE;infer_instance
instance poly_natEq_q339 : PolyTime natEq := by unfold natEq;infer_instance
instance poly_tabulateFin_q339 {n : α → ℕ} {f : (Σ a,Fin (n a)) → β}
    (r : Realizes (finFamilyCode ea n) eb f) (rn : Realizes ea natCode n) [PolyTime r] [PolyTime rn] :
    PolyTime (r.tabulateFin rn) := by unfold Realizes.tabulateFin;infer_instance
instance poly_familyFirst_q339 {n : α → ℕ} : PolyTime (familyFirst (ea:=ea) (n:=n)) := by unfold familyFirst;apply poly_reindex
instance poly_familyIndex_q339 {n : α → ℕ} : PolyTime (familyIndex (ea:=ea) (n:=n)) := by unfold familyIndex;apply poly_reindex
end CurrentKS.Realization
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
namespace CurrentKS.ArchivedMachine
open KS.W01.FixedStack
lemma action_apply_q339 (a : KS.W29.StackAction) (l : List Bool) :
    (action a).apply l=a.apply l := by cases a <;> rfl
lemma heads_eq_q339 (k : ℕ) (s : Fin k → List Bool) :
    KS.W01.FixedStack.headsCode k (fun j => ⟨KS.W29.topCode (s j),KS.W29.topCode_lt_three _⟩)=
      CurrentKS.headsCode k s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [KS.W01.FixedStack.headsCode,CurrentKS.headsCode,ih]
      rfl
lemma heads_lt_q339 (k : ℕ) (s : Fin k → List Bool) : CurrentKS.headsCode k s<3^k := by
  rw [←heads_eq_q339]
  exact KS.W01.FixedStack.headsCode_lt _ _
lemma step_eq_q339 (M : KS.W01.FixedStack.Machine) (c : KS.W01.FixedStack.Config M.stackCount M.states) :
    (machine M).step (config c)=config (M.step c false) := by
  rcases c with ⟨s,ts⟩
  cases s with
  | none => rfl
  | some q =>
      have hi : 3^M.stackCount*q.val+CurrentKS.headsCode M.stackCount ts<
          M.states*3^M.stackCount := by
        have hh := heads_lt_q339 M.stackCount ts
        have hq := q.isLt
        nlinarith
      have hl : 3^M.stackCount*q.val+CurrentKS.headsCode M.stackCount ts<
          (List.ofFn fun i : Fin (M.states*3^M.stackCount) =>
            instruction (M.table.getD (2*i.val) (KS.W01.FixedStack.Instruction.halt _ _))).length := by
        simpa only [List.length_ofFn] using hi
      simp only [CurrentKS.Machine.step,machine,config,List.getD_eq_getElem _ _ hl,
        List.getElem_ofFn,KS.W01.FixedStack.Machine.step]
      rw [KS.W01.FixedStack.tableIndex_val_q339]
      have hh : KS.W01.FixedStack.headsCode M.stackCount
          (KS.W01.FixedStack.observedHeads (⟨some q,ts⟩ : KS.W01.FixedStack.Config _ _))=
          CurrentKS.headsCode M.stackCount ts := heads_eq_q339 _ _
      rw [hh]
      simp only [KS.W29.bitCode,Bool.false_eq_true,↓reduceIte,add_zero]
      have he : 3^M.stackCount*2*q.val+2*CurrentKS.headsCode M.stackCount ts=
          2*(3^M.stackCount*q.val+CurrentKS.headsCode M.stackCount ts) := by ring
      rw [he]
      unfold instruction
      congr 1
      funext j
      exact action_apply_q339 _ _
lemma iterate_eq_q339 (M : KS.W01.FixedStack.Machine) (k : ℕ)
    (c : KS.W01.FixedStack.Config M.stackCount M.states) :
    ((machine M).step^[k]) (config c)=config (M.run c (List.replicate k false)) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply,step_eq_q339]
      exact ih (M.step c false)
theorem runSpec_transfer_q339 {k : ℕ} (P : KS.W29.FixedSequential.Program k)
    (before after : Fin k → List Bool) (ticks : ℕ)
    (h : KS.W03.MachineCombinators.RunSpec P before after ticks) :
    ((machine P.toMachine).step^[ticks]) (⟨some P.initial,before⟩ : CurrentKS.Config k P.states)=
      ⟨none,after⟩ := by
  have hr := h (List.replicate ticks false) (List.length_replicate ..)
  have hi := iterate_eq_q339 P.toMachine ticks ⟨some P.initial,before⟩
  rw [hr] at hi
  exact hi
end CurrentKS.ArchivedMachine
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
namespace CurrentKS
open Realization CleanRoutine
lemma program_ports_run_q339 {k : ℕ} (P : KS.W29.FixedSequential.Program k) (a b : Fin k)
    (c : KS.W01.FixedStack.Config k P.states) (bits : List Bool) :
    ({P with input := a,output := b}.toMachine).run c bits=P.toMachine.run c bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons bit bits ih =>
    have he : ({P with input := a,output := b}.toMachine).step c bit=P.toMachine.step c bit := by
      rcases c with ⟨s,ts⟩
      cases s <;> rfl
    simpa only [KS.W01.FixedStack.Machine.run,he] using ih (P.toMachine.step c bit)
lemma Machine.run_halted_q339 {M : Machine} {input : List Bool} {k t : ℕ}
    (h : (M.run input k).state=none) (ht : k≤t) : M.run input t=M.run input k := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [Nat.add_comm k r,Machine.run,Function.iterate_add_apply,←Machine.run]
  apply Function.iterate_fixed
  simp only [Machine.step,h]
end CurrentKS
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable
variable {α : Type*} {ea : α → Word} {f g : α → ℕ}
instance instPolyTimeNatNadd_q339 {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nadd s) := by unfold Realizes.nadd;infer_instance
instance instPolyTimeNatNmul_q339 {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nmul s) := by unfold Realizes.nmul;infer_instance
end CurrentKS.Realization
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace CurrentKS.Realization
open CleanRoutine KS.W23
variable {α β : Type*} {ea : α → Word} {eb : β → Word}
variable {I J : α → Type*} {n m : α → ℕ}
instance poly_not_q339 {P : α → Prop} [DecidablePred P]
    (r : Realizes ea boolCode (fun a => decide (P a))) [PolyTime r] : PolyTime r.not := by
  unfold Realizes.not;infer_instance
end CurrentKS.Realization
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace CurrentKS.Realization
open CleanRoutine KS.W23
lemma runsPoly_binaryToNat_q339 {ι : Type*} {L : ι → ℕ} (a : ι → ℕ)
    (ha : IsPoly L (fun i => (binaryNatCode (a i)).length)) (hn : IsPoly L a) :
    RunsPoly L binaryToNat a := by
  refine ⟨ha,?_⟩
  exact (((isPoly_const_q339 L 6).mul_q339 hn).add_q339 ((isPoly_const_q339 L 4).mul_q339 ha)).add_q339 (isPoly_const_q339 L 4)
end CurrentKS.Realization
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace AlgorithmicThinTrees
open StrongThinTree Finset
lemma framed_nat_length_pos_q339 (v : ℕ) : 0 < (CurrentKS.encodeNat v).length := by
  unfold CurrentKS.encodeNat
  cases Computability.encodeNat v <;> simp [CurrentKS.frame]
lemma record_count_le_bits_q339 (records : List (List Bool))
    (h : ∀ bits ∈ records, 0 < bits.length) : records.length ≤ records.flatten.length := by
  induction records with
  | nil => simp
  | cons bits records ih =>
    have hb := h bits (List.mem_cons_self ..)
    have hr := ih (fun bs hbs => h bs (List.mem_cons_of_mem _ hbs))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega
end AlgorithmicThinTrees
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack
instance poly_field_q339 (i : ℕ) : PolyTime (field i) := by unfold field;infer_instance
lemma poly_bounded_binary_q339 {α : Type*} {ea : α → Word} {f : α → ℕ}
    (r : Realizes ea binaryNatCode f) [PolyTime r]
    (hf : IsPoly (fun a => (ea a).length) f) : PolyTime (r.then binaryToNat) := by
  have h := RunsPoly.of_poly_q339 r id (isPoly_self_q339 (fun a => (ea a).length))
  exact ⟨(h.then_q339 (runsPoly_binaryToNat_q339 f h.output_q339 hf)).cost⟩
end AlgorithmicThinTrees.InputStack
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack GraphStack
lemma makeProblem_n_q339 {n m : ℕ} (G : MultiGraph n m) (hn : 0<n) (k : ℕ) :
    (makeProblem G hn k).d+1=n := Nat.sub_add_cancel hn
lemma makeProblem_connected_q339 {n m : ℕ} (G : MultiGraph n m) (hn : 0<n) (k : ℕ)
    (hc : G.EdgeConnected k) : (makeProblem G hn k).G.EdgeConnected k := by
  cases n with
  | zero => omega
  | succ d => simpa [makeProblem] using hc
lemma makeProblem_thin_q339 {n m : ℕ} (G : MultiGraph n m) (hn : 0<n) (k : ℕ)
    {C : ℝ} {T : Finset (Fin m)} (h : ThinTree C k (makeProblem G hn k).G T) :
    ThinTree C k G T := by
  cases n with
  | zero => omega
  | succ d => simpa [makeProblem] using h
end AlgorithmicThinTrees.InputStack
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace AlgorithmicThinTrees.OrderedGraph
open Finset StrongThinTree StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma lift_univ_q339 (F : Finset (Fin m)) : liftEdges F univ=F := by
  ext e
  simp only [liftEdges,mem_map,mem_univ,true_and]
  exact ⟨fun ⟨i,hi⟩ => hi ▸ embedding_mem F i, embedding_surj F⟩
end AlgorithmicThinTrees.OrderedGraph
end
end OAI
end
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI
section
namespace CurrentKS.Realization
open CleanRoutine KS.W23 Finset
open AlgorithmicThinTrees.OrderedGraph
variable {α : Type*}
instance poly_maskEntry_q339 (ea : α → Word) : PolyTime (maskEntry ea) := by unfold maskEntry;infer_instance
instance poly_maskArray_q339 (ea : α → Word) (z : α) : PolyTime (maskArray ea z) := by
  unfold maskArray;infer_instance
end CurrentKS.Realization
end
end OAI
end
section


namespace Q339.Wrapper
open OAI OAI.StrongThinTree OAI.CurrentKS OAI.CurrentKS.Realization OAI.CurrentKS.CleanRoutine
open OAI.KS.W23 OAI.AlgorithmicThinTrees OAI.AlgorithmicThinTrees.InputStack
open OAI.AlgorithmicThinTrees.OrderedGraph OAI.AlgorithmicThinTrees.GraphicHalf.Stack
open OAI.AlgorithmicThinTrees.Iteration.Stack

/-! Input format. -/

structure Inp where
  n : ℕ
  m : ℕ
  k : ℕ
  G : RemovingTrees.Main.MultiGraph n m

def Inp.Good (x : Inp) : Prop :=
  2 ≤ x.n ∧ 0 < x.k ∧ RemovingTrees.Main.CutLower x.G Finset.univ x.k

abbrev I := {x : Inp // x.Good}

def iCode (x : I) : Word :=
  RemovingTrees.Main.encNat x.val.k ++ RemovingTrees.Main.encGraph x.val.G

def iFields (x : Inp) : List ℕ :=
  [x.k, x.n, x.m] ++ (List.ofFn fun i => [(x.G.left i).val, (x.G.right i).val]).flatten

lemma iFields_code (x : Inp) :
    fieldsCode (iFields x) = RemovingTrees.Main.encNat x.k ++ RemovingTrees.Main.encGraph x.G := by
  simp only [iFields,listCode_append,listCode_cons,listCode_nil,prodCode,PairRoutine.pair,
    fieldsCode_flatten,List.map_ofFn,Function.comp_def]
  simp [binaryNatCode,RemovingTrees.Main.encGraph,
    CurrentKS.DenseInputMachine.encodeNat_eq,KS.W01.encodeNat,List.append_assoc]

lemma fieldsCode_eq (xs : List ℕ) : fieldsCode xs = xs.flatMap CurrentKS.encodeNat := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change prodCode binaryNatCode fieldsCode (x,xs) = _
    simp only [prodCode,PairRoutine.pair,ih,List.flatMap_cons]
    simp [binaryNatCode,CurrentKS.DenseInputMachine.encodeNat_eq,KS.W01.encodeNat]

abbrev iView : Realizes iCode fieldsCode (fun x => iFields x.val) :=
  (identity fieldsCode).reindex iCode (fun x => iFields x.val) (fun x => (iFields_code x.val).symm)

def iKBinary : Realizes iCode binaryNatCode (fun x => x.val.k) :=
  (iView.then (field 0)).congr (by intro x;rfl)
def iNBinary : Realizes iCode binaryNatCode (fun x => x.val.n) :=
  (iView.then (field 1)).congr (by intro x;rfl)
def iMBinary : Realizes iCode binaryNatCode (fun x => x.val.m) :=
  (iView.then (field 2)).congr (by intro x;rfl)

abbrev iEdgeCode := finFamilyCode iCode (fun x : I => x.val.m)
abbrev ieInput : Realizes iEdgeCode iCode (fun x => x.1) := familyFirst
abbrev ieIndex : Realizes iEdgeCode natCode (fun x => x.2.val) := familyIndex

def iEndpointBinary (right : Bool) : Realizes iEdgeCode binaryNatCode
    (fun x => if right then (x.1.val.G.right x.2).val else (x.1.val.G.left x.2).val) :=
  ((((constant iEdgeCode natCode 3).nadd (ieIndex.nmul (constant iEdgeCode natCode 2))).nadd
    (constant iEdgeCode natCode (if right then 1 else 0))).both (ieInput.then iView)).then
      (getD binaryNatCode 0) |>.congr (by
        intro x
        have hh := records_lookup (w:=2) x.1.val.k x.1.val.n x.1.val.m
          (fun i => [(x.1.val.G.left i).val,(x.1.val.G.right i).val])
          (fun _ => rfl) x.2 (if right then 1 else 0) (by cases right <;> decide)
        cases right <;> simpa [iFields] using hh)

instance poly_iView : PolyTime iView := by unfold iView;apply poly_reindex
instance poly_iKBinary : PolyTime iKBinary := by unfold iKBinary;apply poly_congr
instance poly_iNBinary : PolyTime iNBinary := by unfold iNBinary;apply poly_congr
instance poly_iMBinary : PolyTime iMBinary := by unfold iMBinary;apply poly_congr
instance poly_iEndpointBinary (right : Bool) : PolyTime (iEndpointBinary right) := by
  unfold iEndpointBinary;infer_instance

/-! Size bounds. -/

lemma records_le (x : Inp) :
    x.m ≤ (RemovingTrees.Main.encNat x.k ++ RemovingTrees.Main.encGraph x.G).length := by
  have h := record_count_le_bits_q339 (List.ofFn fun i : Fin x.m =>
    RemovingTrees.Main.encNat (x.G.left i).val ++ RemovingTrees.Main.encNat (x.G.right i).val) (by
      intro bits hb
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
      have hh : 0 < (RemovingTrees.Main.encNat (x.G.left i).val).length :=
        framed_nat_length_pos_q339 (x.G.left i).val
      simp only [List.length_append];omega)
  simp only [List.length_ofFn] at h
  simp only [RemovingTrees.Main.encGraph,List.length_append]
  omega

lemma dims (x : I) : x.val.k ≤ x.val.m ∧ x.val.n ≤ 2*x.val.m := by
  classical
  obtain ⟨hn,hk,hc⟩ := x.property
  have hsingle (v : Fin x.val.n) :
      RemovingTrees.Main.NontrivialShore ({v} : Finset (Fin x.val.n)) := by
    refine ⟨Finset.singleton_nonempty _,?_⟩
    intro he
    have he := congrArg Finset.card he
    simp only [Finset.card_singleton,Finset.card_univ,Fintype.card_fin] at he
    omega
  have hcard (S : Finset (Fin x.val.n)) :
      (RemovingTrees.Main.cut x.val.G Finset.univ S).card ≤ x.val.m := by
    have hh : RemovingTrees.Main.cut x.val.G Finset.univ S ⊆ Finset.univ := Finset.filter_subset _ _
    simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card hh
  have hcut (v : Fin x.val.n) : 0 < (RemovingTrees.Main.cut x.val.G Finset.univ {v}).card := by
    have h1 := hc {v} (hsingle v)
    have h2 : (1:ℝ) ≤ x.val.k := by exact_mod_cast hk
    have h3 : (0:ℝ) < (RemovingTrees.Main.cut x.val.G Finset.univ {v}).card := by linarith
    exact_mod_cast h3
  refine ⟨?_,?_⟩
  · have h1 := hc {⟨0,by omega⟩} (hsingle _)
    have h2 := hcard {⟨0,by omega⟩}
    have h3 : (x.val.k:ℝ) ≤ x.val.m := h1.trans (by exact_mod_cast h2)
    exact_mod_cast h3
  have hcover : (Finset.univ : Finset (Fin x.val.n)) ⊆
      Finset.univ.image x.val.G.left ∪ Finset.univ.image x.val.G.right := by
    intro v _
    obtain ⟨e,he⟩ := Finset.card_pos.mp (hcut v)
    rcases (Finset.mem_filter.mp he).2 with h | h
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨e,Finset.mem_univ _,Finset.mem_singleton.mp h.1⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e,Finset.mem_univ _,Finset.mem_singleton.mp h.1⟩)
  have h := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hl := Finset.card_image_le (s:=Finset.univ) (f:=x.val.G.left)
  have hr := Finset.card_image_le (s:=Finset.univ) (f:=x.val.G.right)
  simp only [Finset.card_univ,Fintype.card_fin] at *
  omega

lemma iM_bound (x : I) : x.val.m ≤ (iCode x).length := records_le _
lemma iN_bound (x : I) : x.val.n ≤ 2*(iCode x).length := by
  have h := (dims x).2
  have h' := iM_bound x
  omega
lemma iK_bound (x : I) : x.val.k ≤ (iCode x).length := (dims x).1.trans (iM_bound x)

def iN : Realizes iCode natCode (fun x => x.val.n) := iNBinary.then binaryToNat
def iM : Realizes iCode natCode (fun x => x.val.m) := iMBinary.then binaryToNat
def iK : Realizes iCode natCode (fun x => x.val.k) := iKBinary.then binaryToNat
def iEndpoint (right : Bool) : Realizes iEdgeCode natCode
    (fun x => if right then (x.1.val.G.right x.2).val else (x.1.val.G.left x.2).val) :=
  (iEndpointBinary right).then binaryToNat

instance poly_iN : PolyTime iN := by
  apply poly_bounded_binary_q339
  exact ((isPoly_const_q339 _ 2).mul_q339 (isPoly_self_q339 _)).mono_q339 iN_bound
instance poly_iM : PolyTime iM := by
  apply poly_bounded_binary_q339
  exact (isPoly_self_q339 _).mono_q339 iM_bound
instance poly_iK : PolyTime iK := by
  apply poly_bounded_binary_q339
  exact (isPoly_self_q339 _).mono_q339 iK_bound
instance poly_iEndpoint (right : Bool) : PolyTime (iEndpoint right) := by
  apply poly_bounded_binary_q339
  apply ((isPoly_const_q339 _ 2).mul_q339 (isPoly_self_q339 _)).mono_q339
  intro x
  have hv := iN_bound x.1
  have hl : (iCode x.1).length ≤ (iEdgeCode x).length :=
    le_prodCode_left_q339 (ea:=iCode) (eb:=natCode) (x.1,x.2.val)
  have h1 := (x.1.val.G.left x.2).isLt
  have h2 := (x.1.val.G.right x.2).isLt
  cases right <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

/-! Removing the loops. -/

def nonLoops {n m : ℕ} (G : RemovingTrees.Main.MultiGraph n m) : Finset (Fin m) :=
  Finset.univ.filter (fun e => G.left e ≠ G.right e)

def loopBit : Realizes iEdgeCode boolCode
    (fun p => decide ((p.1.val.G.left p.2).val = (p.1.val.G.right p.2).val)) :=
  (((iEndpoint false).both (iEndpoint true)).then natEq).congr (fun _ => rfl)

def nonLoopBit : Realizes iEdgeCode boolCode (fun p => decide (p.2 ∈ nonLoops p.1.val.G)) :=
  (Realizes.not (P := fun p : (Σ x : I, Fin x.val.m) =>
      (p.1.val.G.left p.2).val = (p.1.val.G.right p.2).val) loopBit).congr (by
    intro p
    simp [nonLoops,Fin.ext_iff])

instance poly_loopBit : PolyTime loopBit := by unfold loopBit;infer_instance
instance poly_nonLoopBit : PolyTime nonLoopBit := by unfold nonLoopBit;infer_instance

def mask : Realizes iCode boolsCode
    (fun x => List.ofFn (fun e : Fin x.val.m => decide (e ∈ nonLoops x.val.G))) :=
  nonLoopBit.tabulateFin iM
instance poly_mask : PolyTime mask := by unfold mask;infer_instance

def lefts : Realizes iCode indicesCode
    (fun x => List.ofFn (fun e : Fin x.val.m => (x.val.G.left e).val)) :=
  ((iEndpoint false).tabulateFin iM).congr (fun _ => rfl)
def rights : Realizes iCode indicesCode
    (fun x => List.ofFn (fun e : Fin x.val.m => (x.val.G.right e).val)) :=
  ((iEndpoint true).tabulateFin iM).congr (fun _ => rfl)
def allIdx : Realizes iCode indicesCode
    (fun x => List.ofFn (fun e : Fin x.val.m => e.val)) :=
  (iM.then range).congr (by
    intro x
    rw [List.ofFn_eq_map]
    exact range_finRange _)
instance poly_lefts : PolyTime lefts := by unfold lefts;infer_instance
instance poly_rights : PolyTime rights := by unfold rights;infer_instance
instance poly_allIdx : PolyTime allIdx := by unfold allIdx;infer_instance

def select {f : (x : I) → Fin x.val.m → ℕ}
    (r : Realizes iCode indicesCode (fun x => List.ofFn (f x))) :
    Realizes iCode indicesCode
      (fun x => List.ofFn (fun i => f x (edgeEmbedding (nonLoops x.val.G) i))) :=
  ((mask.both r).then (maskArray natCode 0)).congr (fun _ => maskArray_data _ _ 0)
instance poly_select {f : (x : I) → Fin x.val.m → ℕ}
    (r : Realizes iCode indicesCode (fun x => List.ofFn (f x))) [PolyTime r] :
    PolyTime (select r) := by unfold select;infer_instance

def G' (x : Inp) : StrongThinTree.MultiGraph x.n (nonLoops x.G).card where
  left i := x.G.left (edgeEmbedding (nonLoops x.G) i)
  right i := x.G.right (edgeEmbedding (nonLoops x.G) i)
  loopless i := (Finset.mem_filter.mp (embedding_mem _ i)).2

def iProblem (x : I) : Problem :=
  makeProblem (G' x.val) (by have := x.property.1;omega) x.val.k

def iPrepare : Realizes iCode problemCode iProblem :=
  ((iN.both ((select lefts).both (select rights))).both iK).changeOutput problemCode iProblem (by
    intro x
    unfold iProblem
    rw [makeProblem_code]
    rfl)
instance poly_iPrepare : PolyTime iPrepare := by unfold iPrepare;infer_instance

/-! Output. -/

def lift : Realizes (prodCode indicesCode indicesCode) indicesCode
    (fun p => p.2.map (fun i => p.1.getD i 0)) :=
  (((second indicesCode natCode).both (first indicesCode natCode)).then (getD natCode 0)).mapCtx
instance poly_lift : PolyTime lift := by unfold lift;infer_instance

def encOut : Realizes indicesCode fieldsCode (fun xs => xs.length :: xs) :=
  ((((lengthList natCode).then natToBinary).both natToBinary.map).then
    (consList binaryNatCode)).congr (by intro xs;simp)
instance poly_encOut : PolyTime encOut := by unfold encOut;infer_instance

def iEdges (R : ℕ) (x : I) : List (Fin x.val.m) :=
  List.ofFn (fun i => edgeEmbedding (nonLoops x.val.G)
    (edgeEmbedding (Iteration.tree R (iProblem x).r (iProblem x).G) i))

def iOutput (R : ℕ) (x : I) : Word := RemovingTrees.Main.encEdges (iEdges R x)

lemma iOutput_code (R : ℕ) (x : I) :
    fieldsCode (((treeData R (iProblem x)).map (fun i =>
      (List.ofFn (fun j : Fin (nonLoops x.val.G).card =>
        (edgeEmbedding (nonLoops x.val.G) j).val)).getD i 0)).length ::
      ((treeData R (iProblem x)).map (fun i =>
      (List.ofFn (fun j : Fin (nonLoops x.val.G).card =>
        (edgeEmbedding (nonLoops x.val.G) j).val)).getD i 0))) = iOutput R x := by
  have hL : (treeData R (iProblem x)).map (fun i =>
      (List.ofFn (fun j : Fin (nonLoops x.val.G).card =>
        (edgeEmbedding (nonLoops x.val.G) j).val)).getD i 0) = (iEdges R x).map Fin.val := by
    simp only [treeData,iEdges,List.map_ofFn,Function.comp_def]
    congr 1
    funext e
    exact getD_ofFn (fun j : Fin (nonLoops x.val.G).card => (edgeEmbedding _ j).val) _ 0
  rw [hL,fieldsCode_eq]
  simp [iOutput,RemovingTrees.Main.encEdges,RemovingTrees.Main.encList,List.flatMap_map]

def iRun (R : ℕ) : Realizes iCode wordCode (iOutput R) :=
  ((((select allIdx).both (iPrepare.then (treeProgram R))).then lift).then encOut).changeOutput
    wordCode (iOutput R) (fun x => iOutput_code R x)

/-! Loops cross no cut. -/

lemma cut_map (x : Inp) (F : Finset (Fin (nonLoops x.G).card)) (S : Finset (Fin x.n)) :
    RemovingTrees.Main.cut x.G (F.map (edgeEmbedding (nonLoops x.G))) S =
      ((G' x).cut F S).map (edgeEmbedding (nonLoops x.G)) := by
  ext e
  simp only [RemovingTrees.Main.cut,StrongThinTree.MultiGraph.cut,Finset.mem_filter,Finset.mem_map]
  constructor
  · rintro ⟨⟨i,hi,rfl⟩,hc⟩
    exact ⟨i,⟨hi,hc⟩,rfl⟩
  · rintro ⟨i,⟨hi,hc⟩,rfl⟩
    exact ⟨⟨i,hi,rfl⟩,hc⟩

lemma cut_univ (x : Inp) (S : Finset (Fin x.n)) :
    RemovingTrees.Main.cut x.G Finset.univ S =
      RemovingTrees.Main.cut x.G (Finset.univ.map (edgeEmbedding (nonLoops x.G))) S := by
  have hu : Finset.univ.map (edgeEmbedding (nonLoops x.G)) = nonLoops x.G := lift_univ_q339 _
  rw [hu]
  ext e
  simp only [RemovingTrees.Main.cut,Finset.mem_filter,Finset.mem_univ,true_and,nonLoops]
  constructor
  · intro h
    refine ⟨?_,h⟩
    intro he
    rcases h with h | h
    · rw [he] at h;exact h.2 h.1
    · rw [he] at h;exact h.2 h.1
  · exact And.right

lemma card_cut_map (x : Inp) (F : Finset (Fin (nonLoops x.G).card)) (S : Finset (Fin x.n)) :
    (RemovingTrees.Main.cut x.G (F.map (edgeEmbedding (nonLoops x.G))) S).card =
      ((G' x).cut F S).card := by
  rw [cut_map,Finset.card_map]

lemma card_cut_univ (x : Inp) (S : Finset (Fin x.n)) :
    (RemovingTrees.Main.cut x.G Finset.univ S).card = ((G' x).cut Finset.univ S).card := by
  rw [cut_univ,card_cut_map]

lemma connected_iff (x : Inp) (F : Finset (Fin (nonLoops x.G).card)) :
    RemovingTrees.Main.Connected x.G (F.map (edgeEmbedding (nonLoops x.G))) ↔
      (G' x).Connected F := by
  constructor
  · intro h S hS hS'
    have hh := h S ⟨hS,hS'⟩
    rw [cut_map] at hh
    exact Finset.map_nonempty.mp hh
  · intro h S hS
    rw [cut_map]
    exact Finset.map_nonempty.mpr (h S hS.1 hS.2)

lemma tree_lift (x : Inp) (T : Finset (Fin (nonLoops x.G).card)) (hT : (G' x).SpanningTree T) :
    RemovingTrees.Main.Tree x.G (T.map (edgeEmbedding (nonLoops x.G))) := by
  refine ⟨(connected_iff x T).mpr hT.1,?_⟩
  intro e he hc
  obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp he
  rw [← Finset.map_erase] at hc
  exact hT.2 i hi ((connected_iff x _).mp hc)

lemma G'_edgeConnected (x : I) : (G' x.val).EdgeConnected x.val.k := by
  intro S hS hS'
  have h := x.property.2.2 S ⟨hS,hS'⟩
  rw [card_cut_univ] at h
  exact_mod_cast h

/-! Running time. -/

section
variable {R : ℕ}

lemma iProblem_good (x : I) : 2 ≤ (iProblem x).d+1 ∧ 1 ≤ (iProblem x).r ∧
    (iProblem x).G.EdgeConnected (iProblem x).r := by
  refine ⟨by rw [iProblem,makeProblem_n_q339];exact x.property.1,x.property.2.1,?_⟩
  exact makeProblem_connected_q339 _ _ _ (G'_edgeConnected x)

lemma runsPoly_iRun
    (htime : ∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
      IsPoly L (fun i => (problemCode (a i)).length) →
      (∀i, 2 ≤ (a i).d+1 ∧ 1 ≤ (a i).r ∧ (a i).G.EdgeConnected (a i).r) →
      RunsPoly L (treeProgram R) a) :
    RunsPoly (fun x : I => (iCode x).length) (iRun R) (fun x => x) := by
  unfold iRun
  apply RunsPoly.changeOutput_q339
  apply RunsPoly.then_poly_q339
  apply RunsPoly.then_poly_q339
  refine (RunsPoly.of_poly_q339 (select allIdx) _ (isPoly_self_q339 _)).both_q339 ?_
  have hp := RunsPoly.of_poly_q339 iPrepare (fun x : I => x) (isPoly_self_q339 _)
  exact hp.then_q339 (htime _ hp.output_q339 (fun i => iProblem_good i))

end

lemma ofFn_toFinset {m : ℕ} (A : Finset (Fin m)) (T : Finset (Fin A.card)) :
    (List.ofFn (fun i => edgeEmbedding A (edgeEmbedding T i))).toFinset =
      T.map (edgeEmbedding A) := by
  ext e
  simp only [List.mem_toFinset,List.mem_ofFn,Finset.mem_map]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨_,embedding_mem _ i,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    obtain ⟨i,rfl⟩ := embedding_surj _ hj
    exact ⟨i,rfl⟩

lemma realizedMachine_run {α : Type*} {ea : α → Word} {f : α → Word}
    (r : Realizes ea wordCode f) (x : α) :
    (realizedMachine r).run (ea x) (r.cost x) = ⟨none,CleanRoutine.io (f x)⟩ := by
  let P := {r.routine.program with input := 0,output := 0}
  have h : KS.W03.MachineCombinators.RunSpec P (CleanRoutine.io (ea x))
      (CleanRoutine.io (f x)) (r.cost x) := by
    intro bits hb
    exact (CurrentKS.program_ports_run_q339 r.routine.program 0 0 _ bits).trans
      (r.routine.spec x bits hb)
  have ht := ArchivedMachine.runSpec_transfer_q339 P _ _ _ h
  change ((ArchivedMachine.machine P.toMachine).step^[r.cost x])
    ((ArchivedMachine.machine P.toMachine).init (ea x))=_
  have hi : (ArchivedMachine.machine P.toMachine).init (ea x) =
      ⟨some P.initial,CleanRoutine.io (ea x)⟩ := by
    apply congrArg (CurrentKS.Config.mk (some P.initial))
    refine funext (fun (j : Fin (r.routine.scratch+1)) => ?_)
    change (if j=(0 : Fin (r.routine.scratch+1)) then ea x else [])=
      (if j.val=0 then ea x else [])
    simp only [Fin.ext_iff,Fin.val_zero]
  rw [hi]
  exact ht

lemma iOutput_good (R : ℕ) (C : ℝ)
    (hcorrect : ∀p : Problem, 2 ≤ p.d+1 → 1 ≤ p.r → p.G.EdgeConnected p.r →
      ThinTree C p.r p.G (Iteration.tree R p.r p.G)) (x : I) :
    RemovingTrees.Main.TreeOutput x.val.G (fun T => ∀ S, RemovingTrees.Main.NontrivialShore S →
             ((RemovingTrees.Main.cut x.val.G T S).card : ℝ) ≤
               C / x.val.k * (RemovingTrees.Main.cut x.val.G Finset.univ S).card) (iOutput R x) := by
  obtain ⟨hn,hk,hc⟩ := iProblem_good x
  have hT := makeProblem_thin_q339 (G' x.val) (by have := x.property.1;omega) x.val.k
    (hcorrect (iProblem x) hn hk hc)
  obtain ⟨T,hT,hes⟩ : ∃ T : Finset (Fin (nonLoops x.val.G).card),
      ThinTree C x.val.k (G' x.val) T ∧
      (iEdges R x).toFinset = T.map (edgeEmbedding (nonLoops x.val.G)) :=
    ⟨Iteration.tree R (iProblem x).r (iProblem x).G,hT,
      ofFn_toFinset (nonLoops x.val.G) (Iteration.tree R (iProblem x).r (iProblem x).G)⟩
  refine ⟨iEdges R x,?_,rfl,?_,?_⟩
  · exact List.nodup_ofFn.mpr
      (fun i j h => (edgeEmbedding _).injective ((edgeEmbedding _).injective h))
  · rw [hes]
    exact tree_lift x.val _ hT.1
  · rw [hes]
    intro S hS
    rw [card_cut_map,card_cut_univ]
    exact hT.2 S hS.1 hS.2

theorem wrapper (R : ℕ) (C : ℝ) (hC : 0 < C)
    (hcorrect : ∀p : OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Problem,
      2 ≤ p.d+1 → 1 ≤ p.r → p.G.EdgeConnected p.r →
      OAI.AlgorithmicThinTrees.ThinTree C p.r p.G (OAI.AlgorithmicThinTrees.Iteration.tree R p.r p.G))
    (htime : ∀{ι : Type} {L : ι → ℕ} (a : ι → OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Problem),
      OAI.CurrentKS.Realization.IsPoly L
        (fun i => (OAI.AlgorithmicThinTrees.GraphicHalf.Stack.problemCode (a i)).length) →
      (∀i, 2 ≤ (a i).d+1 ∧ 1 ≤ (a i).r ∧ (a i).G.EdgeConnected (a i).r) →
      OAI.CurrentKS.Realization.RunsPoly L (OAI.AlgorithmicThinTrees.Iteration.Stack.treeProgram R) a) :
    ∃ M : OAI.CurrentKS.Machine, ∃ a d : ℕ, 0 < a ∧
      ∀ (n m k : ℕ) (G : RemovingTrees.Main.MultiGraph n m), 2 ≤ n → 0 < k →
        RemovingTrees.Main.CutLower G Finset.univ k →
        RemovingTrees.Main.BitResult M a d
          (RemovingTrees.Main.encNat k ++ RemovingTrees.Main.encGraph G)
          (RemovingTrees.Main.TreeOutput G (fun T => ∀ S, RemovingTrees.Main.NontrivialShore S →
             ((RemovingTrees.Main.cut G T S).card : ℝ) ≤
               C / k * (RemovingTrees.Main.cut G Finset.univ S).card)) := by
  have ht := runsPoly_iRun htime
  obtain ⟨p,hp⟩ := ht.cost
  refine ⟨realizedMachine (iRun R),p.coefficient+1,p.degree,Nat.succ_pos _,?_⟩
  intro n m k G hn hk hcut
  let x : I := ⟨⟨n,m,k,G⟩,hn,hk,hcut⟩
  have hrun := realizedMachine_run (iRun R) x
  have hbound : (iRun R).cost x ≤ (p.coefficient+1)*((iCode x).length+1)^p.degree :=
    ((hp x).trans (p.eval_le_input_polynomial _)).trans
      (Nat.mul_le_mul_right _ (Nat.le_succ p.coefficient))
  have hstate : ((realizedMachine (iRun R)).run (iCode x) ((iRun R).cost x)).state = none := by
    rw [hrun]
  have he := CurrentKS.Machine.run_halted_q339 hstate hbound
  have hin : RemovingTrees.Main.encNat k ++ RemovingTrees.Main.encGraph G = iCode x := rfl
  simp only [RemovingTrees.Main.BitResult]
  rw [hin,he,hrun]
  exact ⟨rfl,iOutput_good R C hcorrect x⟩

end Q339.Wrapper

set_option autoImplicit false

namespace Q339.Final
open RemovingTrees.Main

/-- 80/(2^(1/16)-1) ≤ 1900 (e.g. from 1.0421^16 ≤ 2). -/
theorem lossB_le : OAI.AlgorithmicThinTrees.Iteration.lossB ≤ 1900 := by
  unfold OAI.AlgorithmicThinTrees.Iteration.lossB
  have h16 : (1.0422:ℝ) ^ (16:ℕ) ≤ 2 := by norm_num
  have hb : (1.0422:ℝ) ≤ (2:ℝ) ^ (1/16:ℝ) := by
    have h1 : ((1.0422:ℝ) ^ (16:ℕ)) ^ (1/16:ℝ) ≤ (2:ℝ) ^ (1/16:ℝ) :=
      Real.rpow_le_rpow (by positivity) h16 (by norm_num)
    have h2 : ((1.0422:ℝ) ^ (16:ℕ)) ^ (1/16:ℝ) = 1.0422 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have hpos : (0:ℝ) < (2:ℝ) ^ (1/16:ℝ) - 1 := by linarith
  rw [div_le_iff₀ hpos]
  linarith

/-- the constant we will feed in -/
theorem const_le : 3 * (2:ℝ)^2048 * Real.exp OAI.AlgorithmicThinTrees.Iteration.lossB
    ≤ Real.exp 3400 := by
  have h3 : (3:ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2:ℝ); linarith
  have hlog : Real.log 2 < 0.6932 := Real.log_two_lt_d9.trans (by norm_num)
  have h2 : (2:ℝ)^2048 ≤ Real.exp 1420 := by
    have he : (2:ℝ)^2048 = Real.exp (2048 * Real.log 2) := by
      rw [show (2048:ℝ) * Real.log 2 = ((2048:ℕ):ℝ) * Real.log 2 by norm_num,
        ← Real.log_pow, Real.exp_log (by positivity)]
    rw [he]; exact Real.exp_le_exp.2 (by linarith)
  have hB := lossB_le
  have hE : Real.exp OAI.AlgorithmicThinTrees.Iteration.lossB ≤ Real.exp 1900 :=
    Real.exp_le_exp.2 hB
  calc 3 * (2:ℝ)^2048 * Real.exp OAI.AlgorithmicThinTrees.Iteration.lossB
      ≤ Real.exp 2 * Real.exp 1420 * Real.exp 1900 := by
        gcongr
    _ = Real.exp 3322 := by rw [← Real.exp_add, ← Real.exp_add]; norm_num
    _ ≤ Real.exp 3400 := Real.exp_le_exp.2 (by norm_num)

lemma bitResult_mono {M : OAI.CurrentKS.Machine} {a d : ℕ} {i : Bits} {P Q : Bits → Prop}
    (h : ∀ b, P b → Q b) (hP : BitResult M a d i P) : BitResult M a d i Q :=
  ⟨hP.1, h _ hP.2⟩

lemma treeOutput_mono {n m : ℕ} {G : MultiGraph n m} {P Q : Finset (Fin m) → Prop}
    (h : ∀ T, P T → Q T) (b : Bits) (hP : TreeOutput G P b) : TreeOutput G Q b := by
  obtain ⟨es, h1, h2, h3, h4⟩ := hP
  exact ⟨es, h1, h2, h3, h _ h4⟩

lemma card_cut_le {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m)) (S : Finset (Fin n)) :
    ((cut G Finset.univ S).card : ℝ) ≤
      ((cut G (Finset.univ \ T) S).card : ℝ) + ((cut G T S).card : ℝ) := by
  have hsub : cut G Finset.univ S ⊆ cut G (Finset.univ \ T) S ∪ cut G T S := by
    intro e he
    simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_sdiff] at he ⊢
    by_cases hT : e ∈ T
    · exact Or.inr ⟨hT, he⟩
    · exact Or.inl ⟨hT, he⟩
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  exact_mod_cast this

lemma lossConstant_ge : (89:ℝ) ≤ lossConstant := by
  unfold lossConstant
  have := Real.sqrt_nonneg (20 * Real.log 44)
  linarith

/-- The arithmetic core. -/
lemma core (C A : ℝ) (hC : 0 < C) (hCle : C ≤ Real.exp 3400) (hA : 89 ≤ A)
    (k : ℕ) (hk : 0 < k) (c t r : ℝ) (hc : (k:ℝ) ≤ c) (ht : t ≤ C / k * c)
    (hr : c ≤ r + t) (hr0 : 0 ≤ r) :
    (k:ℝ) - A * k / lossScale k ≤ r := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have hs1 : 1 ≤ lossScale k := by
    unfold lossScale
    have := Real.sqrt_le_sqrt (le_max_left (1:ℝ) (Real.log k))
    rwa [Real.sqrt_one] at this
  have hspos : 0 < lossScale k := by linarith
  by_cases hsA : lossScale k ≤ A
  · have : (k:ℝ) ≤ A * k / lossScale k := by
      rw [le_div_iff₀ hspos]; nlinarith
    linarith
  · replace hsA : A < lossScale k := lt_of_not_ge hsA
    set L := Real.log (k:ℝ) with hL
    have hkL : Real.exp L = k := Real.exp_log hkpos
    have hmax : 7921 < max 1 L := by
      have h89 : (89:ℝ) < Real.sqrt (max 1 L) := by
        have : lossScale k = Real.sqrt (max 1 L) := rfl
        linarith
      have h89' : Real.sqrt 7921 < Real.sqrt (max 1 L) := by
        rw [show (7921:ℝ) = 89^2 by norm_num, Real.sqrt_sq (by norm_num)]; exact h89
      exact (Real.sqrt_lt_sqrt_iff (by norm_num)).1 h89'
    have hL7 : 7921 < L := by
      rcases le_total 1 L with h | h
      · rwa [max_eq_right h] at hmax
      · rw [max_eq_left h] at hmax; norm_num at hmax
    have hmaxL : max 1 L = L := max_eq_right (by linarith)
    have hsL : lossScale k ≤ L := by
      have : lossScale k = Real.sqrt L := by
        show Real.sqrt (max 1 L) = _; rw [hmaxL]
      rw [this, Real.sqrt_le_left (by linarith)]
      nlinarith
    -- L ≤ exp (L/2)
    have hLexp : L ≤ Real.exp (L / 2) := by
      have h4 := Real.add_one_le_exp (L / 4)
      have hsq : Real.exp (L / 2) = Real.exp (L / 4) ^ 2 := by
        rw [sq, ← Real.exp_add]; ring_nf
      rw [hsq]
      have : L ≤ (L / 4) ^ 2 := by nlinarith
      nlinarith
    have h3400 : Real.exp 3400 ≤ Real.exp (L / 2) := Real.exp_le_exp.2 (by linarith)
    have hprod : Real.exp 3400 * L ≤ (k:ℝ) := by
      rw [← hkL]
      have : Real.exp L = Real.exp (L / 2) * Real.exp (L / 2) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      have : 0 ≤ L := by linarith
      exact mul_le_mul h3400 hLexp this (Real.exp_pos _).le
    have hCk : C ≤ (k:ℝ) := by
      have : Real.exp 3400 ≤ Real.exp 3400 * L := le_mul_of_one_le_right (Real.exp_pos _).le
        (by linarith)
      linarith
    -- c - t ≥ k - C
    have hct : (k:ℝ) - C ≤ c - t := by
      have hfrac : C / k ≤ 1 := (div_le_one hkpos).2 hCk
      have h1 : C / k * c ≤ C / k * c := le_rfl
      have hck : C / k * (k:ℝ) = C := by field_simp
      have : C / k * c - C / k * k ≤ c - k := by
        have : C / k * (c - k) ≤ 1 * (c - k) :=
          mul_le_mul_of_nonneg_right hfrac (by linarith)
        nlinarith
      linarith
    -- C ≤ A k / s
    have hCs : C ≤ A * k / lossScale k := by
      rw [le_div_iff₀ hspos]
      have h1 : C * lossScale k ≤ Real.exp 3400 * L :=
        mul_le_mul hCle hsL hspos.le (Real.exp_pos _).le
      have h2 : (k:ℝ) ≤ A * k := le_mul_of_one_le_left hkpos.le (by linarith)
      linarith
    linarith

theorem final (C : ℝ) (hC : 0 < C) (hCle : C ≤ Real.exp 3400)
    (hwrap : ∃ M : OAI.CurrentKS.Machine, ∃ a d : ℕ, 0 < a ∧
      ∀ (n m k : ℕ) (G : MultiGraph n m), 2 ≤ n → 0 < k → CutLower G Finset.univ k →
        BitResult M a d (encNat k ++ encGraph G)
          (TreeOutput G (fun T => ∀ S, NontrivialShore S →
             ((cut G T S).card : ℝ) ≤ C / k * (cut G Finset.univ S).card))) :
    ∃ A : ℝ, 0 < A ∧ A = lossConstant ∧
    ∃ M : OAI.CurrentKS.Machine, ∃ a d : ℕ, 0 < a ∧
    ∀ (n m k : ℕ) (G : MultiGraph n m),
      2 ≤ n → 0 < k → CutLower G Finset.univ k →
      BitResult M a d (encNat k ++ encGraph G)
        (TreeOutput G (fun T => CutLower G (Finset.univ \ T)
          ((k:ℝ) - A*k/lossScale k))) := by
  obtain ⟨M, a, d, ha, hM⟩ := hwrap
  have hA := lossConstant_ge
  refine ⟨lossConstant, by linarith, rfl, M, a, d, ha, ?_⟩
  intro n m k G hn hk hcut
  refine bitResult_mono (treeOutput_mono ?_) (hM n m k G hn hk hcut)
  intro T hT S hS
  exact core C lossConstant hC hCle hA k hk _ _ _ (hcut S hS) (hT S hS)
    (card_cut_le G T S) (by positivity)

end Q339.Final

namespace RemovingTrees.Main

theorem chk_tree_removal_polytime :
    ∃ A : ℝ, 0 < A ∧ A = lossConstant ∧
    ∃ M : OAI.CurrentKS.Machine, ∃ a d : ℕ, 0 < a ∧
    ∀ (n m k : ℕ) (G : MultiGraph n m),
      2 ≤ n → 0 < k → CutLower G Finset.univ k →
      BitResult M a d (encNat k ++ encGraph G)
        (TreeOutput G (fun T => CutLower G (Finset.univ \ T)
          ((k:ℝ) - A*k/lossScale k))) := by
  have hE := OAI.AlgorithmicThinTrees.Iteration.explicit_program_q339
  have hC : (3*(((2^2048:ℕ)):ℝ)*Real.exp OAI.AlgorithmicThinTrees.Iteration.lossB) =
      3*(2:ℝ)^2048*Real.exp OAI.AlgorithmicThinTrees.Iteration.lossB := by push_cast; ring
  exact Q339.Final.final _ (by positivity) (hC ▸ Q339.Final.const_le)
    (Q339.Wrapper.wrapper (2^2048) _ (by positivity) hE.1 hE.2)

end RemovingTrees.Main

theorem solution : type_of% @RemovingTrees.Main.chk_tree_removal_polytime := @RemovingTrees.Main.chk_tree_removal_polytime
