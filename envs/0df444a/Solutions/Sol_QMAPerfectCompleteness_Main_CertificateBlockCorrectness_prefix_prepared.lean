-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CertificateBlockCorrectness.prefix_prepared
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:52:24.741115+00:00
-- url     : https://prove2.me/submissions/2e1ad78a-dc07-4f6e-8995-32be81d2620a

/- Generated from Solutions.CertificatePreparedBlock by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockClockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockImplements
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockProgramPlacement
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockTaggedActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCompilerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateOldPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePostCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateQuantumTransports
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateStageActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Theorems.Thm_QMAPerfectCompleteness_Main_CertificatePreparation_logical_eq_of_data
import Theorems.Thm_QMAPerfectCompleteness_Main_CertificatePreparation_prefix_fiber
import Theorems.Thm_QMAPerfectCompleteness_Main_ThresholdPreparation_Layout_values

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers
namespace QMAPerfectCompleteness.Main.CertificateClaimBits
end QMAPerfectCompleteness.Main.CertificateClaimBits

/- Inline helpers retained from Solutions.BooleanFraming. -/
section


/-! Inverses and frame rules for the concrete Boolean straight-line compiler. -/
namespace QMAPerfectCompleteness.Main.BooleanCircuits





lemma evalCommand_outside {n : ℕ} (c : Command n) (x : Basis n) (w : Fin n)
    (hw : w ≠ c.target) : evalCommand c x w = x w := by
  cases c <;> exact Function.update_of_ne hw _ _

lemma eval_outside {n : ℕ} (p : List (Command n)) (x : Basis n) (w : Fin n)
    (hw : ∀ c ∈ p, w ≠ c.target) : eval p x w = x w := by
  induction p generalizing x with
  | nil => rfl
  | cons c p ih =>
    change eval p (evalCommand c x) w = _
    rw [ih _ (fun d hd => hw d (List.mem_cons_of_mem c hd)),
      evalCommand_outside c x w (hw c (List.mem_cons_self))]

lemma evalCommand_involutive {n : ℕ} (c : Command n) : Function.Involutive (evalCommand c) := by
  intro x
  funext w
  cases c with
  | flip t =>
    by_cases h : w=t
    · subst w; simp [evalCommand]
    · simp [evalCommand,Function.update_of_ne h]
  | copy a t hat =>
    by_cases h : w=t
    · subst w; simp [evalCommand,Function.update_of_ne hat]
    · simp [evalCommand,Function.update_of_ne h]
  | conj a b t hat hbt =>
    by_cases h : w=t
    · subst w; simp [evalCommand,Function.update_of_ne hat,Function.update_of_ne hbt]
    · simp [evalCommand,Function.update_of_ne h]

lemma eval_append' {n : ℕ} (p q : List (Command n)) (x : Basis n) :
    eval (p++q) x = eval q (eval p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons c p ih => exact ih _

/-- Reversal uncomputes the exact classical state, rather than only a measured observable. -/
theorem eval_reverse_left {n : ℕ} (p : List (Command n)) (x : Basis n) :
    eval p.reverse (eval p x) = x := by
  induction p generalizing x with
  | nil => rfl
  | cons c p ih =>
    rw [List.reverse_cons,eval_append']
    change evalCommand c (eval p.reverse (eval p (evalCommand c x))) = x
    rw [ih,evalCommand_involutive]



lemma evalCommand_agrees {n : ℕ} (S : Set (Fin n)) (c : Command n) (hc : c.Within S)
    (x y : Basis n) (h : ∀ w ∈ S, x w = y w) :
    ∀ w ∈ S, evalCommand c x w = evalCommand c y w := by
  intro w hw
  cases c with
  | flip t =>
    by_cases ht : w=t
    · subst w; simp only [evalCommand,Function.update_self]; rw [h t hc]
    · simpa only [evalCommand,Function.update_of_ne ht] using h w hw
  | copy a t hat =>
    obtain ⟨ha,ht⟩ := hc
    by_cases hwt : w=t
    · subst w; simp only [evalCommand,Function.update_self]; rw [h t ht,h a ha]
    · simpa only [evalCommand,Function.update_of_ne hwt] using h w hw
  | conj a b t hat hbt =>
    obtain ⟨ha,hb,ht⟩ := hc
    by_cases hwt : w=t
    · subst w; simp only [evalCommand,Function.update_self]; rw [h t ht,h a ha,h b hb]
    · simpa only [evalCommand,Function.update_of_ne hwt] using h w hw

/-- A program reads only its declared frame. Unrelated output wires may change between the
forward compute phase and its reverse, while all scratch is still correctly uncomputed. -/
theorem eval_agrees {n : ℕ} (S : Set (Fin n)) (p : List (Command n))
    (hp : ∀ c ∈ p, c.Within S) (x y : Basis n) (h : ∀ w ∈ S, x w = y w) :
    ∀ w ∈ S, eval p x w = eval p y w := by
  induction p generalizing x y with
  | nil => exact h
  | cons c p ih =>
    exact ih (fun d hd => hp d (List.mem_cons_of_mem c hd)) _ _
      (evalCommand_agrees S c (hp c List.mem_cons_self) x y h)

end QMAPerfectCompleteness.Main.BooleanCircuits

end

/- Inline helpers retained from Solutions.VariableAddition. -/
section


/-! Literal variable-register addition using a ripple carry, copied sums, and uncomputation. -/
open Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace QMAPerfectCompleteness.Main.VariableAddition
open BooleanCircuits ComparisonCircuits ClockCircuits











lemma eval_append {n : ℕ} (p q : List (Command n)) (x : Basis n) :
    eval (p++q) x = eval q (eval p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons a p ih => exact ih _



namespace Layout
variable {r n : ℕ} (L : Layout r n)



















@[simp] lemma step_zero (j : Fin r) : L.step j 0 = L.left j := rfl
@[simp] lemma step_one (j : Fin r) : L.step j 1 = L.right j := rfl
@[simp] lemma step_two (j : Fin r) : L.step j 2 = L.carry j.castSucc := rfl
@[simp] lemma step_three (j : Fin r) : L.step j 3 = L.carry j.succ := rfl
@[simp] lemma step_four (j : Fin r) : L.step j 4 = L.temp := rfl



































lemma temp_ne_output (j : Fin r) : L.temp ≠ L.output j := by
  intro h
  have hv := congrArg Fin.val (L.slots.injective h)
  have hj := j.isLt
  change 4*r+1 = 3*r+1+j.val at hv
  omega















/-- Every command in the output-copy phase changes exactly an output wire. -/
lemma sumCommands_target (js : List (Fin r)) (c : Command n) (hc : c ∈ L.sumCommands js) :
    ∃ j ∈ js, c.target = L.output j := by
  obtain ⟨j,hj,hc⟩ := List.mem_flatMap.mp hc
  refine ⟨j,hj,?_⟩
  simp only [sumStep,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h|h|h <;> subst c <;> rfl



lemma carryCommands_within (j : Fin r) :
    ∀ c ∈ carryCommands (L.step j), c.Within L.inputFrame := by
  simp [carryCommands,Command.Within,step_zero,step_one,step_two,step_three,step_four,
    inputFrame,L.left_ne_output,L.right_ne_output,L.temp_ne_output,
    fun i k => (L.output_ne_carry k i).symm]

lemma carryPrefix_within (t : ℕ) (ht : t ≤ r) :
    ∀ c ∈ L.carryPrefix t ht, c.Within L.inputFrame := by
  induction t with
  | zero => simp [carryPrefix]
  | succ t ih =>
    intro c hc
    rcases List.mem_append.mp hc with hc|hc
    · exact ih (by omega) c hc
    · exact L.carryCommands_within _ c hc

lemma sumCommands_frame (js : List (Fin r)) (x : Basis n) (w : Fin n) (hw : w ∈ L.inputFrame) :
    eval (L.sumCommands js) x w = x w := by
  apply BooleanCircuits.eval_outside
  intro c hc
  obtain ⟨j,_,ht⟩ := L.sumCommands_target js c hc
  rw [ht]
  exact hw j









/-- Addition restores every nonoutput wire, including both inputs, carry chain, and temporary. -/
theorem commands_frame (x : Basis n) (w : Fin n) (hw : w ∈ L.inputFrame) :
    eval L.commands x w = x w := by
  let p := L.carryPrefix r le_rfl
  let q := L.sumCommands (List.finRange r)
  have hp : ∀ c ∈ p.reverse, c.Within L.inputFrame := by
    intro c hc
    exact L.carryPrefix_within r le_rfl c (List.mem_reverse.mp hc)
  have hag := BooleanCircuits.eval_agrees L.inputFrame p.reverse hp
    (eval q (eval p x)) (eval p x)
    (fun v hv => L.sumCommands_frame _ _ v hv)
  change eval (p++q++p.reverse) x w = x w
  rw [eval_append,eval_append]
  rw [hag w hw,eval_reverse_left]











end Layout
end QMAPerfectCompleteness.Main.VariableAddition

end

/- Inline helpers retained from Solutions.BlockCoordinates. -/
section


/-! Exact basis coordinates for the published block register, including clean workspace. -/
open Matrix
namespace QMAPerfectCompleteness.Main.BlockCoordinates
open BlockCircuit IndexHadamards































theorem coordinates_fst (V : Verifier gatesG2) (w : ℕ) (x : Basis (bodyWires V+w)) :
    (coordinates V w x).1 = decode x := by
  apply Prod.ext
  · apply Fin.ext
    change ComparisonCircuits.littleValue (x ∘ indexWire) =
      ComparisonCircuits.littleValue (x ∘ indexWire) % 2^indexQubits V
    exact (Nat.mod_eq_of_lt (ComparisonCircuits.littleValue_lt_two_pow _)).symm
  · apply Prod.ext
    · apply Fin.ext
      change ComparisonCircuits.littleValue (x ∘ clockWire) =
        bitsValue x clockWire % (ell V.proofQubits+1)
      rw [clock_card]
      exact (Nat.mod_eq_of_lt (ComparisonCircuits.littleValue_lt_two_pow (x ∘ clockWire))).symm
    · rfl



















end QMAPerfectCompleteness.Main.BlockCoordinates

end

/- Inline helpers retained from Solutions.CertificateCoordinates. -/
section


/-! Concrete qubit coordinates for a coherent binary certificate and its history proof. -/
namespace QMAPerfectCompleteness.Main.CertificateCoordinates
open BlockCircuit BlockCoordinates IndexHadamards CertificateMixture














@[simp] theorem computationEquiv_body (V : Verifier gatesG2) (w : ℕ)
    (x : Basis ((bodyWires V+w)+claimQubits V)) :
    (computationEquiv V w x).1.1 = decode (fun i => x (Fin.castAdd (claimQubits V) i)) :=
  coordinates_fst V w _





end QMAPerfectCompleteness.Main.CertificateCoordinates

end

/- Inline helpers retained from Solutions.BlockImplements. -/
section


/-! Exact realization of the literal paper compiler on the published wire layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockImplements
open BlockCompiler BlockCoordinates BlockClockCoordinates ReversibleGadgets















variable (V : Verifier gatesG2)








lemma indexValue_eq_decode (x : Physical V) : (D V).indexValue x = (BlockCircuit.decode x).1.val := by
  change (D V).indexValue x = (D V).indexValue x % 2^indexQubits V
  exact (Nat.mod_eq_of_lt (ComparisonCircuits.littleValue_lt_two_pow (x ∘ (D V).indexWire))).symm





























end QMAPerfectCompleteness.Main.BlockImplements

end

/- Inline helpers retained from Solutions.DynamicBlockCompiler. -/
section


/-! Dynamic range predicates for a coherent certificate, using three linear reversible comparators. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace QMAPerfectCompleteness.Main.DynamicBlockCompiler
open BlockCompiler BooleanCircuits ReversibleGadgets VariableComparison ComparisonCircuits



namespace RangeLayout
variable {n r : ℕ} (L : RangeLayout n r)




















































/-- Numeric wiring contracts identify this dynamic truth table with the fixed paper table. -/
theorem truth_eq_fixed (x : Basis n) (a b j : ℕ)
    (hl : ∀ i, littleValue (x ∘ leftWire (L.comparators i)) = j)
    (hr : ∀ i, littleValue (x ∘ rightWire (L.comparators i)) = (![a,3*a,3*a+b] : Fin 3 → ℕ) i) :
    L.truth x = Layout.rangeTruth a b j := by
  funext i
  fin_cases i <;> simp [truth,bit,VariableEquality.comparisonBit,hl,hr,Layout.rangeTruth]











end RangeLayout


end QMAPerfectCompleteness.Main.DynamicBlockCompiler

end

/- Inline helpers retained from Solutions.DynamicRangeLayout. -/
section


/-! Disjoint source/scratch register constructors for the dynamic range comparator scaffold. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QMAPerfectCompleteness.Main.DynamicBlockCompiler
open VariableComparison





namespace RangeWires
variable {n r : ℕ} (W : RangeWires n r)



lemma comparator_left (t : Fin 3) (i : Fin r) : leftWire (W.comparator t) i = W.index i := by
  change Fin.append (Fin.append W.index (W.thresholds t)) W.scratch
    (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨i.val,by have := i.isLt; omega⟩) = _
  have he : (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨i.val,by have := i.isLt; omega⟩) =
      Fin.castAdd (r+2) (Fin.castAdd r i) := Fin.ext rfl
  rw [he,Fin.append_left,Fin.append_left]

lemma comparator_right (t : Fin 3) (i : Fin r) : rightWire (W.comparator t) i = W.thresholds t i := by
  change Fin.append (Fin.append W.index (W.thresholds t)) W.scratch
    (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨r+i.val,by have := i.isLt; omega⟩) = _
  have he : (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨r+i.val,by have := i.isLt; omega⟩) =
      Fin.castAdd (r+2) (Fin.natAdd r i) := Fin.ext rfl
  rw [he,Fin.append_left,Fin.append_right]

lemma comparator_carry (t : Fin 3) (i : Fin (r+1)) :
    carryWire (W.comparator t) i = W.scratch (Fin.castAdd 1 i) := by
  change Fin.append (Fin.append W.index (W.thresholds t)) W.scratch
    (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨2*r+i.val,by have := i.isLt; omega⟩) = _
  have he : (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨2*r+i.val,by have := i.isLt; omega⟩) =
      Fin.natAdd (r+r) (Fin.castAdd 1 i) := Fin.ext (by
        change 2*r+i.val = r+r+i.val
        omega)
  rw [he,Fin.append_right]

lemma comparator_temp (t : Fin 3) : tempWire (W.comparator t) = W.scratch (Fin.last (r+1)) := by
  change Fin.append (Fin.append W.index (W.thresholds t)) W.scratch
    (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨3*r+1,by omega⟩) = _
  have he : (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨3*r+1,by omega⟩) =
      Fin.natAdd (r+r) (Fin.last (r+1)) := Fin.ext (by simp; omega)
  rw [he,Fin.append_right]



lemma clean_of_scratch (x : Basis n) (hx : ∀ i, x (W.scratch i) = false) : W.toLayout.Clean x := by
  intro t
  constructor
  · intro i
    rw [show W.toLayout.comparators t = W.comparator t from rfl,W.comparator_carry]
    exact hx _
  · rw [show W.toLayout.comparators t = W.comparator t from rfl,W.comparator_temp]
    exact hx _



end RangeWires
end QMAPerfectCompleteness.Main.DynamicBlockCompiler

end

/- Inline helpers retained from Solutions.CertificateValidity. -/
section


/-! Exact polynomial-size certificate validity predicates for the coherent verifier. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateValidity
open BlockCompiler ReversibleGadgets ControlCircuits ComparisonCircuits VariableComparison











namespace Layout
variable {k n : ℕ} (L : Layout k n)































theorem action_outside_tags (x : Basis n) (w : Fin n) (hw : ∀ t, w ≠ L.tags t) :
    L.action x w = x w := by
  simp [action,program,CleanProgram.append,constProgram,flipProgram,varProgram,constAction,
    xAction,Function.comp_apply,Function.update_of_ne,hw]

















end Layout
end QMAPerfectCompleteness.Main.CertificateValidity

end

/- Inline helpers retained from Solutions.CertificateBlockCorrectness. -/
section


/-! Exact coherent block SELECT on the master certificate register layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout CertificateCoordinates BlockCoordinates BlockCompiler
open ReversibleGadgets BlockImplements
variable (V : Verifier gatesG2)










@[simp] lemma coords_embed (s : Key V → Basis (work V)) (p : Logical V) :
    coords V (embed V s p) = (p,s (key V p)) := (coords V).apply_symm_apply _







lemma old_decode (x : Physical V) : BlockCircuit.decode (old V x) = (coords V x).1.1 := by
  rw [computationEquiv_body]
  rfl











































end QMAPerfectCompleteness.Main.CertificateBlockCorrectness

end

/- Inline helpers retained from Solutions.CertificateRangeValues. -/
section


/-! Numeric source contracts for the actual coherent range comparator bank. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout BlockCompiler ComparisonCircuits ClockCircuits
variable (V : Verifier gatesG2)

/-- The two padded high index bits are zero, so k+2-bit comparison reads the same index. -/
lemma paddedIndex_value (x : Physical V) (hz : ∀ j, x (padding V j)=false) :
    littleValue (x ∘ paddedIndex V) = (BlockCircuit.decode (old V x)).1.val := by
  let j := (BlockCircuit.decode (old V x)).1
  have hv : littleValue ((old V x) ∘ (layoutOf V).indexWire) = j.val :=
    BlockImplements.indexValue_eq_decode V (old V x)
  have hb : x ∘ paddedIndex V = (fun i : Fin (r V) => j.val.testBit i.val) := by
    funext i
    by_cases hi : i.val<k V
    · have he : paddedIndex V i = oldEmbedding V ((layoutOf V).indexWire ⟨i.val,hi⟩) := by
        apply Fin.ext
        change (if i.val<k V then i.val else _) = i.val
        rw [if_pos hi]
      change x (paddedIndex V i) = _
      rw [he]
      have hh := littleValue_decode ((old V x) ∘ (layoutOf V).indexWire) ⟨i.val,hi⟩
      rw [hv] at hh
      exact hh.symm
    · have he : paddedIndex V i = padding V ⟨i.val-k V,by have := i.isLt; dsimp only [r,k] at *; omega⟩ := by
        apply Fin.ext
        change (if i.val<k V then _ else _) = _
        rw [if_neg hi]
        change BlockCircuit.bodyWires V+oldWork V+prepWork V+(i.val-k V) =
          BlockCircuit.bodyWires V+(oldWork V+prepWork V)+(i.val-k V)
        omega
      change x (paddedIndex V i) = _
      rw [he,hz]
      exact (Nat.testBit_lt_two_pow (j.isLt.trans_le
        (Nat.pow_le_pow_right (by decide : 0<2) (by omega : k V ≤ i.val)))).symm
  rw [hb,littleValue_testBit]
  exact Nat.mod_eq_of_lt (j.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (by dsimp only [r]; omega)))

lemma range_truth_of_values (x : Physical V) (hz : ∀ j, x (padding V j)=false)
    (ha : littleValue (fun j => x (prepWord V 0 j)) = ((coords V x).1.2).2.1.val)
    (h3a : littleValue (fun j => x (prepWord V 4 j)) = 3*((coords V x).1.2).2.1.val)
    (hup : littleValue (fun j => x (prepWord V 5 j)) =
      3*((coords V x).1.2).2.1.val+((coords V x).1.2).2.2.val) :
    (CertificateRangeCircuit.layout V).truth x =
      Layout.rangeTruth ((coords V x).1.2).2.1.val ((coords V x).1.2).2.2.val
        ((coords V x).1.1).1.val := by
  apply DynamicBlockCompiler.RangeLayout.truth_eq_fixed
  · intro i
    change littleValue (x ∘ VariableComparison.leftWire ((CertificateRangeCircuit.wires V).comparator i)) = _
    simp only [Function.comp_def,DynamicBlockCompiler.RangeWires.comparator_left]
    change littleValue (x ∘ paddedIndex V) = _
    rw [paddedIndex_value V x hz,old_decode]
  · intro i
    change littleValue (x ∘ VariableComparison.rightWire ((CertificateRangeCircuit.wires V).comparator i)) = _
    simp only [Function.comp_def,DynamicBlockCompiler.RangeWires.comparator_right]
    fin_cases i
    · exact ha
    · exact h3a
    · exact hup

end QMAPerfectCompleteness.Main.CertificateBlockCorrectness

end

/- Inline helpers retained from Solutions.RegisterCopies. -/
section


/-! Parallel classical register copies with distinct targets and unchanged source wires. -/
namespace QMAPerfectCompleteness.Main.RegisterCopies
open BooleanCircuits

variable {ι : Type*} [DecidableEq ι] {n : ℕ}
variable (source : ι → Fin n) (target : ι ↪ Fin n)
variable (hd : ∀ i j, source i ≠ target j)





lemma commands_target (js : List ι) (c : Command n) (hc : c ∈ commands source target hd js) :
    ∃ j ∈ js, c.target = target j := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
  exact ⟨j,hj,rfl⟩

theorem eval_outside (js : List ι) (x : Basis n) (w : Fin n)
    (hw : ∀ j ∈ js, w ≠ target j) : eval (commands source target hd js) x w = x w := by
  apply BooleanCircuits.eval_outside
  intro c hc
  obtain ⟨j,hj,ht⟩ := commands_target source target hd js c hc
  rw [ht]
  exact hw j hj







end QMAPerfectCompleteness.Main.RegisterCopies

end

/- Inline helpers retained from Solutions.ThresholdPreparation. -/
section


/-! Certificate-dependent binary threshold preparation. Arithmetic registers are explicit
physical wires; their values may be retained as certificate-dependent ancillary garbage. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.ThresholdPreparation
open BooleanCircuits ComparisonCircuits





namespace Layout
variable {k n : ℕ} (L : Layout k n)





























theorem copies_outside (x : Basis n) (w : Fin n) (hw : ∀ i, w ≠ L.target i) :
    L.copyState x w = x w :=
  RegisterCopies.eval_outside L.source L.targetEmbedding L.source_ne_target _ x w (fun i _ => hw i)
































lemma three_outside (x : Basis n) (w : Fin n) (hw : ∀ j, w ≠ L.wire (.word 4 j)) :
    eval L.three.commands x w = x w := by
  apply L.three.commands_frame
  intro j
  rw [L.three_output]
  exact hw j

lemma upper_outside (x : Basis n) (w : Fin n) (hw : ∀ j, w ≠ L.wire (.word 5 j)) :
    eval L.upper.commands x w = x w := by
  apply L.upper.commands_frame
  intro j
  rw [L.upper_output]
  exact hw j













lemma state_eq (x : Basis n) : L.state x =
    eval L.upper.commands (eval L.three.commands (L.copyState x)) := by
  rw [state,commands,VariableAddition.eval_append,VariableAddition.eval_append]
  rfl

/-- Every wire outside the six threshold words is restored, including the certificate and
shared arithmetic scratch. This also frames arbitrary quantum body registers. -/
theorem state_outside (x : Basis n) (w : Fin n) (hw : ∀ d j, w ≠ L.wire (.word d j)) :
    L.state x w = x w := by
  rw [state_eq,L.upper_outside _ _ (hw 5),L.three_outside _ _ (hw 4)]
  apply L.copies_outside
  intro i
  exact hw _ _















end Layout
end QMAPerfectCompleteness.Main.ThresholdPreparation

end

/- Inline helpers retained from Solutions.CertificateThresholdLayout. -/
section


/-! The actual master-layout placement of the coherent binary threshold preparation. -/
namespace QMAPerfectCompleteness.Main.CertificateMasterLayout
open ThresholdPreparation










@[simp] theorem thresholdWire_word (V : Verifier gatesG2) (s : Fin 6) (j : Fin (r V)) :
    thresholdWire V (.word s j) = prepWord V s j := rfl
@[simp] theorem thresholdWire_carry (V : Verifier gatesG2) (j : Fin (k V+3)) :
    thresholdWire V (.carry j) = prepCarry V j := rfl
@[simp] theorem thresholdWire_temp (V : Verifier gatesG2) : thresholdWire V .temp = prepTemp V := rfl

end QMAPerfectCompleteness.Main.CertificateMasterLayout

end

/- Inline helpers retained from Solutions.CertificatePreparation. -/
section


/-! Actual threshold preparation on the physical coherent verifier, with a certificate-only
workspace fiber. The arithmetic garbage may be retained throughout the quantum block. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.CertificatePreparation
open BlockCircuit BlockCoordinates CertificateCoordinates CertificateMasterLayout ThresholdPreparation
open ComparisonCircuits
variable (V : Verifier gatesG2)






@[simp] theorem coords_raw (p : Logical V) : coords V (rawEncoding V p) = (p,fun _=>false) :=
  (coords V).apply_symm_apply _





lemma raw_work (p : Logical V) (i : Fin (work V)) : rawEncoding V p (workWire V i)=false := by
  have h := congrFun (congrArg Prod.snd (coords_raw V p)) i
  exact h

lemma raw_at_work (p : Logical V) (w : Fin (total V))
    (hw0 : bodyWires V ≤ w.val) (hw1 : w.val < bodyWires V+work V) : rawEncoding V p w=false := by
  let i : Fin (work V) := ⟨w.val-bodyWires V,by omega⟩
  have he : workWire V i=w := Fin.ext (by change bodyWires V+(w.val-bodyWires V)=w.val; omega)
  rw [← he,raw_work]




@[simp] lemma thresholdLayout_wire : (thresholdLayout V).wire = thresholdWire V := rfl




lemma word_work (d : Fin 6) (j : Fin (r V)) :
    bodyWires V ≤ (prepWord V d j).val ∧ (prepWord V d j).val < bodyWires V+work V := by
  have h := CertificateRangeCircuit.word_bounds V d j
  have hm : oldWork V+6*r V ≤ work V := by dsimp only [work,prepWork,r,k]; omega
  dsimp only [r,k] at h hm ⊢
  omega

lemma carry_work (j : Fin (k V+3)) :
    bodyWires V ≤ (prepCarry V j).val ∧ (prepCarry V j).val < bodyWires V+work V := by
  have hj := j.isLt
  change bodyWires V ≤ bodyWires V+(oldWork V+6*r V)+j.val ∧ _
  change _ ∧ bodyWires V+(oldWork V+6*r V)+j.val < bodyWires V+work V
  dsimp [work,prepWork,r,k] at *
  omega

lemma temp_work : bodyWires V ≤ (prepTemp V).val ∧ (prepTemp V).val < bodyWires V+work V := by
  change bodyWires V ≤ bodyWires V+(oldWork V+6*r V+(k V+3))+0 ∧ _
  change _ ∧ bodyWires V+(oldWork V+6*r V+(k V+3))+0 < bodyWires V+work V
  dsimp [work,prepWork,r,k]
  omega

lemma raw_clean (p : Logical V) : (thresholdLayout V).Clean (rawEncoding V p) := by
  refine ⟨?_,?_,?_⟩
  · intro d j
    rw [thresholdLayout_wire,thresholdWire_word]
    exact raw_at_work V p _ (word_work V d j).1 (word_work V d j).2
  · intro j
    rw [thresholdLayout_wire,thresholdWire_carry]
    exact raw_at_work V p _ (carry_work V j).1 (carry_work V j).2
  · rw [thresholdLayout_wire,thresholdWire_temp]
    exact raw_at_work V p _ (temp_work V).1 (temp_work V).2

lemma prep_at_work (p : Logical V) (w : Fin (total V))
    (hw0 : bodyWires V ≤ w.val) (hw1 : w.val < bodyWires V+work V)
    (hn : ∀ d j, w ≠ prepWord V d j) : prepState V (rawEncoding V p) w=false := by
  rw [prepState,ThresholdPreparation.Layout.state_outside]
  · exact raw_at_work V p w hw0 hw1
  · simpa only [thresholdLayout_wire,thresholdWire_word] using hn

lemma prep_data (x : Physical V) (w : Fin (total V))
    (hw : w.val<bodyWires V ∨ bodyWires V+work V ≤ w.val) : prepState V x w=x w := by
  apply (thresholdLayout V).state_outside
  intro d j h
  rw [thresholdLayout_wire,thresholdWire_word] at h
  have hh := congrArg Fin.val h
  have hb := word_work V d j
  omega










end QMAPerfectCompleteness.Main.CertificatePreparation

end

/- Inline helpers retained from Solutions.CertificateClaimBits. -/
section


/-! Physical certificate bits are the published little-endian z,a,b coordinates. -/
namespace QMAPerfectCompleteness.Main.CertificateClaimBits
open CertificateMasterLayout CertificateCoordinates BlockCircuit IndexHadamards
variable (V : Verifier gatesG2)

lemma certificate_zero (j : Fin (k V)) : certificate V 0 j =
    Fin.natAdd (bodyWires V+work V) (Fin.natAdd V.proofQubits (Fin.castAdd (k V) j)) := by
  apply Fin.ext
  simp [certificate,certAB,finProdFinEquiv,k,Nat.add_assoc]

lemma certificate_one (j : Fin (k V)) : certificate V 1 j =
    Fin.natAdd (bodyWires V+work V) (Fin.natAdd V.proofQubits (Fin.natAdd (k V) j)) := by
  apply Fin.ext
  simp [certificate,certAB,finProdFinEquiv,k,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- No modulus or truncation is hidden in the certificate's natural-number reading. -/
theorem a_value (x : Basis (total V)) :
    ComparisonCircuits.littleValue (fun j => x (certificate V 0 j)) =
      (computationEquiv V (work V) x).1.2.2.1.val := by
  simp_rw [certificate_zero]
  rfl

theorem b_value (x : Basis (total V)) :
    ComparisonCircuits.littleValue (fun j => x (certificate V 1 j)) =
      (computationEquiv V (work V) x).1.2.2.2.val := by
  simp_rw [certificate_one]
  rfl



end QMAPerfectCompleteness.Main.CertificateClaimBits

end

/- Inline helpers retained from Solutions.CertificateValidityPreparation. -/
section


/-! The actual arithmetic-plus-validity prefix and its certificate-dependent workspace fiber. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QMAPerfectCompleteness.Main.CertificatePreparation
open BlockCircuit BlockCoordinates CertificateCoordinates CertificateMasterLayout ThresholdPreparation
open ComparisonCircuits CertificateValidityCircuit
variable (V : Verifier gatesG2)



lemma validity_work (t : Fin 6) :
    bodyWires V ≤ (validity V t).val ∧ (validity V t).val < bodyWires V+work V := by
  have ht := t.isLt
  change bodyWires V ≤ bodyWires V+(oldWork V+prepWork V+2)+t.val ∧ _
  change _ ∧ bodyWires V+(oldWork V+prepWork V+2)+t.val < bodyWires V+work V
  dsimp only [work]
  omega

lemma data_ne_validity (w : Fin (total V))
    (hw : w.val<bodyWires V ∨ bodyWires V+work V ≤ w.val) (t : Fin 6) : w ≠ validity V t := by
  intro h
  have ht := validity_work V t
  have hv := congrArg Fin.val h
  omega



lemma prep_scratch (p : Logical V) (j : Fin (r V+2)) :
    prepState V (rawEncoding V p) (CertificateRangeCircuit.scratch V j)=false := by
  have hs := CertificateRangeCircuit.scratch_bounds V j
  have hm : oldWork V+prepWork V ≤ work V := by dsimp only [work]; omega
  apply prep_at_work V p
  · omega
  · omega
  · intro d i h
    have hw := CertificateRangeCircuit.word_bounds V d i
    have hv := congrArg Fin.val h
    omega





lemma raw_a (p : Logical V) : (thresholdLayout V).value (rawEncoding V p) 0=p.2.2.1.val := by
  change ComparisonCircuits.littleValue (fun j => rawEncoding V p (certificate V 0 j)) = _
  rw [CertificateClaimBits.a_value,coords_raw]
lemma raw_b (p : Logical V) : (thresholdLayout V).value (rawEncoding V p) 1=p.2.2.2.val := by
  change ComparisonCircuits.littleValue (fun j => rawEncoding V p (certificate V 1 j)) = _
  rw [CertificateClaimBits.b_value,coords_raw]

lemma prep_values (p : Logical V) (d : Fin 6) :
    littleValue (fun j => prepState V (rawEncoding V p) (prepWord V d j)) =
      (![p.2.2.1.val,2*p.2.2.1.val,p.2.2.2.val,2*p.2.2.2.val,
        3*p.2.2.1.val,3*p.2.2.1.val+p.2.2.2.val] : Fin 6 → ℕ) d := by
  have h := (thresholdLayout V).values (rawEncoding V p) (raw_clean V p) d
  rw [raw_a,raw_b] at h
  simpa only [prepState,thresholdLayout_wire,thresholdWire_word] using h












lemma prefix_data (p : Logical V) (w : Fin (total V))
    (hw : w.val<bodyWires V ∨ bodyWires V+work V ≤ w.val) : prefixEncoding V p w=rawEncoding V p w := by
  rw [prefixEncoding,Function.update_of_ne (data_ne_validity V w hw 5)]
  rw [CertificateValidity.Layout.action_outside_tags]
  · exact prep_data V _ _ hw
  · intro t
    exact data_ne_validity V w hw ⟨t.val,by have := t.isLt; omega⟩

lemma prefix_logical (p : Logical V) : (coords V (prefixEncoding V p)).1=p := by
  rw [logical_eq_of_data V _ (rawEncoding V p) (prefix_data V p),coords_raw]











end QMAPerfectCompleteness.Main.CertificatePreparation

end

/- Inline helpers retained from Solutions.CertificatePreparedFacts. -/
section


/-! Concrete readiness facts for the quantum block and final readout after certificate prep. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.CertificatePreparation
open BlockCircuit BlockCoordinates CertificateCoordinates CertificateMasterLayout ThresholdPreparation
open ComparisonCircuits CertificateValidityCircuit
variable (V : Verifier gatesG2)

/-- Only threshold words and the six validity bits may be nonzero in prepared workspace. -/
theorem prefix_at_work (p : Logical V) (w : Fin (total V))
    (hw0 : bodyWires V ≤ w.val) (hw1 : w.val<bodyWires V+work V)
    (hn : ∀ d j, w ≠ prepWord V d j) (hv : ∀ t, w ≠ validity V t) :
    prefixEncoding V p w=false := by
  rw [prefixEncoding,Function.update_of_ne (hv 5),CertificateValidity.Layout.action_outside_tags]
  · exact prep_at_work V p w hw0 hw1 hn
  · intro t
    exact hv ⟨t.val,by have := t.isLt; omega⟩

theorem prefix_word (p : Logical V) (d : Fin 6) (j : Fin (r V)) :
    prefixEncoding V p (prepWord V d j) = prepState V (rawEncoding V p) (prepWord V d j) := by
  rw [prefixEncoding,Function.update_of_ne (validity_ne_word V 5 d j).symm,
    CertificateValidity.Layout.action_outside_tags]
  intro t
  exact (validity_ne_word V ⟨t.val,by have := t.isLt; omega⟩ d j).symm

theorem prefix_values (p : Logical V) (d : Fin 6) :
    littleValue (fun j => prefixEncoding V p (prepWord V d j)) =
      (![p.2.2.1.val,2*p.2.2.1.val,p.2.2.2.val,2*p.2.2.2.val,
        3*p.2.2.1.val,3*p.2.2.1.val+p.2.2.2.val] : Fin 6 → ℕ) d := by
  simp_rw [prefix_word]
  exact prep_values V p d



theorem prefix_scratch (p : Logical V) (j : Fin (r V+2)) :
    prefixEncoding V p (CertificateRangeCircuit.scratch V j)=false := by
  rw [prefixEncoding,Function.update_of_ne (validity_ne_scratch V 5 j).symm,
    CertificateValidity.Layout.action_outside_tags]
  · exact prep_scratch V p j
  · intro t
    exact (validity_ne_scratch V ⟨t.val,by have := t.isLt; omega⟩ j).symm







end QMAPerfectCompleteness.Main.CertificatePreparation

end



/-! The actual threshold/validity prefix satisfies all dynamic coherent block readiness conditions. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
end QMAPerfectCompleteness.Main.CertificateBlockCorrectness
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout BlockCompiler ComparisonCircuits
variable (V : Verifier gatesG2)

lemma QMAPerfectCompleteness.Main.CertificateBlockCorrectness.embed_prefix (p : Logical V) :
    embed V (certSpace V (CertificatePreparation.prefixWorkspace V)) p = CertificatePreparation.prefixEncoding V p := by
  apply (coords V).injective
  exact (coords_embed V _ p).trans (CertificatePreparation.prefix_fiber V p).symm

lemma QMAPerfectCompleteness.Main.CertificateBlockCorrectness.prefix_old_clean (p : Logical V) :
    BlockCircuit.WorkspaceClean (old V (CertificatePreparation.prefixEncoding V p)) := by
  intro i
  have hi : i.val < oldWork V := i.isLt
  have hm : oldWork V ≤ work V := by dsimp only [work]; omega
  apply CertificatePreparation.prefix_at_work V p (oldEmbedding V (BlockCircuit.workspaceWire i))
  · change BlockCircuit.bodyWires V ≤ BlockCircuit.bodyWires V+i.val
    omega
  · change BlockCircuit.bodyWires V+i.val < BlockCircuit.bodyWires V+work V
    omega
  · intro d j h
    have hw := (CertificateRangeCircuit.word_bounds V d j).1
    have hv := congrArg Fin.val h
    change BlockCircuit.bodyWires V+i.val = (prepWord V d j).val at hv
    omega
  · intro t h
    have ht := CertificateValidityCircuit.validity_bounds V t
    have hv := congrArg Fin.val h
    change BlockCircuit.bodyWires V+i.val = (validity V t).val at hv
    omega

lemma QMAPerfectCompleteness.Main.CertificateBlockCorrectness.prefix_padding (p : Logical V) (i : Fin 2) :
    CertificatePreparation.prefixEncoding V p (padding V i)=false := by
  have hi := i.isLt
  have hm : oldWork V+prepWork V+2 ≤ work V := by dsimp only [work]; omega
  have hw : 6*r V ≤ prepWork V := by dsimp only [prepWork,r]; omega
  apply CertificatePreparation.prefix_at_work V p (padding V i)
  · change BlockCircuit.bodyWires V ≤ BlockCircuit.bodyWires V+(oldWork V+prepWork V)+i.val
    omega
  · change BlockCircuit.bodyWires V+(oldWork V+prepWork V)+i.val < BlockCircuit.bodyWires V+work V
    omega
  · intro d j h
    have hh := (CertificateRangeCircuit.word_bounds V d j).2
    have hv := congrArg Fin.val h
    change BlockCircuit.bodyWires V+(oldWork V+prepWork V)+i.val = (prepWord V d j).val at hv
    omega
  · intro t h
    have ht := CertificateValidityCircuit.validity_bounds V t
    have hv := congrArg Fin.val h
    change BlockCircuit.bodyWires V+(oldWork V+prepWork V)+i.val = (validity V t).val at hv
    omega

/-- All prerequisites are discharged for the actual literal arithmetic/validity prefix. -/
theorem solution :
    Prepared V (certSpace V (CertificatePreparation.prefixWorkspace V)) := by
  constructor
  · intro p
    rw [embed_prefix]
    exact (CertificateRangeCircuit.wires V).clean_of_scratch _ (CertificatePreparation.prefix_scratch V p)
  · intro p
    rw [embed_prefix]
    exact prefix_old_clean V p
  · intro p
    rw [embed_prefix]
    have hc : (coords V (CertificatePreparation.prefixEncoding V p)).1 = p :=
      CertificatePreparation.prefix_logical V p
    have h := range_truth_of_values V (CertificatePreparation.prefixEncoding V p) (prefix_padding V p)
      (by simpa [hc] using CertificatePreparation.prefix_values V p 0)
      (by simpa [hc] using CertificatePreparation.prefix_values V p 4)
      (by simpa [hc] using CertificatePreparation.prefix_values V p 5)
    simpa only [hc] using h
