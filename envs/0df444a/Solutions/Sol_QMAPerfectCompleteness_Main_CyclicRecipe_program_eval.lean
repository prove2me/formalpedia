-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CyclicRecipe.program_eval
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:52:49.297811+00:00
-- url     : https://prove2.me/submissions/883d9fa7-b8ba-442f-bafa-74fbf76b173f

/- Generated from Solutions.CyclicRecipeRealization by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateEtaTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateInitialization
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterReadout
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRecipeRealization
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicVerifier
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCertificateGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawControlGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawThresholdGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeNormalization
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding
import Theorems.Thm_QMAPerfectCompleteness_Main_CircuitRecipe_Gadgets_eval_compareBits
import Theorems.Thm_QMAPerfectCompleteness_Main_CyclicRecipe_eval_copies

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
namespace QMAPerfectCompleteness.Main.CertificateReadoutEffect
end QMAPerfectCompleteness.Main.CertificateReadoutEffect
namespace QMAPerfectCompleteness.Main.CertificateVerifierEffect
end QMAPerfectCompleteness.Main.CertificateVerifierEffect

/- Inline helpers retained from Solutions.CircuitRecipe. -/
section


/-! Finite circuit-generator recipes. Loops range over unary widths; wire arithmetic is
explicit and preserves the dynamic structure of the paper's polynomial circuit constructions. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CircuitRecipe






namespace Expr







end Expr



namespace Recipe








theorem eval_reverse (p : Recipe) (env : Environment) (ctx : List ℕ)
    (src : List RawEncoding.Instruction) :
    p.reverse.eval env ctx src = (p.eval env ctx src).reverse := by
  induction p generalizing ctx with
  | nil => rfl
  | emit t w => simp [reverse,eval]
  | append a b ia ib => simp [reverse,eval,ia,ib]
  | forUp n b ih => simp [reverse,eval,List.reverse_flatMap,Function.comp_def,ih]
  | forDown n b ih => simp [reverse,eval,List.reverse_flatMap,Function.comp_def,ih]
  | ifLt a b y n iy inn => simp only [reverse,eval]; split_ifs <;> simp [iy,inn]
  | source r w => cases r <;> simp [reverse,eval,List.map_reverse]
  | mapWires w b ih => simp [reverse,eval,ih,List.map_reverse]

end Recipe





end QMAPerfectCompleteness.Main.CircuitRecipe

end

/- Inline helpers retained from Solutions.RecipeGadgets. -/
section


/-! Finite recipes realizing the linear reversible circuit templates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.CircuitRecipe

namespace Expr

@[simp] theorem eval_plug (e v : Expr) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (e.plug v).eval env ctx w=e.eval env ctx (v.eval env ctx w) := by
  induction e <;> simp_all [plug,eval]
end Expr

namespace Gadgets
open RawG2 RawEncoding




@[simp] theorem eval_hAppend (p q : Recipe) (env : Environment) (ctx : List ℕ) (src) :
    (p ++ q).eval env ctx src=p.eval env ctx src ++ q.eval env ctx src := rfl
@[simp] theorem eval_add (a b : Expr) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (a+b).eval env ctx w=a.eval env ctx w+b.eval env ctx w := rfl
@[simp] theorem eval_sub (a b : Expr) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (a-b).eval env ctx w=a.eval env ctx w-b.eval env ctx w := rfl
@[simp] theorem eval_nat (n : ℕ) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (OfNat.ofNat n : Expr).eval env ctx w=n := rfl





@[simp] theorem eval_x (a : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (x a).eval env ctx src=[RawG2.x (a.eval env ctx)] := rfl
@[simp] theorem eval_cn (a b : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (cn a b).eval env ctx src=[RawG2.cn (a.eval env ctx) (b.eval env ctx)] := rfl
@[simp] theorem eval_tof (a b c : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (tof a b c).eval env ctx src=[RawG2.tof (a.eval env ctx) (b.eval env ctx) (c.eval env ctx)] := rfl
@[simp] theorem eval_hh (a b : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (hh a b).eval env ctx src=[RawG2.hh (a.eval env ctx) (b.eval env ctx)] := rfl
@[simp] theorem eval_conj (a b c : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (conj a b c).eval env ctx src=[RawG2.compileCommand
      (.conj (a.eval env ctx) (b.eval env ctx) (c.eval env ctx))] := by
  simp only [conj,Recipe.eval,RawG2.compileCommand]
  split_ifs <;> simp_all [tof,cn,Recipe.eval,RawG2.tof,RawG2.cn] <;> omega

/-- Match the syntactic finite index enumeration with the loop counter enumeration. -/
theorem finRange_val (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp













@[simp] theorem eval_useUncompute (a b : Recipe) (env : Environment) (ctx : List ℕ) (src) :
    (useUncompute a b).eval env ctx src=
      RawG2.computeUseUncompute (a.eval env ctx src) (b.eval env ctx src) := by
  simp [useUncompute,RawG2.computeUseUncompute,Recipe.eval_reverse]

/-- The symbolic AND chain is the same literal gate list as the typed clean AND gadget. -/
theorem eval_andCompute (r control flags : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx))
    (hc : ∀ j, L.controls j=control.eval env ctx j.val)
    (hf : ∀ j, L.flags j=flags.eval env ctx j.val) :
    (andCompute r control flags).eval env ctx src=RawG2.andGates L := by
  simp only [andCompute,eval_hAppend,eval_x,Recipe.eval,eval_tof,
    Expr.eval_plug,Expr.eval_lift,eval_add,eval_nat,Expr.eval]
  unfold RawG2.andGates
  congr 1
  · exact congrArg (fun z=>[RawG2.x z]) (hf 0).symm
  · rw [←finRange_val,List.flatMap_map]
    rw [←List.map_eq_flatMap]
    apply List.map_congr_left
    intro j _
    simp only [hf,hc]
    rfl


theorem eval_multiX (r control flags target : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx))
    (hc : ∀j,L.controls j=control.eval env ctx j.val)
    (hf : ∀j,L.flags j=flags.eval env ctx j.val) :
    (multiX r control flags target).eval env ctx src=RawG2.multiControlledX L (target.eval env ctx) := by
  simp only [multiX,eval_useUncompute,eval_andCompute r control flags env ctx src L hc hf,
    eval_cn,Expr.eval_plug,RawG2.multiControlledX]
  rw [hf (Fin.last _)]
  rfl

theorem normalizePrefix_flatMap {r : ℕ} (L : RawG2.AndLayout r) (p : Fin r → Bool)
    (t : ℕ) (ht : t≤r) :
    RawG2.normalizePrefix L p t ht=(List.finRange t).flatMap fun j=>
      if p ⟨j.val,Nat.lt_of_lt_of_le j.isLt ht⟩ then []
      else [RawG2.x (L.controls ⟨j.val,Nat.lt_of_lt_of_le j.isLt ht⟩)] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [RawG2.normalizePrefix,List.finRange_succ_last,List.flatMap_append,
      List.flatMap_map,List.flatMap_singleton]
    rw [ih (by omega)]
    rfl

theorem eval_normalize (r control bit : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx)) (p : Fin (r.eval env ctx) → Bool)
    (hc : ∀j,L.controls j=control.eval env ctx j.val)
    (hb : ∀j,bit.eval env ctx j.val=if p j then 1 else 0) :
    (normalize r control bit).eval env ctx src=RawG2.normalize L p := by
  simp only [normalize,Recipe.eval,Expr.eval_plug,Expr.eval_lift,Expr.eval]
  rw [←finRange_val,List.flatMap_map]
  unfold RawG2.normalize
  rw [normalizePrefix_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  simp only [List.getElem?_cons_zero,Option.getD_some]
  simp only [hb j]
  cases hp : p j <;> simp [hp,x,Recipe.eval,hc,RawG2.x,Expr.eval]

theorem eval_patternX (r control flags bit target : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx)) (p : Fin (r.eval env ctx) → Bool)
    (hc : ∀j,L.controls j=control.eval env ctx j.val)
    (hf : ∀j,L.flags j=flags.eval env ctx j.val)
    (hb : ∀j,bit.eval env ctx j.val=if p j then 1 else 0) :
    (patternX r control flags bit target).eval env ctx src=RawG2.patternControlledX L p (target.eval env ctx) := by
  simp only [patternX,eval_useUncompute,eval_normalize r control bit env ctx src L p hc hb,
    eval_multiX r control flags target env ctx src L hc hf,RawG2.patternControlledX]







@[simp] theorem eval_borrowStep (a b carry next temp : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (borrowStep a b carry next temp).eval env ctx src=
      RawG2.compile (RawG2.borrowCommands ![a.eval env ctx,b.eval env ctx,carry.eval env ctx,
        next.eval env ctx,temp.eval env ctx]) := by
  simp only [borrowStep,eval_hAppend,eval_cn,eval_x,eval_conj]
  rfl

theorem borrowPrefix_flatMap {r : ℕ} (L : RawG2.BorrowLayout r) (t : ℕ) (ht : t≤r) :
    RawG2.borrowPrefix L t ht=(List.finRange t).flatMap fun j=>
      RawG2.borrowCommands ![L.left ⟨j.val,Nat.lt_of_lt_of_le j.isLt ht⟩,
        L.right ⟨j.val,Nat.lt_of_lt_of_le j.isLt ht⟩,
        L.carry ⟨j.val,by have := j.isLt; omega⟩,L.carry ⟨j.val+1,by have := j.isLt; omega⟩,L.temp] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [RawG2.borrowPrefix,List.finRange_succ_last,List.flatMap_append,
      List.flatMap_map,List.flatMap_singleton]
    rw [ih (by omega)]
    rfl

theorem eval_borrowCompute (r a b carry temp : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.BorrowLayout (r.eval env ctx))
    (ha : ∀j,L.left j=a.eval env ctx j.val)
    (hb : ∀j,L.right j=b.eval env ctx j.val)
    (hc : ∀j,L.carry j=carry.eval env ctx j.val)
    (hp : L.temp=temp.eval env ctx) :
    (borrowCompute r a b carry temp).eval env ctx src=
      RawG2.compile (RawG2.borrowPrefix L (r.eval env ctx) le_rfl) := by
  simp only [borrowCompute,Recipe.eval,eval_borrowStep,Expr.eval_plug,Expr.eval_lift,
    eval_add,eval_nat,Expr.eval]
  rw [←finRange_val,List.flatMap_map,borrowPrefix_flatMap]
  simp only [RawG2.compile,List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  simp only [ha,hb,hc,hp]
  rfl

theorem eval_comparator (r a b carry temp target : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.BorrowLayout (r.eval env ctx))
    (ha : ∀j,L.left j=a.eval env ctx j.val)
    (hb : ∀j,L.right j=b.eval env ctx j.val)
    (hc : ∀j,L.carry j=carry.eval env ctx j.val)
    (hp : L.temp=temp.eval env ctx) :
    (comparator r a b carry temp target).eval env ctx src=RawG2.comparator L (target.eval env ctx) := by
  simp only [comparator,eval_useUncompute,eval_borrowCompute r a b carry temp env ctx src L ha hb hc hp,
    eval_cn,Expr.eval_plug,RawG2.comparator]
  rw [hc (Fin.last _)]
  rfl



theorem eval_equality (r a b carry temp target : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.BorrowLayout (r.eval env ctx))
    (ha : ∀j,L.left j=a.eval env ctx j.val)
    (hb : ∀j,L.right j=b.eval env ctx j.val)
    (hc : ∀j,L.carry j=carry.eval env ctx j.val)
    (hp : L.temp=temp.eval env ctx) :
    (equality r a b carry temp target).eval env ctx src=RawG2.equality L (target.eval env ctx) := by
  simp only [equality,eval_hAppend,eval_x,RawG2.equality]
  rw [eval_comparator r a b carry temp target env ctx src L ha hb hc hp,
    eval_comparator r b a carry temp target env ctx src (RawG2.swapBorrow L) hb ha hc hp]










@[simp] theorem eval_carryStep (a b carry next temp : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (carryStep a b carry next temp).eval env ctx src=
      RawG2.compile (RawG2.carryCommands ![a.eval env ctx,b.eval env ctx,carry.eval env ctx,
        next.eval env ctx,temp.eval env ctx]) := by
  simp only [carryStep,eval_hAppend,eval_cn,eval_conj]
  rfl

theorem carryPrefix_flatMap {r : ℕ} (L : RawG2.AdditionLayout r) (t : ℕ) (ht : t≤r) :
    RawG2.carryPrefix L t ht=(List.finRange t).flatMap fun j=>
      RawG2.carryCommands ![L.left ⟨j.val,Nat.lt_of_lt_of_le j.isLt ht⟩,
        L.right ⟨j.val,Nat.lt_of_lt_of_le j.isLt ht⟩,
        L.carry ⟨j.val,by have := j.isLt; omega⟩,L.carry ⟨j.val+1,by have := j.isLt; omega⟩,L.temp] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [RawG2.carryPrefix,List.finRange_succ_last,List.flatMap_append,
      List.flatMap_map,List.flatMap_singleton]
    rw [ih (by omega)]
    rfl

theorem eval_carryCompute (r a b carry temp : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AdditionLayout (r.eval env ctx))
    (ha : ∀j,L.left j=a.eval env ctx j.val)
    (hb : ∀j,L.right j=b.eval env ctx j.val)
    (hc : ∀j,L.carry j=carry.eval env ctx j.val)
    (hp : L.temp=temp.eval env ctx) :
    (carryCompute r a b carry temp).eval env ctx src=
      RawG2.compile (RawG2.carryPrefix L (r.eval env ctx) le_rfl) := by
  simp only [carryCompute,Recipe.eval,eval_carryStep,Expr.eval_plug,Expr.eval_lift,
    eval_add,eval_nat,Expr.eval]
  rw [←finRange_val,List.flatMap_map,carryPrefix_flatMap]
  simp only [RawG2.compile,List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  simp only [ha,hb,hc,hp]
  rfl

theorem eval_sumCompute (r a b carry output : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AdditionLayout (r.eval env ctx))
    (ha : ∀j,L.left j=a.eval env ctx j.val)
    (hb : ∀j,L.right j=b.eval env ctx j.val)
    (hc : ∀j,L.carry j=carry.eval env ctx j.val)
    (ho : ∀j,L.output j=output.eval env ctx j.val) :
    (sumCompute r a b carry output).eval env ctx src=
      RawG2.compile ((List.finRange (r.eval env ctx)).flatMap (RawG2.sumStep L)) := by
  simp only [sumCompute,Recipe.eval,eval_hAppend,eval_cn,Expr.eval_plug,Expr.eval_lift,Expr.eval]
  rw [←finRange_val,List.flatMap_map]
  simp only [RawG2.compile,List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  simp only [RawG2.sumStep,ha,hb,hc,ho]
  rfl

theorem eval_addition (r a b carry output temp : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AdditionLayout (r.eval env ctx))
    (ha : ∀j,L.left j=a.eval env ctx j.val)
    (hb : ∀j,L.right j=b.eval env ctx j.val)
    (hc : ∀j,L.carry j=carry.eval env ctx j.val)
    (ho : ∀j,L.output j=output.eval env ctx j.val)
    (hp : L.temp=temp.eval env ctx) :
    (addition r a b carry output temp).eval env ctx src=RawG2.addition L := by
  simp only [addition,eval_useUncompute,
    eval_carryCompute r a b carry temp env ctx src L ha hb hc hp,
    eval_sumCompute r a b carry output env ctx src L ha hb hc ho,
    RawG2.addition,RawG2.additionCommands,RawG2.compile,List.map_append,List.map_reverse,
    RawG2.computeUseUncompute]










theorem incrementPrefix_flatMap {r : ℕ} (L : RawG2.AndLayout (r+1)) (t : ℕ) (ht : t≤r) :
    RawG2.incrementPrefix L t ht=((List.finRange t).reverse).flatMap fun j=>
      RawG2.incrementStep L j.val (Nat.lt_of_lt_of_le j.isLt ht) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [RawG2.incrementPrefix,List.finRange_succ_last,List.reverse_append,
      List.reverse_singleton,List.flatMap_append,List.flatMap_singleton,←List.map_reverse,List.flatMap_map]
    rw [ih (by omega)]
    rfl

theorem eval_increment (r control flags : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx+1))
    (hc : ∀j,L.controls j=control.eval env ctx j.val)
    (hf : ∀j,L.flags j=flags.eval env ctx j.val) :
    (increment r control flags).eval env ctx src=RawG2.increment L := by
  simp only [increment,Recipe.eval]
  rw [←finRange_val,←List.map_reverse,List.flatMap_map]
  unfold RawG2.increment
  rw [incrementPrefix_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  unfold RawG2.incrementStep
  convert eval_multiX (.bound 0+1) control.lift flags.lift
    (control.lift.plug (.bound 0+1)) env (j.val::ctx) src
    (RawG2.prefixLayout L (j.val+1) (by have := j.isLt; omega))
    (fun i=>by simp [RawG2.prefixLayout,hc]) (fun i=>by simp [RawG2.prefixLayout,hf]) using 1
  · simp [hc,Expr.eval]



theorem eval_pairedH (r wire : Expr) (env : Environment) (ctx : List ℕ) (src)
    (e : Fin (r.eval env ctx) → ℕ) (he : ∀j,e j=wire.eval env ctx j.val) :
    (pairedH r wire).eval env ctx src=RawG2.pairedHadamards e := by
  simp only [pairedH,Recipe.eval,Expr.eval,eval_hh,Expr.eval_plug,Expr.eval_lift,eval_add,
    eval_nat]
  rw [←finRange_val,List.flatMap_map,←List.map_eq_flatMap]
  unfold RawG2.pairedHadamards
  apply List.map_congr_left
  intro j _
  simp only [he,eval_nat]
  rfl


end Gadgets
end QMAPerfectCompleteness.Main.CircuitRecipe

end

/- Inline helpers retained from Solutions.CyclicRecipeCorrectness. -/
section


/-! Exact realization of the coherent verifier by a finite circuit-generator recipe. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe CircuitRecipe.Gadgets RawEncoding RawG2



@[simp] theorem eval_out (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    out.eval P.env ctx w=P.out := rfl

@[simp] theorem eval_k (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    k.eval P.env ctx w=P.k := rfl







@[simp] theorem eval_proof (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    proof.eval P.env ctx w=P.proof := rfl
@[simp] theorem eval_ancilla (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    ancilla.eval P.env ctx w=P.ancilla := rfl
@[simp] theorem eval_clock (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    clock.eval P.env ctx w=P.clock w := rfl
@[simp] theorem eval_verifier (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    verifier.eval P.env ctx w=P.verifier w := rfl

@[simp] theorem eval_carry (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    carry.eval P.env ctx w=P.carry w := rfl
@[simp] theorem eval_pad (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    pad.eval P.env ctx w=P.pad w := rfl


@[simp] theorem eval_flag (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    flag.eval P.env ctx w=P.flag := rfl
@[simp] theorem eval_temp (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    temp.eval P.env ctx w=P.temp := rfl
@[simp] theorem eval_readoutZero (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    readoutZero.eval P.env ctx w=P.readoutZero := rfl
@[simp] theorem eval_readoutOutput (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    readoutOutput.eval P.env ctx w=P.readoutOutput := rfl
@[simp] theorem eval_tag (P : CyclicRaw.Meta) (j : ℕ) (ctx : List ℕ) (w : ℕ) :
    (tag j).eval P.env ctx w=P.tag j := rfl
@[simp] theorem eval_validTag (P : CyclicRaw.Meta) (j : ℕ) (ctx : List ℕ) (w : ℕ) :
    (validTag j).eval P.env ctx w=P.validity j := rfl
@[simp] theorem eval_word (P : CyclicRaw.Meta) (d : ℕ) (ctx : List ℕ) (w : ℕ) :
    (word d).eval P.env ctx w=P.word d w := rfl


@[simp] theorem eval_paddedIndex (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    paddedIndex.eval P.env ctx w=P.paddedIndex w := by
  simp only [paddedIndex,Expr.eval,eval_k,Expr.eval_plug,eval_pad,eval_sub]
  rfl

@[simp] theorem eval_incControl (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    incControl.eval P.env ctx w=if w=0 then P.tag 5 else P.clock (w-1) := by
  simp only [incControl,Expr.eval,Expr.eval_plug,eval_tag,eval_clock,eval_sub,eval_nat]
  split_ifs <;> omega
@[simp] theorem eval_permute (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    permute.eval P.env ctx w=P.permute w := rfl

theorem eval_andNot (a b c : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (andNot a b c).eval env ctx src=RawG2.andNot (a.eval env ctx) (b.eval env ctx) (c.eval env ctx) := by
  simp only [andNot,eval_hAppend,eval_x,eval_conj]
  rfl

@[simp] theorem eval_range (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    range.eval P.env ctx src=P.rangeGates := by
  have hc (d t : ℕ) :
      (Gadgets.comparator r paddedIndex (word d) carry temp (tag t)).eval P.env ctx src=
        RawG2.comparator (P.arithmeticBorrow P.paddedIndex (P.word d)) (P.tag t) := by
    apply eval_comparator _ _ _ _ _ _ P.env ctx src
      <;> intros <;> simp [CyclicRaw.Meta.arithmeticBorrow]
  simp only [range,eval_hAppend,hc,eval_andNot,eval_tag]
  rfl

@[simp] theorem eval_proofEquality (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    proofEquality.eval P.env ctx src=RawG2.equality P.historyLayout.equality (P.tag 8) := by
  apply eval_equality _ _ _ _ _ _ P.env ctx src
    <;> intros <;> rfl

@[simp] theorem eval_lastClock (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    lastClock.eval P.env ctx src=RawG2.patternControlledX P.clockAnd (fun _=>true) (P.tag 6) := by
  apply eval_patternX _ _ _ _ _ P.env ctx src
    <;> intros <;> rfl

@[simp] theorem eval_history (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    history.eval P.env ctx src=RawG2.history P.historyLayout := by
  simp only [history,eval_hAppend,eval_proofEquality,eval_lastClock,eval_tof,eval_tag,Recipe.eval_reverse]
  rfl

@[simp] theorem eval_closing (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    closing.eval P.env ctx src=RawG2.closing P.historyLayout (P.tag 4) P.flag := by
  simp only [closing,eval_useUncompute,eval_history,eval_tof,eval_tag,eval_flag]
  rfl

@[simp] theorem eval_indexH (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    indexH.eval P.env ctx src=P.indexH := by
  apply eval_pairedH _ _ P.env ctx src
  intros
  rfl

@[simp] theorem eval_increment (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    (Gadgets.increment c incControl scratch).eval P.env ctx src=RawG2.increment P.incrementLayout := by
  apply Gadgets.eval_increment _ _ _ P.env ctx src
  · intro j; exact (eval_incControl P ctx j.val).symm
  · intro j; rfl

@[simp] theorem eval_post (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    post.eval P.env ctx src=P.post := by
  simp only [post,eval_hAppend,eval_cn,eval_tag,eval_flag,eval_closing,eval_increment,eval_hh,eval_x]
  simp [CyclicRaw.Meta.post,RawG2.phase,List.append_assoc]

@[simp] theorem eval_zeroTest (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    zeroTest.eval P.env ctx src=RawG2.patternControlledX P.readoutLayout.zeros (fun _=>false) P.readoutZero := by
  apply eval_patternX _ _ _ _ _ P.env ctx src
    <;> intros <;> rfl

@[simp] theorem eval_readout (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    readout.eval P.env ctx src=RawG2.readout P.readoutLayout := by
  simp only [readout,eval_useUncompute,eval_zeroTest,eval_hAppend,eval_x,eval_conj,
    eval_readoutZero,eval_readoutOutput,eval_validTag]
  rfl

end QMAPerfectCompleteness.Main.CyclicRecipe

end

/- Inline helpers retained from Solutions.CyclicRecipePreparation. -/
section


/-! The finite arithmetic prefix recipe matches the proved clean adder circuits. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe CircuitRecipe.Gadgets RawEncoding RawG2





@[simp] theorem eval_three (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    (Gadgets.addition r (word 0) (word 1) carry (word 4) temp).eval P.env ctx src=
      RawG2.addition (RawG2.threeLayout P.thresholds) := by
  apply eval_addition _ _ _ _ _ _ P.env ctx src
    <;> intros <;> rfl

@[simp] theorem eval_upper (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    (Gadgets.addition r (word 4) (word 2) carry (word 5) temp).eval P.env ctx src=
      RawG2.addition (RawG2.upperLayout P.thresholds) := by
  apply eval_addition _ _ _ _ _ _ P.env ctx src
    <;> intros <;> rfl

@[simp] theorem eval_threshold (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    threshold.eval P.env ctx src=P.prepGates := by
  simp only [threshold,eval_hAppend,eval_copies,eval_three,eval_upper]
  simp only [CyclicRaw.Meta.prepGates,RawG2.threshold,RawG2.thresholdCommands,
    RawG2.compile,RawG2.addition,List.map_append]

end QMAPerfectCompleteness.Main.CyclicRecipe

end

/- Inline helpers retained from Solutions.CyclicRecipeValidity. -/
section


/-! Sparse threshold bits realize validity without exponential unary constants. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe CircuitRecipe.Gadgets RawEncoding RawG2

theorem eval_bitAt_pattern (pos : Expr) (env : Environment) (ctx : List ℕ) (n : ℕ)
    (hn : ∀w,pos.eval env ctx w=n) (j : ℕ) :
    (bitAt pos).eval env ctx j=if (2^n).testBit j then 1 else 0 := by
  simp only [bitAt,Expr.eval,hn,Nat.testBit_two_pow,decide_eq_true_eq]
  split_ifs <;> omega

lemma testBit_pow_add_one (n j : ℕ) (hn : 0<n) :
    (2^n+1).testBit j=decide (j=0 ∨ j=n) := by
  have h := Nat.testBit_two_pow_mul_add 1 (Nat.one_lt_two_pow (by omega : n≠0)) j
  simp only [Nat.mul_one] at h
  rw [h]
  have h1 (t : ℕ) : (1 : ℕ).testBit t=decide (0=t) := by
    exact Nat.testBit_two_pow (n:=0) (m:=t)
  simp only [h1]
  by_cases hj : j<n
  · rw [if_pos hj]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  · rw [if_neg hj]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega

theorem eval_upperBits (P : CyclicRaw.Meta) (ctx : List ℕ) (hk : 3≤P.k) (j : ℕ) :
    upperBits.eval P.env ctx j=if (2^(P.k-2)+1).testBit j then 1 else 0 := by
  rw [testBit_pow_add_one _ _ (by omega)]
  simp only [upperBits,bitAt,Expr.eval,eval_sub,eval_k,eval_nat,CyclicRaw.Meta.env,decide_eq_true_eq]
  split_ifs <;> omega

lemma one_lt_width (P : CyclicRaw.Meta) : 1<2^P.r := by
  exact Nat.one_lt_two_pow (by dsimp [CyclicRaw.Meta.r]; omega)
lemma low_lt_width (P : CyclicRaw.Meta) : 2^(P.k-3)<2^P.r := by
  exact Nat.pow_lt_pow_right (by decide : 1<2) (by dsimp [CyclicRaw.Meta.r]; omega)
lemma upper_lt_width (P : CyclicRaw.Meta) : 2^(P.k-2)+1<2^P.r := by
  have h := Nat.pow_le_pow_right (by decide : 0<2) (show P.k-2+2≤P.r by dsimp [CyclicRaw.Meta.r]; omega)
  have h2 : 0<2^(P.k-2) := Nat.two_pow_pos _
  rw [Nat.pow_succ,Nat.pow_succ] at h
  omega

/-- A generic constant-comparison recipe with a supplied compact threshold bit formula. -/
theorem compare_constant (P : CyclicRaw.Meta) (ctx : List ℕ) (src) (d t N : ℕ) (bits : Expr)
    (hN : N<2^P.r) (hb : ∀j : Fin P.r,bits.eval P.env ctx j.val=if N.testBit j.val then 1 else 0) :
    (compareBits r (word d) carry bits (validTag t)).eval P.env ctx src=
      RawG2.compareNatGates (r:=P.r)
        ⟨fun j=>P.word d j.val,fun j=>P.carry j.val⟩ N (P.validity t) := by
  unfold RawG2.compareNatGates
  rw [if_pos hN]
  apply eval_compareBits _ _ _ _ _ P.env ctx src
  · intro j; rfl
  · intro j; rfl
  · exact hb

@[simp] theorem eval_criteria (P : CyclicRaw.Meta) (ctx : List ℕ) (src) (hk : 3≤P.k) :
    criteria.eval P.env ctx src=RawG2.criteria P.validityLayout := by
  have h1 d t := compare_constant P ctx src d t 1 (bitAt 0) (one_lt_width P)
    (fun j=>by simpa only [Nat.pow_zero] using eval_bitAt_pattern 0 P.env ctx 0 (fun _=>rfl) j.val)
  have h2 := compare_constant P ctx src 0 2 (2^(P.k-3)) (bitAt (k-3)) (low_lt_width P)
    (fun j=>eval_bitAt_pattern (k-3) P.env ctx (P.k-3) (fun _=>rfl) j.val)
  have h3 := compare_constant P ctx src 0 3 (2^(P.k-2)+1) upperBits (upper_lt_width P)
    (fun j=>eval_upperBits P ctx hk j.val)
  have hv : (Gadgets.comparator r (word 0) (word 3) carry temp (validTag 4)).eval P.env ctx src=
      RawG2.comparator P.validityLayout.comparison (P.validity 4) := by
    apply eval_comparator _ _ _ _ _ _ P.env ctx src <;> intros <;> rfl
  simp only [criteria,eval_hAppend,h1,h2,h3,hv,eval_x,eval_validTag]
  rfl

@[simp] theorem eval_validity (P : CyclicRaw.Meta) (ctx : List ℕ) (src) (hk : 3≤P.k) :
    validity.eval P.env ctx src=P.validGates := by
  unfold validity CyclicRaw.Meta.validGates RawG2.validity
  rw [eval_hAppend,eval_criteria P ctx src hk]
  congr 1
  apply eval_multiX _ _ _ _ P.env ctx src
  · intro j; rfl
  · intro j
    change P.carry (min j.val (P.k+2))=P.carry j.val
    have hj : j.val<6 := j.isLt
    rw [min_eq_left (by omega)]

@[simp] theorem eval_clockBelow (P : CyclicRaw.Meta) (ctx : List ℕ) (src)
    (hell : P.ell=2^P.c-1) : clockBelow.eval P.env ctx src=
      RawG2.compareNatGates P.clockAnd P.ell (P.tag 6) := by
  unfold clockBelow RawG2.compareNatGates
  have hlt : P.ell<2^P.c := by rw [hell]; have := Nat.two_pow_pos P.c; omega
  rw [if_pos hlt]
  apply eval_compareBits _ _ _ _ _ P.env ctx src
  · intro j; rfl
  · intro j; rfl
  · intro j
    rw [hell,Nat.testBit_two_pow_sub_one]
    simp [j.isLt,Expr.eval]

@[simp] theorem eval_mid (P : CyclicRaw.Meta) (ctx : List ℕ) (src) (hell : P.ell=2^P.c-1) :
    mid.eval P.env ctx src=P.mid := by
  simp only [mid,eval_useUncompute,eval_clockBelow P ctx src hell,tripleFlag,eval_hAppend,
    eval_tof,eval_tag,eval_flag,Expr.eval_plug,eval_verifier,eval_out]
  rfl

end QMAPerfectCompleteness.Main.CyclicRecipe

end



/-! Final executable finite-recipe realization of the paper's coherent certificate verifier. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QMAPerfectCompleteness.Main.CyclicRecipe
end QMAPerfectCompleteness.Main.CyclicRecipe
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe CircuitRecipe.Gadgets RawEncoding RawG2

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRecipe.eval_preparation (P : CyclicRaw.Meta) (ctx : List ℕ) (src) (hk : 3≤P.k) :
    preparation.eval P.env ctx src=P.prefixGates := by
  simp only [preparation,eval_hAppend,eval_threshold,eval_validity P ctx src hk]
  rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRecipe.eval_source (P : CyclicRaw.Meta) (ctx : List ℕ) (src) (rev : Bool) :
    (Recipe.source rev verifier).eval P.env ctx src=
      RawG2.place P.verifier (if rev then src.reverse else src) := by
  simp only [Recipe.eval,eval_verifier]
  rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRecipe.eval_block (P : CyclicRaw.Meta) (ctx : List ℕ) (src)
    (hell : P.ell=2^P.c-1) : block.eval P.env ctx src=P.block src := by
  simp only [block,eval_hAppend,eval_indexH,eval_range,eval_source,eval_mid P ctx src hell,
    eval_post,Recipe.eval_reverse,Bool.false_eq_true,if_false,if_true]
  rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRecipe.eval_physical (P : CyclicRaw.Meta) (ctx : List ℕ) (src)
    (hk : 3≤P.k) (hell : P.ell=2^P.c-1) : physical.eval P.env ctx src=P.gates src := by
  simp only [physical,eval_hAppend,eval_x,eval_flag,eval_preparation P ctx src hk,
    eval_block P ctx src hell,eval_readout]
  rfl

/-- A fixed finite recipe evaluates to the exact raw circuit, using only width-bounded loops. -/
theorem solution (P : CyclicRaw.Meta) (src : List RawEncoding.Instruction)
    (hk : 3≤P.k) (hell : P.ell=2^P.c-1) : program.eval P.env src=P.compile src := by
  unfold program CircuitRecipe.Circuit.eval
  simp only [eval_proof,eval_ancilla,Expr.eval_plug,eval_permute,eval_readoutOutput,
    Recipe.eval,eval_physical P [] src hk hell,eval_permute]
  rfl
