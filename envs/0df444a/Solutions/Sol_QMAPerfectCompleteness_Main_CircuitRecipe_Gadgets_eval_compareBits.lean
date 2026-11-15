-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_compareBits
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:51:02.225201+00:00
-- url     : https://prove2.me/submissions/165c3f5e-0119-45d1-b4fb-60644aa6de0a

/- Generated from Solutions.RecipeGadgets by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawControlGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeNormalization
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

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



/-! Finite recipes realizing the linear reversible circuit templates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.CircuitRecipe
end QMAPerfectCompleteness.Main.CircuitRecipe
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CircuitRecipe

namespace QMAPerfectCompleteness.Main.CircuitRecipe.Expr
end QMAPerfectCompleteness.Main.CircuitRecipe.Expr
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CircuitRecipe QMAPerfectCompleteness.Main.CircuitRecipe.Expr

@[simp] theorem QMAPerfectCompleteness.Main.CircuitRecipe.Expr.eval_plug (e v : Expr) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (e.plug v).eval env ctx w=e.eval env ctx (v.eval env ctx w) := by
  induction e <;> simp_all [plug,eval]
end

namespace QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets
end QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CircuitRecipe QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets
open RawG2 RawEncoding




@[simp] theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_hAppend (p q : Recipe) (env : Environment) (ctx : List ℕ) (src) :
    (p ++ q).eval env ctx src=p.eval env ctx src ++ q.eval env ctx src := rfl
@[simp] theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_add (a b : Expr) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (a+b).eval env ctx w=a.eval env ctx w+b.eval env ctx w := rfl
@[simp] theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_sub (a b : Expr) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (a-b).eval env ctx w=a.eval env ctx w-b.eval env ctx w := rfl
@[simp] theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_nat (n : ℕ) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (OfNat.ofNat n : Expr).eval env ctx w=n := rfl





@[simp] theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_x (a : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (x a).eval env ctx src=[RawG2.x (a.eval env ctx)] := rfl
@[simp] theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_cn (a b : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (cn a b).eval env ctx src=[RawG2.cn (a.eval env ctx) (b.eval env ctx)] := rfl
@[simp] theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_tof (a b c : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (tof a b c).eval env ctx src=[RawG2.tof (a.eval env ctx) (b.eval env ctx) (c.eval env ctx)] := rfl



/-- Match the syntactic finite index enumeration with the loop counter enumeration. -/
theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.finRange_val (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp













@[simp] theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_useUncompute (a b : Recipe) (env : Environment) (ctx : List ℕ) (src) :
    (useUncompute a b).eval env ctx src=
      RawG2.computeUseUncompute (a.eval env ctx src) (b.eval env ctx src) := by
  simp [useUncompute,RawG2.computeUseUncompute,Recipe.eval_reverse]

/-- The symbolic AND chain is the same literal gate list as the typed clean AND gadget. -/
theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_andCompute (r control flags : Expr) (env : Environment) (ctx : List ℕ) (src)
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


theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_multiX (r control flags target : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx))
    (hc : ∀j,L.controls j=control.eval env ctx j.val)
    (hf : ∀j,L.flags j=flags.eval env ctx j.val) :
    (multiX r control flags target).eval env ctx src=RawG2.multiControlledX L (target.eval env ctx) := by
  simp only [multiX,eval_useUncompute,eval_andCompute r control flags env ctx src L hc hf,
    eval_cn,Expr.eval_plug,RawG2.multiControlledX]
  rw [hf (Fin.last _)]
  rfl

theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.normalizePrefix_flatMap {r : ℕ} (L : RawG2.AndLayout r) (p : Fin r → Bool)
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

theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_normalize (r control bit : Expr) (env : Environment) (ctx : List ℕ) (src)
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

theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_patternX (r control flags bit target : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx)) (p : Fin (r.eval env ctx) → Bool)
    (hc : ∀j,L.controls j=control.eval env ctx j.val)
    (hf : ∀j,L.flags j=flags.eval env ctx j.val)
    (hb : ∀j,bit.eval env ctx j.val=if p j then 1 else 0) :
    (patternX r control flags bit target).eval env ctx src=RawG2.patternControlledX L p (target.eval env ctx) := by
  simp only [patternX,eval_useUncompute,eval_normalize r control bit env ctx src L p hc hb,
    eval_multiX r control flags target env ctx src L hc hf,RawG2.patternControlledX]









































theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.comparePrefix_flatMap {r : ℕ} (L : RawG2.AndLayout r) (p : Fin r → Bool) (target : ℕ)
    (t : ℕ) (ht : t≤r) :
    RawG2.comparePrefix L p target t ht=(List.finRange t).flatMap fun j=>
      RawG2.stageGates L p target j.val (Nat.lt_of_lt_of_le j.isLt ht) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [RawG2.comparePrefix,List.finRange_succ_last,List.flatMap_append,
      List.flatMap_map,List.flatMap_singleton]
    rw [ih (by omega)]
    rfl

theorem solution (r control flags bits target : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx)) (p : Fin (r.eval env ctx) → Bool)
    (hc : ∀j,L.controls j=control.eval env ctx j.val)
    (hf : ∀j,L.flags j=flags.eval env ctx j.val)
    (hb : ∀j,bits.eval env ctx j.val=if p j then 1 else 0) :
    (compareBits r control flags bits target).eval env ctx src=RawG2.compareGates L p (target.eval env ctx) := by
  simp only [compareBits,Recipe.eval]
  rw [←finRange_val,List.flatMap_map]
  unfold RawG2.compareGates
  rw [comparePrefix_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  have he : (bits.lift.plug (r.lift-1-.bound 0)).eval env (j.val::ctx)=bits.eval env ctx j.rev.val := by
    simp only [Expr.eval_plug,Expr.eval_lift,eval_sub,eval_nat,Expr.eval,
      List.getElem?_cons_zero,Option.getD_some,Fin.val_rev]
    congr 1
    omega
  simp only [he,eval_nat]
  unfold RawG2.stageGates
  by_cases hp : p j.rev=true
  · have hb' := hb j.rev
    simp [hp] at hb'
    simp only [hb',Nat.zero_lt_one,if_true,hp]
    have h := eval_patternX (.bound 0+1) (control.lift.plug ((r.plug 0).lift-1-.addr)) flags.lift
      (.ifLt .addr (.bound 0) (bits.lift.plug ((r.plug 0).lift-1-.addr)) 0) target.lift env (j.val::ctx) src
      (RawG2.prefixLayout (RawG2.reverseLayout L) (j.val+1) (by have := j.isLt; omega))
      (ComparisonCircuits.stagePattern (fun i=>p i.rev) j.val j.isLt) ?_ ?_ ?_
    · simpa only [Expr.eval_lift,Expr.eval,Fin.val_rev,hb',Nat.zero_lt_one,if_true] using h
    · intro i
      simp only [RawG2.prefixLayout,RawG2.reverseLayout,hc,Expr.eval_plug,Expr.eval_lift,
        eval_sub,eval_nat,Expr.eval,Fin.val_rev,List.getElem?_cons_zero,Option.getD_some]
      congr 1
      omega
    · intro i
      simp only [RawG2.prefixLayout,RawG2.reverseLayout,hf,Expr.eval_lift]
    · intro i
      simp only [Expr.eval,Expr.eval_lift,Expr.eval_plug,eval_sub,eval_nat,
        ComparisonCircuits.stagePattern,List.getElem?_cons_zero,Option.getD_some]
      by_cases hij : i.val<j.val
      · simp only [hij,if_true]
        have hi : i.val<r.eval env ctx := by have := j.isLt; omega
        have h := hb (⟨i.val,hi⟩ : Fin (r.eval env ctx)).rev
        have heq : r.eval env ctx-1-i.val=r.eval env ctx-(i.val+1) := by omega
        simpa only [Fin.val_rev,heq,hij,if_true] using h
      · simp only [hij,if_false,Bool.false_eq_true,if_false]
  · have hb' := hb j.rev
    simp [hp] at hb'
    simp [hb',hp,Expr.eval]
