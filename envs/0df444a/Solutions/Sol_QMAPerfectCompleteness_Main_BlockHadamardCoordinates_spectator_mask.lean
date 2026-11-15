-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.BlockHadamardCoordinates.spectator_mask
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:50:57.671715+00:00
-- url     : https://prove2.me/submissions/33cc6a79-1f79-4e70-b2c0-a56883c055ea

/- Generated from Solutions.BlockHadamardCoordinates by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! The physical paired-H bank implements the logical H bank with clean workspace. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.BlockHadamardCoordinates
open BlockCircuit BlockCoordinates BlockCompiler

set_option maxHeartbeats 2000000 
theorem solution (V : Verifier gatesG2) (w : ℕ)
    (y x : Basis (bodyWires V+w)) :
    (∀ j, (∀ a, (indexWire (V := V) (w := w) a) ≠ j) → y j = x j) ↔
      (y ∘ clockWire = x ∘ clockWire) ∧ (y ∘ verifierWire = x ∘ verifierWire) ∧
        y flagWire = x flagWire ∧ (y ∘ workspaceWire = x ∘ workspaceWire) := by
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_⟩
    · funext i
      apply h
      intro a ha
      have hv := congrArg Fin.val ha
      have ha' := a.isLt
      change a.val = indexQubits V+i.val at hv
      omega
    · funext i
      apply h
      intro a ha
      have hv := congrArg Fin.val ha
      have ha' := a.isLt
      change a.val = indexQubits V+clockWires V+i.val at hv
      omega
    · apply h
      intro a ha
      have hv := congrArg Fin.val ha
      have ha' := a.isLt
      change a.val = indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits) at hv
      omega
    · funext i
      apply h
      intro a ha
      have hv := congrArg Fin.val ha
      have ha' := a.isLt
      change a.val = bodyWires V+i.val at hv
      unfold bodyWires at hv
      omega
  · rintro ⟨hc,hv,hf,hw⟩ j
    refine Fin.addCases (m := bodyWires V) (n := w) (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (m := indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits))
        (n := 1) (fun a => ?_) (fun a => ?_) a
      · refine Fin.addCases (m := indexQubits V+clockWires V) (n := V.proofQubits+V.ancillaQubits)
          (fun a => ?_) (fun a => ?_) a
        · refine Fin.addCases (m := indexQubits V) (n := clockWires V) (fun a => ?_) (fun a => ?_) a
          · intro hj; exact (hj a rfl).elim
          · intro _; exact congrFun hc a
        · intro _; exact congrFun hv a
      · intro _
        have ha : a = 0 := Subsingleton.elim _ _
        subst a
        have he : Fin.castAdd w
            (Fin.natAdd (indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits)) (0 : Fin 1)) =
            (flagWire : Fin (bodyWires V+w)) := by apply Fin.ext; rfl
        rw [he]
        exact hf
    · intro _; exact congrFun hw a
