-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.BlockVerifierCoordinates.spectator_mask
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:50:59.124311+00:00
-- url     : https://prove2.me/submissions/665b2a49-ae86-4e0b-aae8-b5ba3dd5ab91

/- Generated from Solutions.BlockVerifierCoordinates by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition



/-! The two literal verifier calls in logical block coordinates, with arbitrary workspace. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.BlockVerifierCoordinates
end QMAPerfectCompleteness.Main.BlockVerifierCoordinates
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.BlockVerifierCoordinates
open BlockCircuit BlockCoordinates ReversibleGadgets

set_option maxHeartbeats 2000000 
theorem solution (V : Verifier gatesG2) (w : ℕ)
    (y x : Basis (bodyWires V+w)) :
    (∀ j, (∀ a, verifierEmbedding (V := V) w a ≠ j) → y j = x j) ↔
      (y ∘ indexWire = x ∘ indexWire) ∧ (y ∘ clockWire = x ∘ clockWire) ∧
        y flagWire = x flagWire ∧ (y ∘ workspaceWire = x ∘ workspaceWire) := by
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_⟩
    · funext i
      apply h
      intro a ha
      have := congrArg Fin.val ha
      have hi := i.isLt
      change indexQubits V + clockWires V + a.val = i.val at this
      omega
    · funext i
      apply h
      intro a ha
      have := congrArg Fin.val ha
      have hi := i.isLt
      change indexQubits V + clockWires V + a.val = indexQubits V + i.val at this
      omega
    · apply h
      intro a ha
      have := congrArg Fin.val ha
      have ha' := a.isLt
      change indexQubits V + clockWires V + a.val = indexQubits V + clockWires V + (V.proofQubits+V.ancillaQubits) at this
      omega
    · funext i
      apply h
      intro a ha
      have := congrArg Fin.val ha
      have ha' := a.isLt
      change indexQubits V + clockWires V + a.val = bodyWires V + i.val at this
      simp only [bodyWires] at this
      omega
  · rintro ⟨hi,hc,hf,hw⟩ j
    refine Fin.addCases (m := bodyWires V) (n := w) (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (m := indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits)) (n := 1) (fun a => ?_) (fun a => ?_) a
      · refine Fin.addCases (m := indexQubits V+clockWires V) (n := V.proofQubits+V.ancillaQubits) (fun a => ?_) (fun a => ?_) a
        · refine Fin.addCases (m := indexQubits V) (n := clockWires V) (fun a => ?_) (fun a => ?_) a
          · intro _; exact congrFun hi a
          · intro _; exact congrFun hc a
        · intro hj; exact (hj a rfl).elim
      · intro _
        have ha : a = 0 := Subsingleton.elim _ _
        subst a
        have he : Fin.castAdd w
            (Fin.natAdd (indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits)) (0 : Fin 1)) =
            (flagWire : Fin (bodyWires V+w)) := by apply Fin.ext; rfl
        rw [he]
        exact hf
    · intro _; exact congrFun hw a
