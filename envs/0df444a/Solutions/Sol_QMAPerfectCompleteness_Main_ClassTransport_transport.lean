-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.ClassTransport.transport
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:51:02.948748+00:00
-- url     : https://prove2.me/submissions/99032d12-4505-40ed-8deb-d58b5086f0a6

/- Generated from Solutions.ClassTransport by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClassTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! Class assembly needs only continuations of generators whose outputs are verifier codes.
No general polynomial-time composition theorem, nor a runtime specification on malformed
compiler inputs, is required by these reductions. The runtime hypotheses below remain explicit. -/
namespace QMAPerfectCompleteness.Main.ClassTransport
end QMAPerfectCompleteness.Main.ClassTransport
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.ClassTransport
open QAlgorithms.Complexity (Str PolyTimeComputable)



/-- Assemble semantic preservation and a concrete code-generator continuation. -/
theorem solution {G H : GateSet} {c s c' s' : ℝ}
    (compile : Verifier G → Verifier H) (code : Str → Str)
    (hcode : ∀ V, code V.encode = (compile V).encode)
    (htime : UniformOnVerifierCodes G code)
    (hyes : ∀ V, V.AcceptsSomeProof c → (compile V).AcceptsSomeProof c')
    (hno : ∀ V, V.AcceptsAllProofsAtMost s → (compile V).AcceptsAllProofsAtMost s') :
    QMAClass G c s ⊆ QMAClass H c' s' := by
  rintro L ⟨gen,V,hpoly,henc,hyesV,hnoV⟩
  refine ⟨(fun x => code (gen x)),(fun x => compile (V x)),htime gen V hpoly henc,?_,?_,?_⟩
  · intro x
    change code (gen x) = (compile (V x)).encode
    rw [henc x,hcode]
  · intro x hx
    exact hyes (V x) (hyesV x hx)
  · intro x hx
    exact hno (V x) (hnoV x hx)
