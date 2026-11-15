-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CertificateBlockCorrectness.mid_transports
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:45:48.997388+00:00
-- url     : https://prove2.me/submissions/e5c94bc1-788a-4560-9dd5-16cee452bd1f

/- Generated from Solutions.CertificateStageActions by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateOldPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateStageActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
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
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis

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

/- Inline helpers retained from Solutions.BlockCompiler. -/
section


/-! Concrete paper block-compiler scaffolds. Circuit data depend only on layout and certificate. -/

open Matrix
namespace QMAPerfectCompleteness.Main.BlockCompiler
open ReversibleGadgets ControlCircuits EqualityCircuits ComparisonCircuits ClockCircuits





namespace CleanProgram





end CleanProgram

namespace Layout

































































































































































lemma clock_ne_flag (D : Layout) (i : Fin D.clock) : D.clockWire i ≠ D.flagWire := by
  intro h
  have hv := congrArg Fin.val h
  change D.index+(i : ℕ) = D.index+D.clock+(D.proof+D.ancilla) at hv
  have := i.isLt
  omega

lemma clockValue_update_flag (D : Layout) (x : Basis D.total) (v : Bool) :
    D.clockValue (Function.update x D.flagWire v) = D.clockValue x := by
  unfold clockValue BlockCircuit.bitsValue
  apply Finset.sum_congr rfl
  intro i _
  rw [Function.update_of_ne (D.clock_ne_flag i)]























lemma verifier_ne_tag (D : Layout) (i : Fin (D.proof+D.ancilla)) (j : Fin 11) :
    D.verifierWire i ≠ D.tagWire j := by
  intro h
  have hv := congrArg Fin.val h
  change D.index+D.clock+(i : ℕ) = D.body+(j : ℕ) at hv
  have := i.isLt
  dsimp [body] at hv
  omega

/-- The clock tag is erased; the only changed body wire is the rejection flag. -/
theorem midAction_eq (D : Layout) (x : Basis D.total) (h6 : x (D.tagWire 6) = false) :
    D.midAction x = Function.update x D.flagWire
      (xor (x D.flagWire) ((x (D.tagWire 3) && decide (D.clockValue x < ell D.proof)) &&
        x (D.verifierWire D.output))) := by
  funext w
  have h36 := (D.tagWire_injective).ne (by decide : (3 : Fin 11) ≠ 6)
  have h63 := (D.tagWire_injective).ne (by decide : (6 : Fin 11) ≠ 3)
  by_cases hwf : w = D.flagWire
  · subst w
    simp [midAction, midProgram, CleanProgram.append, CleanProgram.reverseOfInvolution,
      clockBelowProgram, forwardFlagProgram, clockBelowAction, forwardFlagAction,
      D.clockValue_update_flag, D.clockValue_update_tag, h6, h36, h63,
      D.flag_ne_tag, D.verifier_ne_tag]
  · by_cases hw6 : w = D.tagWire 6
    · subst w
      simp [midAction, midProgram, CleanProgram.append, CleanProgram.reverseOfInvolution,
        clockBelowProgram, forwardFlagProgram, clockBelowAction, forwardFlagAction,
        D.clockValue_update_flag, D.clockValue_update_tag, h6, h36, h63,
        (D.flag_ne_tag 6).symm]
    · simp [midAction, midProgram, CleanProgram.append, CleanProgram.reverseOfInvolution,
        clockBelowProgram, forwardFlagProgram, clockBelowAction, forwardFlagAction,
        hwf, hw6]



























































end Layout











end QMAPerfectCompleteness.Main.BlockCompiler

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

@[simp] theorem computationEquiv_claim (V : Verifier gatesG2) (w : ℕ)
    (x : Basis ((bodyWires V+w)+claimQubits V)) :
    (computationEquiv V w x).1.2 = claimEquiv V (fun i => x (Fin.natAdd (bodyWires V+w) i)) := rfl



end QMAPerfectCompleteness.Main.CertificateCoordinates

end

/- Inline helpers retained from Solutions.BlockStateCoordinates. -/
section


/-! Pure basis-state identities for the concrete block compiler's register layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Matrix
namespace QMAPerfectCompleteness.Main.BlockStateCoordinates
open BlockCompiler BlockCoordinates
variable (V : Verifier gatesG2)







lemma index_ne_flag (i : Fin (D V).index) : (D V).indexWire i ≠ (D V).flagWire := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = (D V).index+(D V).clock+((D V).proof+(D V).ancilla) at hv
  have := i.isLt
  omega

lemma verifier_ne_flag (i : Fin ((D V).proof+(D V).ancilla)) :
    (D V).verifierWire i ≠ (D V).flagWire := by
  intro h
  have hv := congrArg Fin.val h
  change (D V).index+(D V).clock+i.val = (D V).index+(D V).clock+((D V).proof+(D V).ancilla) at hv
  have := i.isLt
  omega



lemma decode_update_flag (x : Physical V) (b : Bool) :
    BlockCircuit.decode (Function.update x (D V).flagWire b) =
      ((BlockCircuit.decode x).1,(BlockCircuit.decode x).2.1,(BlockCircuit.decode x).2.2.1,b) := by
  apply Prod.ext
  · change Fin.ofNat _ (BlockCircuit.bitsValue (Function.update x (D V).flagWire b) (D V).indexWire) = _
    congr 1
    unfold BlockCircuit.bitsValue
    simp_rw [Function.update_of_ne (index_ne_flag V _)]
    rfl
  · apply Prod.ext
    · change Fin.ofNat _ (BlockCircuit.bitsValue (Function.update x (D V).flagWire b) (D V).clockWire) = _
      congr 1
      unfold BlockCircuit.bitsValue
      simp_rw [Function.update_of_ne ((D V).clock_ne_flag _)]
      rfl
    · apply Prod.ext
      · funext i
        exact Function.update_of_ne (verifier_ne_flag V i) b x
      · exact Function.update_self _ _ _



end QMAPerfectCompleteness.Main.BlockStateCoordinates

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







lemma mul_basisEmbedding {α β : Type*} [Fintype α] [Fintype β] (e : α → β)
    (C : Matrix β β ℂ) (y : β) (x : α) : (C*basisEmbedding e) y x = C y (e x) := by
  classical
  simp [Matrix.mul_apply,basisEmbedding,mul_ite]



lemma basisEmbedding_mul_classical {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α → β) (f : α → α) (y : β) (x : α) :
    (basisEmbedding e * basisMap f) y x = if y = e (f x) then 1 else 0 := by
  classical
  simp [Matrix.mul_apply,basisEmbedding,basisMap,ite_mul,mul_ite]

lemma transports_classical {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e f : α → β) (C : Matrix β β ℂ) (g : α → α)
    (hc : ∀ y x, C y (e x) = if y = f (g x) then 1 else 0) :
    Transports e f C (basisMap g) := by
  ext y x
  rw [mul_basisEmbedding,basisEmbedding_mul_classical]
  exact hc y x

variable (V : Verifier gatesG2)










lemma clockValue_eq_decode (x : Physical V) : (D V).clockValue x = (BlockCircuit.decode x).2.1.val := by
  change (D V).clockValue x = (D V).clockValue x % (ell V.proofQubits+1)
  rw [clock_card]
  exact (Nat.mod_eq_of_lt (ComparisonCircuits.littleValue_lt_two_pow (x ∘ (D V).clockWire))).symm



























end QMAPerfectCompleteness.Main.BlockImplements

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

@[simp] lemma embed_decode (s : Key V → Basis (work V)) (p : Logical V) :
    BlockCircuit.decode (old V (embed V s p)) = p.1 := by rw [old_decode,coords_embed]

lemma coords_work (x : Physical V) : (coords V x).2 = x ∘ workWire V := rfl

lemma embed_work (s : Key V → Basis (work V)) (p : Logical V) (i : Fin (work V)) :
    embed V s p (workWire V i) = s (key V p) i :=
  congrFun (congrArg Prod.snd (coords_embed V s p)) i

lemma old_tag_work (i : Fin 11) :
    oldEmbedding V ((layoutOf V).tagWire i) =
      workWire V ⟨i.val,by have := i.isLt; dsimp only [work,oldWork,Layout.work]; omega⟩ := by
  apply Fin.ext
  rfl

lemma old_scratch_work (i : Fin ((layoutOf V).scale+4)) :
    oldEmbedding V ((layoutOf V).scratchWire i) =
      workWire V ⟨11+i.val,by have := i.isLt; dsimp only [work,oldWork,Layout.work]; omega⟩ := by
  apply Fin.ext
  rfl

lemma old_update_flag (x : Physical V) (f : Bool) :
    old V (Function.update x (oldEmbedding V (layoutOf V).flagWire) f) =
      Function.update (old V x) (layoutOf V).flagWire f := by
  funext i
  simp only [old,Function.comp_apply,Function.update_apply,(oldEmbedding V).injective.eq_iff]

lemma flag_ne_work (i : Fin (work V)) :
    oldEmbedding V (layoutOf V).flagWire ≠ workWire V i := by
  intro h
  have hv := congrArg Fin.val h
  change indexQubits V+BlockCircuit.clockWires V+(V.proofQubits+V.ancillaQubits) =
    BlockCircuit.bodyWires V+i.val at hv
  dsimp only [BlockCircuit.bodyWires] at hv
  omega

lemma flag_ne_claim (i : Fin (claimQubits V)) :
    oldEmbedding V (layoutOf V).flagWire ≠ Fin.natAdd (BlockCircuit.bodyWires V+work V) i := by
  intro h
  have hv := congrArg Fin.val h
  change indexQubits V+BlockCircuit.clockWires V+(V.proofQubits+V.ancillaQubits) =
    BlockCircuit.bodyWires V+work V+i.val at hv
  dsimp only [BlockCircuit.bodyWires] at hv
  omega

lemma coords_update_flag (x : Physical V) (f : Bool) :
    coords V (Function.update x (oldEmbedding V (layoutOf V).flagWire) f) =
      ((((coords V x).1.1.1,(coords V x).1.1.2.1,(coords V x).1.1.2.2.1,f),
        (coords V x).1.2),(coords V x).2) := by
  apply Prod.ext
  · apply Prod.ext
    · rw [← old_decode,old_update_flag,BlockStateCoordinates.decode_update_flag,old_decode]
    · rw [computationEquiv_claim,computationEquiv_claim]
      congr 1
      funext i
      exact Function.update_of_ne (flag_ne_claim V i).symm f x
  · rw [coords_work,coords_work]
    funext i
    exact Function.update_of_ne (flag_ne_work V i).symm f x

lemma embed_update_flag (s : Key V → Basis (work V)) (p : Logical V) (f : Bool) :
    Function.update (embed V s p) (oldEmbedding V (layoutOf V).flagWire) f =
      embed V s (((p.1.1,p.1.2.1,p.1.2.2.1,f)),p.2) := by
  apply (coords V).injective
  rw [coords_update_flag,coords_embed,coords_embed]
  rfl

lemma embed_old_wire (s : Key V → Basis (work V)) (p : Logical V)
    (i : Fin (V.proofQubits+V.ancillaQubits)) :
    embed V s p (oldEmbedding V ((layoutOf V).verifierWire i)) = p.1.2.2.1 i :=
  congrFun (congrArg (fun q : V.BlockReg (indexQubits V) => q.2.2.1) (embed_decode V s p)) i

lemma embed_old_flag (s : Key V → Basis (work V)) (p : Logical V) :
    embed V s p (oldEmbedding V (layoutOf V).flagWire) = p.1.2.2.2 :=
  congrArg (fun q : V.BlockReg (indexQubits V) => q.2.2.2) (embed_decode V s p)



















end QMAPerfectCompleteness.Main.CertificateBlockCorrectness

end

/- Inline helpers retained from Solutions.CertificateOldPrograms. -/
section


/-! Literal old block gadgets lifted into the master coherent-certificate register. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateOldPrograms
open CertificateMasterLayout BlockCompiler ReversibleGadgets
variable (V : Verifier gatesG2)





lemma place_update_of_action {r n : ℕ} (e : Fin r ↪ Fin n) (f : Basis r → Basis r)
    (x : Basis n) (w : Fin r) (b : Bool) (h : f (x ∘ e) = Function.update (x ∘ e) w b) :
    placePermutation e f x = Function.update x (e w) b := by
  calc
    placePermutation e f x = placePermutation e (fun u => Function.update u w b) x := by
      unfold placePermutation
      rw [h]
    _ = _ := place_update e w (fun _ => b) x





lemma mid_action (x : Physical V) (h6 : x (oldTags V 6) = false) :
    (midProgram V).action x = Function.update x (flag V)
      (xor (x (flag V)) ((x (oldTags V 3) &&
        decide ((layoutOf V).clockValue (oldState V x) < ell V.proofQubits)) &&
          x (oldEmbedding V ((layoutOf V).verifierWire V.output)))) := by
  apply place_update_of_action
  exact (layoutOf V).midAction_eq (oldState V x) h6











end QMAPerfectCompleteness.Main.CertificateOldPrograms

end



/-! Actual deterministic master-register stages on the coherent indexed workspace fiber. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
end QMAPerfectCompleteness.Main.CertificateBlockCorrectness
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout BlockCompiler BlockCoordinates BlockImplements
variable (V : Verifier gatesG2)

lemma QMAPerfectCompleteness.Main.CertificateBlockCorrectness.tagged_core (s : Key V → Basis (work V)) (p : Logical V) (i : Fin 11) (hi : i.val<6) :
    embed V (taggedSpace V s) p (oldTags V i) =
      Layout.rangeTruth p.2.2.1.val p.2.2.2.val p.1.1.val ⟨i.val,hi⟩ := by
  change embed V (taggedSpace V s) p (oldEmbedding V ((layoutOf V).tagWire i)) = _
  rw [old_tag_work,embed_work]
  exact dif_pos hi

lemma QMAPerfectCompleteness.Main.CertificateBlockCorrectness.tagged_aux (s : Key V → Basis (work V)) (hs : Prepared V s)
    (p : Logical V) (i : Fin 11) (hi : (6 : ℕ) ≤ i.val) :
    embed V (taggedSpace V s) p (oldTags V i) = false := by
  change embed V (taggedSpace V s) p (oldEmbedding V ((layoutOf V).tagWire i)) = _
  rw [old_tag_work,embed_work]
  change (if h : i.val<6 then _ else s (key V p) _) = false
  rw [dif_neg (by omega)]
  have h := hs.old_clean p ⟨i.val,by have := i.isLt; dsimp only [Layout.work]; omega⟩
  change embed V s p (oldEmbedding V ((layoutOf V).tagWire i)) = false at h
  rw [old_tag_work,embed_work] at h
  exact h

lemma QMAPerfectCompleteness.Main.CertificateBlockCorrectness.tagged_scratch (s : Key V → Basis (work V)) (hs : Prepared V s) (p : Logical V) :
    (layoutOf V).ScratchClean (old V (embed V (taggedSpace V s) p)) := by
  intro i
  change embed V (taggedSpace V s) p (oldEmbedding V ((layoutOf V).scratchWire i)) = false
  rw [old_scratch_work,embed_work]
  change (if h : 11+i.val<6 then _ else s (key V p) _) = false
  rw [dif_neg (by omega)]
  have h := hs.old_clean p ⟨11+i.val,by have := i.isLt; dsimp only [Layout.work]; omega⟩
  change embed V s p (oldEmbedding V ((layoutOf V).scratchWire i)) = false at h
  rw [old_scratch_work,embed_work] at h
  exact h

lemma QMAPerfectCompleteness.Main.CertificateBlockCorrectness.tagged_midClean (s : Key V → Basis (work V)) (hs : Prepared V s) (p : Logical V) :
    (layoutOf V).MidClean (old V (embed V (taggedSpace V s) p)) :=
  ⟨tagged_scratch V s hs p,tagged_aux V s hs p 10 (by decide)⟩



lemma QMAPerfectCompleteness.Main.CertificateBlockCorrectness.mid_action (s : Key V → Basis (work V)) (hs : Prepared V s) (p : Logical V) :
    (CertificateOldPrograms.midProgram V).action (embed V (taggedSpace V s) p) =
      embed V (taggedSpace V s) (midLogical V p) := by
  rw [CertificateOldPrograms.mid_action _ _ (tagged_aux V s hs p 6 (by decide))]
  simp only [CertificateOldPrograms.flag]
  change Function.update (embed V (taggedSpace V s) p) (oldEmbedding V (layoutOf V).flagWire) _ = _
  have hv : (layoutOf V).clockValue (CertificateOldPrograms.oldState V (embed V (taggedSpace V s) p)) =
      p.1.2.1.val :=
    (BlockImplements.clockValue_eq_decode V _).trans
      (congrArg (fun q : V.BlockReg (indexQubits V) => q.2.1.val) (embed_decode V (taggedSpace V s) p))
  have hc := congrArg (fun t : ℕ => decide (t < ell V.proofQubits)) hv
  rw [embed_old_flag,tagged_core V s p 3 (by decide),hc,embed_old_wire,embed_update_flag]
  rfl

theorem solution (s : Key V → Basis (work V)) (hs : Prepared V s) :
    Transports (embed V (taggedSpace V s)) (embed V (taggedSpace V s))
      (circuitMatrix (CertificateOldPrograms.midProgram V).gates) (basisMap (midLogical V)) := by
  apply transports_classical
  intro y p
  rw [(CertificateOldPrograms.midProgram V).sound y _ (tagged_midClean V s hs p),mid_action V s hs]
