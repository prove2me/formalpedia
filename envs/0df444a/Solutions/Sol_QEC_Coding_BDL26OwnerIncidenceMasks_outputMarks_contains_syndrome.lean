-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.outputMarks_contains_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:54:10.650635+00:00
-- url     : https://prove2.me/submissions/f20bfb61-a857-4991-be97-592f91e194a0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
    {V : Type} [Fintype V] [DecidableEq V]
    (O : AssemblyStepOutput D i) (synOwner : C2 i.succ → V)
    (pieceOwner : Fin O.localComponents.length → V)
    (p : C2 i.succ) (hp : O.input.val p ≠ 0) :
    synOwner p ∈ outputMarks O synOwner pieceOwner :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨p, rfl, hp⟩⟩
end QEC.Coding.BDL26OwnerIncidenceMasks
