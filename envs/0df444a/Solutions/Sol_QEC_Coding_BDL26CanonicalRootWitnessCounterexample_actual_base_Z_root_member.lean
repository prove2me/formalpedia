-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_base_Z_root_member
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:36:51.130199+00:00
-- url     : https://prove2.me/submissions/e1238699-efb6-461f-9282-d40192b191d9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_markedAdjacent_iff
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_baseMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_rootComponent
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_parented_base_root_path
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_root_marked_iff_parented_base
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_markedAdjacent_iff
import Theorems.Thm_QEC_Coding_BDL26UniformTopOwnerIsolation_markedAdjacent_iff
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26TopOwnerIsolation.markedAdjacent_iff
attribute [local simp] QEC.Coding.BDL26UniformTopOwnerIsolation.markedAdjacent_iff


section
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
private theorem zVertex_eq (S : OddScale) (n : Nat) (z : (state S n).presentation.Z) :
    zVertex S n z = @Vertex.z (state S n).presentation z := rfl
private theorem actualBaseNode_physical (S : OddScale) (v : GraphVertex S 2) :
    actualBaseNode S v = BDL26CanonicalHistoryMarks.physicalNode S 2 (0 : LevelIndex 2) v := rfl
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
private theorem base_r2_owner (S : OddScale) :
    BDL26CanonicalHistoryMarks.baseSyndromeOwner S 2 (r2 S) =
      zVertex S 1 (baseRetainedZ S) := by
  change @Vertex.z (state S 1).presentation (baseRetainedZ S) =
    zVertex S 1 (baseRetainedZ S)
  exact (zVertex_eq S 1 (baseRetainedZ S)).symm
private theorem base_retained_parent (S : OddScale) :
    parent S 1 (zVertex S 1 (baseRetainedZ S)) = some (zVertex S 0 (seedZ S)) := by
  change rxParent baseTannerSquarePresentation S
    (Vertex.z (Sum.inr (seedZ S,0))) = some (Vertex.z (seedZ S))
  rfl
private theorem actual_base_retained_marked (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S) :
    zVertex S 1 (baseRetainedZ S) ∈ BDL26CanonicalHistoryMarks.baseMarks S 2 sigma := by
  have hvalue : (gamma2 S).val (r2 S) ≠ 0 :=
    fun hz => one_ne_zero ((gamma2_at_r2 S).symm.trans hz)
  have heval : (BDL26CanonicalHistoryMarks.baseInput S 2 sigma).val (r2 S) =
      (gamma2 S).val (r2 S) :=
    congrArg (fun word :
      (BDL26CanonicalHistoryMarks.Data S 2).family.Syndrome (0 : LevelIndex 2) =>
        word.val (r2 S)) hbase
  have hnonzero : (BDL26CanonicalHistoryMarks.baseInput S 2 sigma).val (r2 S) ≠ 0 :=
    fun hz => hvalue (heval.symm.trans hz)
  exact (BDL26CanonicalHistoryMarks.mem_baseMarks S 2 sigma
    (zVertex S 1 (baseRetainedZ S))).mpr
      (Or.inl ⟨r2 S,base_r2_owner S,hnonzero⟩)
private theorem originalRootPath_semantics (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (w : BDL26CanonicalHistoryMarks.Node S n)
    (hp : OriginalRootPath S n sigma w) :
    BDL26CanonicalHistoryMarks.root S n ∈ BDL26CanonicalHistoryMarks.marks S n sigma ∧
      w ∈ BDL26CanonicalHistoryMarks.marks S n sigma ∧
      Relation.ReflTransGen (BDL26CanonicalHistoryMarks.markedAdjacent S n sigma)
        w (BDL26CanonicalHistoryMarks.root S n) := by
  induction hp with
  | rooted hr =>
      exact ⟨hr,hr,Relation.ReflTransGen.refl⟩
  | prepend he _ ih =>
      have hm := (BDL26CanonicalHistoryMarks.markedAdjacent_iff S n sigma _ _).mp he
      exact ⟨ih.1,hm.2.1,(Relation.ReflTransGen.single he).trans ih.2.2⟩
private theorem originalRootPath_prepend_relation (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (u v : BDL26CanonicalHistoryMarks.Node S n)
    (hp : Relation.ReflTransGen (BDL26CanonicalHistoryMarks.markedAdjacent S n sigma) u v) :
    OriginalRootPath S n sigma v → OriginalRootPath S n sigma u := by
  induction hp with
  | refl =>
      exact fun hv => hv
  | tail _ he ih =>
      intro hv
      exact ih (@OriginalRootPath.prepend S n sigma _ _ he hv)
private theorem originalRootPath_congr (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    {u v : BDL26CanonicalHistoryMarks.Node S n} (he : u=v)
    (hp : OriginalRootPath S n sigma v) : OriginalRootPath S n sigma u := by
  cases he
  exact hp
private theorem originalRootPath_mem_iff (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (w : BDL26CanonicalHistoryMarks.Node S n) :
    OriginalRootPath S n sigma w ↔
      w ∈ BDL26CanonicalHistoryMarks.rootComponent S n sigma := by
  constructor
  · intro hp
    exact (BDL26CanonicalHistoryMarks.mem_rootComponent S n sigma w).mpr
      (originalRootPath_semantics S n sigma w hp)
  · intro hw
    obtain ⟨hr,_hm,hp⟩ := (BDL26CanonicalHistoryMarks.mem_rootComponent S n sigma w).mp hw
    exact originalRootPath_prepend_relation S n sigma w
      (BDL26CanonicalHistoryMarks.root S n) hp (@OriginalRootPath.rooted S n sigma hr)
private theorem originalRootPath_parented_base (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (v : GraphVertex S 2) (hv : v ∈ BDL26CanonicalHistoryMarks.baseMarks S n sigma)
    (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    OriginalRootPath S n sigma (BDL26CanonicalHistoryMarks.physicalNode S n 0 v) := by
  have hr := (BDL26CanonicalHistoryMarks.root_marked_iff_parented_base S n sigma).mpr
    ⟨v,hv,u,hp⟩
  have hpath := BDL26CanonicalHistoryMarks.parented_base_root_path S n sigma v hv u hp
  exact originalRootPath_prepend_relation S n sigma _
    (BDL26CanonicalHistoryMarks.root S n) hpath (@OriginalRootPath.rooted S n sigma hr)
private theorem actual_base_original_root_path (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S) :
    OriginalRootPath S 2 sigma (actualBaseNode S (zVertex S 1 (baseRetainedZ S))) := by
  have hmarked := actual_base_retained_marked S sigma hbase
  have hpath := originalRootPath_parented_base S 2 sigma
    (zVertex S 1 (baseRetainedZ S)) hmarked
    (zVertex S 0 (seedZ S)) (base_retained_parent S)
  exact originalRootPath_congr S 2 sigma
    (actualBaseNode_physical S (zVertex S 1 (baseRetainedZ S))) hpath
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
end

set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S) :
    @Membership.mem.{0, 0} (BDL26CanonicalHistoryMarks.Node S 2)
      (Finset (BDL26CanonicalHistoryMarks.Node S 2))
      (@SetLike.instMembership.{0, 0} (Finset (BDL26CanonicalHistoryMarks.Node S 2))
        (BDL26CanonicalHistoryMarks.Node S 2)
        (@Finset.instSetLike.{0} (BDL26CanonicalHistoryMarks.Node S 2)))
      (BDL26CanonicalHistoryMarks.rootComponent S 2 sigma)
      (actualBaseNode S (zVertex S 1 (baseRetainedZ S))) := by
  have hpath := actual_base_original_root_path S sigma hbase
  have hcomponent :
      (fun w : BDL26CanonicalHistoryMarks.Node S 2 =>
        w ∈ BDL26CanonicalHistoryMarks.rootComponent S 2 sigma) =
      OriginalRootPath S 2 sigma := by
    funext w
    exact propext ((originalRootPath_mem_iff S 2 sigma w).symm)
  have hnode := congrFun hcomponent (actualBaseNode S (zVertex S 1 (baseRetainedZ S)))
  rw [hnode]
  exact hpath
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
