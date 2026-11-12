-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_unparented_top_not_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:52:25.111075+00:00
-- url     : https://prove2.me/submissions/6a9d0b75-8982-4d33-876d-9015d4e3f8b8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_no_actual_top_Z_marked_neighbor
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_markedAdjacent_iff
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_rootComponent
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_markedAdjacent_iff
import Theorems.Thm_QEC_Coding_BDL26UniformTopOwnerIsolation_markedAdjacent_iff
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
private theorem no_path_of_no_outgoing {N : Type} (R : N → N → Prop)
    (a r : N) (hne : a ≠ r) (hout : ∀ w, ¬ R a w) :
    ¬ Relation.ReflTransGen R a r := by
  intro hpath
  rcases hpath.cases_head with heq | ⟨next,hedge,_⟩
  · exact hne heq
  · exact hout next hedge
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
private theorem canonical_not_root (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (u : BDL26CanonicalHistoryMarks.Node S n)
    (hne : u ≠ BDL26CanonicalHistoryMarks.root S n)
    (hout : ∀ w, BDL26CanonicalHistoryMarks.markedAdjacent S n sigma u w → False) :
    u ∉ BDL26CanonicalHistoryMarks.rootComponent S n sigma := by
  intro hk
  obtain ⟨_,_,hpath⟩ := (BDL26CanonicalHistoryMarks.mem_rootComponent S n sigma u).mp hk
  exact no_path_of_no_outgoing (BDL26CanonicalHistoryMarks.markedAdjacent S n sigma)
    u (BDL26CanonicalHistoryMarks.root S n) hne hout hpath
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
    (z : (state S 3).presentation.Z)
    (hp : parent S 3 (zVertex S 3 z) = none) :
    actualTopNode S (zVertex S 3 z) ∉
      BDL26CanonicalHistoryMarks.rootComponent S 2 sigma := by
  have hne : actualTopNode S (zVertex S 3 z) ≠
      BDL26CanonicalHistoryMarks.root S 2 := by
    intro heq
    have hl := congrArg (fun w : BDL26CanonicalHistoryMarks.Node S 2 => w.1.val) heq
    change 4 = 0 at hl
    omega
  exact canonical_not_root S 2 sigma (actualTopNode S (zVertex S 3 z)) hne
    (fun w hedge => no_actual_top_Z_marked_neighbor S sigma z hp w
      ((BDL26CanonicalHistoryMarks.markedAdjacent_iff S 2 sigma _ _).mp hedge).2.2
      ((BDL26CanonicalHistoryMarks.markedAdjacent_iff S 2 sigma _ _).mp hedge).1)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
