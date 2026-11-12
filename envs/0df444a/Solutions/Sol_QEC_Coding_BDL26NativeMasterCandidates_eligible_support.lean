-- Prove2me | solution 1 for QEC.Coding.BDL26NativeMasterCandidates.eligible_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:20:11.668732+00:00
-- url     : https://prove2.me/submissions/8ccd98ad-139f-4008-b200-df2d957ffe12

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Mathlib.Data.List.Sublists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeMasterCandidates
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeMasterCandidates
theorem _root_.solution (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ)
    (e : Event (P S n) J r) :
    ∃!row : FourCodes × Option (List (Index S n)),row∈Rows S n ∧
      Rep S n row.1 (eventToMaster (P S n) J r e) ∧
      ∃U,row.2=some U ∧ U.Nodup ∧ U.length≤12 ∧
        ∀i,i∈U ↔ BDL26NativeStateRows.decode S n i∈eventSupport (P S n) J r e := by
  obtain ⟨row,hr,hu⟩ := master_complete_unique S n (eventToMaster (P S n) J r e)
  refine ⟨row,⟨hr.1,hr.2,?_⟩,?_⟩
  · obtain ⟨m,U,hU,hm,_,hUn,hUl,hUm⟩ := master_sound_support S n row hr.1
    have he := Rep_unique S n row.1 m _ hm hr.2
    subst m
    exact ⟨U,hU,hUn,hUl,hUm⟩
  · intro other ho
    exact hu other ⟨ho.1,ho.2.1⟩
end QEC.Coding.BDL26NativeMasterCandidates
