-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.hop_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:46.195938+00:00
-- url     : https://prove2.me/submissions/d3dae34f-8d4a-441f-a177-4c365856fdb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_mem_fixed_iff
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_finiteIndex_stabK
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_hop_eq_reps
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_reps_spec
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_comm_core
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.Rg.BcB.F.EigA
theorem _root_.solution {K : Subgroup G} (hK : GelPair K) (ρ : Representation ℂ G V) (g h : G) {v : V}
    (hv : v ∈ fixed ρ K) : hop ρ K g (hop ρ K h v) = hop ρ K h (hop ρ K g v) := by
  obtain ⟨hfin, τ, hmul, hinv, hdc, hτK⟩ := hK
  haveI := finiteIndex_stabK (hfin g)
  haveI := finiteIndex_stabK (hfin h)
  letI := Fintype.ofFinite (K ⧸ stabK K g)
  letI := Fintype.ofFinite (K ⧸ stabK K h)
  simp only [hop_eq_reps]
  obtain ⟨a1, a2⟩ := reps_spec K g
  obtain ⟨b1, b2⟩ := reps_spec K h
  exact comm_core ρ K τ hmul hinv hdc hτK g h _ _ a1 a2 b1 b2 v (mem_fixed_iff.1 hv)
end PositivityTheory.Rg.BcB.F.EigA
