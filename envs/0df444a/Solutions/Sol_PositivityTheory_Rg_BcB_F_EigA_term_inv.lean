-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.term_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:44.893136+00:00
-- url     : https://prove2.me/submissions/1cfa9735-d41a-4947-9b6d-3ce0850e8d37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_mem_fixed_iff
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_mem_stabK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.Rg.BcB.F.EigA
theorem _root_.solution {ρ : Representation ℂ G V} {K : Subgroup G} {g : G} {v : V} (hv : v ∈ fixed ρ K) :
    ∀ (x : K), ∀ h ∈ stabK K g, ρ (((x * h : K)) : G) (ρ g v) = ρ (x : G) (ρ g v) := by
  intro x h hh
  have h1 := (mem_fixed_iff.1 hv) _ (mem_stabK.1 hh)
  have e : ρ (h : G) (ρ g v) = ρ g v := by
    have : (h : G) * g = g * (g⁻¹ * (h : G) * g) := by group
    rw [← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply, h1]
  rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, e]
end PositivityTheory.Rg.BcB.F.EigA
