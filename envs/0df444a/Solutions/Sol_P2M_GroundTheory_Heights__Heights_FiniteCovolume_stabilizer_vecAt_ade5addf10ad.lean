-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_stabilizer_vecAt_ade5addf10ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:07:07.975974+00:00
-- url     : https://prove2.me/submissions/fecb22e2-f20f-43a6-8166-c604dbea0ee0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAt_injective_5e91e8c6ade2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_smul_vecAt_b12bc12835a1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
attribute [local instance] archMulAction
variable [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W)
    (y : W) : MulAction.stabilizer (archLatticeGroup h v La) (vecAt v y) =
      (vecStabGroup h v La y).subgroupOf (archLatticeGroup h v La) := by
  ext ⟨γ, hγ⟩
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.1 hγ
  change archEmbed h v δ • vecAt v y = vecAt v y ↔ _
  constructor
  · intro he
    rw [archEmbed_smul_vecAt] at he
    exact Subgroup.mem_map.2 ⟨⟨δ, hδ⟩, MulAction.mem_stabilizer_iff.2 (vecAt_injective v he), rfl⟩
  · rintro ⟨ε, hε, he⟩
    have he' : archEmbed h v (ε : h.unitaryGroup) = archEmbed h v δ := he
    rw [← he', archEmbed_smul_vecAt]
    exact congrArg (vecAt v) (MulAction.mem_stabilizer_iff.1 hε)
end GroundTheory.Heights₂.Heights.FiniteCovolume
