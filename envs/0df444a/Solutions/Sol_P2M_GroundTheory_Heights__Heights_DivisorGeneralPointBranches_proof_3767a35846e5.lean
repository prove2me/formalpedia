-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DivisorGeneralPointBranches_proof_3767a35846e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:55:48.005618+00:00
-- url     : https://prove2.me/submissions/27e0e297-7174-478e-8dd4-36d87ad50caa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorOneComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorGeneralPointBranches
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorGeneralPointBranches_quotient_inf_dim_lt_0ab1cb66b420

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches
namespace GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches
theorem _root_.solution (hOne : DivisorOneComponent.Statement) (hBr : DivisorBranches.Statement) :
    DivisorGeneralPointBranches.Statement := by
  intro n d J u hJ hdim hu
  obtain ⟨I₁, hle₁, hdim₁, hI₁⟩ := hOne n d J u hJ hdim hu
  obtain ⟨I₂, hle₂, hdim₂, hI₂⟩ := hBr n d J u hJ hdim hu
  refine ⟨I₁ ⊓ I₂, le_inf hle₁ hle₂, quotient_inf_dim_lt hdim₁ hdim₂, ?_⟩
  intro q hqJ hqu hqI
  have hq₁ : q ∉ zeroSet I₁ := fun h => hqI fun f hf => h f (Ideal.mem_inf.1 hf).1
  have hq₂ : q ∉ zeroSet I₂ := fun h => hqI fun f hf => h f (Ideal.mem_inf.1 hf).2
  obtain ⟨W, hW, hqW, huniq, hnear⟩ := hI₁ q hqJ hqu hq₁
  obtain ⟨m, γ, ord, π, hcov, ⟨N, hN, hsl⟩, hpair, hord, hbij⟩ := hI₂ q hqJ hqu hq₂
  refine ⟨W, hW, hqW, huniq, hnear, m, γ, ord, π, hcov, ⟨N, hN, fun b x hx => ?_⟩, hpair, hord, hbij⟩
  have hKW : J ⊔ Ideal.span {linForm u} ≤ W := hW.1.2
  refine hsl x ⟨fun f hf => hx.1 f (hKW (Ideal.mem_sup_left hf)), hx.2⟩ ?_ b
  have hx0 := hx.1 _ (hKW (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  simpa [linForm, linEval] using hx0
end GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches
