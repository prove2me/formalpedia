-- Prove2me | solution 1 for PositivityTheory.ThKH.Evl.exists_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:38.851672+00:00
-- url     : https://prove2.me/submissions/7de6d336-0379-4606-813f-83359ac28603

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CyclicAndLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Theorems.Thm_PositivityTheory_ThKH_Evl_t2Space_local_field_bis
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
import Theorems.Thm_GlobalTheory_WeilM_nonarch_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Evl
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ : Type} [Fintype κ] {ψ : AddChar k ℂ}
omit [Invertible (2 : k)]
namespace PositivityTheory.ThKH.Evl
theorem _root_.solution (κ : Type) [Fintype κ] : ∃ U : AddSubgroup (κ → k), IsCompact (U : Set (κ → k)) ∧
    (U : Set (κ → k)).indicator (fun _ => (1 : ℂ)) ∈ SB (κ → k) := by
  have := t2Space_local_field_bis (k := k)
  have := nonarch_pi k κ
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : κ → k)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean K hK0
  have hcl : IsClopen (V : Set (κ → k)) := V.isClopen
  have hcp : IsCompact (V : Set (κ → k)) := hK.of_isClosed_subset hcl.1 hV
  exact ⟨V, hcp, (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hcl).isLocallyConstant,
    HasCompactSupport.intro hcp fun x hx => Set.indicator_of_notMem hx _⟩
end PositivityTheory.ThKH.Evl
