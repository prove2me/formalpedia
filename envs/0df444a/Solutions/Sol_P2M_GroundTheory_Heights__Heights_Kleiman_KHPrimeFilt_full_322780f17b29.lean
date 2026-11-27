-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_full_322780f17b29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:01:30.084397+00:00
-- url     : https://prove2.me/submissions/8274e4fc-3538-4f76-b1c9-d186585201a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isMultiHomogIdeal_of_isHomogeneous_45acc6349d53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_next_mem_80fce6c3a8f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_next_spec_72b93845cbd1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_seq_isGradedSub_971d8254db49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_seq_eq_span_b0b2775f0156
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_exists_seq_eq_top_3b904fd29028
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_image_fin_lt_3e118475c124
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_range_fin_a26432bcb02f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open KHPrimeFilt
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace KHPrimeFilt
theorem _root_.solution : PrimeFiltStatement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 hS hfin hgr
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ := hgr.1.chooseDecomposition
  have hex : ∃ n, seq ι 𝓜 n = ⊤ := exists_seq_eq_top hgr
  classical
  refine ⟨Nat.find hex, fun j => gen ι 𝓜 j, fun j => (next ι 𝓜 (seq ι 𝓜 j)).2,
    fun j => colon (seq ι 𝓜 j) (gen ι 𝓜 j), ?_⟩
  unfold IsPrimeFilt
  refine ⟨fun j => next_mem ι 𝓜 _, fun j => ?_, fun j p => ?_, ?_⟩
  · have hne : seq ι 𝓜 j ≠ ⊤ := Nat.find_min hex j.2
    obtain ⟨hp, hh⟩ := next_spec hgr (seq_isGradedSub hgr j) hne
    refine ⟨hp, isMultiHomogIdeal_of_isHomogeneous hh, fun p hp' => ?_⟩
    rw [mem_colon, Module.mem_annihilator.mp hp']
    exact Submodule.zero_mem _
  · rw [image_fin_lt, ← seq_eq_span]
    exact mem_colon.symm
  · rw [range_fin, ← seq_eq_span]
    exact Nat.find_spec hex
end KHPrimeFilt
end GroundTheory.Heights₂.Heights.Kleiman
