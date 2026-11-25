-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.exists_compact_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:43.337038+00:00
-- url     : https://prove2.me/submissions/d4c00408-19b3-4239-80c8-582a32a71ae1

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActInt
import Theorems.Thm_PositivityTheory_ThK_LinAct_norm_char
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_GoodInh_exists_goodChar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory ValuativeRel Topology Filter PositivityTheory.ThKH.Evl
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.LinAct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ ι : Type} [Fintype κ] [Fintype ι] {ψ : AddChar k ℂ}
omit [Invertible (2 : k)]
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution (hc : Continuous ψ) (h1 : ψ ≠ 1) {U : Set (ι → k)} (hU : U ∈ 𝓝 (0 : ι → k)) :
    ∃ C : Set (ι → k), IsCompact C ∧ ∀ x, (∀ y ∈ U, ψ (x ⬝ᵥ y) = 1) → x ∈ C := by
  classical
  obtain ⟨u, hu⟩ := (GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar k).2 ψ hc (norm_char hc) h1
  have : ∀ i, ∃ v : kˣ, ∀ y ∈ 𝒪[k], Pi.single i ((v : k) * y) ∈ U := fun i =>
    hu.basis ((fun t => (Pi.single i t : ι → k)) ⁻¹' U)
      ((continuous_single (A := fun _ => k) i).continuousAt.preimage_mem_nhds (by simpa using hU))
  choose v hv using this
  refine ⟨Set.univ.pi fun i => (fun t => (u : k) * ((v i)⁻¹ : kˣ) * t) '' (𝒪[k] : Set k),
    isCompact_univ_pi fun i => hu.compact.image (continuous_const.mul continuous_id), fun x hx i _ => ?_⟩
  refine ⟨_, (hu.ann (x i * v i)).1 fun y hy => ?_, ?_⟩
  · simpa [mul_assoc] using hx _ (hv i y hy)
  · simp only [Units.val_inv_eq_inv_val]
    field_simp
end PositivityTheory.ThK.LinAct
