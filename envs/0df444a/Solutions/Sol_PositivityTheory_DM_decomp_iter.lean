-- Prove2me | solution 1 for PositivityTheory.DM.decomp_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:20.937791+00:00
-- url     : https://prove2.me/submissions/ebb963c4-25d3-4f53-9a1f-5715886d0deb

import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_DixmierMalliavin_DecompDirection
import Theorems.Thm_PositivityTheory_DM_decomp_direction
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_revProdExp_zero
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_sum_integral_cons_kernel
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_contDiff_cons_kernel
import Theorems.Thm_GroundTheory_Automorphic_tsupport_cons_kernel
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open PositivityTheory PositivityTheory.DM
open GroundTheory.Automorphic GroundTheory.Automorphic.IsExpLieAlgebra
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory Metric
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
namespace PositivityTheory.DM
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) : ∀ {d : ℕ} (X : Fin d → 𝔤) (f : G → ℂ),
    (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) → HasCompactSupport f →
    ∃ (m : ℕ) (F : Fin m → G → ℂ) (K : Fin m → (Fin d → ℝ) → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (F i)) ∧
        tsupport (F i) ⊆ tsupport f) ∧
      (∀ i, ContDiff ℝ ∞ (K i) ∧ tsupport (K i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ x, f x = ∑ i, ∫ t, K i t * F i (h.revProdExp X t * x)
  | 0, X, f, hf, hfc => by
    refine ⟨1, fun _ => f, fun _ _ => 1, fun _ => ⟨hf, subset_rfl⟩, fun _ => ⟨contDiff_const, ?_⟩,
      fun x => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp [h.revProdExp_zero, hv]
  | d + 1, X, f, hf, hfc => by
    let := h.chartedSpace
    obtain ⟨f₁, hf₁, hf₁c, g, k, hg, hk, hgs, hks, hdec⟩ :=
      decomp_direction h hf hfc (X 0) hε
    obtain ⟨m₁, F₁, K₁, hF₁, hK₁, hd₁⟩ := solution hε (Fin.tail X) f₁ hf₁ (hfc.of_isClosed_subset (isClosed_tsupport _) hf₁c)
    obtain ⟨m₂, F₂, K₂, hF₂, hK₂, hd₂⟩ := solution hε (Fin.tail X) f hf hfc
    refine ⟨m₁ + m₂, Fin.append F₁ F₂,
      Fin.append (fun i t => g (t 0) * K₁ i (Fin.tail t)) (fun i t => k (t 0) * K₂ i (Fin.tail t)),
      ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using And.intro (hF₁ i).1 ((hF₁ i).2.trans hf₁c)
      · simpa only [Fin.append_right] using hF₂ i
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        exact ⟨contDiff_cons_kernel hg (hK₁ i).1, tsupport_cons_kernel hε.le hgs (hK₁ i).2⟩
      · simp only [Fin.append_right]
        exact ⟨contDiff_cons_kernel hk (hK₂ i).1, tsupport_cons_kernel hε.le hks (hK₂ i).2⟩
    · intro x
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hdec x]
      congr 1
      · exact (h.sum_integral_cons_kernel X hε.le hg.continuous hgs (fun i => (hK₁ i).1.continuous)
          (fun i => (hK₁ i).2) (fun i => (hF₁ i).1.continuous) hd₁ x).symm
      · exact (h.sum_integral_cons_kernel X hε.le hk.continuous hks (fun i => (hK₂ i).1.continuous)
          (fun i => (hK₂ i).2) (fun i => (hF₂ i).1.continuous) hd₂ x).symm
end PositivityTheory.DM
