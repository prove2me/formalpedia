-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.PCD.good_of_joint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:50:59.868844+00:00
-- url     : https://prove2.me/submissions/32b9c2a1-c4e4-4957-944c-9ed5df296582

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_Good_continuousOn
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_slice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.PCD
variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {Ω : Set F}
namespace PositivityTheory.Rg.Sw.HSt.PCD
theorem _root_.solution (hΩ : IsOpen Ω) (k : F × V → E) (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (v : X → V)
    (hv : Continuous v) (h : X → ℂ) (hh : Continuous h)
    (hsupp : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, k (x', v u) = 0) :
    Good Ω (fun x u => h u • k (x, v u)) := by
  have hsl : ∀ u, ContDiffOn ℝ ∞ (fun x => k (x, v u)) Ω := fun u =>
    hk.comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
  refine ⟨fun u => (hsl u).const_smul (h u), fun N => ?_, fun x hx => ?_⟩
  · have hS : IsOpen (Ω ×ˢ (univ : Set V)) := hΩ.prod isOpen_univ
    have hcont : ContinuousOn (fun q : F × V => iteratedFDeriv ℝ N k q) (Ω ×ˢ univ) := by
      have := hk.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) hS.uniqueDiffOn
      exact this.congr fun q hq => (iteratedFDerivWithin_of_isOpen N hS hq).symm
    let hL := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := E)
      (fun _ : Fin N => ContinuousLinearMap.inl ℝ F V)
    have hc2 : ContinuousOn (fun p : F × X => h p.2 • (hL (iteratedFDeriv ℝ N k (p.1, v p.2)))) (Ω ×ˢ univ) := by
      refine (hh.comp continuous_snd).continuousOn.smul (hL.continuous.comp_continuousOn ?_)
      exact hcont.comp (continuous_fst.prodMk (hv.comp continuous_snd)).continuousOn fun p hp => ⟨hp.1, mem_univ _⟩
    refine hc2.congr fun p hp => ?_
    have hx : p.1 ∈ Ω := hp.1
    simp only
    rw [iteratedFDeriv_const_smul_apply' ((hsl p.2).contDiffAt (hΩ.mem_nhds hx) |>.of_le (by exact_mod_cast le_top)),
      slice hΩ hk N hx (v p.2)]
    rfl
  · obtain ⟨W, hW, C, hC, hKW⟩ := hsupp x hx
    obtain ⟨W', hW'W, hW'o, hxW'⟩ := mem_nhds_iff.1 hW
    exact ⟨W', hW'o, hxW', C, hC, fun x' hx' u hu => by simp [hKW x' (hW'W hx') u hu]⟩
end PositivityTheory.Rg.Sw.HSt.PCD
