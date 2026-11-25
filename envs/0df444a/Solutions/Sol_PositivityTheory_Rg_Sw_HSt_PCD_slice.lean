-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.PCD.slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:39:40.709836+00:00
-- url     : https://prove2.me/submissions/09b5ef52-84f5-4d19-afd5-0ae6523afc81

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD

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
omit [FiniteDimensional ℝ F]
namespace PositivityTheory.Rg.Sw.HSt.PCD
theorem _root_.solution (hΩ : IsOpen Ω) {k : F × V → E} (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (N : ℕ) {x : F} (hx : x ∈ Ω) (w : V) :
    iteratedFDeriv ℝ N (fun x => k (x, w)) x =
      (iteratedFDeriv ℝ N k (x, w)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ F V) := by
  set f' : F × V → E := fun p => k (p + (0, w))
  have hS : IsOpen (Ω ×ˢ (univ : Set V)) := hΩ.prod isOpen_univ
  have hf' : ContDiffOn ℝ ∞ f' (Ω ×ˢ univ) := by
    refine hk.comp (contDiffOn_id.add contDiffOn_const) fun p hp => ?_
    exact ⟨by simpa using hp.1, mem_univ _⟩
  have hpre : (ContinuousLinearMap.inl ℝ F V) ⁻¹' (Ω ×ˢ univ) = Ω := by ext y; simp
  have h1 := ContinuousLinearMap.iteratedFDerivWithin_comp_right (ContinuousLinearMap.inl ℝ F V) hf'
    hS.uniqueDiffOn (by rw [hpre]; exact hΩ.uniqueDiffOn) (x := x) (by simpa using hx) (i := N) (by exact_mod_cast le_top)
  rw [hpre, iteratedFDerivWithin_of_isOpen N hΩ hx, iteratedFDerivWithin_of_isOpen N hS (by simpa using hx)] at h1
  have h2 : (f' ∘ ContinuousLinearMap.inl ℝ F V) = fun x => k (x, w) := by
    funext y; simp [f']
  rw [h2] at h1
  rw [h1]
  congr 1
  have h3 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := k) N ((0 : F), w) (ContinuousLinearMap.inl ℝ F V x)
  simpa using h3
end PositivityTheory.Rg.Sw.HSt.PCD
