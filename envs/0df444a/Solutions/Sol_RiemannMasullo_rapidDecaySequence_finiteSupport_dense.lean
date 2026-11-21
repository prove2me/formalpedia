-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequence_finiteSupport_dense
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:50:37.943535+00:00
-- url     : https://prove2.me/submissions/f3c5cc0f-5fc1-44d1-bc18-6c84f5e32adf

-- New supporting theorem for the rapidly decreasing lattice sequences of Appendix D.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L545-L547
import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
import Theorems.Thm_RiemannMasullo_mem_rapidDecaySequenceSubmodule_of_finiteSupport
import Theorems.Thm_RiemannMasullo_rapidDecaySequence_withSeminorms
import Mathlib
open RiemannMasullo Set Filter Topology
open scoped ENNReal

theorem solution (r : ℕ) :
    Dense {s : RapidDecaySequence r | (Function.support (fun a => s a)).Finite} := by
  classical
  intro s
  let f (S : Finset (Fin r → ℤ)) : (Fin r → ℤ) → ℂ := (↑S : Set (Fin r → ℤ)).indicator (fun a => s a)
  have hs (S : Finset (Fin r → ℤ)) : (Function.support (f S)).Finite :=
    S.finite_toSet.subset Set.support_indicator_subset
  let u (S : Finset (Fin r → ℤ)) : RapidDecaySequence r :=
    (⟨f S,mem_rapidDecaySequenceSubmodule_of_finiteSupport _ (hs S)⟩ : rapidDecaySequenceSubmodule r)
  apply mem_closure_of_tendsto (f:=u) (b:=atTop)
  · apply (rapidDecaySequence_withSeminorms.tendsto_nhds u s).mpr
    intro j ε hε
    let w (a : (Fin r → ℤ)) : ℝ≥0∞ :=
      (1 + (‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖₊ : ℝ≥0∞)) ^ j *
        (‖s a‖₊ : ℝ≥0∞)
    have hf : (∑' a, w a) ≠ ⊤ := (s.property j).ne
    have ht := ENNReal.tendsto_tsum_compl_atTop_zero hf
    have hlim : Tendsto (fun S : Finset (Fin r → ℤ) => (∑' a : {x // x ∉ S}, w a).toReal) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.toReal_zero] using (ENNReal.continuousAt_toReal (x:=0) (by simp)).tendsto.comp ht
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with S hS
    change (rapidDecaySequenceBound j (f S - s.val)).toReal < ε
    have hident : rapidDecaySequenceBound j (f S - s.val) =
        ∑' a : ↥((↑S : Set (Fin r → ℤ))ᶜ), w a := by
      unfold rapidDecaySequenceBound
      rw [tsum_subtype ((↑S : Set (Fin r → ℤ))ᶜ) w]
      apply tsum_congr
      intro a
      by_cases ha : a ∈ S <;> simp [w,f,Set.indicator_apply,ha]
    rw [hident]
    exact hS
  · exact Eventually.of_forall hs
