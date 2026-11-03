-- Prove2me | solution 1 for PrivLearn.LocalSim.avg_is_private
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:09:16.734192+00:00
-- url     : https://prove2.me/submissions/95fce110-e594-4c76-a909-26309256ed9a

import Mathlib
import Definitions.Def_PrivLearn_LocalSim_Privacy
import Definitions.Def_PrivLearn_LocalSim_Simulation

open MeasureTheory PrivLearn.LocalSim

private lemma randomizer_is_local_aux {Dom : Type*} (g : Dom → ℝ) (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (hg : ∀ u, |g u| ≤ b) :
    IsLocalRandomizer (randomizerLaw g (2 * b / ε)) ε := by
  classical
  intro u u' S hS
  set s := 2 * b / ε with hs
  have hspos : 0 < s := by positivity
  set p : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp (-|x| / s) / (2 * s)) with hp
  have hpm : Measurable p := by
    apply ENNReal.measurable_ofReal.comp
    exact ((Real.measurable_exp.comp ((measurable_id.abs.neg).div_const s)).div_const _)
  have key : ∀ c : ℝ, ((PrivLearn.Generic.laplace s).map fun η => c + η) S =
      ∫⁻ x, (if c + x ∈ S then p x else 0) := by
    intro c
    have hT : MeasurableSet ((fun η => c + η) ⁻¹' S) := measurable_const_add c hS
    rw [Measure.map_apply (measurable_const_add c) hS]
    unfold PrivLearn.Generic.laplace
    rw [withDensity_apply _ hT, ← lintegral_indicator hT]
    simp only [Set.indicator_apply, Set.mem_preimage, hp]
  unfold randomizerLaw
  rw [key, key]
  set c := g u
  set c' := g u'
  set d := c' - c with hd
  have hdb : |d| ≤ ε * s := by
    have h1 := hg u; have h2 := hg u'
    have : ε * s = 2 * b := by rw [hs]; field_simp
    rw [this, hd]
    calc |c' - c| ≤ |c'| + |c| := abs_sub _ _
      _ ≤ 2 * b := by linarith
  have hshift : ∫⁻ x, (if c + x ∈ S then p x else 0) =
      ∫⁻ x, (if c' + x ∈ S then p (x + d) else 0) := by
    rw [← lintegral_add_right_eq_self _ d]
    congr 1
    funext x
    rw [show c + (x + d) = c' + x by rw [hd]; ring]
  rw [hshift, ← lintegral_const_mul _ (by
    exact Measurable.ite (measurable_const_add c' hS) hpm measurable_const)]
  apply lintegral_mono
  intro x
  dsimp only
  split_ifs
  · simp only [hp]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hpt : Real.exp (-|x + d| / s) ≤ Real.exp ε * Real.exp (-|x| / s) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : |x| ≤ |x + d| + |d| := by
        calc |x| = |(x + d) - d| := by ring_nf
          _ ≤ |x + d| + |d| := abs_sub _ _
      have h2 : |d| / s ≤ ε := by rw [div_le_iff₀ hspos]; linarith
      have h3 : |x| / s ≤ |x + d| / s + |d| / s := by
        rw [← add_div]; exact div_le_div_of_nonneg_right h1 hspos.le
      rw [neg_div, neg_div]
      linarith
    have hden : 0 < 2 * s := by positivity
    calc Real.exp (-|x + d| / s) / (2 * s) ≤ Real.exp ε * Real.exp (-|x| / s) / (2 * s) :=
          div_le_div_of_nonneg_right hpt hden.le
      _ = Real.exp ε * (Real.exp (-|x| / s) / (2 * s)) := by ring
  · simp

theorem solution {Dom : Type*} (g : Dom → ℝ) (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (hg : ∀ u, |g u| ≤ b) (n : ℕ) :
    PrivLearn.Generic.IsDP (fun z : Fin n → Dom => avgRespLaw g b ε z) ε := by
  classical
  intro z z' hzz' S hS
  rcases hzz' with ⟨i₀, _, hj⟩
  rcases n with _ | m
  · exact Fin.elim0 i₀
  set s := 2 * b / ε
  set μ : Measure ℝ := PrivLearn.Generic.laplace s
  have : SigmaFinite μ := by
    dsimp [μ, PrivLearn.Generic.laplace]
    infer_instance
  set ν : Measure (Fin m → ℝ) := Measure.pi (fun _ : Fin m => μ)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i₀
  have hmp : (μ.prod ν).map e.symm = Measure.pi (fun _ : Fin (m + 1) => μ) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) i₀).symm.map_eq
  have hmeas_avg : ∀ z₀ : Fin (m + 1) → Dom, Measurable (avgResp g z₀) := by
    intro z₀
    unfold avgResp
    refine measurable_const.mul (Finset.measurable_sum Finset.univ fun i _ => ?_)
    exact measurable_const.add (measurable_pi_apply i)
  have hlaw : ∀ z₀ : Fin (m + 1) → Dom,
      avgRespLaw g b ε z₀ S =
        ∫⁻ y : Fin m → ℝ,
          randomizerLaw g s (z₀ i₀)
            ((fun w : ℝ => (1 / ((m + 1 : ℕ) : ℝ)) *
              (w + ∑ j : Fin m, (g (z₀ (i₀.succAbove j)) + y j))) ⁻¹' S) ∂ν := by
    intro z₀
    unfold avgRespLaw
    change (Measure.pi fun _ : Fin (m + 1) => μ).map (avgResp g z₀) S = _
    rw [Measure.map_apply (hmeas_avg z₀) hS, ← hmp,
      Measure.map_apply e.symm.measurable ((hmeas_avg z₀) hS),
      Measure.prod_apply_symm (e.symm.measurable ((hmeas_avg z₀) hS))]
    refine lintegral_congr fun y => ?_
    unfold randomizerLaw
    have hm_aff : Measurable (fun w : ℝ => (1 / ((m + 1 : ℕ) : ℝ)) *
        (w + ∑ j : Fin m, (g (z₀ (i₀.succAbove j)) + y j))) :=
      measurable_const.mul (measurable_id.add measurable_const)
    rw [Measure.map_apply (measurable_const_add (g (z₀ i₀))) (hm_aff hS)]
    congr 1
    ext x
    simp only [Set.mem_preimage, avgResp]
    have he : e.symm (x, y) = i₀.insertNth x y := rfl
    have hsum : ∑ i : Fin (m + 1), (g (z₀ i) + e.symm (x, y) i) =
        (g (z₀ i₀) + x) + ∑ j : Fin m, (g (z₀ (i₀.succAbove j)) + y j) := by
      rw [he, Fin.sum_univ_succAbove _ i₀, Fin.insertNth_apply_same]
      simp [Fin.insertNth_apply_succAbove]
    rw [hsum]
  rw [hlaw z, hlaw z', ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  have hrest : (∑ j : Fin m, (g (z (i₀.succAbove j)) + y j)) =
      ∑ j : Fin m, (g (z' (i₀.succAbove j)) + y j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hj (i₀.succAbove j) (Fin.succAbove_ne i₀ j)]
  rw [hrest]
  have hm_aff : Measurable (fun w : ℝ => (1 / ((m + 1 : ℕ) : ℝ)) *
      (w + ∑ j : Fin m, (g (z' (i₀.succAbove j)) + y j))) :=
    measurable_const.mul (measurable_id.add measurable_const)
  exact randomizer_is_local_aux g b ε hb hε hg (z i₀) (z' i₀) _ (hm_aff hS)
