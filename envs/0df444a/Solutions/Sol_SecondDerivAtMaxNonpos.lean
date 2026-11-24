-- Prove2me | solution 1 for SecondDerivAtMaxNonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:13:48.63469+00:00
-- url     : https://prove2.me/submissions/e2f95e39-484b-4d0a-88cf-21c18d933b41

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_SecondDerivAtMaxNonpos

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution (g : ℝ → ℝ) (L : ℝ) (hdiff : Differentiable ℝ g)
    (hmax : ∀ σ : ℝ, g σ ≤ g 0) (hDD : HasDerivAt (deriv g) L 0) : L ≤ 0 := by
  by_contra hcon
  rw [not_le] at hcon
  have hlm : IsLocalMax g 0 := Filter.Eventually.of_forall hmax
  have hD0 : deriv g 0 = 0 := hlm.deriv_eq_zero
  have hev2 : ∀ᶠ σ in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ, 0 < slope (deriv g) 0 σ :=
    (hasDerivAt_iff_tendsto_slope.mp hDD).eventually_const_lt hcon
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev2
  obtain ⟨δ, hδ, hball⟩ := hev2
  have hpos : ∀ x : ℝ, 0 < x → x < δ → 0 < deriv g x := by
    intro x hx0 hxδ
    have hne : x ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx0
    have hd : dist x (0 : ℝ) < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx0]
      exact hxδ
    have h1 := hball hd hne
    rw [slope_def_field, hD0] at h1
    have h2 : 0 < deriv g x / x := by simpa using h1
    exact (div_pos_iff.mp h2).elim (fun hh => hh.1)
      (fun hh => absurd hx0 (not_lt.mpr (le_of_lt hh.2)))
  have hmono : StrictMonoOn g (Set.Icc 0 (δ / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hdiff.continuous.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    exact hpos x hx.1 (by linarith [hx.2])
  have hlt : g 0 < g (δ / 2) :=
    hmono (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
      (by linarith)
  linarith [hmax (δ / 2)]
