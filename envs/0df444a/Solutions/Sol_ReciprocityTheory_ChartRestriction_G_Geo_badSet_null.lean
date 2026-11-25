-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.badSet_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:31.939601+00:00
-- url     : https://prove2.me/submissions/423a1904-643f-4a7a-ba35-65ad740a137f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterOsgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coincide_null
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_secSet_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_secSet_of_sheet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Metric Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (fibre P Ψ y).Finite) :
    volume (badSet P Ψ) = 0 := by
  obtain ⟨Dc, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin e → ℂ)
  let S : (Fin e → ℂ) → ℚ → Set (Fin e → ℂ) := fun d q =>
    ⋃ G ∈ secSet P Ψ (ball d q), ⋃ G' ∈ secSet P Ψ (ball d q), {y | G ≠ G' ∧ y ∈ ball d (q : ℝ) ∧ G y = G' y}
  have hS : ∀ d q, volume (S d q) = 0 := by
    intro d q
    by_cases hq : (0 : ℝ) < q
    · have hfinS := secSet_finite hA hfin d hq
      refine (measure_biUnion_null_iff hfinS.countable).2 fun G hG =>
        (measure_biUnion_null_iff hfinS.countable).2 fun G' hG' => ?_
      by_cases h : G = G'
      · simp [h]
      · refine measure_mono_null ?_ (coincide_null hA hG hG' h)
        intro y hy
        exact ⟨hy.2.1, hy.2.2⟩
    · have hempty : ball d (q : ℝ) = ∅ := Metric.ball_eq_empty.2 (not_lt.1 hq)
      refine measure_mono_null ?_ measure_empty
      intro y hy
      simp only [S, Set.mem_iUnion] at hy
      obtain ⟨G, _, G', _, _, hyb, _⟩ := hy
      rw [hempty] at hyb
      exact hyb
  have hcount : volume (⋃ d ∈ Dc, ⋃ q : ℚ, S d q) = 0 :=
    (measure_biUnion_null_iff hDc).2 fun d _ => measure_iUnion_null fun q => hS d q
  refine measure_mono_null ?_ hcount
  intro y hy
  obtain ⟨w, γ, γ', ⟨hγw, hγev⟩, ⟨hγ'w, hγ'ev⟩, hne⟩ := hy
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hγev.and hγ'ev)
  obtain ⟨q, hq0, hqε⟩ : ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < ε / 2 := by
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (half_pos hε)
    exact ⟨q, h1, h2⟩
  obtain ⟨d, hdD, hd⟩ := hDd.exists_mem_open isOpen_ball ⟨y, mem_ball_self hq0⟩
  have hdy : dist y d < q := by
    rw [dist_comm]
    exact hd
  have hyB : y ∈ ball d (q : ℝ) := by
    rw [mem_ball]
    exact hdy
  have hBsub : ball d (q : ℝ) ⊆ ball y ε := by
    intro y' hy'
    rw [mem_ball] at hy' ⊢
    calc dist y' y ≤ dist y' d + dist d y := dist_triangle _ _ _
      _ < q + q := by
        rw [dist_comm d y]
        exact add_lt_add hy' hdy
      _ < ε := by linarith
  have hG : (ball d (q : ℝ)).indicator (fun y' => segre (γ y')) ∈ secSet P Ψ (ball d (q : ℝ)) :=
    mem_secSet_of_sheet (fun y' hy' => (hball y' (hBsub hy')).1)
  have hG' : (ball d (q : ℝ)).indicator (fun y' => segre (γ' y')) ∈ secSet P Ψ (ball d (q : ℝ)) :=
    mem_secSet_of_sheet (fun y' hy' => (hball y' (hBsub hy')).2)
  refine Set.mem_iUnion₂.2 ⟨d, hdD, Set.mem_iUnion.2 ⟨q, Set.mem_iUnion₂.2 ⟨_, hG,
    Set.mem_iUnion₂.2 ⟨_, hG', ?_, hyB, ?_⟩⟩⟩⟩
  · intro heq
    apply hne
    filter_upwards [isOpen_ball.mem_nhds hyB] with y' hy'
    have h1 := congrFun heq y'
    simpa [Set.indicator_of_mem hy'] using h1
  · simp [Set.indicator_of_mem hyB, hγw, hγ'w]
end ReciprocityTheory.ChartRestriction.G.Geo
