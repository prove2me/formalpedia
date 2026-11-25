-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalGraphMass_proof_f1af90aa1200
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:10:22.862585+00:00
-- url     : https://prove2.me/submissions/ffe801a6-0eff-4388-b735-bac76a3f31eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_mass_piece_387f19b7a495
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_tsum_frameFibreCount_le_2c51850231c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_tsum_lintegral_le_075e4d26f535
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameFibreCount_ball_le_26a4f9913696

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open LocalGraphMass
namespace GroundTheory.Heights₂.Heights
namespace LocalGraphMass
theorem _root_.solution (hPF : ProjectionFormula.Statement) : LocalGraphMass.Statement := by
  intro n d b I₀ S hd hS R
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hS' : ∀ z : S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ (z : EuclideanSpace ℂ (Fin n)) ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω :=
    fun z => hS z z.2
  choose Ω V g hΩ hV hzV hg hfix hSV using hS'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
  have hmemT : ∀ z ∈ S, ∃ i ∈ T, z ∈ V i := by
    intro z hz
    have : z ∈ ⋃ i ∈ T, V i := hTU ▸ Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV _⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 this
    exact ⟨i, hi, hzi⟩
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨i, hi, -⟩ := hmemT z hz
    exact ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  let W : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun k => V (f k)
  have hcover : S ⊆ ⋃ k, disjointed W k := by
    intro z hz
    rw [iUnion_disjointed]
    obtain ⟨i, hi, hzi⟩ := hmemT z hz
    rw [hf] at hi
    obtain ⟨k, rfl⟩ := hi
    exact Set.mem_iUnion.2 ⟨k, hzi⟩
  have hDmeas : ∀ k, MeasurableSet (disjointed W k) :=
    MeasurableSet.disjointed fun k => (hV _).measurableSet
  have hpiece : ∀ k, S ∩ Metric.ball 0 R ∩ disjointed W k =
      g (f k) '' Ω (f k) ∩ (Metric.ball 0 R ∩ disjointed W k) := by
    intro k
    rw [← hSV (f k)]
    ext z
    constructor
    · rintro ⟨⟨hzS, hzB⟩, hzD⟩
      exact ⟨⟨hzS, disjointed_subset W k hzD⟩, hzB, hzD⟩
    · rintro ⟨⟨hzS, -⟩, hzB, hzD⟩
      exact ⟨⟨hzS, hzB⟩, hzD⟩
  have hdisj : Pairwise (Disjoint on fun k => S ∩ Metric.ball 0 R ∩ disjointed W k) :=
    fun i j hij => (disjoint_disjointed W hij).mono Set.inter_subset_right Set.inter_subset_right
  calc μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball 0 R)
      ≤ μH[((2 * d : ℕ) : ℝ)] (⋃ k, S ∩ Metric.ball 0 R ∩ disjointed W k) := by
        refine measure_mono fun z hz => ?_
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcover hz.1)
        exact Set.mem_iUnion.2 ⟨k, hz, hk⟩
    _ ≤ ∑' k, μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball 0 R ∩ disjointed W k) := measure_iUnion_le _
    _ = ∑' k, ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount b I (S ∩ Metric.ball 0 R ∩ disjointed W k) (WithLp.ofLp x)
            ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        congr 1
        funext k
        rw [hpiece k]
        exact mass_piece hPF b I₀ hd _ _ (hΩ _) (hg _) (hfix _) _
          (Metric.isOpen_ball.measurableSet.inter (hDmeas k))
    _ = ∑ I ∈ Finset.univ.powersetCard d, ∑' k, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount b I (S ∩ Metric.ball 0 R ∩ disjointed W k) (WithLp.ofLp x)
            ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ I ∈ Finset.univ.powersetCard d,
          (⨆ x : I → ℂ, frameFibreCount b I S x) *
            μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ I) R) := by
        refine Finset.sum_le_sum fun I _ => ?_
        calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, ∑' k,
              frameFibreCount b I (S ∩ Metric.ball 0 R ∩ disjointed W k) (WithLp.ofLp x)
                ∂(μH[((2 * d : ℕ) : ℝ)]) := tsum_lintegral_le _ _
          _ ≤ ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount b I (S ∩ Metric.ball 0 R) (WithLp.ofLp x)
                ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              lintegral_mono fun x =>
                tsum_frameFibreCount_le b I _ (fun k => Set.inter_subset_left) hdisj _
          _ ≤ ∫⁻ x : EuclideanSpace ℂ I, (Metric.ball (0 : EuclideanSpace ℂ I) R).indicator
                (fun _ => ⨆ y : I → ℂ, frameFibreCount b I S y) x ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              lintegral_mono fun x => frameFibreCount_ball_le b I S R x
          _ = _ := lintegral_indicator_const Metric.isOpen_ball.measurableSet _
end LocalGraphMass
end GroundTheory.Heights₂.Heights
