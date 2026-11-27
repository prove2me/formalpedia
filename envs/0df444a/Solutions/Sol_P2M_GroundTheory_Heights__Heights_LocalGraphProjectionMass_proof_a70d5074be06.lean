-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_proof_a70d5074be06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:04:07.256992+00:00
-- url     : https://prove2.me/submissions/4f67abba-80cf-4ae1-80a4-4a7ba3718c3a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphProjectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphProjectionMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_mass_piece_frame_d4356ba17c2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_lintegral_count_le_0c5dc6a305d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_tsum_frameFibreCount_le_2c51850231c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_tsum_lintegral_le_075e4d26f535
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MassFinite_exists_frame_37c550a38a85


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
open LocalGraphProjectionMass
namespace GroundTheory.Heights₂.Heights
namespace LocalGraphProjectionMass
theorem _root_.solution (hPF : ProjectionFormula.Statement) :
    LocalGraphProjectionMass.Statement := by
  intro n d b I₀ S hd hS U hU B hB
  classical
  obtain ⟨c, hc⟩ := MassFinite.exists_frame U hU
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
  have hpiece : ∀ k, S ∩ B ∩ disjointed W k = g (f k) '' Ω (f k) ∩ (B ∩ disjointed W k) := by
    intro k
    rw [← hSV (f k)]
    ext z
    constructor
    · rintro ⟨⟨hzS, hzB⟩, hzD⟩
      exact ⟨⟨hzS, disjointed_subset W k hzD⟩, hzB, hzD⟩
    · rintro ⟨⟨hzS, -⟩, hzB, hzD⟩
      exact ⟨⟨hzS, hzB⟩, hzD⟩
  have hdisj : Pairwise (Disjoint on fun k => S ∩ B ∩ disjointed W k) :=
    fun i j hij => (disjoint_disjointed W hij).mono Set.inter_subset_right Set.inter_subset_right
  let G : (Fin d → Fin n) → ℝ≥0∞ := fun s =>
    (⨆ x : EuclideanSpace ℂ (Fin d),
        (({z | z ∈ S ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
      μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (S ∩ B))
  calc μH[((2 * d : ℕ) : ℝ)] (S ∩ B)
      ≤ μH[((2 * d : ℕ) : ℝ)] (⋃ k, S ∩ B ∩ disjointed W k) := by
        refine measure_mono fun z hz => ?_
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcover hz.1)
        exact Set.mem_iUnion.2 ⟨k, hz, hk⟩
    _ ≤ ∑' k, μH[((2 * d : ℕ) : ℝ)] (S ∩ B ∩ disjointed W k) := measure_iUnion_le _
    _ = ∑' k, ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        congr 1
        funext k
        rw [hpiece k]
        exact mass_piece_frame hPF b c I₀ hd _ _ (hΩ _) (hg _) (hfix _) _ (hB.inter (hDmeas k))
    _ = ∑ I ∈ Finset.univ.powersetCard d, ∑' k, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ I ∈ Finset.univ.powersetCard d, ⨆ hI : I.card = d, G (I.orderEmbOfFin hI) := by
        refine Finset.sum_le_sum fun I hI => ?_
        have hIc := (Finset.mem_powersetCard.1 hI).2
        refine le_trans ?_ (le_iSup (fun h : I.card = d => G (I.orderEmbOfFin h)) hIc)
        calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, ∑' k,
              frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              LocalGraphMass.tsum_lintegral_le _ _
          _ ≤ ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I (S ∩ B) (WithLp.ofLp x)
                ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              lintegral_mono fun x =>
                LocalGraphMass.tsum_frameFibreCount_le c I _ (fun k => Set.inter_subset_left) hdisj _
          _ ≤ G (I.orderEmbOfFin hIc) := lintegral_count_le U c hc I hIc (S ∩ B)
    _ = ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s), G s := by
        refine Finset.sum_bij (fun I hI => ⇑(I.orderEmbOfFin (Finset.mem_powersetCard.1 hI).2))
          (fun I hI => Finset.mem_filter.2 ⟨Finset.mem_univ _, (I.orderEmbOfFin _).strictMono⟩)
          (fun I₁ hI₁ I₂ hI₂ h => ?_) (fun t ht => ?_) (fun I hI => ?_)
        · have := congrArg Set.range h
          rw [Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin] at this
          exact Finset.coe_inj.1 this
        · have hmono := (Finset.mem_filter.1 ht).2
          have hcard : (Finset.univ.image t).card = d := by
            rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
          refine ⟨Finset.univ.image t, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hcard⟩, ?_⟩
          exact (Finset.orderEmbOfFin_unique hcard
            (fun x => Finset.mem_image_of_mem t (Finset.mem_univ x)) hmono).symm
        · exact iSup_pos (Finset.mem_powersetCard.1 hI).2
end LocalGraphProjectionMass
end GroundTheory.Heights₂.Heights
