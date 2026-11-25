-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.detAdm_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:24.606276+00:00
-- url     : https://prove2.me/submissions/c51d24b5-c248-4f56-bdf1-473ec20d67c3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdm
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_boxes_inter
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_boxes_seq
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_generateFrom_boxes
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_isCompact_boxS
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_key_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabW.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabW
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported
namespace PI.VolStabW.DeterminantAdmissible
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M : ℕ} (ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (h1 : ∀ K, IsCompact K → ν1 K < ⊤) (h2 : ∀ K, IsCompact K → ν2 K < ⊤)
    (h : ∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) : ν1 = ν2 := by
  classical
  let ι := Fin a × Fin M × Fin (Module.finrank F E)
  let Ψ := psiH F E a M
  let Ψm := Ψ.toMeasurableEquiv
  have hfin : ∀ ν : Measure (Fin a → Fin M → AF F ⊗[F] E), (∀ K, IsCompact K → ν K < ⊤) →
      ∀ K, IsCompact K → ν.map Ψm K < ⊤ := by
    intro ν hν K hK
    rw [Ψm.map_apply]
    exact hν _ (Ψ.isCompact_preimage.2 hK)
  suffices hμ : ν1.map Ψm = ν2.map Ψm by
    rw [← Ψm.map_symm_map (μ := ν1), ← Ψm.map_symm_map (μ := ν2), hμ]
  set μ1 := ν1.map Ψm with hμ1
  set μ2 := ν2.map Ψm with hμ2

  have hbox : ∀ D, IsBoxD D → ∀ U : Set (ι → Ainf F), MeasurableSet U →
      μ1 (U ×ˢ boxS D) = μ2 (U ×ˢ boxS D) := by
    intro D hD
    let ρ := fun μ : Measure ((ι → Ainf F) × (ι → Af F)) =>
      (μ.restrict (univ ×ˢ boxS D)).map Prod.fst
    have hβ : MeasurableSet (boxS D) := (isCompact_boxS hD).isClosed.measurableSet
    have hρ : ∀ μ U, MeasurableSet U → ρ μ U = μ (U ×ˢ boxS D) := by
      intro μ U hU
      simp only [ρ]
      rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU)]
      congr 1
      ext p
      simp
    have hint : ∀ μ (f : C_c(ι → Ainf F, ℝ)), ∫ x, f x ∂(ρ μ) =
        ∫ p, f p.1 * (boxS D).indicator (fun _ => (1 : ℝ)) p.2 ∂μ := by
      intro μ f
      simp only [ρ]
      rw [integral_map measurable_fst.aemeasurable (map_continuous f).aestronglyMeasurable,
        ← integral_indicator (MeasurableSet.univ.prod hβ)]
      congr 1
      funext p
      by_cases hp : p.2 ∈ boxS D
      · rw [Set.indicator_of_mem (mk_mem_prod (mem_univ p.1) hp : p ∈ univ ×ˢ boxS D),
          Set.indicator_of_mem hp, mul_one]
      · rw [Set.indicator_of_notMem (fun h' => hp h'.2), Set.indicator_of_notMem hp, mul_zero]
    have hfc : ∀ μ : Measure ((ι → Ainf F) × (ι → Af F)), (∀ K, IsCompact K → μ K < ⊤) →
        IsFiniteMeasureOnCompacts (ρ μ) := fun μ hμ =>
      ⟨fun K hK => by
        rw [hρ μ K hK.measurableSet]
        exact hμ _ (hK.prod (isCompact_boxS hD))⟩
    have := hfc μ1 (hfin ν1 h1)
    have := hfc μ2 (hfin ν2 h2)
    have hρeq : ρ μ1 = ρ μ2 := Measure.ext_of_integral_eq_on_compactlySupported fun f => by
      rw [hint, hint, hμ1, hμ2, integral_map_equiv, integral_map_equiv]
      exact key_int ν1 ν2 h hD f
    intro U hU
    rw [← hρ μ1 U hU, ← hρ μ2 U hU, hρeq]

  obtain ⟨bs, hbs, hbU⟩ := boxes_seq (F := F) (ι := ι)
  refine Measure.ext_of_generateFrom_of_iUnion
    (image2 (· ×ˢ ·) {U : Set (ι → Ainf F) | MeasurableSet U} (boxes F ι))
    (fun n => compactCovering (ι → Ainf F) n.unpair.1 ×ˢ bs n.unpair.2) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← generateFrom_prod_eq isCountablySpanning_measurableSet ⟨bs, hbs, hbU⟩,
      generateFrom_boxes, MeasurableSpace.generateFrom_measurableSet]
  · rintro _ ⟨U, hU, β, hβ, rfl⟩ _ ⟨U', hU', β', hβ', rfl⟩ _
    rw [prod_inter_prod]
    have hU2 : MeasurableSet U := hU
    have hU2' : MeasurableSet U' := hU'
    exact mem_image2_of_mem (hU2.inter hU2') (boxes_inter hβ hβ')
  · refine eq_univ_of_forall fun p => mem_iUnion.2 ?_
    have h1' : p.1 ∈ ⋃ m, compactCovering (ι → Ainf F) m := by
      rw [iUnion_compactCovering]
      trivial
    have h2' : p.2 ∈ ⋃ n, bs n := by
      rw [hbU]
      trivial
    obtain ⟨m, hm⟩ := mem_iUnion.1 h1'
    obtain ⟨n, hn⟩ := mem_iUnion.1 h2'
    refine ⟨Nat.pair m n, ?_⟩
    simp only [Nat.unpair_pair]
    exact ⟨hm, hn⟩
  · intro n
    exact mem_image2_of_mem (show MeasurableSet (compactCovering (ι → Ainf F) n.unpair.1) from
      (isCompact_compactCovering _ _).measurableSet) (hbs _)
  · intro n
    obtain ⟨D, hD, e⟩ := hbs n.unpair.2
    rw [e]
    exact (hfin ν1 h1 _ ((isCompact_compactCovering _ _).prod (isCompact_boxS hD))).ne
  · rintro _ ⟨U, hU, β, ⟨D, hD, rfl⟩, rfl⟩
    exact hbox D hD U hU
end PI.VolStabW.DeterminantAdmissible
