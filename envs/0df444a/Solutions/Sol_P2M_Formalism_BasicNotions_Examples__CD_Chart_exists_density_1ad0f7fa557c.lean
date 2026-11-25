-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_density_1ad0f7fa557c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:49.960966+00:00
-- url     : https://prove2.me/submissions/85c0e5aa-84c9-4640-a96d-d47daeb56e47

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_img_eq_2b325c8b99f9
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_rho_2d4d0a8259f7
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_apply_3ee47408ca0b
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_finite_542036c95c54
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_pos_0059071125f9
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_qinv_c73e74073ecd
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exists_density_03e233a4d5e1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open Formalism.BasicNotions.Examples₂.CD.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G)
variable [IsTopologicalGroup G] [μ.IsHaarMeasure]
namespace Formalism.BasicNotions.Examples₂.CD.Chart
theorem _root_.solution (lam : Measure V) [lam.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ (C.img (S r)) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨ρ, hρ, hR⟩ := C.exists_rho
  haveI := C.nu_finite hR μ
  obtain ⟨c, hc0, hctop, hup, hdown⟩ := Formalism.BasicNotions.Examples₂.CD.exists_density (nu := C.nu ρ μ) (lam := lam)
    (fun ε h0 h1 => C.nu_qinv hR μ hρ ε h0 h1) (fun r hr => C.nu_pos hR μ hρ r hr)
  refine ⟨c, hc0, hctop, fun S hS hsmall hlam => ?_⟩
  have key : ∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      S r ⊆ ball 0 δ ∧ S r ⊆ ball 0 ρ ∧ lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤ := fun δ hδ =>
    (((hsmall δ hδ).and (hsmall ρ hρ)).and hlam).mono fun r h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  have heq : ∀ r, S r ⊆ ball 0 ρ → μ (C.img (S r)) = C.nu ρ μ (S r) := by
    intro r hr
    rw [C.img_eq, C.nu_apply hR μ (hS r), Set.inter_eq_left.2 hr]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨C', haC', hC'c⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    obtain ⟨δ, hδ, hδs⟩ := hdown C' hC'c
    filter_upwards [key δ hδ] with r hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [heq r h2]
    exact lt_of_lt_of_le haC' ((ENNReal.le_div_iff_mul_le (Or.inl h3) (Or.inl h4)).2 (hδs _ h1))
  · obtain ⟨C', hcC', hC'b⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hb
    obtain ⟨δ, hδ, hδs⟩ := hup C' hcC'
    filter_upwards [key δ hδ] with r hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [heq r h2]
    exact lt_of_le_of_lt (ENNReal.div_le_of_le_mul (hδs _ h1)) hC'b
end Formalism.BasicNotions.Examples₂.CD.Chart
