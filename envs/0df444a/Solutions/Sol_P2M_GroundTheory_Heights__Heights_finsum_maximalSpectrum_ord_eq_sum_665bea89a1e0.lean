-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finsum_maximalSpectrum_ord_eq_sum_665bea89a1e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:32.682571+00:00
-- url     : https://prove2.me/submissions/e78b4a9a-d9cc-4a26-ab41-0a129990f42c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLength

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {O B ι : Type*} [CommRing O] [CommRing B] [Algebra O B] (θ : B)
    (S : Finset ι) (c : ι → Ideal B) (hc : Set.BijOn c ↑S {P | P.IsMaximal ∧ θ ∈ P}) (m : ι → ℕ∞)
    (hm : ∀ i ∈ S, ∀ _ : (c i).IsPrime,
      Ring.ord (Localization.AtPrime (c i)) (algebraMap B _ θ) * Module.length O (B ⧸ c i) = m i) :
    ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal) =
      ∑ i ∈ S, m i := by
  classical
  let ψ : Ideal B → ℕ∞ := fun P => if h : P.IsMaximal then
    (haveI := h.isPrime
     Ring.ord (Localization.AtPrime P) (algebraMap B (Localization.AtPrime P) θ) * Module.length O (B ⧸ P))
    else 0
  calc ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal)
      = ∑ᶠ 𝔓 ∈ {𝔓 : MaximalSpectrum B | θ ∈ 𝔓.asIdeal},
          Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) *
            Module.length O (B ⧸ 𝔓.asIdeal) := by
        refine finsum_congr fun 𝔓 => ?_
        rw [finsum_eq_if]
        split_ifs with h
        · rfl
        · have hu : IsUnit (algebraMap B (Localization.AtPrime 𝔓.asIdeal) θ) :=
            IsLocalization.map_units (M := 𝔓.asIdeal.primeCompl) (Localization.AtPrime 𝔓.asIdeal) ⟨θ, h⟩
          rw [Ring.ord_of_isUnit hu, zero_mul]
    _ = ∑ᶠ P ∈ {P : Ideal B | P.IsMaximal ∧ θ ∈ P}, ψ P :=
        finsum_mem_eq_of_bijOn MaximalSpectrum.asIdeal
          ⟨fun 𝔓 h => ⟨𝔓.isMaximal, h⟩, fun a _ b _ h => MaximalSpectrum.ext h,
            fun P hP => ⟨⟨P, hP.1⟩, hP.2, rfl⟩⟩
          (fun 𝔓 _ => by simp only [ψ, dif_pos 𝔓.isMaximal])
    _ = ∑ᶠ i ∈ (S : Set ι), ψ (c i) := (finsum_mem_eq_of_bijOn c hc fun _ _ => rfl).symm
    _ = ∑ i ∈ S, ψ (c i) := finsum_mem_coe_finset _ _
    _ = ∑ i ∈ S, m i := Finset.sum_congr rfl fun i hi => by
        have hmax : (c i).IsMaximal := (hc.mapsTo (Finset.mem_coe.mpr hi)).1
        simp only [ψ, dif_pos hmax]
        exact hm i hi hmax.isPrime
end GroundTheory.Heights₂.Heights
