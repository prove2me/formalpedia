-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_form_chart_1de3df5576aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:23:28.964245+00:00
-- url     : https://prove2.me/submissions/81247a55-a83f-4530-a1fd-0c004a45c6a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ChartInvertible_mul_6cd6215982f3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I : Chart x} {P : Submodule (chartRing S x I) Ω} (hP : ChartInvertible P)
    {σ : Ω} (hσ : σ ∈ P) (hσ0 : σ ≠ 0) : ∃ (g : Poly S N) (e : ℕ), g.IsHomogeneous e ∧
      aeval x g ≠ 0 ∧ ∀ δ ∈ P, ∃ o ∈ twistMod S x (e : ℤ) I, aeval x g * δ = σ * o := by
  obtain ⟨Q', hQ'⟩ := hP
  have hq : ∃ q ∈ Q', q ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hbot : Q' = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
    have h1 : (1 : Ω) ∈ (1 : Submodule (chartRing S x I) Ω) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    rw [← hQ', hbot, Submodule.mul_bot, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨q, hqQ, hq0⟩ := hq
  obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hQ' ▸ Submodule.mul_mem_mul hσ hqQ :
    σ * q ∈ (1 : Submodule (chartRing S x I) Ω))
  obtain ⟨g, s, e, hs, hg, hse, hbg⟩ := b.2
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hb' : (b : Ω) = σ * q := hb
  have hgx : aeval x g = σ * q * aeval x s := by
    rw [← hb', hbg, div_mul_cancel₀ _ hs0]
  refine ⟨g, e, hg, by rw [hgx]; exact mul_ne_zero (mul_ne_zero hσ0 hq0) hs0, fun δ hδ => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hQ' ▸ Submodule.mul_mem_mul hδ hqQ :
    δ * q ∈ (1 : Submodule (chartRing S x I) Ω))
  obtain ⟨h, t, e', ht, hh, hte, hah⟩ := a.2
  have ha' : aeval x h / aeval x t = δ * q := by rw [← hah]; exact ha
  refine ⟨aeval x (s * h) / aeval x t,
    Submodule.subset_span ⟨s * h, t, e', e + e', ht, hse.mul hh, hte, by push_cast; ring, rfl⟩, ?_⟩
  rw [map_mul, mul_div_assoc, ha', hgx]
  ring
end GroundTheory.Heights₂.Heights.Kleiman
