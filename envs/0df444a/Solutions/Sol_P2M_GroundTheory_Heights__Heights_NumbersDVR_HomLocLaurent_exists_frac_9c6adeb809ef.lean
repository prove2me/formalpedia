-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_exists_frac_9c6adeb809ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:44:51.625975+00:00
-- url     : https://prove2.me/submissions/1c60e8ed-75db-4817-acd1-2ee48b7f878e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isMultiHomog_add_6df46c87f520
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isMultiHomog_neg_fa06f6ab8e21

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
variable {P W}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
theorem _root_.solution [W.IsPrime] (hPW : P ≤ W) {a : FractionRing (MRing ι R ⧸ P)}
    (ha : a ∈ homLocRing P W) : ∃ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b ∧
      IsMultiHomog g b ∧ g ∉ W ∧ a = fr P f / fr P g := by
  have h1 : (1 : MRing ι R) ∉ W := (Ideal.ne_top_iff_one W).mp Ideal.IsPrime.ne_top'
  have hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0 := fun hg => fr_ne_zero (fun h => hg (hPW h))
  induction ha using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := hx
    exact ⟨b, f, g, hf, hg, hgW, rfl⟩
  | zero => exact ⟨0, 0, 1, isWeightedHomogeneous_zero _ _ _, isWeightedHomogeneous_one _ _, h1, by simp⟩
  | one => exact ⟨0, 1, 1, isWeightedHomogeneous_one _ _, isWeightedHomogeneous_one _ _, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := hx
    obtain ⟨b', f', g', hf', hg', hgW', rfl⟩ := hy
    refine ⟨b + b', f * g' + f' * g, g * g', isMultiHomog_add (isMultiHomog_mul hf hg')
      (add_comm b' b ▸ isMultiHomog_mul hf' hg), isMultiHomog_mul hg hg',
      fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hgW hgW', ?_⟩
    rw [div_add_div _ _ (hne hgW) (hne hgW')]
    simp only [map_add, map_mul]
    ring
  | neg x _ hx =>
    obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := hx
    exact ⟨b, -f, g, isMultiHomog_neg hf, hg, hgW, by simp [neg_div]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := hx
    obtain ⟨b', f', g', hf', hg', hgW', rfl⟩ := hy
    refine ⟨b + b', f * f', g * g', isMultiHomog_mul hf hf', isMultiHomog_mul hg hg',
      fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hgW hgW', ?_⟩
    rw [div_mul_div_comm]
    simp only [map_mul]
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
