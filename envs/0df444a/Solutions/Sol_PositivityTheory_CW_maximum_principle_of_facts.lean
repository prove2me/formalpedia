-- Prove2me | solution 1 for PositivityTheory.CW.maximum_principle_of_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:38:21.852796+00:00
-- url     : https://prove2.me/submissions/ac058f0a-a923-49f9-be4a-21e88b7d1ffe

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MaximumPrincipleOfFacts
import Theorems.Thm_PositivityTheory_CW_MaximumPrincipleOneFunction_step
import Theorems.Thm_PositivityTheory_CW_MaximumPrincipleOneFunction_hilbert_schmidt_nonneg_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open MaximumPrincipleOneFunction
namespace PositivityTheory.CW
theorem _root_.solution : B2 → B3 → UnitaryGroupFacts → MaximumPrincipleVar := by
  intro hB2 hB3 hB3g n ε r
  choose cf hcf0 hcf using hB2
  have hcr0 : 0 ≤ ∑ p ∈ nc ε, cf n (Xp p.1 p.2) r := Finset.sum_nonneg fun p _ => hcf0 _ _ _
  have hcr10 : 0 ≤ ∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1) := Finset.sum_nonneg fun p _ => hcf0 _ _ _
  refine ⟨(∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) + 1, by linarith, ?_⟩
  intro u A hA hcont hgrowth hsub
  obtain ⟨C, hC⟩ := hgrowth
  obtain ⟨hcpt, h1, hmem, -, hhs, hX⟩ := hB3g n ε
  have key : ∀ η : ℝ, 0 < η → u 1 ≤ A * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ r +
      η * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) := by
    intro η hη
    by_contra hneg
    push Not at hneg
    have hW : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => 1 + hs2 g := continuous_const.add hhs
    have hK := hcpt (|C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ))
    have hKne : ({g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} : Set _).Nonempty :=
      ⟨1, h1, by have := div_nonneg (abs_nonneg C) hη.le; linarith⟩
    have hψc : ContinuousOn (fun g => u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1))
        {g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} := by
      have hu : ContinuousOn u {g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} :=
        hcont.mono fun g hg => hg.1
      exact (hu.sub (continuous_const.mul (hW.pow r)).continuousOn).sub
        (continuous_const.mul (hW.pow (r + 1))).continuousOn
    obtain ⟨g0, hg0K, hg0max⟩ := hK.exists_isMaxOn hKne hψc
    have hψ1 : u 1 - A * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ r -
        η * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) ≤
        u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1) :=
      hg0max ⟨h1, by have := div_nonneg (abs_nonneg C) hη.le; linarith⟩
    have hglob : ∀ g ∈ UJset ε, u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1) ≤
        u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1) := by
      intro g hg
      by_cases hgρ : hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)
      · exact hg0max ⟨hg, hgρ⟩
      · push Not at hgρ
        have hs1 := hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)
        have hsg := hilbert_schmidt_nonneg_alt g
        have hlt : |C| / η < 1 + hs2 g := by linarith
        have hCl : C < η * (1 + hs2 g) := by
          have := (div_lt_iff₀ hη).mp hlt
          have := le_abs_self C
          linarith
        have hWr : 0 < (1 + hs2 g) ^ r := pow_pos (by linarith) r
        have hAW : 0 ≤ A * (1 + hs2 g) ^ r := mul_nonneg hA hWr.le
        have hug := hC g hg
        have hprod := mul_pos hWr (sub_pos.mpr hCl)
        rw [pow_succ]
        nlinarith
    have hg0 : g0 ∈ UJset ε := hg0K.1
    obtain ⟨d, hd, hdsum⟩ := hsub g0 hg0
    have hW0 := hilbert_schmidt_nonneg_alt g0
    have hWr : 0 < (1 + hs2 g0) ^ r := pow_pos (by linarith) r
    have hWr1 : 0 < (1 + hs2 g0) ^ (r + 1) := pow_pos (by linarith) (r + 1)
    have hp : ∀ p ∈ nc ε, d p ≤ A * cf n (Xp p.1 p.2) r * (1 + hs2 g0) ^ r +
        η * cf n (Xp p.1 p.2) (r + 1) * (1 + hs2 g0) ^ (r + 1) := by
      intro p hp
      obtain ⟨u', hu', hdp⟩ := hd p hp
      obtain ⟨v', v'', hv', hv'', hvb⟩ := hcf n (Xp p.1 p.2) r g0
      obtain ⟨w', w'', hw', hw'', hwb⟩ := hcf n (Xp p.1 p.2) (r + 1) g0
      have hst := step hB3 hB3g ε r u A η g0 hglob hg0 p hp u' (d p) hu' hdp v' v'' hv' hv'' w' w'' hw' hw''
      have h1 := mul_le_mul_of_nonneg_left hvb hA
      have h2 := mul_le_mul_of_nonneg_left hwb hη.le
      nlinarith
    have hsum : ∑ p ∈ nc ε, d p ≤ A * (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) * (1 + hs2 g0) ^ r +
        η * (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) * (1 + hs2 g0) ^ (r + 1) := by
      refine (Finset.sum_le_sum hp).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
    have hpos : 0 < (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) + 1 := by
      linarith
    have hug0 : A * (1 + hs2 g0) ^ r + η * (1 + hs2 g0) ^ (r + 1) < u g0 := by linarith
    have hm := mul_lt_mul_of_pos_left hug0 hpos
    have e1 := mul_nonneg hcr10 (mul_nonneg hA hWr.le)
    have e2 := mul_pos (by linarith : (0:ℝ) < (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + 1) (mul_pos hη hWr1)
    nlinarith
  have hW1 : 0 < (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) :=
    pow_pos (by linarith [hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)]) (r + 1)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have := key (δ / (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1)) (div_pos hδ hW1)
  rwa [div_mul_cancel₀ _ hW1.ne'] at this
end PositivityTheory.CW
