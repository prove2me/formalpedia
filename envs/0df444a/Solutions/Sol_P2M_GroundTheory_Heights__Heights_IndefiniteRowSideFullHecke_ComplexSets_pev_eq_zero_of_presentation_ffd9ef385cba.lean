-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_eq_zero_of_presentation_ffd9ef385cba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:22.3483+00:00
-- url     : https://prove2.me/submissions/90fdf25c-8ccc-49ae-904a-c86c6cd1de1c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_sub_3625d3b8717d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_evalAt_apply_3dcf9480b1b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_C_84d2b4612e3e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_X_1c14eb6f22af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_eq_sum_range_6018055aec67
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAt_pev_comp_d9a9192a1847
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_presPoly_monic_7d7498d43648
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_presPoly_degree_1fc8a47ccfd5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_presPoly_5e3853e9f33d
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.evalAt_apply
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.pev_C
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.pev_X

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ}
    {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {ℓ : (σ → ℂ) →L[ℂ] ℂ} {N : ℕ} {c : Fin N → (Fin d → ℂ) → ℂ}
    {δ : (Fin d → ℂ) → ℂ} (hP : IsPrimitivePresentation w p A ℓ c δ) (H : (analyticSubring (A w))[X])
    (hH : IsGermCombination w p (fun z => pev (A z) (ℓ z) H)) :
    ∀ᶠ y in 𝓝 (A w), ∀ t : ℂ, t ^ N + ∑ j, c j y * t ^ (j : ℕ) = 0 → pev y t H = 0 := by
  obtain ⟨hc, -, h1, h2, -⟩ := hP
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact Eventually.of_forall fun y t ht => by simp at ht
  set F := presPoly c hc with hFdef
  have hmon : F.Monic := presPoly_monic c hc
  set R := H %ₘ F with hRdef
  set Q := H /ₘ F with hQdef
  have hdec : ∀ y t, pev y t H = pev y t R + pev y t F * pev y t Q := by
    intro y t
    rw [← map_mul, ← map_add, hRdef, hQdef, modByMonic_add_div]
  have hRdeg : R.natDegree < N := by
    by_cases hR0 : R = 0
    · rw [hR0, natDegree_zero]; exact hN
    rw [natDegree_lt_iff_degree_lt hR0, ← presPoly_degree c hc]
    exact degree_modByMonic_lt _ hmon
  have hRsum : ∀ y t, pev y t R = ∑ j : Fin N, (R.coeff j : (Fin d → ℂ) → ℂ) y * t ^ (j : ℕ) := by
    intro y t
    rw [pev_eq_sum_range R hRdeg, Fin.sum_univ_eq_sum_range (fun i => (R.coeff i : (Fin d → ℂ) → ℂ) y * t ^ i)]
  have hRP : IsGermCombination w p
      (fun z => ∑ j : Fin N, (R.coeff j : (Fin d → ℂ) → ℂ) (A z) * ℓ z ^ (j : ℕ)) := by
    refine (hH.sub (IsGermCombination.mul_left (analyticAt_pev_comp w A ℓ Q) h1)).congr
      (Eventually.of_forall fun z => ?_)
    rw [← hRsum, hdec, pev_presPoly]
    ring
  have hzero := h2 (fun j => (R.coeff j : (Fin d → ℂ) → ℂ)) (fun j => (R.coeff j).2) hRP
  filter_upwards [eventually_all.2 hzero] with y hy t ht
  rw [hdec, hRsum, pev_presPoly, ht, zero_mul, add_zero]
  exact Finset.sum_eq_zero fun j _ => by rw [hy j, zero_mul]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
