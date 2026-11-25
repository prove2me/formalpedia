-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_sheets_nonzero_68832576f450
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:32:32.699352+00:00
-- url     : https://prove2.me/submissions/45bc529c-aec5-442b-8334-0c9031cb6faf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeaklyHolomorphicIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {k m : ℕ} (Z W : Set (σ → ℂ))
    (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (G : (σ → ℂ) → ℂ) (O Q : Set (Fin k → ℂ))
    (s : Fin m → (Fin k → ℂ) → σ → ℂ) (hWo : IsOpen W) (hOo : IsOpen O) (hQo : IsOpen Q) (hQO : Q ⊆ O)
    (hQne : Q.Nonempty) (hsd : ∀ j, DifferentiableOn ℂ (s j) O)
    (hsO : ∀ y' ∈ O, (∀ j, s j y' ∈ Z ∩ W ∧ A (s j y') = y') ∧ Function.Injective (fun j => s j y') ∧
      ∀ z ∈ Z ∩ W, A z = y' → z ∈ Set.range (fun j => s j y'))
    (hGc : ContinuousOn G W) (hnd : ∀ z ∈ Z ∩ W, ∀ V ∈ 𝓝 z, ∃ x ∈ Z ∩ V, G x ≠ 0) :
    ∃ y ∈ Q, ∀ j, G (s j y) ≠ 0 := by
  have key : ∀ Q' : Set (Fin k → ℂ), IsOpen Q' → Q' ⊆ O → Q'.Nonempty → ∀ j, ∃ y ∈ Q', G (s j y) ≠ 0 := by
    intro Q' hQ'o hQ'O ⟨y1, hy1⟩ j
    have hx1 := (hsO y1 (hQ'O hy1)).1 j
    have hV : ∀ᶠ z in 𝓝 (s j y1), z ∈ W ∧ A z ∈ Q' ∧ ∀ i, i ≠ j → s i (A z) - z ≠ 0 := by
      refine Filter.Eventually.and (hWo.mem_nhds hx1.1.2 : ∀ᶠ z in 𝓝 (s j y1), z ∈ W)
        (Filter.Eventually.and (A.continuous.continuousAt.preimage_mem_nhds
          (hQ'o.mem_nhds (by rw [hx1.2]; exact hy1)) : ∀ᶠ z in 𝓝 (s j y1), A z ∈ Q')
          (Filter.eventually_all.2 fun i => ?_))
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => absurd hij h
      · have hsi : ContinuousAt (s i) (A (s j y1)) := by
          rw [hx1.2]
          exact ((hsd i).differentiableAt (hOo.mem_nhds (hQ'O hy1))).continuousAt
        have hc : ContinuousAt (fun z => s i (A z) - z) (s j y1) :=
          (hsi.comp A.continuous.continuousAt).sub continuousAt_id
        have hne : s i (A (s j y1)) - s j y1 ≠ 0 := by
          rw [hx1.2, sub_ne_zero]
          exact fun h => hij ((hsO y1 (hQ'O hy1)).2.1 h)
        exact (hc.eventually_ne hne).mono fun _ h _ => h
    obtain ⟨x, ⟨hxZ, hxW, hxQ, hxs⟩, hGx⟩ := hnd _ hx1.1 _ hV
    obtain ⟨i, hi⟩ := (hsO (A x) (hQ'O hxQ)).2.2 x ⟨hxZ, hxW⟩ rfl
    by_cases hij : i = j
    · subst hij
      refine ⟨A x, hxQ, ?_⟩
      simp only at hi
      rw [hi]
      exact hGx
    · exact absurd (sub_eq_zero.2 hi) (hxs i hij)
  have hcont : ∀ j, ContinuousOn (fun y => G (s j y)) O := fun j =>
    hGc.comp (hsd j).continuousOn fun y hy => ((hsO y hy).1 j).1.2
  have step : ∀ n, n ≤ m → ∃ Q' : Set (Fin k → ℂ), IsOpen Q' ∧ Q' ⊆ Q ∧ Q'.Nonempty ∧
      ∀ y ∈ Q', ∀ j : Fin m, (j : ℕ) < n → G (s j y) ≠ 0 := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨Q, hQo, subset_rfl, hQne, fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn
      obtain ⟨Q', hQ'o, hQ'Q, hQ'ne, hQ'⟩ := ih (by omega)
      obtain ⟨y, hyQ', hy⟩ := key Q' hQ'o (hQ'Q.trans hQO) hQ'ne ⟨n, by omega⟩
      refine ⟨Q' ∩ (fun y => G (s ⟨n, by omega⟩ y)) ⁻¹' {0}ᶜ,
        ((hcont _).mono (hQ'Q.trans hQO)).isOpen_inter_preimage hQ'o isOpen_compl_singleton,
        Set.inter_subset_left.trans hQ'Q, ⟨y, hyQ', hy⟩, ?_⟩
      rintro y' ⟨hy'Q', hy'⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hQ' y' hy'Q' j hj
      · have : j = ⟨n, by omega⟩ := Fin.ext hj
        rw [this]
        exact hy'
  obtain ⟨Q', -, hQ'Q, ⟨y, hy⟩, hQ'⟩ := step m le_rfl
  exact ⟨y, hQ'Q hy, fun j => hQ' y hy j j.isLt⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
