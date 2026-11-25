-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_continuousAt_of_count_ne_ca785de3f3fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:30.88117+00:00
-- url     : https://prove2.me/submissions/33546014-a6ab-41cf-9c66-8b3478ea1956

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_norm_prod_le_pow_309320c6e6da
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_exists_bound_pairs_7ea5a7f18a7c

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
open Topology Filter Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
theorem _root_.solution {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {D : Set (Fin d → ℂ)} {N : ℕ} (l : (σ → ℂ) →L[ℂ] ℂ) (hD : IsOpen D)
    (hproper : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K})
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N) {y₀ : Fin d → ℂ} (hy₀ : y₀ ∈ D)
    (hN : {x | x ∈ Y ∧ A x = y₀}.encard ≠ N) : ContinuousAt (fibreDiscr Y A l N) y₀ := by
  have hf0 : fibreDiscr Y A l N y₀ = 0 := by
    unfold fibreDiscr
    rw [dif_neg hN]
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.1 hD y₀ hy₀
  have hKD : closedBall y₀ (ρ / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hρD
  have hYK := hproper _ hKD (isCompact_closedBall y₀ (ρ / 2))
  obtain ⟨C, hC1, hC⟩ := exists_bound_pairs l hYK
  have hS₀fin : {x | x ∈ Y ∧ A x = y₀}.Finite := Set.finite_of_encard_le_coe (hle y₀ hy₀)
  have hS₀card : hS₀fin.toFinset.card < N := by
    have h1 := hS₀fin.encard_eq_coe_toFinset_card
    have h3 : {x | x ∈ Y ∧ A x = y₀}.encard < N := lt_of_le_of_ne (hle y₀ hy₀) hN
    rw [h1] at h3
    exact_mod_cast h3
  unfold ContinuousAt
  rw [hf0, Metric.tendsto_nhds]
  intro ε hε
  have hcont : Continuous fun η : ℝ => ‖l‖ * (2 * η) * C ^ (N * N) := by fun_prop
  obtain ⟨η, hηε, hη⟩ : ∃ η : ℝ, ‖l‖ * (2 * η) * C ^ (N * N) < ε ∧ η ∈ Ioi (0 : ℝ) := by
    have h0 : (fun η : ℝ => ‖l‖ * (2 * η) * C ^ (N * N)) 0 < ε := by simpa using hε
    exact ((((hcont.tendsto 0).eventually (gt_mem_nhds h0)).filter_mono
      (nhdsWithin_le_nhds (s := Ioi 0))).and self_mem_nhdsWithin).exists
  have hclosed : IsClosed {x : σ → ℂ | ∀ s ∈ {x | x ∈ Y ∧ A x = y₀}, η ≤ dist x s} := by
    have : {x : σ → ℂ | ∀ s ∈ {x | x ∈ Y ∧ A x = y₀}, η ≤ dist x s} =
        ⋂ s ∈ {x | x ∈ Y ∧ A x = y₀}, {x | η ≤ dist x s} := by
      ext x
      simp
    rw [this]
    exact isClosed_biInter fun s _ => isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hKη := hYK.inter_right hclosed
  have hy₀K : y₀ ∉ A '' ({x | x ∈ Y ∧ A x ∈ closedBall y₀ (ρ / 2)} ∩
      {x : σ → ℂ | ∀ s ∈ {x | x ∈ Y ∧ A x = y₀}, η ≤ dist x s}) := by
    rintro ⟨x, hx, hxy⟩
    have := hx.2 x ⟨hx.1.1, hxy⟩
    rw [dist_self] at this
    exact absurd hη (not_lt.2 this)
  have hnear := ((hKη.image A.continuous).isClosed.isOpen_compl).mem_nhds hy₀K
  filter_upwards [hnear, ball_mem_nhds y₀ (by linarith : (0 : ℝ) < ρ / 2)] with y hyK hyb
  rw [dist_zero_right]
  have hyK' : y ∈ closedBall y₀ (ρ / 2) := ball_subset_closedBall hyb
  by_cases hNy : {x | x ∈ Y ∧ A x = y}.encard = N
  swap
  · unfold fibreDiscr
    rw [dif_neg hNy, norm_zero]
    exact hε
  unfold fibreDiscr
  rw [dif_pos hNy]
  have hTcard : (Set.finite_of_encard_eq_coe hNy).toFinset.card = N := by
    have := (Set.finite_of_encard_eq_coe hNy).encard_eq_coe_toFinset_card
    rw [hNy] at this
    exact_mod_cast this.symm
  have hclose : ∀ x ∈ (Set.finite_of_encard_eq_coe hNy).toFinset,
      ∃ s ∈ hS₀fin.toFinset, dist x s < η := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    by_contra hno
    simp only [not_exists, not_and, not_lt] at hno
    apply hyK
    refine ⟨x, ⟨⟨hx.1, by rw [hx.2]; exact hyK'⟩, fun s hs => hno s (hS₀fin.mem_toFinset.2 hs)⟩, hx.2⟩
  choose! c hcS hcd using hclose
  obtain ⟨a, ha, b, hb, hab, hcab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by rw [hTcard]; exact hS₀card) hcS
  have hdist : dist a b < 2 * η := by
    calc dist a b ≤ dist a (c a) + dist (c a) b := dist_triangle _ _ _
      _ = dist a (c a) + dist b (c b) := by rw [hcab, dist_comm (c b) b]
      _ < η + η := add_lt_add (hcd a ha) (hcd b hb)
      _ = 2 * η := by ring
  have hmem : (a, b) ∈ (Set.finite_of_encard_eq_coe hNy).toFinset.offDiag :=
    Finset.mem_offDiag.2 ⟨ha, hb, hab⟩
  rw [← Finset.mul_prod_erase _ _ hmem, norm_mul]
  have h1 : ‖l a - l b‖ ≤ ‖l‖ * (2 * η) := by
    rw [← map_sub]
    refine (l.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [← dist_eq_norm]
    exact hdist.le
  have h2 : ‖∏ q ∈ (Set.finite_of_encard_eq_coe hNy).toFinset.offDiag.erase (a, b), (l q.1 - l q.2)‖ ≤
      C ^ (N * N) := by
    apply norm_prod_le_pow _ _ hC1
    · calc ((Set.finite_of_encard_eq_coe hNy).toFinset.offDiag.erase (a, b)).card
          ≤ (Set.finite_of_encard_eq_coe hNy).toFinset.offDiag.card := Finset.card_erase_le
        _ ≤ N * N := by rw [Finset.offDiag_card, hTcard]; exact Nat.sub_le _ _
    · intro q hq
      have hq' := Finset.mem_of_mem_erase hq
      rw [Finset.mem_offDiag, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hq'
      exact hC _ ⟨hq'.1.1, by rw [hq'.1.2]; exact hyK'⟩ _ ⟨hq'.2.1.1, by rw [hq'.2.1.2]; exact hyK'⟩
  calc ‖l a - l b‖ * _ ≤ ‖l‖ * (2 * η) * C ^ (N * N) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by have := mem_Ioi.1 hη; positivity)
    _ < ε := hηε
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
