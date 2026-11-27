-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RatPrimeDense_proof_9d77bb516c00
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:57:27.203862+00:00
-- url     : https://prove2.me/submissions/71de801e-6446-45b8-b3fd-10d57bf9d5ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRatPrimeDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiniteSeparatingModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsBounded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolyNonvanishDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRatPrimeDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RatPrimeDense_continuous_aeval_9170a0851d8e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace RatPrimeDense
theorem _root_.solution (h₁ : FiniteSeparatingModel.Statement) (h₂ : RootsNear.Statement)
    (h₃ : RootsBounded.Statement) (h₄ : PolyNonvanishDense.Statement) : RatPrimeDense.Statement := by
  intro σ _ P f hP hf x hx
  obtain ⟨e, ℓ, u, G, c, D, hG, hc, hD, hint, hGz, hcf, hlift, hsep⟩ := h₁ σ P f x hP hf hx
  set L : (σ → ℂ) → Fin e → ℂ := fun z j => aeval z (ℓ j) with hL
  have hLc : Continuous L := continuous_pi fun j => RatPrimeDense.continuous_aeval (ℓ j)
  have huc : Continuous fun z : σ → ℂ => aeval z u := RatPrimeDense.continuous_aeval u
  have hZ : IsClosed {z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun g => isClosed_iInter fun _ =>
      isClosed_eq (RatPrimeDense.continuous_aeval g) continuous_const

  choose p hp hpz using hint
  choose R hR using fun i => h₃ e (p i) (hp i) (L x)
  set Rb : ℝ := ∑ i, max (R i) 0
  have hRb : 0 ≤ Rb := Finset.sum_nonneg fun i _ => le_max_right _ _
  rw [Metric.mem_closure_iff]
  intro ε hε
  set C := ({z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} ∩ Metric.closedBall 0 Rb) ∩ {z | ε ≤ dist z x}
  have hCc : IsCompact C := ((isCompact_closedBall 0 Rb).inter_left hZ).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  set φ : (σ → ℂ) → ℝ := fun z => dist (L z) (L x) + dist (aeval z u) (aeval x u)
  have hφc : Continuous φ :=
    (hLc.dist continuous_const).add (huc.dist continuous_const)
  obtain ⟨δ, hδ, hδC⟩ : ∃ δ > 0, ∀ z ∈ C, δ ≤ φ z := by
    rcases C.eq_empty_or_nonempty with hC | hC
    · exact ⟨1, one_pos, by simp [hC]⟩
    obtain ⟨z₀, hz₀, hmin⟩ := hCc.exists_isMinOn hC hφc.continuousOn
    refine ⟨φ z₀, ?_, fun z hz => hmin hz⟩
    refine lt_of_le_of_ne (add_nonneg dist_nonneg dist_nonneg) fun h0 => ?_
    have h1 := (add_eq_zero_iff_of_nonneg dist_nonneg dist_nonneg).mp h0.symm
    have := hsep z₀ hz₀.1.1 (dist_eq_zero.mp h1.1) (dist_eq_zero.mp h1.2)
    have h2 := hz₀.2
    simp only [Set.mem_ofPred_eq, this, dist_self] at h2
    exact absurd h2 (not_le.mpr hε)

  have hE : ∀ᶠ y in 𝓝 (L x), (∃ t : ℂ, G.eval₂ (aeval y).toRingHom t = 0 ∧
      dist t (aeval x u) < δ / 2) ∧ (∀ i, ∀ t : ℂ, (p i).eval₂ (aeval y).toRingHom t = 0 → ‖t‖ ≤ R i) ∧
      dist y (L x) < δ / 2 :=
    (h₂ e G hG (L x) (aeval x u) (hGz x hx) (δ / 2) (half_pos hδ)).and
      ((eventually_all.mpr hR).and (Metric.ball_mem_nhds _ (half_pos hδ)))
  obtain ⟨y, ⟨⟨t, ht, htd⟩, hyR, hyd⟩, hyB⟩ := (mem_closure_iff_nhds.mp
    (h₄ e (D * c) (mul_ne_zero hD hc) (L x)) _ hE)
  simp only [Set.mem_ofPred_eq, map_mul, mul_ne_zero_iff] at hyB
  obtain ⟨z, hz, hzy, hzt⟩ := hlift y t hyB.1 ht
  have hzL : L z = y := hzy
  refine ⟨z, ⟨hz, hcf z hz (by rw [hzy]; exact hyB.2)⟩, ?_⟩
  have hzR : z ∈ Metric.closedBall 0 Rb := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hRb]
    intro i
    have := hyR i (z i) (by rw [← hzL]; exact hpz i z hz)
    exact this.trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right (R j) 0) (Finset.mem_univ i)))
  by_contra hfar
  have hφz : φ z < δ := by
    change dist (L z) (L x) + dist (aeval z u) (aeval x u) < δ
    rw [hzL, hzt]
    linarith
  exact absurd (hδC z ⟨⟨hz, hzR⟩, by show ε ≤ dist z x; rw [dist_comm]; exact not_lt.mp hfar⟩) (not_le.mpr hφz)
end RatPrimeDense
end GroundTheory.Heights₂.Heights.HilbertSamuel
