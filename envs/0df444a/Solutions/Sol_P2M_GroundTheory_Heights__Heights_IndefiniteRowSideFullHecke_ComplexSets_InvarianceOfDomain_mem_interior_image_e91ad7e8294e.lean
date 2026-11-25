-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_mem_interior_image_e91ad7e8294e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:38.480542+00:00
-- url     : https://prove2.me/submissions/d31cb220-ceb9-4b1b-8253-a2e2df2002bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInvarianceOfDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBrouwerFixedPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInvarianceOfDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_brouwer_closedBall_bd2448227ce8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_exists_differentiable_near_09dee22485d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_exists_small_avoid_f177da726c82
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_exists_pos_le_d7a26518d166
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_radialPush_of_le_bcd60f3082f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_radialPush_mem_sphere_21c7ebc5639d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_continuousOn_radialPush_72f8328fa18f

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
open Metric Set MeasureTheory
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
theorem _root_.solution (hB : BrouwerFixedPoint.Statement) {f : (Fin n → ℝ) → Fin n → ℝ}
    {a : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hc : ContinuousOn f (closedBall a r))
    (hi : InjOn f (closedBall a r)) : f a ∈ interior (f '' closedBall a r) := by
  have hK : IsCompact (closedBall a r) := isCompact_closedBall a r

  obtain ⟨G, hGf⟩ : ∃ G : C(Fin n → ℝ, Fin n → ℝ), ∀ x ∈ closedBall a r, G (f x) = x := by
    have : CompactSpace (closedBall a r) := isCompact_iff_compactSpace.mp hK
    have hce : Topology.IsClosedEmbedding ((closedBall a r).domRestrict f) :=
      hc.domRestrict.isClosedEmbedding hi.injective
    obtain ⟨G, hG⟩ := ContinuousMap.exists_extension' hce ⟨Subtype.val, continuous_subtype_val⟩
    exact ⟨G, fun x hx => congrFun hG ⟨x, hx⟩⟩
  have hGa : G (f a) = a := hGf a (mem_closedBall_self hr.le)
  by_contra hno

  obtain ⟨ρ3, hρ3, hρG⟩ := Metric.continuousAt_iff.mp G.continuous.continuousAt (r / 4) (by positivity)
  obtain ⟨ρ, hρ, hρlt⟩ : ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ < ρ3 := ⟨ρ3 / 3, by positivity, by linarith⟩
  have hGnear : ∀ y, dist y (f a) ≤ 2 * ρ → dist (G y) a < r / 4 := fun y hy => by
    have h1 := hρG (show dist y (f a) < ρ3 by linarith)
    rwa [hGa] at h1

  obtain ⟨c, hcball, hcK⟩ : ∃ c, dist c (f a) < ρ ∧ c ∉ f '' closedBall a r := by
    by_contra! hall
    exact hno (mem_interior_iff_mem_nhds.2
      (Metric.mem_nhds_iff.2 ⟨ρ, hρ, fun c hc => hall c (mem_ball.1 hc)⟩))
  have hfK : IsCompact (f '' closedBall a r) := hK.image_of_continuousOn hc
  have hS1c : IsCompact (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) :=
    hfK.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hSc : IsCompact ((f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ) :=
    hS1c.union (isCompact_sphere c ρ)

  have hS1pos : ∀ y ∈ f '' closedBall a r ∩ {y | ρ ≤ dist y c}, 0 < dist (G y) a := by
    rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
    rw [hGf x hx, dist_pos]
    intro hxa
    subst hxa
    rw [mem_ofPred_eq, dist_comm] at hy
    linarith
  obtain ⟨δ0, hδ0, hδ0le⟩ :=
    exists_pos_le hS1c (G.continuous.dist continuous_const).continuousOn hS1pos
  obtain ⟨δ, hδ, hδδ0, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ r / 4 :=
    ⟨min δ0 (r / 4), lt_min hδ0 (by positivity), min_le_left _ _, min_le_right _ _⟩

  obtain ⟨P, hPd, hPS⟩ := exists_differentiable_near hSc G G.continuous (half_pos hδ)
  obtain ⟨v, hv, hPv⟩ := exists_small_avoid hPd c a hρ (half_pos hδ)
  have hQG : ∀ y ∈ (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ,
      ‖P y - v - G y‖ < δ := fun y hy => by
    have h1 := hPS y hy
    calc ‖P y - v - G y‖ = ‖(P y - G y) - v‖ := by congr 1; abel
      _ ≤ ‖P y - G y‖ + ‖v‖ := norm_sub_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add h1 hv
      _ = δ := add_halves δ
  have hQne : ∀ y ∈ (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ, P y - v ≠ a := by
    rintro y (hy | hy) hQa
    · have h1 := hQG y (Or.inl hy)
      have h2 := hδ0le y hy
      rw [hQa, norm_sub_rev] at h1
      rw [dist_eq_norm] at h2
      linarith
    · exact hPv y hy (eq_add_of_sub_eq hQa)

  have hfc : ∀ x ∈ closedBall a r, f x ≠ c := fun x hx h => hcK ⟨x, hx, h⟩
  have hΦS : ∀ x ∈ closedBall a r,
      radialPush c ρ (f x) ∈ (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ := by
    intro x hx
    by_cases hle : ρ ≤ dist (f x) c
    · rw [radialPush_of_le hρ hle]
      exact Or.inl ⟨⟨x, hx, rfl⟩, hle⟩
    · exact Or.inr (radialPush_mem_sphere (not_le.1 hle) (hfc x hx))
  have hΦc : ContinuousOn (fun x => radialPush c ρ (f x)) (closedBall a r) :=
    (continuousOn_radialPush c ρ).comp hc (fun x hx => hfc x hx)
  have hPΦ : ContinuousOn (fun x => P (radialPush c ρ (f x))) (closedBall a r) :=
    hPd.continuous.comp_continuousOn hΦc
  have hH : ContinuousOn (fun x => x - (P (radialPush c ρ (f x)) - v - a)) (closedBall a r) := by
    have h1 := (hPΦ.sub (continuousOn_const (c := v))).sub (continuousOn_const (c := a))
    exact continuousOn_id.sub h1

  obtain ⟨x, hxK, hfix⟩ := brouwer_closedBall hB (a := a) hr
    (h := fun x => x - (P (radialPush c ρ (f x)) - v - a)) hH (by
      intro x hx
      have hGx : G (f x) = x := hGf x hx
      rw [mem_closedBall, dist_eq_norm]
      show ‖x - (P (radialPush c ρ (f x)) - v - a) - a‖ ≤ r
      by_cases hle : ρ ≤ dist (f x) c
      · rw [radialPush_of_le hρ hle]
        have h1 := hQG (f x) (Or.inl ⟨⟨x, hx, rfl⟩, hle⟩)
        rw [hGx] at h1
        calc ‖x - (P (f x) - v - a) - a‖ = ‖-(P (f x) - v - x)‖ := by congr 1; abel
          _ = ‖P (f x) - v - x‖ := norm_neg _
          _ ≤ r := by linarith
      · have hzS := radialPush_mem_sphere (not_le.1 hle) (hfc x hx)
        have hxa : dist x a < r / 4 := by
          rw [← hGx]
          apply hGnear
          calc dist (f x) (f a) ≤ dist (f x) c + dist c (f a) := dist_triangle _ _ _
            _ ≤ 2 * ρ := by linarith [not_le.1 hle]
        generalize radialPush c ρ (f x) = z at hzS ⊢
        have h1 := hQG z (Or.inr hzS)
        have hza : dist (G z) a < r / 4 := by
          apply hGnear
          have hzc : dist z c = ρ := mem_sphere.mp hzS
          calc dist z (f a) ≤ dist z c + dist c (f a) := dist_triangle _ _ _
            _ ≤ 2 * ρ := by linarith
        rw [dist_eq_norm] at hxa hza
        calc ‖x - (P z - v - a) - a‖ = ‖(x - a) - (P z - v - G z) - (G z - a)‖ := by congr 1; abel
          _ ≤ ‖(x - a) - (P z - v - G z)‖ + ‖G z - a‖ := norm_sub_le _ _
          _ ≤ ‖x - a‖ + ‖P z - v - G z‖ + ‖G z - a‖ := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ r := by linarith)
  exact hQne _ (hΦS x hxK) (sub_eq_zero.mp (sub_eq_self.mp hfix))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
