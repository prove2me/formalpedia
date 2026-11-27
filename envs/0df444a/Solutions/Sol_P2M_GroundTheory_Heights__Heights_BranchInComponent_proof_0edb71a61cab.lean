-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BranchInComponent_proof_0edb71a61cab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:20.296555+00:00
-- url     : https://prove2.me/submissions/01629224-3811-4f9c-9e67-12cfc7cd0c83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchInComponent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchInComponent_differentiable_eval_a74d15f8973d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchInComponent_exists_open_prod_ne_zero_3bcf5e18f9ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_analyticOnNhd_of_differentiableOn_c966cce3f6fd


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
open MvPolynomial ComplexSets Metric Filter Topology Set
noncomputable section
open GroundTheory.Heights₂.Heights.BranchInComponent
namespace GroundTheory.Heights₂.Heights.BranchInComponent
theorem _root_.solution : BranchInComponent.Statement := by
  classical
  intro n I k q c
  by_contra hcon
  push Not at hcon
  set B : Set (Fin k → ℂ) := ball 0 c.radius with hB
  have hBo : IsOpen B := isOpen_ball
  have hBc : IsPreconnected B := (convex_ball (0 : Fin k → ℂ) c.radius).isPreconnected
  have hBne : B.Nonempty := ⟨0, mem_ball_self c.radius_pos⟩
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I

  have hch : ∀ J : I.minimalPrimes, ∃ g ∈ (J : Ideal (MvPolynomial (Fin n) ℂ)),
      ¬ EqOn (fun τ => eval (c.toFun τ) g) 0 B := by
    intro J
    have hJ := hcon J J.2
    simp only [Set.MapsTo, not_forall, exists_prop] at hJ
    obtain ⟨τ, hτB, hτZ⟩ := hJ
    simp only [zeroSet, mem_ofPred_eq, not_forall] at hτZ
    obtain ⟨g, hg, hgτ⟩ := hτZ
    exact ⟨g, hg, fun h => hgτ (h hτB)⟩
  choose g hgJ hgnz using hch
  let _ : Fintype I.minimalPrimes := hfin.fintype
  have han : ∀ J : I.minimalPrimes, AnalyticOnNhd ℂ (fun τ => eval (c.toFun τ) (g J)) B := fun J =>
    IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hBo
      ((differentiable_eval (g J)).comp_differentiableOn c.differentiableOn)
  obtain ⟨V, hVB, -, ⟨x, hx⟩, hV⟩ := exists_open_prod_ne_zero hBo hBc hBne Finset.univ
    (fun J τ => eval (c.toFun τ) (g J)) (fun J _ => han J) (fun J _ => hgnz J)

  set G : MvPolynomial (Fin n) ℂ := ∏ J : I.minimalPrimes, g J with hG
  have hGrad : G ∈ I.radical := by
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro J hJ
    rw [hG, ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ ⟨J, hJ⟩)]
    exact Ideal.mul_mem_right _ _ (hgJ ⟨J, hJ⟩)
  obtain ⟨N, hN⟩ := hGrad
  have h0 := c.mapsTo (hVB hx) _ hN
  rw [map_pow, hG, map_prod] at h0
  exact hV x hx (pow_eq_zero_iff'.1 h0).1
end GroundTheory.Heights₂.Heights.BranchInComponent
