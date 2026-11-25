-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_false_of_forms_vanish_c8ace799b146
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:15:56.135191+00:00
-- url     : https://prove2.me/submissions/ad21f782-660f-4559-bcd7-d25e6599e4da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreCoordGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_segQ_ccbce2b0c3b4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_segre_scaleBlock_124690bb4980
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_forms_b88abb73bfef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.SegreCoordGoodProj
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SegreCoordGoodProj
theorem _root_.solution (P : Ideal (MRing ι)) (hhom : IsMultiHomogIdeal P) (k0 : K) {r : ℕ}
    (L : Fin r → ((k : K) → ι k) → ℚ) (hL : ∀ t, IntOver ℚ (forms (segQ P) L) (segQ P t))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hV : ∀ j, ∑ t, (L j t : ℂ) * segre z t = 0) : False := by
  choose i1 hi1 using hz.1
  have hs : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi1 k
  obtain ⟨p, hpm, hp⟩ := hL i1
  let g0 : MvPolynomial (Fin r) ℚ →+* ℂ := eval₂Hom (algebraMap ℚ ℂ) 0
  have key : ∀ c : ℂ, c ≠ 0 → Polynomial.eval (c * segre z i1) (p.map g0) = 0 := by
    intro c hc
    have hzc := scaleBlock_mem_zeroLocus P hhom k0 hc hz
    have hcomp : (evQ P _ hzc).comp
        ((aeval (forms (segQ P) L) : MvPolynomial (Fin r) ℚ →ₐ[ℚ] _) : MvPolynomial (Fin r) ℚ →+* _) =
        g0 := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [g0]
      · intro j
        have h1 : ∑ t, (L j t : ℂ) * (c * segre z t) = c * ∑ t, (L j t : ℂ) * segre z t := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
        simp [g0, evQ_forms, segre_scaleBlock, h1, hV j]
    have := congrArg (evQ P _ hzc) hp
    rw [Polynomial.hom_eval₂, hcomp, evQ_segQ, segre_scaleBlock, map_zero] at this
    rw [Polynomial.eval_map]
    exact this
  have hinf : {x : ℂ | (p.map g0).IsRoot x}.Infinite := by
    refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro x hx
    have hx0 : x ≠ 0 := hx
    have := key (x / segre z i1) (div_ne_zero hx0 hs)
    rw [div_mul_cancel₀ x hs] at this
    exact this
  exact (hpm.map g0).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ hinf)
end GroundTheory.Heights₂.Heights.SegreCoordGoodProj
