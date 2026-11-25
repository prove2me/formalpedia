-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isGoodProj_of_intOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:25:10.006671+00:00
-- url     : https://prove2.me/submissions/3ea2311e-f4d1-4a18-8b49-11693bdd63f4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushC
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_evQ_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {P : Ideal (MRing ι)} (hK : Nonempty K) (hhom : IsMultiHomogIdeal P)
    {e r : ℕ} (hr : r ≤ e + 1) (L : Fin r → ((k : K) → ι k) → ℚ)
    (hL : ∀ t, IntOver ℚ (forms (segQ P) L) (segQ P t)) :
    IsGoodProj P (projOfForms (e := e) L) := by
  intro z hz hΨ
  obtain ⟨k0⟩ := hK
  choose i1 hi1 using hz.1
  have hs : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi1 k
  obtain ⟨p, hpm, hp⟩ := hL i1
  let g0 : MvPolynomial (Fin r) ℚ →+* ℂ := eval₂Hom (algebraMap ℚ ℂ) 0
  have key : ∀ c : ℂ, c ≠ 0 → Polynomial.eval (c * segre z i1) (p.map g0) = 0 := by
    intro c hc
    have hzc := scaleBlock_mem_zeroLocus P hhom k0 hc hz
    have hv : ∀ t, evQ P _ hzc (segQ P t) = c * segre z t := by
      intro t
      rw [segQ, evQ_mk, segMon, eval₂_prod]
      simp only [eval₂_X, scaleBlock, Finset.prod_mul_distrib, segre]
      congr 1
      simp
    have hforms : ∀ j, evQ P _ hzc (forms (segQ P) L j) = 0 := by
      intro j
      have hΨj := congrFun hΨ ⟨j.1, by omega⟩
      simp only [projOfForms, LinearMap.coe_mk, AddHom.coe_mk, dif_pos j.2, Fin.eta,
        Pi.zero_apply] at hΨj
      simp only [forms, map_sum, map_rat_smul, hv, Rat.smul_def]
      rw [show ∑ t, (L j t : ℂ) * (c * segre z t) = c * ∑ t, (L j t : ℂ) * segre z t by
        rw [Finset.mul_sum]; congr 1; funext t; ring, hΨj, mul_zero]
    have hcomp : (evQ P _ hzc).comp
        ((aeval (forms (segQ P) L) : MvPolynomial (Fin r) ℚ →ₐ[ℚ] _) :
          MvPolynomial (Fin r) ℚ →+* _) = g0 := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [g0]
      · intro j
        simp [g0, hforms]
    have := congrArg (evQ P _ hzc) hp
    rw [Polynomial.hom_eval₂, hcomp, hv, map_zero] at this
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
end ReciprocityTheory.ChartRestriction.G.Geo
