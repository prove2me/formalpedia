-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.exists_implicit_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:37:42.61882+00:00
-- url     : https://prove2.me/submissions/9ff59721-dc06-4936-956b-e2820ca508dc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (f : E × ℂ → ℂ) (u : E × ℂ) (hf : ContDiffAt ℂ 1 f u) {c : ℂ} (hc : c ≠ 0)
    (hd : HasDerivAt (fun t => f (u.1, t)) c u.2) :
    ∃ (U : Set E) (τ : E → ℂ), IsOpen U ∧ u.1 ∈ U ∧ DifferentiableOn ℂ τ U ∧ τ u.1 = u.2 ∧
      ∀ w ∈ U, f (w, τ w) = f u := by
  have hfd : HasFDerivAt f (fderiv ℂ f u) u := (hf.differentiableAt one_ne_zero).hasFDerivAt
  have hi : HasFDerivAt (fun t : ℂ => (u.1, t)) (ContinuousLinearMap.inr ℂ E ℂ) u.2 := by
    first
    | exact hasFDerivAt_prodMk_right u.1 u.2
    | exact hasFDerivAt_prod_mk_right u.1 u.2
    | exact (hasFDerivAt_const u.1 u.2).prodMk (hasFDerivAt_id u.2)
    | exact (hasFDerivAt_const u.1 u.2).prod (hasFDerivAt_id u.2)
  have hcomp : HasFDerivAt (fun t : ℂ => f (u.1, t))
      ((fderiv ℂ f u).comp (ContinuousLinearMap.inr ℂ E ℂ)) u.2 := by
    have hfd' : HasFDerivAt f (fderiv ℂ f u) (u.1, u.2) := hfd
    exact hfd'.comp u.2 hi
  have heq : (fderiv ℂ f u).comp (ContinuousLinearMap.inr ℂ E ℂ) =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c := hcomp.unique hd.hasFDerivAt
  have hinv : ((fderiv ℂ f u).comp (ContinuousLinearMap.inr ℂ E ℂ)).IsInvertible := by
    rw [heq]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hc), ?_⟩
    first
    | (ext; simp)
    | (ext x; simp [mul_comm])
  have ev := IsContDiffImplicitAt.apply_implicitFunction hf one_ne_zero hinv
  have cd := IsContDiffImplicitAt.contDiffAt_implicitFunction hf one_ne_zero hinv
  have ev2 := IsContDiffImplicitAt.eventually_implicitFunction_apply_eq hf one_ne_zero hinv
  have hval : hf.implicitFunction one_ne_zero hinv u.1 = u.2 := (ev2.self_of_nhds).1 rfl
  have ecd : ∀ᶠ y in 𝓝 u.1, ContDiffAt ℂ 1 (hf.implicitFunction one_ne_zero hinv) y := by
    first
    | exact cd.eventually (by simp)
    | exact cd.eventually (by decide)
    | exact cd.eventually ENat.one_ne_top
  obtain ⟨U, hUsub, hUo, hUmem⟩ := eventually_nhds_iff.mp (ev.and ecd)
  exact ⟨U, hf.implicitFunction one_ne_zero hinv, hUo, hUmem,
    fun y hy => ((hUsub y hy).2.differentiableAt one_ne_zero).differentiableWithinAt, hval,
    fun y hy => (hUsub y hy).1⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
