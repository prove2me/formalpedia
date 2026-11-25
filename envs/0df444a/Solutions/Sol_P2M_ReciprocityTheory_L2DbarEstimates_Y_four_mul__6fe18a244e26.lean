-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_Y_four_mul__6fe18a244e26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:04.543419+00:00
-- url     : https://prove2.me/submissions/6ed8a790-7e32-4699-98e8-27029d0374cd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fm_conv
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fm_fourCoeff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fsFun_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ComplexConjugate
noncomputable section
attribute [local instance] ReciprocityTheory.L2DbarEstimates.Y._p2m_local_instance_19aabe418c_38
attribute [local instance] ReciprocityTheory.L2DbarEstimates.Y._p2m_local_instance_19aabe418c_40
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (f : ℕ) : FOURMulStatement' f := by
  intro Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν
  have hopen : IsOpen (tube f Ω) := hΩ.preimage (by fun_prop)
  have hmem : ∀ x : Fin f → ℝ, (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) ∈ tube f Ω := by
    intro x
    show (fun k => ((x k : ℂ) + (b k : ℂ) * Complex.I).im) ∈ Ω
    convert hb using 1
    funext k
    simp
  have hc : ∀ hh : (Fin f → ℂ) → ℂ, DifferentiableOn ℂ hh (tube f Ω) →
      Continuous (fmLine hh b) := by
    intro hh hd
    have hcc : Continuous (fun y : Fin f → ℝ => (fun k => (y k : ℂ) + (b k : ℂ) * Complex.I)) := by
      fun_prop
    refine continuous_iff_continuousAt.2 fun y => ?_
    exact ((hd _ (hmem y)).differentiableAt (hopen.mem_nhds (hmem y))).continuousAt.comp
      hcc.continuousAt
  have hper : ∀ hh : (Fin f → ℂ) → ℂ,
      (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, hh (s + fun k => (m k : ℂ)) = hh s) →
      ∀ x (n : Fin f → ℤ), fmLine hh b (x + fun i => (n i : ℝ)) = fmLine hh b x := by
    intro hh hp x n
    have := hp _ (hmem x) n
    simp only [fmLine]
    convert this using 2
    funext k
    simp only [Pi.add_apply]
    push_cast
    ring
  have hper12 : ∀ x (n : Fin f → ℤ),
      fmLine (h1 * h2) b (x + fun i => (n i : ℝ)) = fmLine (h1 * h2) b x := by
    intro x n
    show fmLine h1 b _ * fmLine h2 b _ = fmLine h1 b x * fmLine h2 b x
    rw [hper h1 hp1, hper h2 hp2]
  let F1 : C(UnitAddTorus (Fin f), ℂ) :=
    ⟨fsFun (fmLine h1 b), fsFun_continuous _ (hc h1 hd1) (hper h1 hp1)⟩
  let F2 : C(UnitAddTorus (Fin f), ℂ) :=
    ⟨fsFun (fmLine h2 b), fsFun_continuous _ (hc h2 hd2) (hper h2 hp2)⟩
  have e12 : fsFun (fmLine (h1 * h2) b) = ⇑F1 * ⇑F2 := rfl
  rw [fm_fourCoeff (h1 * h2) b hper12, e12]
  have H := (fm_conv F1 F2 ν).mul_left (Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)))
  refine H.congr_fun fun ν' => ?_
  rw [fm_fourCoeff h1 b (hper h1 hp1), fm_fourCoeff h2 b (hper h2 hp2)]
  have hE : Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)) =
      Complex.exp (2 * Real.pi * ∑ k, (ν' k : ℂ) * (b k : ℂ)) *
        Complex.exp (2 * Real.pi * ∑ k, ((ν - ν') k : ℂ) * (b k : ℂ)) := by
    rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
    congr 3
    funext k
    simp only [Pi.sub_apply, Int.cast_sub]
    ring
  rw [hE]
  simp only [F1, F2, ContinuousMap.coe_mk]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
