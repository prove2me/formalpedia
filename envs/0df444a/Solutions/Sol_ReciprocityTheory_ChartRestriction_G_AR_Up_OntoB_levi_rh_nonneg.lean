-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.levi_rh_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:24:47.44212+00:00
-- url     : https://prove2.me/submissions/157899a7-21f8-4e7a-a525-a225352bf0e6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_isOpen_OmF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_rhF_contDiffAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
open scoped ComplexConjugate ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)
variable {X x0}
variable (X x0)
variable {X x0}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
theorem _root_.solution (hGrad : RhGradFStatement (E := E)) (hx0 : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re := by
  have hG := hGrad r X x0 hx0 z hz ξ
  by_cases hC : ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) = 0
  · have hwd : ∀ w ∈ OmF X x0, ∀ j,
        wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) w = 0 := by
      intro w hw j
      have h := hGrad r X x0 hx0 w hw (Pi.single j 1)
      rw [hC, zero_mul] at h
      have h' := le_antisymm h (Complex.normSq_nonneg _)
      rw [Complex.normSq_eq_zero] at h'
      simpa [Pi.single_apply] using h'
    have hwdb : ∀ w ∈ OmF X x0, ∀ k,
        wdb (nd X) k (fun w => ((rhF X x0 w : ℝ) : ℂ)) w = 0 := by
      intro w hw k
      have hd : DifferentiableAt ℝ (rhF X x0) w := (rhF_contDiffAt hw).differentiableAt (by simp)
      have hf : ∀ v, fderiv ℝ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w v =
          ((fderiv ℝ (rhF X x0) w v : ℝ) : ℂ) := by
        intro v
        have hh : HasFDerivAt (fun w => ((rhF X x0 w : ℝ) : ℂ))
            (Complex.ofRealCLM.comp (fderiv ℝ (rhF X x0) w)) w :=
          Complex.ofRealCLM.hasFDerivAt.comp w hd.hasFDerivAt
        rw [hh.fderiv]
        rfl
      have h0 := hwd w hw k
      simp only [wd, hf] at h0
      simp only [wdb, hf]
      set p := fderiv ℝ (rhF X x0) w (bas (nd X) k)
      set q := fderiv ℝ (rhF X x0) w (Complex.I • bas (nd X) k)
      have h2 : (p : ℂ) - Complex.I * (q : ℂ) = 0 := by
        rcases div_eq_zero_iff.mp h0 with h0 | h0
        · exact h0
        · norm_num at h0
      have hp : p = 0 := by
        have h3 := congrArg Complex.re h2
        simpa using h3
      have hq : q = 0 := by
        have h3 := congrArg Complex.im h2
        simpa using h3
      rw [hp, hq]
      simp
    have hL : leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ = 0 := by
      unfold leviV
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      have hev : wdb (nd X) k (fun w => ((rhF X x0 w : ℝ) : ℂ)) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [(isOpen_OmF X x0).mem_nhds hz] with w hw using hwdb w hw k
      have hfd : fderiv ℝ (wdb (nd X) k (fun w => ((rhF X x0 w : ℝ) : ℂ))) z = 0 := by
        rw [hev.fderiv_eq]
        simp
      simp [wd, hfd]
    rw [hL]
    simp
  · have hCpos : (0 : ℝ) < ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hC)
    have h0 : ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) * 0 ≤
        ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) *
          (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re := by
      rw [mul_zero]
      exact le_trans (Complex.normSq_nonneg _) hG
    exact le_of_mul_le_mul_left h0 hCpos
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
