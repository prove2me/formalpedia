-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds.maj_csmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:47:23.448253+00:00
-- url     : https://prove2.me/submissions/73488bd6-ca04-47a0-85dc-73a803c7ccee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscreteLatticeMinimum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankRieszBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds
open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds
theorem _root_.solution {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj z τ (c • v) = ‖c‖ ^ 2 * X.maj z τ v := by
  have hl : ∀ w, hermC τ.1 X.Gm (c • v) w = c * hermC τ.1 X.Gm v w := by
    intro w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hr : hermC τ.1 X.Gm v (c • v) = conj c * hermC τ.1 X.Gm v v := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hcc : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hH : hermC τ.1 X.Gm (c • v) (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hl, hr, ← mul_assoc, hcc]
  have hP : X.posPart z τ (c • v) = ‖c‖ ^ 2 * X.posPart z τ v := by
    simp only [Data.posPart, hl, map_mul]
    rw [← Complex.re_ofReal_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hcc]
    ring
  simp only [Data.maj, hP, hH, Complex.re_ofReal_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds
