-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.enorm_poin_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:39.21924+00:00
-- url     : https://prove2.me/submissions/9e3a08ba-8226-4c7e-9a6d-5bd8fd934af5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfB
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    ENNReal.ofReal ‖poin X la P x‖ ≤ ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ := by
  unfold poin
  have hχ : ∀ γ : X.Γ, ‖X.χ la γ.1‖ = 1 := fun γ => by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1
      (by rw [← norm_pow, h γ.1 γ.2, norm_one])
  have hn : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ = ‖P (lact γ.1 x)‖ := fun γ => by
    rw [norm_mul, norm_inv, hχ γ, inv_one, one_mul]
  by_cases hs : Summable fun γ : X.Γ => ‖P (lact γ.1 x)‖
  · calc ENNReal.ofReal ‖∑' γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖
        ≤ ENNReal.ofReal (∑' γ : X.Γ, ‖P (lact γ.1 x)‖) := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hn))
          exact hs.congr fun γ => (hn γ).symm
      _ = ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
          simp only [ofReal_norm_eq_enorm]
  · have htop : ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ = ⊤ := by
      by_contra h
      apply hs
      have h2 : Summable fun γ : X.Γ => ‖P (lact γ.1 x)‖₊ := by
        rw [← ENNReal.tsum_coe_ne_top_iff_summable]
        simpa only [enorm_eq_nnnorm] using h
      exact NNReal.summable_coe.2 h2
    rw [htop]
    exact le_top
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
