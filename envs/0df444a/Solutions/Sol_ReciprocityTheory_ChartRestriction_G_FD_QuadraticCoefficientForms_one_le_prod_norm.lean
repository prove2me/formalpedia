-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.one_le_prod_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:31.587143+00:00
-- url     : https://prove2.me/submissions/4131c4b6-04b4-465f-b5f8-a7209732827a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticCoefficientForms_toCP_bij
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Classical
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
theorem _root_.solution (γ : E) (hint : IsIntegral ℤ γ) (hγ : γ ≠ 0) :
    1 ≤ ∏ τ : X.Ψ, ‖τ.1 γ‖ ^ 2 := by
  have hall : ∀ w : InfinitePlace E, w.IsComplex := fun w => IsTotallyComplex.isComplex w
  have h1 : ∏ τ : X.Ψ, ‖τ.1 γ‖ ^ 2 = ∏ w : TraceIntegralBasis.CP E, w.1 γ ^ 2 :=
    Fintype.prod_bijective (toCP X) (toCP_bij X) _ _ fun τ => by
      show _ = (InfinitePlace.mk τ.1 γ) ^ 2
      rw [InfinitePlace.apply]
  have h2 : ∏ w : TraceIntegralBasis.CP E, w.1 γ ^ 2 = ∏ w : InfinitePlace E, w γ ^ w.mult := by
    refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv hall) _ _ fun w => ?_
    show w.1 γ ^ 2 = w.1 γ ^ InfinitePlace.mult w.1
    rw [InfinitePlace.mult_isComplex w]
  rw [h1, h2, InfinitePlace.prod_eq_abs_norm]
  have hI : IsIntegral ℤ (Algebra.norm ℚ γ) := by
    first
    | exact Algebra.isIntegral_norm ℚ hint
    | exact Algebra.isIntegral_norm hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
  have hN : Algebra.norm ℚ γ ≠ 0 := Algebra.norm_ne_zero_iff.2 hγ
  rw [← hn] at hN ⊢
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hN (map_zero _)
  have h3 := Int.one_le_abs hn0
  simp only [algebraMap_int_eq, eq_intCast]
  push_cast
  exact_mod_cast h3
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
