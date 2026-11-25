-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds.norm_mul_discr_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:13.316213+00:00
-- url     : https://prove2.me/submissions/85309759-2f4b-4794-874d-b14be93aa8cb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
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
open ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
open NumberField Complex Module Matrix
open scoped ComplexConjugate nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
theorem _root_.solution {x : E} (hx : x ≠ 0)
    (htr : ∀ β : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (x * β) = m) :
    1 ≤ |Algebra.norm ℚ x| * |(NumberField.discr E : ℚ)| := by
  classical
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_top, Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact top_ne_bot
  have hD0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ h10
  have hmem : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨β, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨m, hm⟩ := htr β
    refine ⟨m, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hm.symm
  have hsp : FractionalIdeal.spanSingleton (𝓞 E)⁰ x ≤ FractionalIdeal.dual ℤ ℚ 1 :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem
  have hdiff := coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)
  have hJ : FractionalIdeal.spanSingleton (𝓞 E)⁰ x *
      (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) ≤ 1 := by
    rw [hdiff]
    calc _ ≤ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) *
          (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
            first
            | exact mul_le_mul' hsp le_rfl
            | exact mul_right_mono hsp
            | exact FractionalIdeal.mul_right_mono _ hsp
      _ = 1 := mul_inv_cancel₀ hD0
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
  have hJ0 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x *
      (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    refine mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) ?_
    rw [hdiff]
    exact inv_ne_zero hD0
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hJ0
    rw [← hI]
    simp
  have hnorm := congrArg FractionalIdeal.absNorm hI
  rw [FractionalIdeal.coeIdeal_absNorm, map_mul, FractionalIdeal.absNorm_span_singleton,
    FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal E (𝓞 E)] at hnorm
  have h1 : (1 : ℚ) ≤ (Ideal.absNorm I : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h))
  rw [hnorm] at h1
  have h2 : (((NumberField.discr E).natAbs : ℕ) : ℚ) = |(NumberField.discr E : ℚ)| := by
    rw [Nat.cast_natAbs]
    push_cast
    rfl
  rw [h2] at h1
  exact h1
end ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
