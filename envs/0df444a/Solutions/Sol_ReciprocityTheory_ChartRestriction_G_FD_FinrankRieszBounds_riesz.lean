-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds.riesz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:51:06.172624+00:00
-- url     : https://prove2.me/submissions/0ebd7e01-77e0-44f9-802b-f087f091e4a0

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_Hf_zero_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_smul_fam_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_inner_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_smul_left
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
variable (z : Frame X.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ X.dom)]
namespace ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds
theorem _root_.solution (δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ) :
    ∃ d : VT (X := X) z ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ, δ τ (u τ) = X.Hf z τ (u τ) (d.val τ) := by
  classical
  let ℓ : VT (X := X) z ξ →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∑ τ, (δ τ (u.val τ)).re
      map_add' := fun u v => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [VT.val_add, Pi.add_apply, map_add, Complex.add_re]
      map_smul' := fun c u => by
        rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [VT.val_smul, Pi.smul_apply, ← Complex.coe_smul, map_smul, smul_eq_mul,
          Complex.re_ofReal_mul] }
  let d := (InnerProductSpace.toDual ℝ (VT (X := X) z ξ)).symm (LinearMap.toContinuousLinearMap ℓ)
  refine ⟨d, fun u hu τ0 => ?_⟩
  have hd : ∀ v : VT (X := X) z ξ, inner ℝ d v = ℓ v := fun v => by
    rw [InnerProductSpace.toDual_symm_apply]
    rfl

  have key : ∀ w ∈ X.Uz z ξ, (δ τ0 (w τ0)).re = (X.Hf z τ0 (w τ0) (d.val τ0)).re := by
    intro w hw
    let s : X.Ψ → ℂ := fun τ => if τ = τ0 then 1 else 0
    have hw' := MajorantOperators.smul_fam_mem s hw
    have h := hd (VT.mk _ hw')
    rw [inner_eq] at h
    simp only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, VT.val_mk, MajorantOperators.gI] at h
    rw [Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ, MajorantOperators.Hf_zero_right])
      (fun h => absurd (Finset.mem_univ τ0) h),
      Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ]) (fun h => absurd (Finset.mem_univ τ0) h)]
      at h
    simp only [s, if_true, one_smul] at h
    rw [← h, ← UnipotentCoefficientShift.Hf_conj hz.out, Complex.conj_re]
  have h1 := key u hu
  have h2 := key _ (MajorantOperators.smul_fam_mem (fun _ => Complex.I) hu)
  simp only [map_smul, smul_eq_mul, UnipotentCoefficientShift.Hf_smul_left, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub] at h2
  apply Complex.ext
  · exact h1
  · linarith
end ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds
