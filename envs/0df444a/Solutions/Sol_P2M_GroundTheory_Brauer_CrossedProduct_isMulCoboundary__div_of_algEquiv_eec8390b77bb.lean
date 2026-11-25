-- Prove2me | solution 1 for P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__div_of_algEquiv_eec8390b77bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:09:32.770046+00:00
-- url     : https://prove2.me/submissions/95676613-b3df-4c56-ac42-f92c53907dde

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_eq_single_of_mul_incl
import Theorems.Thm_GroundTheory_Brauer_AlgEquiv_exists_unit_conj
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_basis_apply
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_incl_mul_single
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_isUnit_u
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_incl
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_u
import Theorems.Thm_GroundTheory_Brauer_H2mul_mulEquivH2_mk
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_exists_unit_conj
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.CrossedProduct.basis_apply
attribute [local simp] GroundTheory.Brauer.H2mul.mulEquivH2_mk
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Brauer
open groupCohomology
universe u v
open GroundTheory.Brauer.CrossedProduct
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}
variable [FiniteDimensional K L] [IsGalois K L]
namespace GroundTheory.Brauer.CrossedProduct
theorem _root_.solution {g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
    (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g) (e : CrossedProduct hf ≃ₐ[K] CrossedProduct hg) :
    IsMulCoboundary₂ (f / g) := by
  obtain ⟨a, ha⟩ := exists_unit_conj
    ((e : CrossedProduct hf →ₐ[K] CrossedProduct hg).comp incl) (incl : L →ₐ[K] CrossedProduct hg)

  set φ : CrossedProduct hf → CrossedProduct hg := fun y => (a : CrossedProduct hg) * e y * ↑a⁻¹
    with hφ
  have φmul : ∀ y z, φ (y * z) = φ y * φ z := by
    intro y z
    simp only [hφ, map_mul, mul_assoc, Units.inv_mul_cancel_left]
  have φone : φ 1 = 1 := by
    simp only [hφ, map_one, mul_one, Units.mul_inv]
  have φincl : ∀ b, φ (incl b) = incl b := fun b => (ha b).symm
  obtain ⟨c, hw⟩ : ∃ c : (L ≃ₐ[K] L) → L, ∀ σ, φ (u σ) = single σ (c σ) :=
    ⟨fun σ => (φ (u σ)).coeff σ, fun σ =>
      eq_single_of_mul_incl σ _ fun b => by rw [← φincl, ← φmul, u_mul_incl, φmul, φincl]⟩
  have hc0 : ∀ σ, c σ ≠ 0 := by
    intro σ h0
    obtain ⟨w, hw'⟩ := (isUnit_u σ (hf := hf)).exists_right_inv
    have h := congrArg φ hw'
    rw [φmul, φone, hw σ, h0, single_zero, zero_mul] at h
    exact zero_ne_one h
  have key : ∀ σ τ, c σ * σ (c τ) * g (σ, τ) = f (σ, τ) * c (σ * τ) := by
    intro σ τ
    have h := congrArg φ (u_mul_u (hf := hf) σ τ)
    simp only [φmul, φincl] at h
    rw [hw σ, hw τ, hw (σ * τ), single_mul_single, incl_mul_single] at h
    exact single_injective _ h
  refine ⟨fun σ => Units.mk0 (c σ) (hc0 σ), fun σ τ => ?_⟩
  ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, val_smul_units, Units.val_mk0, Pi.div_apply]
  rw [div_mul_eq_mul_div, div_eq_div_iff (hc0 _) (g (σ, τ)).ne_zero]
  linear_combination key σ τ
end GroundTheory.Brauer.CrossedProduct
