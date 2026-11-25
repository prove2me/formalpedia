-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.maj_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:30.871057+00:00
-- url     : https://prove2.me/submissions/198cb588-549f-4f0b-87b1-1d96f67f6a67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Jp_Jp__4f74ff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Jp_add__70eb83
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Jp_adj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Jp_smul__7bc6d8
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermitian_pairing_Je_Je_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermitian_pairing_e_Je
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hsym
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable {x : Frame X.Ψ r} {τ : X.Ψ}
variable {e : Fin r → ℂ} (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ) (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0)
  (hq : X.d2q x τ e ≠ 0) (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
include hx he hq hself
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (w : Fin r → ℂ) (hw1 : hermC τ.1 X.Gm w e = 0)
    (hw2 : hermC τ.1 X.Gm w (X.Jp x τ e) = 0) (a b : ℂ) :
    X.maj x τ (w + a • e + b • X.Jp x τ e) =
      Complex.normSq a * X.maj x τ e + Complex.normSq b * X.maj x τ e + X.maj x τ w := by
  have k1 : hermC τ.1 X.Gm (X.Jp x τ w) e = 0 := by rw [Jp_adj X hx, hw2]
  have k2 : hermC τ.1 X.Gm (X.Jp x τ w) (X.Jp x τ e) = 0 := by
    rw [Jp_adj X hx, Jp_Jp X hx, hw1]
  have k3 : hermC τ.1 X.Gm (X.Jp x τ e) w = 0 := by rw [hsym, hw2, map_zero]
  have k4 : hermC τ.1 X.Gm e w = 0 := by rw [hsym, hw1, map_zero]
  have k5 := hermitian_pairing_Je_Je_zero X hx he
  have k6 : hermC τ.1 X.Gm (X.Jp x τ e) e = X.Hf x τ e e := rfl
  have k7 : hermC τ.1 X.Gm e (X.Jp x τ e) = X.Hf x τ e e := hermitian_pairing_e_Je X hx
  have h3 : X.Hf x τ (w + a • e + b • X.Jp x τ e) (w + a • e + b • X.Jp x τ e) =
      a * conj a * X.Hf x τ e e + b * conj b * X.Hf x τ e e + X.Hf x τ w w := by
    show hermC τ.1 X.Gm (X.Jp x τ (w + a • e + b • X.Jp x τ e)) (w + a • e + b • X.Jp x τ e) =
      a * conj a * X.Hf x τ e e + b * conj b * X.Hf x τ e e + hermC τ.1 X.Gm (X.Jp x τ w) w
    rw [Jp_add, Jp_add, Jp_smul, Jp_smul, Jp_Jp X hx]
    simp only [hC_add_left, hC_smul_left, hC_add_right, hC_smul_right, k1, k2, k3, k4, k5, k6, k7,
      he]
    ring
  rw [hself, hself, hself, Complex.mul_conj, Complex.mul_conj] at h3
  exact_mod_cast h3
end ReciprocityTheory.ChartRestriction.G.FD.Data
