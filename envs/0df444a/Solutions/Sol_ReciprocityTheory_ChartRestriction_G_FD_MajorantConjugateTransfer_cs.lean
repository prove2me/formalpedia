-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:26:36.01619+00:00
-- url     : https://prove2.me/submissions/3d7e36ff-6d04-4ad5-86ac-378aad40b69f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_maj_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_maj_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_Hf_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_Hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_Hf_sub_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_Hf_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_Hf_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos


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
open ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    ‖X.Hf x τ u v‖ ^ 2 ≤ X.maj x τ u * X.maj x τ v := by
  by_cases hv : v = 0
  · have h0 : X.Hf x τ u 0 = 0 := by
      have := Hf_sub_right X x τ u 0 0
      simpa using this
    rw [hv, h0, maj_zero X x τ]
    simp
  have hm : 0 < X.maj x τ v := X.maj_pos hx τ hv
  have hmu := maj_nonneg X hx τ u

  set H := X.Hf x τ u v with hH
  have hw := X.Hf_self hx τ ((X.maj x τ v : ℂ) • u - H • v)
  have hn := maj_nonneg X hx τ ((X.maj x τ v : ℂ) • u - H • v)
  simp only [Hf_sub_left, Hf_sub_right, Hf_smul_left, Hf_smul_right] at hw
  rw [X.Hf_self hx τ u, X.Hf_self hx τ v, ← Hf_conj X hx τ u v, ← hH, Complex.conj_ofReal] at hw
  have hHH : H * conj H = (Complex.normSq H : ℂ) := Complex.mul_conj H
  have e : ((X.maj x τ ((X.maj x τ v : ℂ) • u - H • v) : ℝ) : ℂ) =
      ((X.maj x τ v * (X.maj x τ v * X.maj x τ u - Complex.normSq H) : ℝ) : ℂ) := by
    rw [← hw]
    push_cast
    linear_combination (-(X.maj x τ v : ℂ)) * hHH
  have e' := Complex.ofReal_injective e
  rw [e'] at hn
  have hle : Complex.normSq H ≤ X.maj x τ v * X.maj x τ u := by
    by_contra hc
    push_neg at hc
    have : X.maj x τ v * (X.maj x τ v * X.maj x τ u - Complex.normSq H) < 0 :=
      mul_neg_of_pos_of_neg hm (by linarith)
    linarith
  rw [Complex.sq_norm]
  linarith [mul_comm (X.maj x τ u) (X.maj x τ v)]
end ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer
