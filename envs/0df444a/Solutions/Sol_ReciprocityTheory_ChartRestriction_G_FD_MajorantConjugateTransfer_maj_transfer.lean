-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:49:48.576412+00:00
-- url     : https://prove2.me/submissions/dfd6271c-6096-46f5-ac61-a094ea5f2aeb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_ppos_colP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_ppos_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_ppos_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right


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
theorem _root_.solution {x y : Frame X.Ψ r} (hx : x ∈ X.dom) (hy : y ∈ X.dom) (τ : X.Ψ)
    (g g' : Matrix (Fin r) (Fin r) ℂ) (hgg' : ∀ w, Matrix.mulVec g (Matrix.mulVec g' w) = w)
    (hiso : ∀ u v, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g v) = hermC τ.1 X.Gm u v)
    (H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec g (X.colP x τ c) = ∑ a, K a • X.colP y τ a)
    (H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP y τ a = ∑ c, L c • Matrix.mulVec g (X.colP x τ c))
    (w : Fin r → ℂ) : X.maj y τ w = X.maj x τ (Matrix.mulVec g' w) := by
  have pp : ∀ (x' : Frame X.Ψ r) (v : Fin r → ℂ),
      X.posPart x' τ v = (hermC τ.1 X.Gm (X.ppos x' τ v) v).re := by
    intro x' v
    rw [X.hermC_ppos_self]
    rfl
  set u := Matrix.mulVec g' w with hu
  set p := Matrix.mulVec g (X.ppos x τ u) with hp
  set z := Matrix.mulVec g u with hz
  have hA : ∀ d : Fin r → ℂ, (∀ c', hermC τ.1 X.Gm d (X.colP y τ c') = 0) →
      ∀ c, hermC τ.1 X.Gm d (Matrix.mulVec g (X.colP x τ c)) = 0 := by
    intro d hd c
    obtain ⟨K, hK⟩ := H1 c
    rw [hK, hermC_sum_right]
    exact Finset.sum_eq_zero fun a _ => by rw [hermC_smul_right, hd, mul_zero]
  have hB : ∀ b, hermC τ.1 X.Gm z (X.colP y τ b) = hermC τ.1 X.Gm p (X.colP y τ b) := by
    intro b
    rw [← sub_eq_zero, ← hermC_sub_left]
    obtain ⟨L, hL⟩ := H2 b
    rw [hL, hermC_sum_right]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [hermC_smul_right, hz, hp, ← Matrix.mulVec_sub, hiso, hermC_sub_left,
      X.hermC_ppos_colP hx, sub_self, mul_zero]
  have h1 : X.ppos y τ z = X.ppos y τ p := by
    rw [X.ppos_eq, X.ppos_eq]
    simp only [hB]
  have h2 : ∀ c', hermC τ.1 X.Gm (X.ppos y τ p - p) (X.colP y τ c') = 0 := by
    intro c'
    rw [hermC_sub_left, X.hermC_ppos_colP hy, sub_self]
  have h3 : ∀ d, (∀ c', hermC τ.1 X.Gm d (X.colP y τ c') = 0) → hermC τ.1 X.Gm d p = 0 := by
    intro d hd
    rw [hp, X.ppos_eq x τ u, Matrix.mulVec_sum, hermC_sum_right]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Matrix.mulVec_smul, hermC_smul_right, hA d hd a, mul_zero]
  have key : hermC τ.1 X.Gm (X.ppos y τ z) z = hermC τ.1 X.Gm (X.ppos x τ u) u := by
    have e := h3 _ h2
    rw [hermC_sub_left, sub_eq_zero] at e
    rw [X.hermC_ppos_left hy τ z z, h1, ← X.hermC_ppos_left hy τ p p, e, hp, hiso,
      ← X.hermC_ppos_left hx τ u u]
  have hwz : w = z := (hgg' w).symm
  rw [hwz]
  simp only [Data.maj]
  rw [pp, pp, key, hz, hiso]
end ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer
