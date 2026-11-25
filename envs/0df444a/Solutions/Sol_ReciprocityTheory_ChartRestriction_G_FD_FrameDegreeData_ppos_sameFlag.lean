-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ppos_sameFlag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:34:41.962916+00:00
-- url     : https://prove2.me/submissions/34464292-6a28-480d-84e8-3c21bd83e874

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_ppos_colP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_neg_of_perp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace FrameDegreeData
noncomputable section
variable {r : ℕ} (X : Data E r)
private theorem hermC_sub_left_of_natDim {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (u v w : Fin r → ℂ) : hermC τ G (u - v) w = hermC τ G u w - hermC τ G v w := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
private theorem hermC_eq_zero_of_mem_span' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (w : Fin r → ℂ)
    (S : Set (Fin r → ℂ)) (h : ∀ s ∈ S, hermC τ G w s = 0) {v : Fin r → ℂ}
    (hv : v ∈ Submodule.span ℂ S) : hermC τ G w v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp [hermC]
  | add x y _ _ hx hy =>
    have e : hermC τ G w (x + y) = hermC τ G w x + hermC τ G w y := by
      simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    rw [e, hx, hy, add_zero]
  | smul c x _ hx =>
    have e : hermC τ G w (c • x) = (starRingEnd ℂ) c * hermC τ G w x := by
      simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [e, hx, mul_zero]
end
end FrameDegreeData
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (h : X.SameFlag x x')
    (τ : X.Ψ) (u : Fin r → ℂ) : X.ppos x τ u = X.ppos x' τ u := by
  have hspan := h τ
  have hmem : ∀ y : Frame X.Ψ r, X.ppos y τ u ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat y τ) (Fin.castLE X.p0_le a)) := by
    intro y
    rw [X.ppos_eq]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have horth : ∀ y ∈ X.dom, ∀ c ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat y τ) (Fin.castLE X.p0_le a)),
      hermC τ.1 X.Gm (X.ppos y τ u - u) c = 0 := by
    intro y hy c hc
    refine hermC_eq_zero_of_mem_span' τ.1 X.Gm _ _ (fun s hs => ?_) hc
    obtain ⟨d, rfl⟩ := hs
    rw [hermC_sub_left_of_natDim]
    exact sub_eq_zero.2 (X.hermC_ppos_colP hy τ u d)
  set v := X.ppos x τ u - X.ppos x' τ u with hv
  have hvmem : v ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)) := by
    refine Submodule.sub_mem _ (hmem x) ?_
    rw [hspan]
    exact hmem x'
  have hvperp : ∀ c ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)),
      hermC τ.1 X.Gm v c = 0 := by
    intro c hc
    have e : v = (X.ppos x τ u - u) - (X.ppos x' τ u - u) := by
      rw [hv]
      abel
    rw [e, hermC_sub_left_of_natDim, horth x hx c hc, horth x' hx' c (hspan ▸ hc), sub_zero]
  by_contra hne
  have hne' : v ≠ 0 := sub_ne_zero.2 hne
  have hlt := X.neg_of_perp hx τ hne' (fun b => hvperp _ (Submodule.subset_span ⟨b, rfl⟩))
  rw [hvperp v hvmem] at hlt
  simp at hlt
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
