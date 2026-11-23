-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Jp_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:30.53411+00:00
-- url     : https://prove2.me/submissions/c8f0d549-7580-47dd-91e2-cb7af4518ac9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_sub_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_zero_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable section
section herm
variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
private lemma hermC_sub_left_section (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
private lemma hermC_add_right_section (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
private lemma hermC_smul_right_section (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (c • v) = conj c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end herm
namespace Data
variable {r : ℕ} (X : Data E r)
private lemma hermC_Gm_eq_conj_swap (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm u w = conj (hermC τ.1 X.Gm w u) := by
  have hG : ∀ a b, τ.1 (X.Gm a b) = conj (τ.1 (X.Gm b a)) := fun a b => by
    rw [← X.Gm_herm b a, cc]
    first
      | exact NumberField.IsCMField.complexEmbedding_complexConj E _ _
      | exact (NumberField.IsCMField.complexEmbedding_complexConj E _ _).symm
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hG a b]
  ring
private lemma hermC_finset_sum_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    (s : Finset ι) (f : ι → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, f i) w = ∑ i ∈ s, hermC τ G (f i) w := by
  induction s using Finset.cons_induction with
  | empty => simp [hC_zero_left]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hC_add_left, ih]
private lemma hermC_finset_sum_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    (s : Finset ι) (f : ι → Fin r → ℂ) (u : Fin r → ℂ) :
    hermC τ G u (∑ i ∈ s, f i) = ∑ i ∈ s, hermC τ G u (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [hermC]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hermC_add_right_section, ih]
private lemma hermC_ppos_left_eq_ppos_right_frame (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hH : (X.gramPos x τ).IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply]
    exact (X.hermC_Gm_eq_conj_swap τ (col (mat x τ) (Fin.castLE X.p0_le a)) (col (mat x τ) (Fin.castLE X.p0_le b))).symm
  have hGi : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b :=
    fun a b => hH.inv.apply a b
  simp only [ppos, hermC_finset_sum_left, hermC_finset_sum_right, hC_smul_left, hermC_smul_right_section, map_sum,
    map_mul]
  simp only [← X.hermC_Gm_eq_conj_swap, hGi, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
section perTau
variable (x : Frame X.Ψ r) (τ : X.Ψ) (e : Fin r → ℂ) (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ)
variable {x τ e}
variable (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0) (hq : X.d2q x τ e ≠ 0)
include hx he hq
end perTau
end Data
end
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.Jp x τ u) w = hermC τ.1 X.Gm u (X.Jp x τ w) := by
  simp only [Jp, hermC_sub_left_section, hC_sub_right, hC_smul_left, hermC_smul_right_section, X.hermC_ppos_left_eq_ppos_right_frame,
    map_ofNat]
end ReciprocityTheory.ChartRestriction.G.FD.Data
