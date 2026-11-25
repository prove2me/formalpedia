-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.gram_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:08:42.598556+00:00
-- url     : https://prove2.me/submissions/b01be620-5165-4e42-b153-5281fbb429ac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_col_mul_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_ppos_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_ppos_colP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_Hf_eq_of_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_Hf_eq_of_zero
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
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


section
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace MajorantNormalForms
open Matrix NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma hermC_sum_left_lemma {ι : Type} [Fintype ι] (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u : ι → ℂ) (v : ι → Fin r → ℂ) (y : Fin r → ℂ) :
    hermC τ G (∑ k, u k • v k) y = ∑ k, u k * hermC τ G (v k) y := by
  let f : (Fin r → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => hermC τ G x y
      map_add' := fun x x' => by
        simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum f (fun k => u k • v k) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h
private lemma hermC_sum_right_lemma_2 {ι : Type} [Fintype ι] (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Fin r → ℂ) (w : ι → ℂ) (z : ι → Fin r → ℂ) :
    hermC τ G x (∑ l, w l • z l) = ∑ l, conj (w l) * hermC τ G x (z l) := by
  let g : (Fin r → ℂ) →ₗ⋆[ℂ] ℂ :=
    { toFun := fun y => hermC τ G x y
      map_add' := fun y y' => by
        simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum g (fun l => w l • z l) Finset.univ
  simp only [map_smulₛₗ, smul_eq_mul] at h
  exact h
private lemma hermC_smul_sub_left_lemma_3 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (p q y : Fin r → ℂ) : hermC σ G (a • p - q) y = a * hermC σ G p y - hermC σ G q y := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private lemma hermC_ppos_lemma_5 (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hGp : Matrix.conjTranspose (X.gramPos x τ) = X.gramPos x τ := by
    ext a b
    exact hermC_conj τ.1 X.Gm_herm (col (mat x τ) (Fin.castLE X.p0_le b))
      (col (mat x τ) (Fin.castLE X.p0_le a))
  have hM : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b := by
    intro a b
    have h := congrFun (congrFun (show Matrix.conjTranspose ((X.gramPos x τ)⁻¹) =
      (X.gramPos x τ)⁻¹ by rw [Matrix.conjTranspose_nonsing_inv, hGp]) a) b
    exact h
  unfold Data.ppos
  rw [hermC_sum_left_lemma, hermC_sum_right_lemma_2]
  simp only [map_sum, map_mul, hM, hermC_conj τ.1 X.Gm_herm, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
end MajorantNormalForms
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
open Matrix NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {B : Matrix (Fin r) (Fin r) ℂ}
    (hBd : B.det ≠ 0) (hBt : ∀ a c : Fin r, c < a → B a c = 0)
    (hB : ∀ a c, X.Hf x τ (col (mat x τ * B) a) (col (mat x τ * B) c) = if a = c then 1 else 0) :
    gram τ.1 X.Gm (mat x τ * B) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  have hpos : ∀ a : Fin r, (a : ℕ) < X.p0 →
      X.ppos x τ (col (mat x τ * B) a) = col (mat x τ * B) a := by
    intro a ha
    rw [col_mul_eq, ppos_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < X.p0
    · have h := ppos_colP X hx τ ⟨k, hk⟩
      simp only [Data.colP] at h
      rw [show Fin.castLE X.p0_le ⟨(k : ℕ), hk⟩ = k from Fin.ext rfl] at h
      rw [h]
    · rw [hBt k a (Fin.lt_iff_val_lt_val.mpr (by omega))]
      simp
  have hzero : ∀ a : Fin r, X.p0 ≤ (a : ℕ) → X.ppos x τ (col (mat x τ * B) a) = 0 := by
    intro a ha
    have h1 : ∀ j : Fin r, (j : ℕ) < X.p0 →
        hermC τ.1 X.Gm (col (mat x τ * B) a) (col (mat x τ * B) j) = 0 := by
      intro j hj
      have hne : a ≠ j := fun h => by
        subst h
        omega
      have h := hB a j
      rw [if_neg hne] at h
      unfold Data.Hf at h
      rw [hermC_smul_sub_left_lemma_3, hermC_ppos_lemma_5 X x τ, hpos j hj] at h
      linear_combination h
    have hBinv : ∀ i j : Fin r, j < i → B⁻¹ i j = 0 := by
      haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hBd)
      intro i j hij
      exact Matrix.blockTriangular_inv_of_blockTriangular (b := id)
        (fun i' j' h' => hBt i' j' h' : B.BlockTriangular id) hij
    have hc : ∀ k, col (mat x τ) k = ∑ j, B⁻¹ j k • col (mat x τ * B) j := by
      intro k
      have hY : mat x τ = (mat x τ * B) * B⁻¹ := by
        rw [mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hBd), mul_one]
      conv_lhs => rw [hY]
      exact col_mul_eq (mat x τ * B) B⁻¹ k
    have h2 : ∀ b : Fin X.p0,
        hermC τ.1 X.Gm (col (mat x τ * B) a) (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
      intro b
      rw [hc, hermC_sum_right_lemma_2]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : (j : ℕ) < X.p0
      · rw [h1 j hj, mul_zero]
      · rw [hBinv j (Fin.castLE X.p0_le b)
          (Fin.lt_iff_val_lt_val.mpr (by simp only [Fin.coe_castLE]; omega)), map_zero, zero_mul]
    unfold Data.ppos
    simp only [h2, zero_mul, Finset.sum_const_zero, zero_smul]
  ext a c
  show hermC τ.1 X.Gm (col (mat x τ * B) a) (col (mat x τ * B) c) = diagonal _ a c
  rw [Matrix.diagonal_apply]
  have hBac := hB a c
  by_cases ha : (a : ℕ) < X.p0
  · rw [Hf_eq_of_pos X x τ (hpos a ha)] at hBac
    rw [hBac]
    simp only [sgn, if_pos ha, Complex.ofReal_one]
  · rw [Hf_eq_of_zero X x τ (hzero a (not_lt.mp ha))] at hBac
    rw [neg_eq_iff_eq_neg.mp hBac]
    simp only [sgn, if_neg ha, Complex.ofReal_neg, Complex.ofReal_one]
    split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
