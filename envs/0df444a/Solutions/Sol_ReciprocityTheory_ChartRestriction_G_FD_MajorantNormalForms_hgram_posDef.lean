-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.hgram_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:47:06.937718+00:00
-- url     : https://prove2.me/submissions/0e494e76-4044-41ca-971a-0aaf0240e555

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_Hf_sum_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
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
private lemma maj_eq_lemma_4 (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj x τ v = (X.Hf x τ v v).re := by
  have hP : hermC τ.1 X.Gm (X.ppos x τ v) v = ∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) * (X.gramPos x τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b))) := by
    unfold Data.ppos
    rw [hermC_sum_left_lemma]
    simp only [Finset.sum_mul, hermC_conj τ.1 X.Gm_herm]
    conv_lhs => rw [Finset.sum_comm]
  unfold Data.maj Data.posPart Data.Hf
  rw [← hP, hermC_smul_sub_left_lemma_3, Complex.sub_re, Complex.mul_re]
  simp
private lemma hermC_smul_sub_right_lemma_6 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (y p q : Fin r → ℂ) :
    hermC σ G y (a • p - q) = conj a * hermC σ G y p - hermC σ G y q := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private lemma Hf_conj_lemma_7 (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) :
    conj (X.Hf x τ u w) = X.Hf x τ w u := by
  unfold Data.Hf
  rw [hermC_conj τ.1 X.Gm_herm, hermC_smul_sub_right_lemma_6, hermC_smul_sub_left_lemma_3,
    hermC_ppos_lemma_5 X x τ w u, map_ofNat]
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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    (Matrix.of fun a c => X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · ext a c
    show star (X.Hf x τ (col (mat x τ) c) (col (mat x τ) a)) =
      X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)
    rw [Complex.star_def, Hf_conj_lemma_7]
  have hy : star v ⬝ᵥ ((Matrix.of fun a c => X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)) *ᵥ v) =
      X.Hf x τ (∑ a, star (v a) • col (mat x τ) a) (∑ a, star (v a) • col (mat x τ) a) := by
    rw [Hf_sum_sum]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
      Complex.star_def, Complex.conj_conj]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  have hy0 : (∑ a, star (v a) • col (mat x τ) a) ≠ 0 := by
    intro h0
    have hmv : mat x τ *ᵥ (fun a => star (v a)) = ∑ a, star (v a) • col (mat x τ) a := by
      funext i
      show ∑ k, mat x τ i k * star (v k) = (∑ a, star (v a) • col (mat x τ) a) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [← hmv] at h0
    have h1 := Matrix.eq_zero_of_mulVec_eq_zero (hx τ).1 h0
    apply hv
    funext a
    have h2 := congrFun h1 a
    simpa using h2
  have hpos := X.maj_pos hx τ hy0
  rw [maj_eq_lemma_4 X x τ] at hpos
  have him := Complex.conj_eq_iff_im.mp (Hf_conj_lemma_7 X x τ (∑ a, star (v a) • col (mat x τ) a)
    (∑ a, star (v a) • col (mat x τ) a))
  rw [hy]
  exact Complex.lt_def.mpr ⟨hpos, him.symm⟩
end ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
