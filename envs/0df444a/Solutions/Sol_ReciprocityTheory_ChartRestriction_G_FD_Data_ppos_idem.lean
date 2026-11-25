-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:09:59.762072+00:00
-- url     : https://prove2.me/submissions/4081a0e2-8551-40ad-9144-2d00c668bc6b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
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
end herm
namespace Data
variable {r : ℕ} (X : Data E r)
private lemma hermC_finset_sum_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    (s : Finset ι) (f : ι → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, f i) w = ∑ i ∈ s, hermC τ G (f i) w := by
  induction s using Finset.cons_induction with
  | empty => simp [hC_zero_left]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hC_add_left, ih]
private lemma sum_mul_mul_eq_of_mul_eq_one {n : ℕ} (k : Fin n → ℂ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : A * B = 1) (a : Fin n) : ∑ b, (∑ a', k a' * A a' b) * B b a = k a := by
  calc ∑ b, (∑ a', k a' * A a' b) * B b a = Matrix.vecMul (Matrix.vecMul k A) B a := rfl
    _ = Matrix.vecMul k (A * B) a := by rw [Matrix.vecMul_vecMul]
    _ = k a := by rw [h, Matrix.vecMul_one]
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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.ppos x τ (X.ppos x τ v) = X.ppos x τ v := by
  have hdet : (X.gramPos x τ).det ≠ 0 := by
    have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    intro h0
    have h1 : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = 0 := h0
    rw [h1] at h
    simp at h
  have hinv : X.gramPos x τ * (X.gramPos x τ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hP : ∀ b, hermC τ.1 X.Gm (X.ppos x τ v) (col (mat x τ) (Fin.castLE X.p0_le b)) =
      ∑ a', (∑ b', hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b')) * (X.gramPos x τ)⁻¹ b' a') *
        X.gramPos x τ a' b := by
    intro b
    simp only [ppos, hermC_finset_sum_left, hC_smul_left]
    rfl
  show ∑ a : Fin X.p0, (∑ b : Fin X.p0, hermC τ.1 X.Gm (X.ppos x τ v) (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a) • col (mat x τ) (Fin.castLE X.p0_le a) = X.ppos x τ v
  simp only [hP]
  simp only [sum_mul_mul_eq_of_mul_eq_one (fun a' => ∑ b', hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b')) * (X.gramPos x τ)⁻¹ b' a')
    _ _ hinv]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.Data
