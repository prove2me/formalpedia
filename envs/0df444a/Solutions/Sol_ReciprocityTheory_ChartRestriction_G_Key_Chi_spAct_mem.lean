-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:13.562409+00:00
-- url     : https://prove2.me/submissions/bb83af42-5189-4116-96c3-64651ef8b293

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sub_conjTranspose_of_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_re_pos_of_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sp_keyH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_isUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_isSymm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_real_quad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) : spAct γ τ ∈ SiegelH (Fin g) := by
  have hj := jAut_isUnit hγ hτ
  have hs := spAct_isSymm hγ hτ.1 hj
  refine ⟨hs, ?_⟩
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    have h := congrFun (congrFun hs.eq i) j
    simp only [Matrix.transpose_apply] at h
    simp [Matrix.conjTranspose_apply, h]
  · intro x hx
    rw [star_trivial]
    have hJh : IsUnit (jAut γ τ)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hj.star
    have hk := sp_keyH hγ τ
    have e1 : spAct γ τ - (spAct γ τ)ᴴ = ((jAut γ τ)⁻¹)ᴴ * (τ - τᴴ) * (jAut γ τ)⁻¹ := by
      rw [← hk, show spAct γ τ = nAut γ τ * (jAut γ τ)⁻¹ from rfl, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_nonsing_inv, Matrix.mul_sub, Matrix.sub_mul]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ hJh, Matrix.one_mul]
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv _ hj, Matrix.mul_one]
    have e2 : imC (spAct γ τ) = ((jAut γ τ)⁻¹)ᴴ * imC τ * (jAut γ τ)⁻¹ := by
      have h2I : (2 * Complex.I) ≠ 0 := by simp
      apply smul_right_injective _ h2I
      show (2 * Complex.I) • imC (spAct γ τ) = (2 * Complex.I) • (((jAut γ τ)⁻¹)ᴴ * imC τ * (jAut γ τ)⁻¹)
      rw [← sub_conjTranspose_of_symm hs, e1, sub_conjTranspose_of_symm hτ.1, Matrix.mul_smul,
        Matrix.smul_mul]
    have hxc : (fun i => (x i : ℂ)) ≠ 0 := by
      intro h
      apply hx
      funext i
      have := congrFun h i
      simpa using this
    have hw : (jAut γ τ)⁻¹ *ᵥ (fun i => (x i : ℂ)) ≠ 0 := by
      intro h
      apply hxc
      have := congrArg (jAut γ τ *ᵥ ·) h
      simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hj] using this
    have hq := real_quad (spAct γ τ) x
    rw [e2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (star fun i => (x i : ℂ)), ← Matrix.star_mulVec] at hq
    have hpos := re_pos_of_posDef hτ.2 hw
    have hre := congrArg Complex.re hq
    rw [Complex.ofReal_re] at hre
    rw [hre]
    exact hpos
end ReciprocityTheory.ChartRestriction.G.Key.Chi
