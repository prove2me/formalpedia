-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.chiU_spDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:00:22.146335+00:00
-- url     : https://prove2.me/submissions/22bafde1-1f55-4de5-9628-fbe90bf87cdb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_mulVec_halfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_cMat_spDiag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_spDiag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_spDiag_inv
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero
import Theorems.Thm_ReciprocityTheory_PTheta_thetaGL_holds


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
theorem _root_.solution {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : ChiAtU g (spDiag U) := by
  intro n n'
  obtain ⟨e, he⟩ : ∃ e : ℂ,
      e = ((((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ).det : ℤ) : ℂ) := ⟨_, rfl⟩
  have hjd : ∀ τ, (jAut (spDiag U) τ).det = e := by
    intro τ
    rw [jAut_spDiag, Matrix.det_transpose, he]
    exact (RingHom.map_det (Int.castRingHom ℂ) _).symm
  have he2 : e * e = 1 := by
    have hu := (Matrix.isUnit_iff_isUnit_det _).1
      (Units.isUnit (U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ))
    rcases Int.isUnit_iff.1 hu with h | h <;> rw [he, h] <;> norm_num
  refine ⟨((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ)ᵀ *ᵥ n,
    (U : Matrix (Fin g) (Fin g) ℤ) *ᵥ n', e, ?_, ?_⟩
  · calc e ^ 4 = (e * e) * (e * e) := by ring
      _ = 1 := by rw [he2, one_mul]
  · intro τ _ z
    have hz : zAct (spDiag U) τ z = (U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)) *ᵥ z := by
      rw [zAct, jAut_spDiag_inv, Matrix.transpose_transpose]
    have hs : spAct (spDiag U) τ = (U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)) * τ *
        ((U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ := by
      rw [spAct, jAut_spDiag_inv, cMat_spDiag]
      simp
    have hx : expArg (spDiag U) τ z = 0 := by simp [expArg, cMat_spDiag]
    have ha : ((U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℝ)))ᵀ *ᵥ
        halfVec (((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ)ᵀ *ᵥ n) = halfVec n := by
      rw [← Matrix.transpose_map, mulVec_halfVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
        Units.inv_mul, Matrix.transpose_one, Matrix.one_mulVec]
    have hb : ((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℝ)) *ᵥ
        halfVec ((U : Matrix (Fin g) (Fin g) ℤ) *ᵥ n') = halfVec n' := by
      rw [mulVec_halfVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [hz, hs, hx, hjd, eC_zero, thetaGL_holds (Fin g) U _ _ z τ, ha, hb]
    linear_combination (-(theta (halfVec n) (halfVec n') z τ ^ 2)) * he2
end ReciprocityTheory.ChartRestriction.G.Key.Chi
