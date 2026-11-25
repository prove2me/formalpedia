-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.detG_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:09:45.692442+00:00
-- url     : https://prove2.me/submissions/ed700a79-961c-4cfe-b010-523d0d81e823

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegW
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_no_line
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_hermForm_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsLattice L) (hSD : IsSelfDual S L) :
    S.G.det ≠ 0 := by
  intro hdet
  have hdetT : S.Gᵀ.det = 0 := by rw [Matrix.det_transpose]; exact hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  have hw0 : (fun a => S.c (v a)) ≠ 0 := by
    intro h
    apply hv0
    funext a
    have h1 := congrArg S.c (congrFun h a)
    simpa [S.c_invol] using h1
  have hzero : ∀ y, S.h (fun a => S.c (v a)) y = 0 := by
    intro y
    simp only [HermForm.h, S.c_invol]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b _
    have hb := congrFun hv b
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hb
    rw [← Finset.sum_mul]
    have h2 : ∑ a, v a * S.G a b = 0 := by
      rw [← hb]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    rw [h2, zero_mul]
  apply no_line L hL.1 _ hw0
  intro t
  apply hSD.2
  intro y _
  rw [hermForm_smul_left, hzero, mul_zero]
  exact ⟨0, by simp⟩
end ReciprocityTheory.MultiplicativeHeights.SemiPt
