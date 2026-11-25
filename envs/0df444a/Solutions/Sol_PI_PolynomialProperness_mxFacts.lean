-- Prove2me | solution 1 for PI.PolynomialProperness.mxFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:55:22.811289+00:00
-- url     : https://prove2.me/submissions/5ad4c2dc-0922-4a4d-a7f1-67f33dbb2059

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
import Theorems.Thm_PI_PolynomialProperness_TM_herm_coords
import Theorems.Thm_PI_PolynomialProperness_TM_uh_of_herm
import Theorems.Thm_PI_PolynomialProperness_TM_mX_mulVec_eI
import Theorems.Thm_PI_PolynomialProperness_TM_mX_mulVec_esI
import Theorems.Thm_PI_PolynomialProperness_TM_mX_mulVec_mid
import Theorems.Thm_PI_PolynomialProperness_TM_pX_mX
import Theorems.Thm_PI_PolynomialProperness_TM_qX_mX
import Theorems.Thm_PI_PolynomialProperness_TM_midF_mX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness
open TM
namespace PI.PolynomialProperness
theorem _root_.solution : MXFacts := by
  intro k r vX hU
  have hU1 : ∀ i j, j < i → vX i j = 0 := hU.1
  have hU2 : ∀ i, vX i i = 1 := hU.2
  have hdet : vX.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hU1 i j hij)]
    simp [hU2]
  have hu : IsUnit vX.det := by rw [hdet]; exact isUnit_one
  have hu' : IsUnit vXᴴ.det := by rw [Matrix.det_conjTranspose, hdet, star_one]; exact isUnit_one
  have d1 : ∀ p q : Fin r → ℂ, star ((vXᴴ)⁻¹ *ᵥ q) ⬝ᵥ (vX *ᵥ p) = star q ⬝ᵥ p := by
    intro p q
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have d2 : ∀ p q : Fin r → ℂ, star (vX *ᵥ p) ⬝ᵥ ((vXᴴ)⁻¹ *ᵥ q) = star p ⬝ᵥ q := by
    intro p q
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu',
      Matrix.vecMul_one]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Nset, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · apply uh_of_herm
      intro x y
      rw [herm_coords, herm_coords]
      simp only [pX_mX, qX_mX, midF_mX]
      rw [d1, d2]
    · intro a i hai
      unfold mX
      by_cases hi : i.val < r
      · rw [dif_pos hi, dif_pos (show (eI k r a).val < r from a.isLt)]
        by_cases hia : i = eI k r a
        · rw [if_pos hia]
          subst hia
          exact hU2 a
        · rw [if_neg hia]
          apply hU1
          have hne : i.val ≠ a.val := fun h => hia (Fin.ext h)
          show a.val < i.val
          have hai' : a.val ≤ i.val := hai
          omega
      · rw [dif_neg hi]
        have hne : i ≠ eI k r a := by
          intro h
          apply hi
          rw [h]
          exact a.isLt
        by_cases hi2 : r + k < i.val
        · have ha := a.isLt
          rw [dif_pos hi2, dif_neg (show ¬ (r + k < (eI k r a).val) by show ¬ (r + k < a.val); omega),
            if_neg hne]
        · rw [dif_neg hi2]
    · intro i j hj1 hj2 hi
      unfold mX
      rw [dif_neg (show ¬ (i.val < r) by omega)]
      by_cases hi2 : r + k < i.val
      · rw [dif_pos hi2, dif_neg (show ¬ (r + k < j.val) by omega),
          if_neg (show i ≠ j from fun h => by rw [h] at hi2; omega)]
      · rw [dif_neg hi2]
  · intro p
    funext i
    have hiL := i.isLt
    by_cases hi : i.val < r
    · have h1 := mX_mulVec_eI k r vX (xiV k r p) ⟨i.val, hi⟩
      have e : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
      rw [e] at h1
      rw [h1]
      have hp : pX k r (xiV k r p) = p := by
        funext a
        show xiV k r p (eI k r a) = p a
        unfold xiV
        rw [dif_pos (show (eI k r a).val < r from a.isLt)]
        try rfl
      rw [hp]
      unfold xiV
      rw [dif_pos hi]
    · have hz : xiV k r (vX *ᵥ p) i = 0 := by
        unfold xiV
        rw [dif_neg hi]
      rw [hz]
      by_cases hi2 : r + k < i.val
      · have h1 := mX_mulVec_esI k r vX (xiV k r p) ⟨2 * r + k - i.val, by omega⟩
        have e : esI k r ⟨2 * r + k - i.val, by omega⟩ = i :=
          Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)
        rw [e] at h1
        rw [h1]
        have hq : qX k r (xiV k r p) = 0 := by
          funext a
          have ha := a.isLt
          show xiV k r p (esI k r a) = 0
          unfold xiV
          rw [dif_neg (show ¬ ((esI k r a).val < r) by show ¬ (2 * r + k - a.val < r); omega)]
        rw [hq, Matrix.mulVec_zero, Pi.zero_apply]
      · rw [mX_mulVec_mid k r vX _ i (by omega) (by omega)]
        unfold xiV
        rw [dif_neg hi]
  · intro w hw
    funext i
    have hiL := i.isLt
    by_cases hi : i.val < r
    · have h1 := mX_mulVec_eI k r vX w ⟨i.val, hi⟩
      have e : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
      rw [e] at h1
      have hp : pX k r w = 0 := by
        funext a
        exact hw _ (Or.inl a.isLt)
      rw [h1, hp, Matrix.mulVec_zero, Pi.zero_apply, hw i (Or.inl hi)]
    · by_cases hi2 : r + k < i.val
      · have h1 := mX_mulVec_esI k r vX w ⟨2 * r + k - i.val, by omega⟩
        have e : esI k r ⟨2 * r + k - i.val, by omega⟩ = i :=
          Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)
        rw [e] at h1
        have hq : qX k r w = 0 := by
          funext a
          have ha := a.isLt
          exact hw _ (Or.inr (by show r + k < 2 * r + k - a.val; omega))
        rw [h1, hq, Matrix.mulVec_zero, Pi.zero_apply, hw i (Or.inr hi2)]
      · exact mX_mulVec_mid k r vX w i (by omega) (by omega)
end PI.PolynomialProperness
