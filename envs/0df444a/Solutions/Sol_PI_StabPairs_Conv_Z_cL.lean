-- Prove2me | solution 1 for PI.StabPairs.Conv.Z_cL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:29.788797+00:00
-- url     : https://prove2.me/submissions/24c56c70-94a5-4e53-9a59-bd28350835cd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec
import Theorems.Thm_PI_StabPairs_Conv_gram_Km
import Theorems.Thm_PI_StabPairs_Conv_FH_apply
import Theorems.Thm_PI_StabPairsW_herm_GV
import Theorems.Thm_PI_StabPairsW_herm_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
namespace PI.StabPairs.Conv
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hS : Std k r z z')
    (hP : PosPt k r z z' γ) (hGi : IsUnit (gramM k r z z' γ).det) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ b : Fin (r + 1), b.val < r → herm (Hpk k r) v (γ *ᵥ fvec k r z' b) = 0) :
    ∀ b : Fin (r + 1), b.val < r → ((Zhat k r z z' γ)ᴴ *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inl)) b = 0 := by
  have hHz : ∀ e c : Fin (2 * r + k + 1), e.val < r → c.val ≤ r + k → Hpk k r e c = 0 := by
    intro e c he hc
    unfold Hpk
    rw [if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.2 (by omega)),
      if_neg (fun h => absurd h.1 (by omega))]
  have hrow : ∀ (y : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)), a.val < r →
      ∀ x : Fin (2 * r + k + 1) → ℂ, (∀ c : Fin (2 * r + k + 1), r + k < c.val → x c = 0) →
      herm (Hpk k r) x (fvec k r y a) = 0 := by
    intro y a ha x hx
    unfold fvec
    rw [dif_pos ha]
    simp only [herm, bvec, dotProduct, Matrix.mulVec, Pi.star_apply]
    rw [Finset.sum_eq_single (eI k r ⟨a.val, ha⟩)]
    · simp only [Pi.single_eq_same, star_one, one_mul]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : r + k < c.val
      · rw [hx c hc, mul_zero]
      · rw [hHz _ _ ha (by omega), zero_mul]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfz : ∀ (y : Fin (2 * r + k + 1) → ℂ), inWb k r y → ∀ (b : Fin (r + 1)) (c : Fin (2 * r + k + 1)),
      r + k < c.val → fvec k r y b c = 0 := by
    intro y hy b c hc
    unfold fvec
    split_ifs with hb
    · exact Pi.single_eq_of_ne (fun h' => by
        have := congrArg Fin.val h'
        simp [eI] at this
        omega) _
    · exact hy c (Or.inr hc)
  intro b hb
  have hK := congrFun (gram_Km k r z z' γ hGi v) (Sum.inr b)
  rw [FH_apply] at hK
  generalize Km k r z z' γ *ᵥ v = w at hK ⊢
  have h0 : herm (Hpk k r) v (gramVec k r z z' γ (Sum.inr b)) = 0 := hv b hb
  rw [h0] at hK
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] at hK
  have h1 : ∀ a, gramM k r z z' γ (Sum.inr b) (Sum.inr a) = 0 := by
    intro a
    show herm (Hpk k r) (γ *ᵥ fvec k r z' a) (γ *ᵥ fvec k r z' b) = 0
    rw [herm_GV hP.1]
    exact hrow z' b hb _ (hfz z' hS.2.2.1 a)
  simp only [h1, zero_mul, Finset.sum_const_zero, add_zero] at hK
  simp only [Matrix.mulVec, dotProduct, Function.comp, Matrix.conjTranspose_apply]
  rw [← hK]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  show star (herm (Hpk k r) (γ *ᵥ fvec k r z' b) (fvec k r z a)) =
    herm (Hpk k r) (fvec k r z a) (γ *ᵥ fvec k r z' b)
  rw [herm_swap (fvec k r z a)]
end PI.StabPairs.Conv
