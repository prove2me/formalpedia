-- Prove2me | solution 1 for PI.StabPairs.Conv.Z_cR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:32.964447+00:00
-- url     : https://prove2.me/submissions/4187dbfd-5aeb-4145-a3eb-b093cbf96666

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec
import Theorems.Thm_PI_StabPairs_Conv_gram_Km
import Theorems.Thm_PI_StabPairs_Conv_FH_apply

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
    (hv : ∀ a : Fin (r + 1), a.val < r → herm (Hpk k r) v (fvec k r z a) = 0) :
    ∀ a : Fin (r + 1), a.val < r → (Zhat k r z z' γ *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inr)) a = 0 := by
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
  intro a ha
  have hK := congrFun (gram_Km k r z z' γ hGi v) (Sum.inl a)
  rw [FH_apply] at hK
  generalize Km k r z z' γ *ᵥ v = w at hK ⊢
  have h0 : herm (Hpk k r) v (gramVec k r z z' γ (Sum.inl a)) = 0 := hv a ha
  rw [h0] at hK
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] at hK
  have h1 : ∀ b, gramM k r z z' γ (Sum.inl a) (Sum.inl b) = 0 :=
    fun b => hrow z a ha _ (hfz z hS.2.1.1 b)
  simp only [h1, zero_mul, Finset.sum_const_zero, zero_add] at hK
  simp only [Matrix.mulVec, dotProduct, Function.comp]
  exact hK
end PI.StabPairs.Conv
