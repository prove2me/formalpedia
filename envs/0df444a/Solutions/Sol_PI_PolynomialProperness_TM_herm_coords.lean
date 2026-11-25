-- Prove2me | solution 1 for PI.PolynomialProperness.TM.herm_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:33.459403+00:00
-- url     : https://prove2.me/submissions/893350cb-846e-413d-8efc-09a98df77daf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
import Theorems.Thm_PI_PolynomialProperness_TM_sum_emb
import Theorems.Thm_PI_PolynomialProperness_TM_eIe_apply
import Theorems.Thm_PI_PolynomialProperness_TM_esIe_apply
import Theorems.Thm_PI_PolynomialProperness_TM_esI_val
import Theorems.Thm_PI_PolynomialProperness_TM_sig_eI
import Theorems.Thm_PI_PolynomialProperness_TM_sig_esI
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq


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
open PI PI.PolynomialProperness PI.PolynomialProperness.TM
namespace PI.PolynomialProperness.TM
theorem _root_.solution (k r : ℕ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (qX k r y) ⬝ᵥ pX k r x + star (pX k r y) ⬝ᵥ qX k r x + midF k r x y := by
  have hmul : ∀ i, (Hpk k r *ᵥ x) i = GBasic.sgn k r i * x (GBasic.sig k r i) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, GBasic.Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hsplit : ∀ i : Fin (2 * r + k + 1),
      star (y i) * (GBasic.sgn k r i * x (GBasic.sig k r i)) =
        (if i.val < r then star (y i) * x (GBasic.sig k r i) else 0) +
        (if r + k < i.val then star (y i) * x (GBasic.sig k r i) else 0) +
        (if r ≤ i.val ∧ i.val ≤ r + k then star (y i) * (GBasic.sgn k r i * x i) else 0) := by
    intro i
    by_cases h1 : i.val < r
    · have hs : GBasic.sgn k r i = 1 := by
        unfold GBasic.sgn
        rw [if_neg (show ¬ (i.val = r + k) by omega)]
      rw [if_pos h1, if_neg (show ¬ (r + k < i.val) by omega),
        if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega), hs]
      ring
    · by_cases h2 : r + k < i.val
      · have hs : GBasic.sgn k r i = 1 := by
          unfold GBasic.sgn
          rw [if_neg (show ¬ (i.val = r + k) by omega)]
        rw [if_neg h1, if_pos h2, if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega), hs]
        ring
      · have hs : GBasic.sig k r i = i := by
          unfold GBasic.sig
          rw [if_neg (show ¬ (i.val < r ∨ r + k < i.val) by omega)]
        rw [if_neg h1, if_neg h2, if_pos (show r ≤ i.val ∧ i.val ≤ r + k by omega), hs]
        ring
  have hA : (∑ i : Fin (2 * r + k + 1), if i.val < r then star (y i) * x (GBasic.sig k r i) else 0)
      = star (pX k r y) ⬝ᵥ qX k r x := by
    refine (sum_emb (eIe k r) _ ?_).trans ?_
    · intro i hi
      by_cases h : i.val < r
      · exact absurd (Fin.ext rfl : eIe k r ⟨i.val, h⟩ = i) (hi _)
      · rw [if_neg h]
    · simp only [dotProduct, pX, qX, Pi.star_apply, eIe_apply]
      apply Finset.sum_congr rfl
      intro t _
      have hc : (eI k r t).val < r := t.isLt
      simp [hc, sig_eI]
  have hB : (∑ i : Fin (2 * r + k + 1), if r + k < i.val then star (y i) * x (GBasic.sig k r i) else 0)
      = star (qX k r y) ⬝ᵥ pX k r x := by
    refine (sum_emb (esIe k r) _ ?_).trans ?_
    · intro i hi
      by_cases h : r + k < i.val
      · exfalso
        have hiL := i.isLt
        apply hi ⟨2 * r + k - i.val, by omega⟩
        apply Fin.ext
        rw [esIe_apply, esI_val]
        show 2 * r + k - (2 * r + k - i.val) = i.val
        omega
      · rw [if_neg h]
    · simp only [dotProduct, pX, qX, Pi.star_apply, esIe_apply]
      apply Finset.sum_congr rfl
      intro t _
      have ht := t.isLt
      have hc : r + k < (esI k r t).val := by rw [esI_val]; omega
      simp [hc, sig_esI]
  have hH : herm (Hpk k r) x y = ∑ i, star (y i) * (GBasic.sgn k r i * x (GBasic.sig k r i)) := by
    unfold herm
    simp only [dotProduct, Pi.star_apply, hmul]
  rw [hH, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB]
  unfold midF
  ring
end PI.PolynomialProperness.TM
