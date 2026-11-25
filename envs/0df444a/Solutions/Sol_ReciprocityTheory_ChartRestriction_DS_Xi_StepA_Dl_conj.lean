-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Dl_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:10.442234+00:00
-- url     : https://prove2.me/submissions/cddfe039-ce87-44e7-9de7-acd90d900509

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos


section
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section lev
variable (k r' : ℕ)
end lev
section dl
variable (k r : ℕ)
private lemma Hpk_mul_Hpk_eq_one : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hc : i.val < r ∨ r + k < i.val
  · rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · simp only [Hpk, Fin.val_mk, Fin.ext_iff, and_true, true_and]
      (try split_ifs) <;> (first | omega | norm_num)
    · intro m _ hm
      have hm' : m.val ≠ 2 * r + k - i.val := fun h => hm (Fin.ext h)
      simp only [Hpk, Fin.ext_iff, and_true, true_and]
      (try split_ifs) <;> (first | omega | norm_num)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single i]
    · simp only [Hpk, Fin.ext_iff, and_true, true_and]
      (try split_ifs) <;> (first | omega | norm_num)
    · intro m _ hm
      have hm' : m.val ≠ i.val := fun h => hm (Fin.ext h)
      simp only [Hpk, Fin.ext_iff, and_true, true_and]
      (try split_ifs) <;> (first | omega | norm_num)
    · intro h
      exact absurd (Finset.mem_univ _) h
private lemma herm_sub_smul_left' {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v w u : Fin m → ℂ) (c : ℂ) :
    herm H (v - c • w) u = herm H v u - c * herm H w u := by
  simp [herm, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul]
private lemma herm_sub_smul_right' {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u v w : Fin m → ℂ) (c : ℂ) :
    herm H u (v - c • w) = herm H u v - star c * herm H u w := by
  simp [herm, star_sub, star_smul, sub_dotProduct, smul_dotProduct]
end dl
section a1
variable (k r' : ℕ)
end a1
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (l : Fin (r + 1)) (Y n n' : Mat k r) (hn : n ∈ GV k r) (α β : Fin (r + 1) → ℂ)
    (hα : α 0 = 0) (hβ : β 0 = 0)
    (hn' : ∀ b, n' *ᵥ phiV' k r b = phiV' k r b - α b • phiV' k r 0)
    (hnn : ∀ a, n *ᵥ phiV' k r a = phiV' k r a - β a • phiV' k r 0) :
    Dl k r l (n⁻¹ * Y * n') = Dl k r l Y := by
  have HH : Hpk k r * Hpk k r = 1 := Hpk_mul_Hpk_eq_one k r
  have hinv : n⁻¹ = Hpk k r * nᴴ * Hpk k r := by
    apply Matrix.inv_eq_left_inv
    have h1 : nᴴ * Hpk k r * n = Hpk k r := hn
    calc Hpk k r * nᴴ * Hpk k r * n = Hpk k r * (nᴴ * Hpk k r * n) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, HH]
  have hherm : ∀ z w : Fin (2 * r + k + 1) → ℂ,
      herm (Hpk k r) (n⁻¹ *ᵥ z) w = herm (Hpk k r) z (n *ᵥ w) := by
    intro z w
    have e1 : Hpk k r * (Hpk k r * nᴴ * Hpk k r) = nᴴ * Hpk k r := by
      simp only [← Matrix.mul_assoc, HH, Matrix.one_mul]
    unfold herm
    rw [hinv, Matrix.mulVec_mulVec, e1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec]
  have hc0 : ∀ h : l.val + 1 ≤ r + 1, Fin.castLE h (0 : Fin (l.val + 1)) = 0 :=
    fun h => Fin.ext (by simp)
  have detP : (1 - Matrix.of fun a c : Fin (l.val + 1) =>
      if c = 0 then star (β (Fin.castLE (by omega) a)) else 0).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · apply Finset.prod_eq_one
      intro i _
      by_cases hi : i = 0
      · subst hi
        simp [hc0, hβ]
      · simp [hi]
    · intro i j hij
      have hij' : i < j := hij
      have hj : j ≠ 0 := fun h => absurd (h ▸ hij') (Fin.not_lt_zero i)
      simp [hj, Matrix.one_apply, ne_of_lt hij']
  have detQ : (1 - Matrix.of fun d b : Fin (l.val + 1) =>
      if d = 0 then α (Fin.castLE (by omega) b) else 0).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · apply Finset.prod_eq_one
      intro i _
      by_cases hi : i = 0
      · subst hi
        simp [hc0, hα]
      · simp [hi]
    · intro i j hij
      have hij' : j < i := hij
      have hi : i ≠ 0 := fun h => absurd (h ▸ hij') (Fin.not_lt_zero j)
      simp [hi, Matrix.one_apply, ne_of_gt hij']
  unfold Dl
  have hM : (Matrix.of fun a b : Fin (l.val + 1) =>
      herm (Hpk k r) ((n⁻¹ * Y * n') *ᵥ phiV' k r (Fin.castLE (by omega) b))
        (phiV' k r (Fin.castLE (by omega) a))) =
      (1 - Matrix.of fun a c : Fin (l.val + 1) =>
          if c = 0 then star (β (Fin.castLE (by omega) a)) else 0) *
        (Matrix.of fun a b : Fin (l.val + 1) =>
          herm (Hpk k r) (Y *ᵥ phiV' k r (Fin.castLE (by omega) b))
            (phiV' k r (Fin.castLE (by omega) a))) *
        (1 - Matrix.of fun d b : Fin (l.val + 1) =>
          if d = 0 then α (Fin.castLE (by omega) b) else 0) := by
    ext a b
    simp only [Matrix.of_apply, ← Matrix.mulVec_mulVec, hherm, hn', hnn, Matrix.mulVec_sub,
      Matrix.mulVec_smul, herm_sub_smul_left', herm_sub_smul_right']
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, sub_mul, mul_sub,
      Finset.sum_sub_distrib, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', hc0]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, detP, detQ, one_mul, mul_one]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
