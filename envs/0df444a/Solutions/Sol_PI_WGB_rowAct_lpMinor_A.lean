-- Prove2me | solution 1 for PI.WGB.rowAct_lpMinor_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:29:35.315979+00:00
-- url     : https://prove2.me/submissions/29000638-a16f-4bae-a503-483a1a1ea652

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Theorems.Thm_PI_WGB_rowAct_X_A
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, i < j → M i j = 0)
    (hd : ∀ i, M i i = 1) (s : ℕ) (hs : s ≤ n) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) M (Formalism.GradedWeylDivisibility.lpMinor ℂ s hs hs) = Formalism.GradedWeylDivisibility.lpMinor ℂ s hs hs := by
  unfold Formalism.GradedWeylDivisibility.lpMinor
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply]
  have hmat : (Matrix.of fun p q : Fin s =>
      (X (Fin.castLE hs p, Fin.castLE hs q) : MvPolynomial (Fin n × Fin n) ℂ)).map
        (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) M) =
      (Matrix.of fun p b : Fin s => (C (M (Fin.castLE hs p) (Fin.castLE hs b)) :
        MvPolynomial (Fin n × Fin n) ℂ)) *
      Matrix.of fun p q : Fin s => (X (Fin.castLE hs p, Fin.castLE hs q) : MvPolynomial (Fin n × Fin n) ℂ) := by
    ext p q
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply]
    rw [rowAct_X_A]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hs))), Finset.sum_map]
    · rfl
    · intro b _ hb
      have hbs : s ≤ b.val := by
        by_contra hlt
        apply hb
        exact Finset.mem_map.mpr ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
      simp only
      rw [hM _ _ (by rw [Fin.lt_def]; simp; omega), map_zero, zero_mul]
  have hL : (Matrix.of fun p b : Fin s => (C (M (Fin.castLE hs p) (Fin.castLE hs b)) :
        MvPolynomial (Fin n × Fin n) ℂ)).IsLowerTriangular := by
    intro i j hij
    simp only [Matrix.of_apply]
    rw [hM _ _ (by rw [Fin.lt_def]; simpa using hij), map_zero]
  rw [hmat, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ hL]
  simp [hd]
end PI.WGB
