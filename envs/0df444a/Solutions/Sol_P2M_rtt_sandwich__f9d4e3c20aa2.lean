-- Prove2me | solution 1 for P2M_rtt_sandwich__f9d4e3c20aa2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:26:00.764587+00:00
-- url     : https://prove2.me/submissions/1b0ff848-89bd-460a-bddb-8048b7810efc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RTTIndependence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EntrywiseSandwichCommute_Imports
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmSandwich
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_entries_mem_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_first_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_first_second_embedding_commute
import Theorems.Thm_Formalism_YangianSpanCharacter_P_rttRelation
import Theorems.Thm_PI_QmSandwichWork_block_embedding_mul_entry
import Theorems.Thm_PI_QmSandwichWork_block_embedding_mul_entry_swap
import Theorems.Thm_PI_QmSandwichWork_flip_col
import Theorems.Thm_PI_QmSandwichWork_flip_row
import Theorems.Thm_PI_QmSandwichWork_tm_entry_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem rtt_commutator_sandwich_eq_of_relations {M : Type} [Ring M] (R e2b e1b' e1q' e2q e1a' e2a : M)
    (h1 : e2q * e1a' = e1a' * e2q) (h2 : e2b * e1q' = e1q' * e2b) (h3 : e2b * e1a' = e1a' * e2b)
    (h4 : e2a * e1b' = e1b' * e2a) (h5 : e2q * e1b' = e1b' * e2q) (h6 : e2a * e1q' = e1q' * e2a)
    (hP : R * e1b' * e2b = e2b * e1b' * R) (hU : R * e1a' * e2a = e2a * e1a' * R) :
    e2b * e1b' * (R * e1q' * e2q - e2q * e1q' * R) * (e1a' * e2a) =
      R * (e1b' * e1q' * e1a' * (e2b * e2q * e2a)) - e2b * e2q * e2a * (e1b' * e1q' * e1a') * R := by
  rw [mul_sub, sub_mul]
  congr 1
  · calc e2b * e1b' * (R * e1q' * e2q) * (e1a' * e2a)
        = e2b * e1b' * R * e1q' * (e2q * e1a') * e2a := by simp only [mul_assoc]
      _ = R * e1b' * e2b * e1q' * (e1a' * e2q) * e2a := by rw [← hP, h1]
      _ = R * e1b' * (e2b * e1q') * e1a' * e2q * e2a := by simp only [mul_assoc]
      _ = R * e1b' * e1q' * (e2b * e1a') * e2q * e2a := by rw [h2]; simp only [mul_assoc]
      _ = R * (e1b' * e1q' * e1a' * (e2b * e2q * e2a)) := by rw [h3]; simp only [mul_assoc]
  · calc e2b * e1b' * (e2q * e1q' * R) * (e1a' * e2a)
        = e2b * e1b' * e2q * e1q' * (R * e1a' * e2a) := by simp only [mul_assoc]
      _ = e2b * e1b' * e2q * e1q' * (e2a * e1a' * R) := by rw [hU]
      _ = e2b * (e1b' * e2q) * (e1q' * e2a) * e1a' * R := by simp only [mul_assoc]
      _ = e2b * (e2q * e1b') * (e2a * e1q') * e1a' * R := by rw [← h5, ← h6]
      _ = e2b * e2q * (e1b' * e2a) * e1q' * e1a' * R := by simp only [mul_assoc]
      _ = e2b * e2q * e2a * (e1b' * e1q' * e1a') * R := by rw [← h4]; simp only [mul_assoc]
end

set_option autoImplicit false

theorem _root_.solution : PI.RTTSandwich := by
  intro A _ _ QQ p c ci p' c' ci' hW hW' hcomm hQ Y Y'
  dsimp only
  have hbu : ∀ (y : ℂ) (i j : Fin 2), ∀ u ∈ ({p, c, ci} : Set A), Commute (Formalism.YangianSpanCharacter.T.Tm y p' c' ci' i j) u := by
    intro y i j u hu
    exact PI.QmSandwichWork.tm_entry_comm y (hcomm u hu p' (by simp)).symm (hcomm u hu c' (by simp)).symm
      (hcomm u hu ci' (by simp)).symm i j
  have hab : ∀ (y y' : ℂ) (i j k l : Fin 2),
      Commute (Formalism.YangianSpanCharacter.T.Tm y p c ci i j) (Formalism.YangianSpanCharacter.T.Tm y' p' c' ci' k l) := by
    intro y y' i j k l
    exact PI.QmSandwichWork.tm_entry_comm y (hbu y' k l p (by simp)).symm (hbu y' k l c (by simp)).symm
      (hbu y' k l ci (by simp)).symm i j
  have haq : ∀ (y y' : ℂ) (i j k l : Fin 2), Commute (Formalism.YangianSpanCharacter.T.Tm y p c ci i j) (QQ y' k l) :=
    fun y y' i j k l => PI.QmSandwichWork.tm_entry_comm y (hQ p (by simp) y' k l) (hQ c (by simp) y' k l)
      (hQ ci (by simp) y' k l) i j
  have hbq : ∀ (y y' : ℂ) (i j k l : Fin 2), Commute (Formalism.YangianSpanCharacter.T.Tm y p' c' ci' i j) (QQ y' k l) :=
    fun y y' i j k l => PI.QmSandwichWork.tm_entry_comm y (hQ p' (by simp) y' k l) (hQ c' (by simp) y' k l)
      (hQ ci' (by simp) y' k l) i j
  have h1 : Formalism.YangianSpanCharacter.T.E2 (QQ Y) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (QQ Y) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => haq Y' Y i j k l).symm
  have h2 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (QQ Y') =
      Formalism.YangianSpanCharacter.T.E1 (QQ Y') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => (hbq Y Y' k l i j).symm).symm
  have h3 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => hab Y' Y i j k l).symm
  have h4 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => (hab Y Y' k l i j).symm).symm
  have h5 : Formalism.YangianSpanCharacter.T.E2 (QQ Y) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (QQ Y) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => hbq Y' Y i j k l).symm
  have h6 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) * Formalism.YangianSpanCharacter.T.E1 (QQ Y') =
      Formalism.YangianSpanCharacter.T.E1 (QQ Y') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => (haq Y Y' k l i j).symm).symm
  have hP : ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) *
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') =
      Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') *
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) :=
    Formalism.YangianSpanCharacter.P.rttRelation ℂ A p' c' ci' Y Y' hW'
  have hU : ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) *
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) =
      Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) *
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) :=
    Formalism.YangianSpanCharacter.P.rttRelation ℂ A p c ci Y Y' hW
  have hmat := rtt_commutator_sandwich_eq_of_relations _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 hP hU
  change _ = (Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') *
    (_ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) *
    (Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci))) (0, 0) (0, 0)
  rw [hmat, Matrix.sub_apply, PI.QmSandwichWork.flip_row, PI.QmSandwichWork.flip_col, ← Formalism.FourierDecayAlt.P.W.first_embedding_mul,
    ← Formalism.FourierDecayAlt.P.W.first_embedding_mul, ← Formalism.FourierDecayAlt.P.W.entries_mem_mul, ← Formalism.FourierDecayAlt.P.W.entries_mem_mul, PI.QmSandwichWork.block_embedding_mul_entry,
    PI.QmSandwichWork.block_embedding_mul_entry_swap, mul_sub]
