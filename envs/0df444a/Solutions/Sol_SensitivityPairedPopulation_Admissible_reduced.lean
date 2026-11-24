-- Prove2me | solution 1 for SensitivityPairedPopulation.Admissible.reduced
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:35.731252+00:00
-- url     : https://prove2.me/submissions/61831314-77ac-4ef0-af77-5bb208bdee80

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedPopulationConstraints
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedReducedPopulation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityPairedPopulation
end SensitivityPairedPopulation

section


/-! The literal paired objectives have a common price on all tiers below the
last. Their finite population bound therefore needs two cumulative counts. -/
namespace SensitivityPairedPopulation





theorem powerConstraints_mono (data : PowerData) (size spent larger : ℕ)
    (hle : spent ≤ larger) (h : powerConstraints data size spent) :
    powerConstraints data size larger := by
  obtain ⟨outgoing,ho⟩ := h
  refine ⟨⟨outgoing.val,lt_of_lt_of_le outgoing.isLt (Nat.add_le_add_right hle 1)⟩,?_⟩
  intro order hr
  have ht := ho order hr
  unfold powerConstraint at ht ⊢
  exact ht.trans (Nat.mul_le_mul_left _ hle)

theorem TierAdmissible.mono_spent {data : GradedGeometry} {q : Fin 4} {size spent larger : ℕ}
    (h : TierAdmissible data q size spent) (hle : spent ≤ larger) :
    TierAdmissible data q size larger := by
  obtain ⟨hcap,hedge,hmarks,hpower⟩ := h
  refine ⟨hcap,hedge.trans hle,?_,?_⟩
  · intro m
    have hm := hmarks m
    cases he : data.markerResidual m with
    | none => trivial
    | some residual =>
      simp only [he,optional] at hm ⊢
      constructor
      · exact hm.1.trans (Nat.add_le_add_right (Nat.add_le_add_right hle residual) _)
      · exact ⟨hm.2.1.trans (Nat.mul_le_mul_left (m.val+1) hle),hm.2.2⟩
  · cases he : data.powers with
    | none => trivial
    | some p =>
      simp only [he,optional] at hpower ⊢
      exact powerConstraints_mono p size spent larger hle hpower

theorem Admissible.tier {data : GradedGeometry} {n : Population}
    (h : Admissible data n) (q : Fin 4) (hq : q ≤ data.tolerance) :
    TierAdmissible data q (prefixCount n q) (budget n q) := by
  obtain ⟨hc,he,hf,hm,hp,hl⟩ := h
  refine ⟨hc q hq,he q hq,hm q hq,?_⟩
  cases hh : data.powers with
  | none => trivial
  | some p =>
    simp only [hh,optional] at hp ⊢
    exact hp q hq





theorem previousTier_le (q : Fin 4) : previousTier q ≤ q := by
  fin_cases q <;> decide

theorem previousCount_le (n : Population) (q : Fin 4) : previousCount n q ≤ prefixCount n q := by
  fin_cases q <;> simp [previousCount,previousTier,prefixCount] <;> omega

theorem budget_le_reduced (n : Population) (q : Fin 4) :
    budget n q ≤ q.val * prefixCount n q - previousCount n q := by
  fin_cases q <;> simp [previousCount,previousTier,prefixCount,budget] <;> omega

theorem previous_budget_le_reduced (n : Population) (q : Fin 4) (hq : 0 < q.val) :
    budget n (previousTier q) ≤ (q.val-1) * previousCount n q := by
  fin_cases q <;> simp [previousCount,previousTier,prefixCount,budget] at * <;> omega





theorem markerForest_mono (alpha beta small large marks residual : ℕ)
    (hs : small ≤ large) (h : markerForest alpha beta large marks residual) :
    markerForest alpha beta small marks residual := by
  unfold markerForest at h ⊢
  split_ifs at h ⊢ with hm
  · exact (Nat.mul_le_mul_left 2 hs).trans h
  · exact (Nat.mul_le_mul_left marks hs).trans h
































end SensitivityPairedPopulation

end

/-! The literal paired objectives have a common price on all tiers below the
last. Their finite population bound therefore needs two cumulative counts. -/
open SensitivityPairedPopulation

theorem solution {data : GradedGeometry} {n : Population}
    (h : Admissible data n) :
    ReducedAdmissible data (previousCount n data.tolerance) (prefixCount n data.tolerance) := by
  have ht := h.tier data.tolerance le_rfl
  refine ⟨previousCount_le n _,?_,ht.mono_spent (budget_le_reduced n _),?_,?_,?_,?_⟩
  · intro hz
    simp only [previousCount,hz,if_true]
  · intro hp
    have hh := h.tier (previousTier data.tolerance) (previousTier_le _)
    have he : previousCount n data.tolerance = prefixCount n (previousTier data.tolerance) := by
      simp only [previousCount,if_neg (by omega : ¬ data.tolerance.val = 0)]
    rw [he]
    apply hh.mono_spent
    simpa only [he] using previous_budget_le_reduced n data.tolerance hp
  · intro hq
    have hf := h.2.2.1 (by omega : 1 ≤ data.tolerance.val)
    have he : data.tolerance = (1 : Fin 4) := Fin.ext hq
    have hh : previousCount n data.tolerance + prefixCount n data.tolerance =
        prefixCount n 1 + prefixCount n 0 := by
      simp [he,previousCount,previousTier,prefixCount]
      omega
    simpa only [hh] using hf
  · intro hq
    have hf := h.2.2.1 (by omega : 1 ≤ data.tolerance.val)
    have he : data.tolerance = (2 : Fin 4) := Fin.ext hq
    have hh : previousCount n data.tolerance = prefixCount n 1 := by
      simp [he,previousCount,previousTier,prefixCount]
    rw [hh]
    refine ⟨by omega,by omega,?_⟩
    intro m
    have hm := hf.2.2 m
    cases hr : data.markerResidual m with
    | none => trivial
    | some residual =>
      simp only [hr,_root_.SensitivityPairedPopulation.optional] at hm ⊢
      exact markerForest_mono _ _ _ _ _ _ (Nat.le_add_right _ _) hm
  · have hl := h.2.2.2.2.2
    cases hh : data.lowOne with
    | none => trivial
    | some lo =>
      simp only [hh,_root_.SensitivityPairedPopulation.optional] at hl ⊢
      constructor
      · intro hq
        have hb := hl (by omega : 1 ≤ data.tolerance.val)
        have he : data.tolerance = (1 : Fin 4) := Fin.ext hq
        simp [he,previousCount,previousTier,prefixCount] at hb ⊢
        omega
      · intro hq
        have hb := hl (by omega : 1 ≤ data.tolerance.val)
        have he : data.tolerance = (2 : Fin 4) := Fin.ext hq
        simp [he,previousCount,previousTier,prefixCount] at hb ⊢
        omega
