-- Prove2me | solution 1 for UnderstandingML.uc_implies_agnostic_pac
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T12:52:48.536599+00:00
-- url     : https://prove2.me/submissions/eac00e31-8e07-4318-95b8-14df92a037be

import Definitions.Def_UnderstandingML_Framework

open MeasureTheory UnderstandingML

theorem solution {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}
    (loss : Hyp → Z → ℝ) (H : Set Hyp) (mUC : ℝ → ℝ → ℕ)
    (hUC : HasUniformConvergenceWith loss H mUC) :
    (∀ A : Learner Z Hyp, IsERMLearner loss H A →
      IsAgnosticPACWith loss H A (fun ε δ ↦ mUC (ε / 2) δ)) ∧
    ((∃ A : Learner Z Hyp, IsERMLearner loss H A) → AgnosticPACLearnable loss H) := by
  have key : ∀ A : Learner Z Hyp, IsERMLearner loss H A →
      IsAgnosticPACWith loss H A (fun ε δ ↦ mUC (ε / 2) δ) := by
    intro A hA
    refine ⟨fun m S ↦ (hA m S).1, ?_⟩
    intro ε δ hε hε1 hδ hδ1 D hD m hm
    refine le_trans (measure_mono ?_)
      (hUC (ε / 2) δ (by linarith) (by linarith) hδ hδ1 D hD m hm)
    rintro S ⟨h', hh', hlt⟩ hrep
    have e1 := abs_le.mp (hrep (A m S) (hA m S).1)
    have e2 := abs_le.mp (hrep h' hh')
    have e3 := (hA m S).2 h' hh'
    linarith [e1.1, e2.2]
  exact ⟨key, fun ⟨A, hA⟩ ↦ ⟨_, A, key A hA⟩⟩
