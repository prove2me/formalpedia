-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QnFFZero.ffZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:55.381178+00:00
-- url     : https://prove2.me/submissions/fb14ce04-6c82-44cf-8996-1917e449fe7c

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelGeneralLinear_GlevZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_QnFFZero_glev_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_QnFFZero_nset_uh
import Theorems.Thm_PI_UnitaryGroupMassFormula_QnFFZero_nlev_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_QnFFZero_psi_one
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts
import Theorems.Thm_Formalism_QuantumDeterminants_nSubgroup
import Theorems.Thm_Formalism_QuantumDeterminants_uHGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QnFFZero
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.QnFFZero
theorem _root_.solution : FFZero := by
  intro Wp Wq _ _ _ _ k r z z' π π' hz hz'
  have hdet : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hmul : ∀ g ∈ UH (Hpk k r), ∀ h ∈ UH (Hpk k r), g * h ∈ UH (Hpk k r) :=
    (uHGroup (2 * r + k + 1) (Hpk k r) hdet).2.1
  have hN1 : (1 : Mx k r) ∈ Nset k r := (nSubgroup k r).1
  ext J
  simp only [FFl, EqF, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hS, hL, hR, hW⟩
    refine ⟨?_, ?_, ?_⟩
    · intro g₀ hg₀
      obtain ⟨U, F, hU, hgU, hF, hE⟩ := hS g₀ (Set.mem_inter ((glev_zero k r g₀).2 hg₀) (Set.mem_univ _))
      exact ⟨U, F, hU, hgU, hF, fun g hg hgH => hE g hg ((glev_zero k r g).2 hgH)⟩
    · intro g hg n hn n' hn'
      have hng : n * g ∈ UH (Hpk k r) := hmul n (nset_uh k r n hn) g hg
      rw [hR (n * g) (Set.mem_inter ((glev_zero k r _).2 hng) (Set.mem_univ _)) n' ((nlev_zero k r n').2 hn'),
        hL g (Set.mem_inter ((glev_zero k r g).2 hg) (Set.mem_univ _)) n ((nlev_zero k r n).2 hn),
        smul_smul, mul_comm]
    · intro g hg h hh h' hh'
      exact hW g (Set.mem_inter ((glev_zero k r g).2 hg) (Set.mem_univ _)) h hh h' hh'
  · rintro ⟨hS, hNN, hW⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g₀ hg₀
      obtain ⟨U, F, hU, hgU, hF, hE⟩ := hS g₀ ((glev_zero k r g₀).1 hg₀.1)
      exact ⟨U, F, hU, hgU, hF, fun g hg hgG => hE g hg ((glev_zero k r g).1 hgG)⟩
    · intro g hg n hn
      have h1 := hNN g ((glev_zero k r g).1 hg.1) n ((nlev_zero k r n).1 hn) 1 hN1
      rw [mul_one, psi_one k r z' cStd hz', mul_one] at h1
      exact h1
    · intro g hg n hn
      have h1 := hNN g ((glev_zero k r g).1 hg.1) 1 hN1 n ((nlev_zero k r n).1 hn)
      rw [one_mul, psi_one k r z cStd hz, one_mul] at h1
      exact h1
    · intro g hg h hh h' hh'
      exact hW g ((glev_zero k r g).1 hg.1) h hh h' hh'
end PI.UnitaryGroupMassFormula.QnFFZero
