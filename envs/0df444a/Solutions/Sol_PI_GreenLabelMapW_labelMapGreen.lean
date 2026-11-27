-- Prove2me | solution 1 for PI.GreenLabelMapW.labelMapGreen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:16:36.956689+00:00
-- url     : https://prove2.me/submissions/5300e3fa-fded-473c-ba15-62bc27613c65

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_GaloisClause
import Theorems.Thm_PI_GreenLabelMapW_galois_clause
import Theorems.Thm_PI_GreenLabelMapW_dual_clause
import Theorems.Thm_PI_GreenLabelMapW_greenLab_iso
import Theorems.Thm_PI_GreenLabelMapW_greenLab_one
import Theorems.Thm_PI_GreenLabelMapW_greenLab_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace PI.GreenLabelMapW
theorem _root_.solution : LabelMapGreen K := by
  intro C hC
  refine ⟨{ lab := greenLab C
            lab_iso := greenLab_iso C
            lab_spec := ?_
            lab_inj := ?_
            lab_one := ?_ }, ⟨?_, ?_⟩, ?_⟩
  · intro d τ hd hs hc
    obtain ⟨h1, h2, h3, h4, -⟩ := greenLab_spec C hC hd hs hc
    exact ⟨h1, h2, h3, by simpa using h4⟩
  · intro d τ τ' hd hs hc hs' hc' heq
    have h' : HasCuspLabel C τ' (greenLab C d τ) := by
      rw [heq]
      exact greenLab_spec C hC hd hs' hc'
    exact (hC d hd).2.2 τ τ' (greenLab C d τ) hs hc hs' hc' (greenLab_spec C hC hd hs hc) h'
  · intro τ x hs hx htr
    exact greenLab_one C hC τ x hs hx htr
  · intro d α a hα τ τ' hd hs hc hs' hc' htr
    exact galois_clause C hC d α a hα τ τ' hd hs hc hs' hc' htr
  · intro d τ τ' hd hs hc hs' hc' htr
    exact dual_clause C hC d τ τ' hd hs hc hs' hc' htr
  · intro d τ hd hs hc
    exact greenLab_spec C hC hd hs hc
end PI.GreenLabelMapW
