-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.antiE_isGlRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:47.945988+00:00
-- url     : https://prove2.me/submissions/306c130e-5aab-46f1-9bbc-289ecd79bc08

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_AntiEIsGlRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) : IsGlRep (antiE E) := by
  intro a b c d
  have h := hE (Fin.rev d) (Fin.rev c) (Fin.rev b) (Fin.rev a)
  simp only [Fin.rev_inj, show (c = b) ↔ (b = c) from eq_comm,
    show (a = d) ↔ (d = a) from eq_comm] at h
  simp only [antiE, neg_mul_neg]
  rw [← neg_sub, h]
  split_ifs <;> simp <;> abel
end ReciprocityTheory.ChartRestriction.DS
