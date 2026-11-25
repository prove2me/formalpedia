-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.rmu_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:52:00.468694+00:00
-- url     : https://prove2.me/submissions/2f1dfae6-7f3f-4292-9673-18d94fc4a0ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FrobFixNegOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_frobFix_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (x : ℂ_[l]) (hx : x ∈ Rmu l) :
    ∃ f : ℕ, 0 < f ∧ ∃ r ∈ Rmu l, x ^ (l ^ f) - x = (l : ℂ_[l]) * r := by
  have hp : l.Prime := Fact.out
  have key : ∀ (y : ℂ_[l]) (hy : y ∈ Subring.closure (muP l)), FrobFix l (⟨y, hy⟩ : Rmu l) := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem z hz =>
      obtain ⟨n, hn, hln, hzn⟩ := hz
      exact frobFix_root hp hn hln (Subtype.ext (by simpa using hzn))
    | zero => exact frobFix_zero hp
    | one => exact frobFix_one
    | add a b ha' hb' ha hb =>
      have e : (⟨a + b, Subring.add_mem _ ha' hb'⟩ : Rmu l) = ⟨a, ha'⟩ + ⟨b, hb'⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact frobFix_add hp ha hb
    | neg a ha' ha =>
      have e : (⟨-a, Subring.neg_mem _ ha'⟩ : Rmu l) = -⟨a, ha'⟩ := Subtype.ext (by simp)
      rw [e]
      exact frobFix_neg hp ha
    | mul a b ha' hb' ha hb =>
      have e : (⟨a * b, Subring.mul_mem _ ha' hb'⟩ : Rmu l) = ⟨a, ha'⟩ * ⟨b, hb'⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact frobFix_mul ha hb
  obtain ⟨f, hf, r, hr⟩ := key x hx
  refine ⟨f, hf, r, r.2, ?_⟩
  have h := congrArg Subtype.val hr
  simpa using h
end ReciprocityTheory.ChartRestriction.L1
