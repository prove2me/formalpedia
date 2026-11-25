-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.KE.finite_domain_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:40:56.368309+00:00
-- url     : https://prove2.me/submissions/b154198d-75e5-44c8-a301-4c715f99aa46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1 ReciprocityTheory.ChartRestriction.L1.KE
open Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1.KE
theorem _root_.solution (R : Type*) [CommRing R] [IsDomain R] [Finite R] (l : ℕ) (hl : l.Prime)
    (h0 : (l : R) = 0) : ∃ f : ℕ, 0 < f ∧ ∀ x : R, x ^ (l ^ f) = x := by
  classical
  have hch : CharP R l := (CharP.charP_iff_prime_eq_zero hl).mpr h0
  let _ := Fintype.ofFinite R
  let _ : Field R := Fintype.fieldOfDomain R
  obtain ⟨n, -, hq⟩ := FiniteField.card R l
  exact ⟨n, n.pos, fun x => hq ▸ FiniteField.pow_card x⟩
end ReciprocityTheory.ChartRestriction.L1.KE
