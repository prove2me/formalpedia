-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Tm_prime_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:12.817809+00:00
-- url     : https://prove2.me/submissions/e11ad457-526f-480d-a567-4767397eb94d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {p : ℕ} (hp : p.Prime) :
    ((p, 0, 1) : ℕ × ℕ × ℕ) ∉ (Finset.range p).image fun b => ((1, b, p) : ℕ × ℕ × ℕ) := by
  intro h
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
  simp only [Prod.mk.injEq] at hb
  exact hp.one_lt.ne hb.1
end ReciprocityTheory.ChartRestriction.L1
