-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence.exists_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:56:26.888974+00:00
-- url     : https://prove2.me/submissions/11d82c51-69c1-4e4a-8830-983d7d6ce686

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
theorem _root_.solution {u : Fin 2 → Fin r → E} (hu : LinearIndependent E u) :
    ∃ a b : Fin r, u 0 a * u 1 b - u 0 b * u 1 a ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hu0 : u 0 ≠ 0 := hu.ne_zero 0
  obtain ⟨a, ha⟩ : ∃ a, u 0 a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu0 (funext h)
  have key := Fintype.linearIndependent_iff.1 hu ![u 1 a, -(u 0 a)] (by
    funext b
    have hb := hcon a b
    simp only [Fin.sum_univ_two, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply]
    linear_combination -hb)
  exact ha (by simpa using key 1)
end ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
