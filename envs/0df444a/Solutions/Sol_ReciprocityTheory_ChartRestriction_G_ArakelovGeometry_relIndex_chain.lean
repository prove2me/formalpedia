-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.relIndex_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:25:32.228727+00:00
-- url     : https://prove2.me/submissions/5ba24059-398d-473c-906d-4bf608cbb1df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsMPrimeFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_RelIndexNeZeroOfMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Module
variable {Ω : Type} [Field Ω] [CharZero Ω]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {G : Type*} [AddGroup G] (H : ℕ → AddSubgroup G) (n : ℕ)
    (hle : ∀ j < n, H j ≤ H (j + 1)) :
    ∀ k ≤ n, (H 0).relIndex (H k) = ∏ j ∈ Finset.range k, (H j).relIndex (H (j + 1)) ∧ H 0 ≤ H k
  | 0, _ => by simp [AddSubgroup.relIndex_self]
  | k + 1, hk => by
    obtain ⟨h1, h2⟩ := solution H n hle k (by omega)
    refine ⟨?_, h2.trans (hle k (by omega))⟩
    rw [Finset.prod_range_succ, ← h1]
    exact (AddSubgroup.relIndex_mul_relIndex (hHK := h2) (hKL := hle k (by omega))).symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
