-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomogIdeal_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:11.086324+00:00
-- url     : https://prove2.me/submissions/a6c61f6c-21e4-4996-ad62-fbc5f02dc642

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_LengthLocQuotEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)} {f : Fin N → MRing ι}
    {c : Fin N → K → ℕ} (h0 : IsMultiHomogIdeal (F 0))
    (hj : ∀ j : Fin N, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j}) :
    ∀ j : Fin (N + 1), IsMultiHomogIdeal (F j) := by
  intro j
  induction j using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    obtain ⟨S, hS, hSe⟩ := ih
    refine ⟨S ∪ {f i}, ?_, ?_⟩
    · rintro g (hg | hg)
      · exact hS g hg
      · rw [Set.mem_singleton_iff.1 hg]; exact ⟨c i, (hj i).1⟩
    · rw [(hj i).2, hSe, Ideal.span_union]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
