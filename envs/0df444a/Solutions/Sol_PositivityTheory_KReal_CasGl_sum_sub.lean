-- Prove2me | solution 1 for PositivityTheory.KReal.CasGl.sum_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:06.325037+00:00
-- url     : https://prove2.me/submissions/de58fbd4-be10-41bc-9375-9b77f205135c

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCas
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
open PositivityTheory.KReal.CasGl
variable {r s : ℕ}
namespace PositivityTheory.KReal.CasGl
theorem _root_.solution {N : Type} [AddCommMonoid N] (P : Ix r s → Ix r s → Prop) [∀ a b, Decidable (P a b)]
    (F : Ix r s → Ix r s → N) :
    ∑ k : {ab : Ix r s × Ix r s // P ab.1 ab.2}, F k.1.1 k.1.2 = ∑ a, ∑ b, if P a b then F a b else 0 := by
  rw [← Fintype.sum_prod_type' (f := fun a b => if P a b then F a b else 0), ← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun ab : Ix r s × Ix r s => P ab.1 ab.2)
    (Finset.univ.filter fun ab : Ix r s × Ix r s => P ab.1 ab.2) (by simp) (fun ab => F ab.1 ab.2)).symm
end PositivityTheory.KReal.CasGl
