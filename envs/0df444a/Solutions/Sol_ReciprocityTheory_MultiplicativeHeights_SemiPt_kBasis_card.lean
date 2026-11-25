-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.kBasis_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:48:58.287916+00:00
-- url     : https://prove2.me/submissions/249a662e-908c-4e50-aa83-e62165152724

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ
import Definitions.Def_Lemmata_GeneralBFactSecondAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsLattice L) (b : Fin k → Fin r → K)
    (hb : IsKBasisIn L b) : k = r := by
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    rw [eq_top_iff, ← hL.2, Submodule.span_le]
    intro x hx
    exact hb.2.2 x hx
  have h := finrank_span_eq_card hb.2.1
  rw [hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h
  exact h.symm
end ReciprocityTheory.MultiplicativeHeights.SemiPt
