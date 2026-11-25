-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CGlue.cas_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:17.12448+00:00
-- url     : https://prove2.me/submissions/a34bc65f-d596-4f1f-8fb3-785850df3aca

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CoefficientGluing_SumFinVal
import Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_tE_diag_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Formalism.REAL
open scoped TensorProduct
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CGlue
variable {n : ℕ} {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.CGlue
theorem _root_.solution (S : Finset P) (s : ℂ) (f : TV n ℂ P) :
    ∑ i, ∑ j, (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) i j
        (tE S 0 j i f - if j = i then s • f else 0) - if i = j then s • (tE S 0 j i f - if j = i then s • f else 0) else 0) =
      (∑ a, ∑ c, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c * tE S 0 c a : Module.End ℂ (TV n ℂ P)) f -
        (2 * s * S.card - n * s ^ 2) • f := by
  have h1 : ∀ i j, (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) i j (tE S 0 j i f - if j = i then s • f else 0) -
      if i = j then s • (tE S 0 j i f - if j = i then s • f else 0) else 0) =
      tE S 0 i j (tE S 0 j i f) - if i = j then (s • tE S 0 i i f + s • tE S 0 i i f - (s * s) • f) else 0 := by
    intro i j
    by_cases h : i = j
    · subst h; simp only [if_true, map_sub, map_smul, smul_sub, smul_smul]; abel
    · rw [if_neg h, if_neg (Ne.symm h), if_neg h]; simp
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, tE_diag_sum]
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module
end PositivityTheory.Rg.Cz.CGlue
