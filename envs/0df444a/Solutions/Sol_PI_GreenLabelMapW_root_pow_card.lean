-- Prove2me | solution 1 for PI.GreenLabelMapW.root_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:44.152913+00:00
-- url     : https://prove2.me/submissions/45bedea2-f8e9-4440-9231-493536ac9109

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Theorems.Thm_PI_GreenLabelMapW_root_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K]
namespace PI.GreenLabelMapW
theorem _root_.solution {P : K[X]} (hm : P.Monic) (hi : Irreducible P) (hX : P ≠ X)
    {w : AlgebraicClosure K} (hw : aeval w P = 0) :
    w ^ (Fintype.card K ^ P.natDegree - 1) = 1 := by
  have hint : IsIntegral K w := ⟨P, hm, hw⟩
  have hmin : P = minpoly K w := minpoly.eq_of_irreducible_of_monic hi hw hm
  have hw0 := root_ne_zero hm hi hX hw
  haveI : FiniteDimensional K K⟮w⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K⟮w⟯ := Module.finite_of_finite K
  letI : Fintype K⟮w⟯ := Fintype.ofFinite _
  have hcard : Fintype.card K⟮w⟯ = Fintype.card K ^ P.natDegree := by
    rw [Module.card_eq_pow_finrank (K := K), IntermediateField.adjoin.finrank hint, ← hmin]
  have h1 := FiniteField.pow_card_sub_one_eq_one (⟨w, IntermediateField.mem_adjoin_simple_self K w⟩ : K⟮w⟯)
    (fun h => hw0 (by simpa using congrArg Subtype.val h))
  rw [hcard] at h1
  simpa using congrArg Subtype.val h1
end PI.GreenLabelMapW
