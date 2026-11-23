-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hint_eval_indep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:52.479089+00:00
-- url     : https://prove2.me/submissions/4e4fd152-0be5-44c3-b259-c8cd19166c48

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {D n : ℕ} {a : Fin (D + 1) → ℕ} {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ}
    (hq : IsMultiHomogeneous a q) (ha : a 0 = 0) (x y : Fin (D + 1) × Fin n → ℂ)
    (hxy : ∀ v : Fin (D + 1) × Fin n, v.1 ≠ 0 → x v = y v) :
    MvPolynomial.eval x q = MvPolynomial.eval y q := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun s hs => ?_
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v.1 = 0
  · have h0 : s v = 0 := by
      have hsum := hq s hs 0
      rw [ha] at hsum
      have hle : s (0, v.2) ≤ ∑ j : Fin n, s (0, j) :=
        Finset.single_le_sum (f := fun j => s (0, j)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ _)
      have hz : s (0, v.2) = 0 := by omega
      have hv' : v = (0, v.2) := Prod.ext hv rfl
      rw [hv']
      exact hz
    rw [h0, pow_zero, pow_zero]
  · rw [hxy v hv]
end ReciprocityTheory.ChartRestriction.G.T0
