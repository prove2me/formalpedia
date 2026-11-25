-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_entry_le_fsq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:52.348094+00:00
-- url     : https://prove2.me/submissions/ce390b17-235b-41bf-b2cc-ac232f01b86f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) (i : m) (j : n) :
    Complex.normSq (X i j) ≤ sumBdFsq X := by
  unfold sumBdFsq
  calc Complex.normSq (X i j) ≤ ∑ j', Complex.normSq (X i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (X i j')) (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (X i' j'))
        (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
end ReciprocityTheory.ChartRestriction.G.AR.Up
