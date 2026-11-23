-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hStd_eq_span_pi_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:50.189624+00:00
-- url     : https://prove2.me/submissions/9945910c-b9bc-4000-a309-68d68fdeb4c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Definitions.Def_ReciprocityTheory_SemistableReduction_DegAddHolds
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_mem_standardLattice_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_pi_single_one_mem_hStd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution : hStd K r =
    Submodule.span (𝓞 K) (Set.range fun i : Fin r => (Pi.single i (1 : K) : Fin r → K)) := by
  apply le_antisymm
  · intro x hx
    rw [mem_standardLattice_iff] at hx
    choose y hy using hx
    have e : x = ∑ i, y i • (Pi.single i (1 : K) : Fin r → K) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp [← hy j, Algebra.smul_def]
      · intro i _ hij
        simp [Pi.single_apply, Ne.symm hij]
      · simp
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact pi_single_one_mem_hStd i
end ReciprocityTheory.ChartRestriction.G.T0
