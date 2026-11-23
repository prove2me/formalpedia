-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.finiteDimensional_Kloc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:30.372633+00:00
-- url     : https://prove2.me/submissions/50564dad-7041-4009-844c-3ff5bb57b0bd

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) : FiniteDimensional ℚ_[p] (Kloc F ι) := by
  classical
  let b := Module.finBasis ℚ F
  let f := ι.comp (algebraMap F Ω)
  have hle : Kloc F ι ≤ IntermediateField.adjoin ℚ_[p] (Set.range fun i => f (b i)) := by
    apply IntermediateField.adjoin_le_iff.2
    rintro _ ⟨y, rfl⟩
    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul, Rat.smul_def, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p))]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (Set.range fun i => f (b i))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)
end ReciprocityTheory.Neutral.Cmp
