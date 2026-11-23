-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isOpen_subG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:23.190797+00:00
-- url     : https://prove2.me/submissions/609aa3c2-e40b-4d52-b1bc-864e2ba852f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hL : FiniteDimensional ℚ_[p] L) : IsOpen (subG p K L : Set (GK p K)) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  let b := Module.finBasis ℚ_[p] L
  have hopen : IsOpen (⋂ i, {σ : GK p K | σ (b i : PadicAlgCl p) = b i}) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := K) (b i : PadicAlgCl p)
  have heq : (subG p K L : Set (GK p K)) = ⋂ i, {σ : GK p K | σ (b i : PadicAlgCl p) = b i} := by
    ext σ
    rw [Set.mem_iInter]
    constructor
    · intro hσ i
      exact hσ _ (b i).2
    · intro hσ x hx
      have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : PadicAlgCl p) := by
        have := congrArg L.val (b.sum_repr ⟨x, hx⟩)
        rw [map_sum] at this
        exact this.symm
      rw [hx', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul]
      exact congrArg₂ _ ((σ.restrictScalars ℚ_[p]).commutes _) (hσ i)
  rw [heq]
  exact hopen
end ReciprocityTheory.DiscreteGroups.LocalClassField
