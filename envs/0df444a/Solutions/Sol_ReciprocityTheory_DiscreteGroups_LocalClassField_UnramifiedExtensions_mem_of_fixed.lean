-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.mem_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:49.385476+00:00
-- url     : https://prove2.me/submissions/36c9a2b8-9b63-4cb5-b4b9-d18751d5b7db

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {x : PadicAlgCl p}
    (h : ∀ σ : GK p K, σ x = x) : x ∈ K := by
  obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (K := PadicAlgCl p) x).2 h
  rw [← hy]
  exact y.2
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
