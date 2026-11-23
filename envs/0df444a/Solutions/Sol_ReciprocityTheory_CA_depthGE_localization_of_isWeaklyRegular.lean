-- Prove2me | solution 1 for ReciprocityTheory.CA.depthGE_localization_of_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:14.065644+00:00
-- url     : https://prove2.me/submissions/9f8a32a7-5a93-4d8a-9aa9-2b84e9c52b2a

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularOfLeHeight
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
namespace ReciprocityTheory.CA
theorem _root_.solution {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime]
    {rs : List R} (hrs : ∀ x ∈ rs, x ∈ P) (reg : IsWeaklyRegular R rs) :
    DepthGE (Localization.AtPrime P) rs.length := by
  have hmem : ∀ r ∈ rs.map (algebraMap R (Localization.AtPrime P)),
      r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P x).2 (hrs x hx)
  refine ⟨rs.map (algebraMap R (Localization.AtPrime P)), List.length_map _, hmem, reg.of_flat, ?_⟩
  intro h
  have hle : Ideal.ofList (rs.map (algebraMap R (Localization.AtPrime P))) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    Ideal.span_le.2 fun r hr => hmem r hr
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at h
  rw [← h] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime P)).ne_top (top_le_iff.1 hle)
end ReciprocityTheory.CA
