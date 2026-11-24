-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.isLocData_atPrime_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:11.001784+00:00
-- url     : https://prove2.me/submissions/140628a5-5c39-4f18-a0bb-c671da3a1b16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
theorem _root_.solution {R : Type*} [CommRing R] (V Z : Ideal R) [Z.IsPrime]
    (hVZ : V ≤ Z) [(Z.map (Ideal.Quotient.mk V)).IsPrime] :
    IsLocData R (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))) Z.primeCompl V := by
  have hcm : Ideal.comap (Ideal.Quotient.mk V) (Z.map (Ideal.Quotient.mk V)) = Z := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 hVZ]
  have hmem : ∀ s : R, Ideal.Quotient.mk V s ∈ Z.map (Ideal.Quotient.mk V) ↔ s ∈ Z := fun s => by
    rw [← Ideal.mem_comap, hcm]
  have halg : ∀ r : R, algebraMap R (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))) r =
      algebraMap (R ⧸ V) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))) (Ideal.Quotient.mk V r) :=
    fun r => by rw [IsScalarTower.algebraMap_apply R (R ⧸ V), Ideal.Quotient.algebraMap_eq]
  refine ⟨fun s hs => ?_, fun y => ?_, fun r hr => ?_, fun v hv => ?_⟩
  · rw [halg]
    exact IsLocalization.map_units _
      (⟨Ideal.Quotient.mk V s, fun h' => hs ((hmem s).1 h')⟩ : (Z.map (Ideal.Quotient.mk V)).primeCompl)
  · obtain ⟨⟨x, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Z.map (Ideal.Quotient.mk V)).primeCompl y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (m : R ⧸ V)
    refine ⟨a, t, ?_, ?_⟩
    · intro htZ
      apply m.2
      rw [← ht]
      exact (hmem t).2 htZ
    · rw [halg, halg, ht]
      exact (IsLocalization.mk'_spec _ _ m).symm
  · rw [halg, IsLocalization.map_eq_zero_iff (Z.map (Ideal.Quotient.mk V)).primeCompl] at hr
    obtain ⟨m, hm⟩ := hr
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (m : R ⧸ V)
    refine ⟨t, ?_, ?_⟩
    · intro htZ
      apply m.2
      rw [← ht]
      exact (hmem t).2 htZ
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, ht]
      exact hm
  · rw [halg, Ideal.Quotient.eq_zero_iff_mem.2 hv, map_zero]
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
