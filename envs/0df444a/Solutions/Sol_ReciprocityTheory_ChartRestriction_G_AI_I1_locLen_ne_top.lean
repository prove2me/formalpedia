-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:24.296868+00:00
-- url     : https://prove2.me/submissions/86e13b8a-769b-40c4-a763-871ed1e53091

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_ne_top_iff_support


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution [IsNoetherianRing R] {J W : Ideal R} (hW : W ∈ J.minimalPrimes) :
    locLen (R ⧸ J) ⟨W, hW.1.1⟩ ≠ ⊤ := by
  have := hW.1.1
  let A := Localization.AtPrime W
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing W.primeCompl A inferInstance
  have : Module.Finite A (LocalizedModule W.primeCompl (R ⧸ J)) :=
    Module.Finite.of_isLocalizedModule W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl _)
  unfold locLen
  rw [length_ne_top_iff_support]
  intro p hp
  rw [Module.mem_support_iff_of_finite] at hp
  have hJ : J ≤ p.asIdeal.comap (algebraMap R A) := by
    intro r hr
    refine hp (Module.mem_annihilator.mpr fun n => ?_)
    induction n using LocalizedModule.induction_on with
    | h m s =>
      rw [algebraMap_smul, LocalizedModule.smul'_mk]
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).mpr
        (show r • m ∈ J from J.mul_mem_right m hr), LocalizedModule.zero_mk]
  have hle : p.asIdeal.comap (algebraMap R A) ≤ W := by
    have hm : (IsLocalRing.maximalIdeal A).comap (algebraMap R A) = W :=
      Localization.AtPrime.under_maximalIdeal
    exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)).trans hm.le
  have heq : p.asIdeal.comap (algebraMap R A) = W :=
    le_antisymm hle (hW.2 ⟨Ideal.comap_isPrime _ _, hJ⟩ hle)
  have : p.asIdeal = IsLocalRing.maximalIdeal A := by
    calc p.asIdeal = (p.asIdeal.comap (algebraMap R A)).map (algebraMap R A) :=
          (IsLocalization.map_under W.primeCompl A p.asIdeal).symm
      _ = W.map (algebraMap R A) := congrArg (Ideal.map (algebraMap R A)) heq
      _ = IsLocalRing.maximalIdeal A := Localization.AtPrime.map_eq_maximalIdeal
  rw [this]
  exact IsLocalRing.maximalIdeal.isMaximal A
end ReciprocityTheory.ChartRestriction.G.AI.I1
