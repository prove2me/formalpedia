-- Prove2me | solution 1 for QEC.Locality.exists_uniform_explicitProfileEdgeDivision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:01:22.719219+00:00
-- url     : https://prove2.me/submissions/1a753ef6-56d3-4b0b-9c4d-ec4b375225e5

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedPotential
import Definitions.Def_QEC_Locality_SeparatorProfile_ExplicitDivision
import Theorems.Thm_QEC_Locality_profileDivisionRegionConstant_pos


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (beta exponent : ℝ) (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1) :
    ∃ threshold : Nat, ∃ countConstant : ℝ,
      threshold = profileDivisionThreshold beta exponent ∧
      countConstant = profileDivisionRegionConstant beta exponent ∧
      0 < countConstant ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
        (G : ConnectivityGraph ι)
        (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
        (r : Nat), 2 ≤ r → threshold ≤ r →
          Nonempty (ExplicitProfileEdgeDivision G r
            (weightedProfileBoundaryBudget beta exponent r)
            (Nat.ceil (countConstant * Fintype.card ι / r))) := by
  refine ⟨profileDivisionThreshold beta exponent,
    profileDivisionRegionConstant beta exponent, rfl, rfl,
    profileDivisionRegionConstant_pos hbeta hexponent, ?_⟩
  intro ι instFintype instDecidableEq G hProfile r hr hthreshold
  exact ⟨explicitProfileEdgeDivision G beta exponent hProfile hexponent r hr hthreshold⟩
end QEC.Locality
