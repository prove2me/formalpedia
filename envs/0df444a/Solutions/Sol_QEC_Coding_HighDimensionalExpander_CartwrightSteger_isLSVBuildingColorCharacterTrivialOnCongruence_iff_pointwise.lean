-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVBuildingColorCharacterTrivialOnCongruence_iff_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:06:18.382372+00:00
-- url     : https://prove2.me/submissions/3a07f16e-59e8-4b96-8d5a-2096eb965f10

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (character : Multiplicative (ZMod r.matrixRank) →* ℂ) :
    IsLSVBuildingColorCharacterTrivialOnCongruence
        P r level character ↔
      ∀ g : BuildingCartwrightStegerCongruenceSubgroup P r level,
        character (lsvBuildingLatticeColor P r g.1) = 1 := by
  constructor
  · intro h g
    rw [← MonoidHom.mem_ker]
    exact h ⟨g.1, g.2, rfl⟩
  · intro h z hz
    obtain ⟨g, hg, rfl⟩ := hz
    rw [MonoidHom.mem_ker]
    exact h ⟨g, hg⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
