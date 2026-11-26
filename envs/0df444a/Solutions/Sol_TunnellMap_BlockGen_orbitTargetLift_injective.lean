-- Prove2me | solution 1 for TunnellMap.BlockGen.orbitTargetLift_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:30:24.550522+00:00
-- url     : https://prove2.me/submissions/4f304af9-748c-44a8-b945-648c10f259f4

import Definitions.Def_TunnellMap_BlockGenerator
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Theorems.Thm_TunnellMap_FreeInvolution_orbit_canonicalRepresentative
import Theorems.Thm_TunnellMap_residualTargetLift_injective


set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution {n : ℤ} (hnpos : 0 < n) :
    Function.Injective (orbitTargetLift hnpos) := by
  intro o₁ o₂ h
  have ht := residualTargetLift_injective h
  calc
    o₁ = (aResidualInvolution n hnpos).orbit
          (canonicalAResidualRepresentative hnpos o₁) :=
      ((aResidualInvolution n hnpos).orbit_canonicalRepresentative
        aResidualLexKey aResidualLexKey_injective o₁).symm
    _ = (aResidualInvolution n hnpos).orbit
          (canonicalAResidualRepresentative hnpos o₂) := by rw [ht]
    _ = o₂ := (aResidualInvolution n hnpos).orbit_canonicalRepresentative
        aResidualLexKey aResidualLexKey_injective o₂
end TunnellMap.BlockGen
