-- Prove2me | solution 1 for P2M_PI_DvRows_length_ne_top_of_le_locS__f6d46dbe9ad4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:40.646506+00:00
-- url     : https://prove2.me/submissions/945e766e-65b7-4e63-acdf-d0ed959a3ee9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_finLen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
open Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace PI.DvRows
theorem _root_.solution [IsNoetherianRing R] [Ring.KrullDimLE 1 R] (p : Ideal R)
    [p.IsPrime] (X Y : Submodule R V) (hX : X.FG) (hXY : X ≤ locS (nonZeroDivisors R) Y) :
    Module.length R (↥(localization₂ p X) ⧸ (localization₂ p Y).comap (localization₂ p X).subtype) ≠ ⊤ := by
  obtain ⟨d, hd, hdY⟩ := indexBasic_denom (nonZeroDivisors R) X Y hX hXY
  exact Module.length_ne_top_iff.mpr (indexBasic_finLen p X Y hX hd hdY)
end PI.DvRows
