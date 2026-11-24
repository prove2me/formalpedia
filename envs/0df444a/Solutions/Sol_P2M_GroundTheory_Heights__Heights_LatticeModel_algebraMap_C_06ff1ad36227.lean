-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_algebraMap_C_06ff1ad36227
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:40.500082+00:00
-- url     : https://prove2.me/submissions/d6370778-672d-4bcb-b8f1-c7a27d1657ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K]
variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (a : K) :
    algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (C a) = algebraMap K (LatticeField K r) a := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin r) K) (LatticeField K r), MvPolynomial.algebraMap_eq]
end GroundTheory.Heights₂.Heights.LatticeModel
