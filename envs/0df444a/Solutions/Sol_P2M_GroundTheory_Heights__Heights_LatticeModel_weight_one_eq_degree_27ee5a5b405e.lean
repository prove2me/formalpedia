-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_weight_one_eq_degree_27ee5a5b405e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:30.815854+00:00
-- url     : https://prove2.me/submissions/3eb81e79-e474-40ca-8e26-2e2029591bfc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA

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
variable {R : Type*} [CommSemiring R]
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution {σ : Type*} (s : σ →₀ ℕ) : Finsupp.weight (1 : σ → ℕ) s = s.degree := by
  rw [Finsupp.degree_eq_weight_one]
  rfl
end GroundTheory.Heights₂.Heights.LatticeModel
