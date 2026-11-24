-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Conservation_not_horizontal_d25330750319
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:01.461172+00:00
-- url     : https://prove2.me/submissions/6c785d21-8ae9-4eac-9959-c1353780f932

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_comap_eq_of_mem_03b704367dba

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.Inter.Conservation
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.Conservation
theorem _root_.solution {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    ¬ IsHorizontal W := by
  intro h
  have := comap_eq_of_mem hp hW
  rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from h, eq_comm, Ideal.span_singleton_eq_bot] at this
  exact hp.ne_zero (by exact_mod_cast this)
end GroundTheory.Heights₂.Heights.Inter.Conservation
