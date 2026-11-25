-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Conservation_charOf_eq_fb1e6fa2063a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:57:33.34964+00:00
-- url     : https://prove2.me/submissions/fe11e5c3-3468-4cd8-b5f3-624f44cbe374

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
    charOf W = p := by
  have h := comap_eq_of_mem hp hW
  unfold charOf
  have hg : Ideal.span {Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))} =
      Ideal.span {(p : ℤ)} := by
    rw [← h]; exact Submodule.IsPrincipal.span_singleton_generator _
  rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at hg
  simpa using hg
end GroundTheory.Heights₂.Heights.Inter.Conservation
