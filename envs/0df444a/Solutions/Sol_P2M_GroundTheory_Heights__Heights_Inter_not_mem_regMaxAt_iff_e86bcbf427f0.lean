-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_not_mem_regMaxAt_iff_e86bcbf427f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:50.213927+00:00
-- url     : https://prove2.me/submissions/b2b9108e-84f0-4072-b9fe-6e07628b13f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IntCastMemRegMaxAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regToLoc_coe_e35c08fdab1a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W)
    (hloc : IsLocalRing (locRing P W)) (x : regRing P) :
    x ∉ regMaxAt P W hW hPW hloc ↔
      ∃ z ∈ locRing P W, ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1 := by
  have hc : ∀ b : locRing P W, ((regToLoc P W hW hPW x * b : locRing P W) : FractionRing (MRing ι ⧸ P)) =
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) * b := fun b => by
    rw [Subring.coe_mul, regToLoc_coe]
  simp only [regMaxAt, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    refine ⟨b.1, b.2, ?_⟩
    rw [← hc b, hb, Subring.coe_one]
  · rintro ⟨z, hz, h⟩
    refine IsUnit.of_mul_eq_one (a := regToLoc P W hW hPW x) ⟨z, hz⟩ (Subtype.ext ?_)
    rw [hc, Subring.coe_one]
    exact h
end GroundTheory.Heights₂.Heights.Inter
