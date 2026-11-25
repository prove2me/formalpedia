-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.length_quot_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:37:11.564842+00:00
-- url     : https://prove2.me/submissions/9bc7bb6b-3a6a-43ce-b39f-bb9a0702c76b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BallQuotLen
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}
namespace PI.UnitaryGroupMassFormula.BallQuotLen
theorem _root_.solution {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N P Q : Submodule R M} (h1 : N ≤ P) (h2 : P ≤ Q) :
    Module.length R (↥Q ⧸ N.comap Q.subtype) =
      Module.length R (↥P ⧸ N.comap P.subtype) + Module.length R (↥Q ⧸ P.comap Q.subtype) := by
  have hle1 : N.comap P.subtype ≤ (N.comap Q.subtype).comap (Submodule.inclusion h2) := by
    intro x hx
    simpa using hx
  have hle2 : N.comap Q.subtype ≤ (P.comap Q.subtype).comap LinearMap.id := by
    intro x hx
    exact h1 hx
  refine Module.length_eq_add_of_exact
    (Submodule.mapQ _ _ (Submodule.inclusion h2) hle1) (Submodule.mapQ _ _ LinearMap.id hle2) ?_ ?_ ?_
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy ⊢
    simpa using hxy
  · intro y
    obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.Quotient.mk q, by simp⟩
  · intro y
    obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply, Set.mem_range,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro hq
      refine ⟨Submodule.Quotient.mk ⟨q, hq⟩, ?_⟩
      rw [Submodule.mapQ_apply]
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hx
      have h3 := h1 hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
        Submodule.coe_inclusion] at h3
      have h4 := P.sub_mem p.2 h3
      simpa using h4
end PI.UnitaryGroupMassFormula.BallQuotLen
