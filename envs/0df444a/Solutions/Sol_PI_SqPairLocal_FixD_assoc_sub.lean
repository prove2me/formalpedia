-- Prove2me | solution 1 for PI.SqPairLocal.FixD.assoc_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:58.878345+00:00
-- url     : https://prove2.me/submissions/2360666d-fe50-4a9d-bec1-55ce0f2774f3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnitIffSub
import Theorems.Thm_PI_SqPairLocal_mem_fixSub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open PI PI.SqPairLocal PI.SqPairLocal.FixD
variable {R : Type} [CommRing R] [IsDomain R] (σ : R ≃+* R)
namespace PI.SqPairLocal.FixD
theorem _root_.solution [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) (h : ϖ ∈ fixSub σ)
    {x : fixSub σ} (hx : x ≠ 0) : ∃ n : ℕ, Associated ((⟨ϖ, h⟩ : fixSub σ) ^ n) x := by
  have hne : (x : R) ≠ 0 := fun h0 => hx (Subtype.ext h0)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hϖ
  refine ⟨n, ?_⟩
  have hx' : σ (x : R) = x := (mem_fixSub σ x).1 x.2
  have hϖ' : σ ϖ = ϖ := (mem_fixSub σ ϖ).1 h
  have hmem : (u : R) ∈ fixSub σ := by
    rw [mem_fixSub]
    have h2 : (x : R) * σ u = (x : R) * u := by
      calc (x : R) * σ u = σ (x : R) * σ u := by rw [hx']
        _ = σ ((x : R) * u) := (map_mul σ _ _).symm
        _ = σ (ϖ ^ n) := by rw [hu]
        _ = ϖ ^ n := by rw [map_pow, hϖ']
        _ = (x : R) * u := hu.symm
    exact mul_left_cancel₀ hne h2
  have hU : IsUnit (⟨u, hmem⟩ : fixSub σ) := isUnit_sub σ u.isUnit
  refine Associated.symm (⟨hU.unit, Subtype.ext ?_⟩ : Associated x ((⟨ϖ, h⟩ : fixSub σ) ^ n))
  rw [IsUnit.unit_spec]
  simpa using hu
end PI.SqPairLocal.FixD
