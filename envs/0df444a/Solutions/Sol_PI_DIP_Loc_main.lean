-- Prove2me | solution 1 for PI.DIP.Loc.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:15:38.078868+00:00
-- url     : https://prove2.me/submissions/2db90121-23a0-4b3a-b24f-974b2a3a7e2e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_SmulMemOfMemSpan
import Theorems.Thm_PI_DIP_Loc_common_denom
import Theorems.Thm_PI_DIP_Loc_smul_mem_of_mem_span
import Theorems.Thm_PI_DIP_Loc_isPID

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.DIP PI.DIP.Loc
variable (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
variable {K p}
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.DIP.Loc
theorem _root_.solution : LocBasisProp := by
  intro K _ _ V _ _ _ _ p hp Y hY
  have : Fact p.Prime := ⟨hp⟩
  have := isPID K p
  set Y' : Submodule (A K p) V := Submodule.span (A K p) (Y : Set V) with hY'
  have : Module.Finite (A K p) Y' := by
    obtain ⟨S, hS⟩ := hY
    rw [Module.Finite.iff_fg]
    refine ⟨S, ?_⟩
    rw [hY', ← hS, Submodule.span_span_of_tower]
  have : Module.IsTorsionFree (A K p) Y' := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a m h => ?_
    have hV : (a : K) • (m : V) = 0 := congrArg Subtype.val h
    rcases smul_eq_zero.mp hV with h0 | h0
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext h0)
  obtain ⟨r, B⟩ := Module.basisOfFiniteTypeTorsionFree' (R := A K p) (M := Y')
  refine ⟨r, fun i => (B i : V), ?_, fun i => smul_mem_of_mem_span Y (B i).2, ?_⟩
  · have h1 : LinearIndependent (A K p) (fun i => (B i : V)) :=
      B.linearIndependent.map' Y'.subtype Y'.ker_subtype
    exact (LinearIndependent.iff_fractionRing (A K p) K).mp h1
  · intro y hy
    have hy' : y ∈ Y' := Submodule.subset_span hy
    obtain ⟨s, hs, x, hx⟩ := common_denom (fun i => B.repr ⟨y, hy'⟩ i)
    refine ⟨s, hs, x, ?_⟩
    have hsum : (∑ i, B.repr ⟨y, hy'⟩ i • (B i : V)) = y := by
      have := congrArg Subtype.val (B.sum_repr ⟨y, hy'⟩)
      rw [Submodule.coe_sum] at this
      exact this
    conv_lhs => rw [← hsum]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Subalgebra.smul_def, smul_smul, hx i]
end PI.DIP.Loc
