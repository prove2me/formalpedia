-- Prove2me | solution 1 for PI.LocDualGen.FpU.one_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:04:40.35184+00:00
-- url     : https://prove2.me/submissions/c1801180-9f2c-4438-88ba-933fc7cdf5b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Theorems.Thm_PI_LocDualGen_FpU_res_Phi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsLocalRing
open PI PI.LocDualGen PI.LocDualGen.FpU
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
variable [CharP 𝓀[K] l]
attribute [local instance] algRes
namespace PI.LocDualGen.FpU
theorem _root_.solution (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ∃ c, ∃ y : 𝒪[K], x = Phi K l hcont c + (l : 𝒪[K]) * y := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  set r := (bb K l).repr (residue 𝒪[K] x) with hr
  refine ?_
  have hc : residue 𝒪[K] (Phi K l hcont (fun i => ((r i).val : ℤ_[l]))) = residue 𝒪[K] x := by
    rw [res_Phi]
    have h1 : ∀ i, PadicInt.toZMod (((r i).val : ℕ) : ℤ_[l]) = r i := fun i => by
      rw [map_natCast, ZMod.natCast_zmod_val]
    simp_rw [h1]
    exact (bb K l).sum_repr (residue 𝒪[K] x)
  have hm : x - Phi K l hcont (fun i => ((r i).val : ℤ_[l])) ∈ maximalIdeal 𝒪[K] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hc, sub_self]
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 huni,
    Ideal.mem_span_singleton'] at hm
  obtain ⟨y, hy⟩ := hm
  exact ⟨_, y, by rw [mul_comm, hy]; ring⟩
end PI.LocDualGen.FpU
