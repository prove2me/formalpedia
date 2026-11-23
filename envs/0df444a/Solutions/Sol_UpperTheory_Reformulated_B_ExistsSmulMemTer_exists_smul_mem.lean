-- Prove2me | solution 1 for UpperTheory.Reformulated.B.ExistsSmulMemTer.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:14.464798+00:00
-- url     : https://prove2.me/submissions/d09aa459-3548-403f-84ef-084aec99cf81

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.ExistsSmulMemTer
theorem _root_.solution :
    ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (M : Submodule (NumberField.RingOfIntegers K) V),
    ∀ x ∈ Submodule.span K (↑M : Set V),
      ∃ (a : NumberField.RingOfIntegers K), a ≠ (0 : NumberField.RingOfIntegers K) ∧ a • x ∈ M := by
  intro K _ _ V _ _ _ _ M x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hay
    · rw [mul_smul]
      exact M.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    refine ⟨a * (q : NumberField.RingOfIntegers K),
      mul_ne_zero ha (nonZeroDivisors.coe_ne_zero q), ?_⟩
    have h1 : (q : NumberField.RingOfIntegers K) • c • y = p • y := by
      rw [← algebraMap_smul K (q : NumberField.RingOfIntegers K), ← mul_smul, mul_comm]
      simp only at hpq
      rw [hpq, algebraMap_smul]
    rw [mul_smul, h1, ← mul_smul, mul_comm, mul_smul]
    exact M.smul_mem p hay
end UpperTheory.Reformulated.B.ExistsSmulMemTer
