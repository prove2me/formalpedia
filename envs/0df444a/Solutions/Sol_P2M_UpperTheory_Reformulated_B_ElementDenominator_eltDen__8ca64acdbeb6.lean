-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_ElementDenominator_eltDen__8ca64acdbeb6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:15.260022+00:00
-- url     : https://prove2.me/submissions/8b96cc4b-277a-4072-afb0-00993c5559dd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ElementDenominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.ElementDenominator.eltDen
theorem _root_.solution.{u_1, u_2, u_3} :
    ∀ {K : Type u_1} [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [IsDomain R] [inst_3 : Algebra R K]
    [IsFractionRing R K] {V : Type u_3} [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V]
    [inst_7 : _root_.Module R V] [IsScalarTower R K V] (Y : Submodule R V) {y : V},
    y ∈ Submodule.span K (↑Y : Set V) → ∃ (s : R), s ≠ (0 : R) ∧ s • y ∈ Y := by
  intro K _ R _ _ _ _ V _ _ _ _ Y y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Y.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    rw [smul_add]
    refine Y.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact Y.smul_mem t hsx
    · rw [mul_smul]
      exact Y.smul_mem s htz
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) c
    refine ⟨s * (b : R), mul_ne_zero hs (nonZeroDivisors.coe_ne_zero b), ?_⟩
    have h1 : (b : R) • (c • x) = a • x := by
      rw [← algebraMap_smul K (b : R) (c • x), smul_smul, mul_comm, hab, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact Y.smul_mem a hsx
end UpperTheory.Reformulated.B.ElementDenominator.eltDen
