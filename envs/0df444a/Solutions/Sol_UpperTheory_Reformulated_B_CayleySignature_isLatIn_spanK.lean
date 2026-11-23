-- Prove2me | solution 1 for UpperTheory.Reformulated.B.CayleySignature.isLatIn_spanK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:29.591177+00:00
-- url     : https://prove2.me/submissions/0259e7d5-4773-41ad-b960-fd57b19fcb50

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleySignature

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.CayleySignature
theorem _root_.solution :
    ∀ {O K V : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field K] [inst_3 : Algebra O K] [IsFractionRing O K]
      [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V] [inst_7 : _root_.Module O V] [inst_8 : IsScalarTower O K V]
      {N : Submodule O V}, N.FG → UpperTheory.Reformulated.B.CayleySignature.IsLatIn N (Submodule.restrictScalars O (Submodule.span K (↑N : Set V))) := by
  intro O K V _ _ _ _ _ _ _ _ _ N hN
  refine ⟨hN, fun x hx => Submodule.subset_span hx, fun x hx => ?_⟩
  rw [Submodule.restrictScalars_mem] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hay
    · rw [mul_smul]
      exact N.smul_mem a hbz
  | smul k y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors O) k
    refine ⟨a * (q : O), mul_ne_zero ha (nonZeroDivisors.coe_ne_zero q), ?_⟩
    have h1 : (q : O) • (k • y) = p • y := by
      rw [← algebraMap_smul K (q : O), smul_smul, mul_comm, hpq, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact N.smul_mem p hay
end UpperTheory.Reformulated.B.CayleySignature
