-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TildeShift_proof_a3c21ad26a82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:02:49.764784+00:00
-- url     : https://prove2.me/submissions/849cb06e-32fe-41f5-a4f2-d9838e762ad1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeShiftSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeShift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_zpow_smul_mem_tilde_035f3a2ed6d6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace TildeShift
theorem _root_.solution : TildeShift.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ M c
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  apply le_antisymm
  · intro y hy
    have h0 : x i ^ (-c) • y ∈ M.tilde 0 I := by
      simpa using M.zpow_smul_mem_tilde hi (-c) c hy
    refine Submodule.subset_span ⟨x i ^ c, ?_, x i ^ (-c) • y, h0, ?_⟩
    · change x i ^ c ∈ twistMod S x c I
      rw [twistMod_eq_span c I hi]
      exact Submodule.mem_span_singleton_self _
    · rw [smul_smul, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero, one_smul]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x c I at hq
    rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
    obtain ⟨a, rfl⟩ := hq
    have hy' : x i ^ c • y ∈ M.tilde c I := by
      simpa using M.zpow_smul_mem_tilde hi c 0 hy
    have : (a • x i ^ c) • y = a • (x i ^ c • y) := by
      rw [chartRing_smul_def, Subalgebra.smul_def, smul_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ a hy'
end TildeShift
end GroundTheory.Heights₂.Heights.Kleiman
