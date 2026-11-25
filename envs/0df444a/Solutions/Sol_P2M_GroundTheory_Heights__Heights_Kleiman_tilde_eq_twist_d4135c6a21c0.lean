-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_tilde_eq_twist_d4135c6a21c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:54.514216+00:00
-- url     : https://prove2.me/submissions/f12942d1-1f63-473b-9598-f5f10d305ac6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_zpow_mul_mem_tilde_8a9044ba1dc2

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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) (I : Chart x) :
    M.tilde c I = ((M.tildeSys 0).twist (twistSys S x c)).sub I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  apply le_antisymm
  · intro y hy
    have h0 : x i ^ (-c) * y ∈ M.tilde 0 I := by
      simpa using zpow_mul_mem_tilde M hi (-c) c hy
    refine Submodule.subset_span ⟨x i ^ c, ?_, x i ^ (-c) * y, h0, ?_⟩
    · change x i ^ c ∈ twistMod S x c I
      rw [twistMod_eq_span c I hi]
      exact Submodule.mem_span_singleton_self _
    · rw [smul_eq_mul, ← mul_assoc, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero, one_mul]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x c I at hq
    rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
    obtain ⟨a, rfl⟩ := hq
    have hy' : x i ^ c * y ∈ M.tilde c I := by
      simpa using zpow_mul_mem_tilde M hi c 0 hy
    have : (a • x i ^ c) • y = a • (x i ^ c * y) := by
      rw [chartRing_smul_def, chartRing_smul_def, smul_eq_mul, mul_assoc]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ a hy'
end GroundTheory.Heights₂.Heights.Kleiman
