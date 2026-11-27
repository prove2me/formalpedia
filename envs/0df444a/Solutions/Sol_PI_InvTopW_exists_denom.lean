-- Prove2me | solution 1 for PI.InvTopW.exists_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:15:13.715732+00:00
-- url     : https://prove2.me/submissions/410487eb-2afe-4746-b812-191c1aa8ba31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LinearIndependentOneBeta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_CoordFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_CoordFinInv
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
variable (I : AutInst)
namespace PI.InvTopW
theorem _root_.solution : ∃ D : ℕ, 1 ≤ D ∧ ∀ o : 𝓞 I.E, ∀ j : Fin 2,
    ∃ r : 𝓞 I.F, (D : I.F) * (basisE I).repr (o : I.E) j = algebraMap (𝓞 I.F) I.F r := by
  classical
  set eb := NumberField.RingOfIntegers.basis I.E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((Finset.univ : Finset (_ × Fin 2)).image
      (fun p => (basisE I).repr ((eb p.1 : 𝓞 I.E) : I.E) p.2))
  refine ⟨y.natAbs, Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hy0), ?_⟩
  have hint : ∀ c : I.F, IsIntegral ℤ (y • c) → IsIntegral ℤ ((y.natAbs : I.F) * c) := by
    intro c hc
    rcases Int.natAbs_eq y with h | h
    · have : ((y.natAbs : ℤ) : I.F) * c = y • c := by rw [← h, zsmul_eq_mul]
      rw [← Int.cast_natCast, this]
      exact hc
    · have : ((y.natAbs : ℤ) : I.F) * c = -(y • c) := by
        rw [zsmul_eq_mul]
        conv_rhs => rw [h]
        push_cast
        ring
      rw [← Int.cast_natCast, this]
      exact hc.neg
  have gen : ∀ i j, ∃ r : 𝓞 I.F,
      (y.natAbs : I.F) * (basisE I).repr ((eb i : 𝓞 I.E) : I.E) j = algebraMap (𝓞 I.F) I.F r := by
    intro i j
    have hm := hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
    exact ⟨⟨_, hint _ hm⟩, rfl⟩
  intro o
  have ho : o ∈ Submodule.span ℤ (Set.range eb) := by rw [eb.span_eq]; exact Submodule.mem_top
  induction ho using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact gen i
  | zero =>
    intro j
    exact ⟨0, by simp⟩
  | add x y' _ _ hx hy' =>
    intro j
    obtain ⟨r, hr⟩ := hx j
    obtain ⟨r', hr'⟩ := hy' j
    refine ⟨r + r', ?_⟩
    rw [map_add, ← hr, ← hr']
    push_cast
    rw [map_add, Finsupp.add_apply, mul_add]
  | smul a x _ hx =>
    intro j
    obtain ⟨r, hr⟩ := hx j
    refine ⟨a • r, ?_⟩
    rw [map_zsmul, ← hr]
    have e : ((a • x : 𝓞 I.E) : I.E) = a • (x : I.E) := by push_cast; rfl
    rw [e, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul, zsmul_eq_mul]
    ring
end PI.InvTopW
