-- Prove2me | solution 1 for QEC.Semantics.Qubit.localX_localX_commute
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:13:58.940404+00:00
-- url     : https://prove2.me/submissions/217e3227-3968-40fe-81b0-f50f6eaf2749

-- ID: 64c0a779-c9d1-4a65-a2bb-8707cd4ae98a | NAME: QEC.Semantics.Qubit.localX_localX_commute | 未本地编译验证
import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution (i j : ι) :
    localX i * localX j = localX j * localX i := by
  ext ψ bits
  simp only [Module.End.mul_apply, localX_apply]
  have hcomm : flipAt j (flipAt i bits) = flipAt i (flipAt j bits) := by
    by_cases hij : i = j
    · subst j
      rfl
    · simp only [flipAt]
      rw [Function.update_of_ne (Ne.symm hij), Function.update_of_ne hij]
      exact Function.update_comm hij (flipBit (bits i)) (flipBit (bits j)) bits
  rw [hcomm]
