-- Prove2me | solution 1 for QEC.Semantics.Qubit.flipAt_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:39:00.274647+00:00
-- url     : https://prove2.me/submissions/e632b965-a609-4ba1-8fa4-3097805f83df

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
namespace QEC.Semantics.Qubit
theorem _root_.solution {ι : Type u} [DecidableEq ι]
    (i j : ι) (bits : Bitstring ι) :
    flipAt i (flipAt j bits) = flipAt j (flipAt i bits) := by
  by_cases hij : i = j
  · subst j
    simp
  · funext k
    by_cases hki : k = i
    · subst k
      simp [flipAt, hij, Ne.symm hij]
    · by_cases hkj : k = j
      · subst k
        simp [flipAt, hki, hij]
      · simp [flipAt, hki, hkj]
end QEC.Semantics.Qubit
