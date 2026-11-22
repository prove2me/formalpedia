-- Prove2me | solution 1 for OrderClosures.cnfExtensionLT_linear_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:25.541553+00:00
-- url     : https://prove2.me/submissions/2bbcd2bc-704d-44a2-bfe3-b1f5d04838ad

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Theorems.Thm_OrderClosures_CNFListLT_ordinal_lt
public import Theorems.Thm_OrderClosures_cnfExtensionLT_iff_CNFListLT
public import Theorems.Thm_OrderClosures_CNFListLT_upper_trichotomy

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution (ζ : Ordinal.{u}) :
    ∀ {η η' : Ordinal.{u}}, cnfExtensionLT ζ η → cnfExtensionLT ζ η' →
      (cnfExtensionLT η η' ↔ η < η') := by
  intro η η' hη hη'
  constructor
  · intro h
    exact CNFListLT.ordinal_lt (cnfExtensionLT_iff_CNFListLT.mp h)
  · intro hlt
    rcases CNFListLT.upper_trichotomy
      (cnfExtensionLT_iff_CNFListLT.mp hη)
      (cnfExtensionLT_iff_CNFListLT.mp hη') with heq | h | h
    · have hηeq : η = η' := by
        rw [← Ordinal.CNF.foldr Ordinal.omega0 η,
          ← Ordinal.CNF.foldr Ordinal.omega0 η', heq]
      exact (hlt.ne hηeq).elim
    · exact cnfExtensionLT_iff_CNFListLT.mpr h
    · exact ((CNFListLT.ordinal_lt h).asymm hlt).elim
end OrderClosures
