-- Prove2me | solution 1 for SoficGroups.hasPropertyT_of_finiteOuterBlockCyclicRootFamily_generate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/b34cd800-401c-4006-91b0-2c9a12e5d72d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_inv_sqrt_eight_pos
import Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_inv_sqrt_eight_lt_one_half
import Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_norm_inner_le_inv_sqrt_eight_of_sq
import Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_hasPropertyT_of_three_finite_subgroups_friedrichs_angle
import Theorems.Thm_SoficGroups_finite_finiteOuterBlockRootSubgroup
import Theorems.Thm_SoficGroups_finiteOuterBlockCyclicRootFamily_pair_inner_sq_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators
universe vSharp
namespace SoficGroups
theorem _root_.solution
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    (W : Submodule (ZMod 2) R) [Finite W]
    (hgen :
      (⨆ i : Fin 3, finiteOuterBlockCyclicRootFamily W i) = ⊤) :
    HasPropertyT.{_, vSharp}
      (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) := by
  classical
  have hfinite (i : Fin 3) :
      Finite (finiteOuterBlockCyclicRootFamily W i) := by
    fin_cases i
    · exact finite_finiteOuterBlockRootSubgroup W 0 1 (by decide)
    · exact finite_finiteOuterBlockRootSubgroup W 1 2 (by decide)
    · exact finite_finiteOuterBlockRootSubgroup W 2 0 (by decide)
  letI (i : Fin 3) : Finite (finiteOuterBlockCyclicRootFamily W i) :=
    hfinite i
  letI (i : Fin 3) : Fintype (finiteOuterBlockCyclicRootFamily W i) :=
    Fintype.ofFinite _
  apply ErshovJaikinFiniteSpectral.hasPropertyT_of_three_finite_subgroups_friedrichs_angle
    (finiteOuterBlockCyclicRootFamily W) hgen
    (Real.sqrt (8 : ℝ))⁻¹
    (le_of_lt ErshovJaikinFiniteSpectral.inv_sqrt_eight_pos)
    ErshovJaikinFiniteSpectral.inv_sqrt_eight_lt_one_half
  intro H _ _ _ π i j hij a b ha haQ hb hbQ
  have hfixed
      (K : Subgroup
        (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))) :
      unitaryFixedSubmodule π K = ejUnitaryFixedSubmodule π K := by
    ext z
    rfl
  rw [← hfixed] at ha haQ hb hbQ
  exact ErshovJaikinFiniteSpectral.norm_inner_le_inv_sqrt_eight_of_sq a b
    (finiteOuterBlockCyclicRootFamily_pair_inner_sq_le
      W π i j hij a b ha haQ hb hbQ)
end SoficGroups
