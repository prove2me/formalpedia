-- Prove2me | solution 1 for ValuationSubring.valuation_completion_smul_sub_self_lt_one_of_mem_inertiaSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e5f595a2-bb20-5cb9-84be-45697241fc2e

import Mathlib
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_valuation_completion_smul_sub_self_lt_one_of_mem_inertiaSubgroup

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped Classical
open MonoidWithZeroHom ValuationSubring

namespace P2mR1W0inertia

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (A : ValuationSubring K)

theorem valuation_smul_sub_lt_one_of_mem_inertiaSubgroup {σ : A.decompositionSubgroup F}
    (hσ : σ ∈ A.inertiaSubgroup F) (a : A) :
    A.valuation (((σ • a : A) : K) - (a : K)) < 1 := by
  have h1 : σ • IsLocalRing.residue A a = IsLocalRing.residue A a := by
    have := MonoidHom.mem_ker.mp hσ
    have h := RingEquiv.congr_fun this (IsLocalRing.residue A a)
    simpa using h
  rw [← IsLocalRing.ResidueField.residue_smul] at h1
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1
  have h2 := (ValuationSubring.valuation_lt_one_iff A (σ • a - a)).mp h1
  simpa using h2

theorem coe_smul_eq (σ : A.decompositionSubgroup F) (a : A) :
    ((σ • a : A) : K) = (σ : K ≃ₐ[F] K) (a : K) := rfl

theorem exists_valuation_sub_coe_lt_one (x : A.valuation.Completion) (hx : Valued.v x ≤ 1) :
    ∃ a : A, Valued.v (x - ((a : K) : A.valuation.Completion)) < 1 := by
  have hnhds : {z : A.valuation.Completion | Valued.v (z - x) < 1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun z hz => ?_⟩
    simp only [Set.mem_setOf_eq, Units.val_one] at hz
    exact (Valuation.restrict_lt_one_iff _).mp hz
  obtain ⟨y, hy⟩ :=
    (UniformSpace.Completion.denseRange_coe (α := WithVal A.valuation)).mem_nhds hnhds
  simp only [Set.mem_setOf_eq] at hy
  set a : K := WithVal.equiv A.valuation y with ha
  have hya : (y : A.valuation.Completion) = ((a : K) : A.valuation.Completion) := by
    simp [ha]
  rw [hya] at hy
  have haA : a ∈ A := by
    rw [← A.valuation_le_one_iff]
    have hv : Valued.v ((a : K) : A.valuation.Completion) = A.valuation a :=
      Valued.valuedCompletion_apply (K := WithVal A.valuation) _
    rw [← hv]
    have : ((a : K) : A.valuation.Completion) = (((a : K) : A.valuation.Completion) - x) + x := by
      ring
    rw [this]
    exact (Valued.v.map_add _ _).trans (max_le hy.le hx)
  refine ⟨⟨a, haA⟩, ?_⟩
  rw [← Valuation.map_neg, neg_sub]
  exact hy

theorem valuation_smul_sub_lt_one [Fact (A.DecompositionIsometric F)]
    {σ : A.decompositionSubgroup F} (hσ : σ ∈ A.inertiaSubgroup F)
    (x : A.valuation.Completion) (hx : Valued.v x ≤ 1) :
    Valued.v (σ • x - x) < 1 := by
  obtain ⟨a, ha⟩ := exists_valuation_sub_coe_lt_one A x hx
  set y : A.valuation.Completion := x - ((a : K) : A.valuation.Completion) with hy
  have hxy : x = y + ((a : K) : A.valuation.Completion) := by rw [hy]; ring
  have hσa : σ • (((a : A) : K) : A.valuation.Completion) =
      (((σ • a : A) : K) : A.valuation.Completion) := by
    rw [smul_completion_coe]; rfl
  have hdecomp : σ • x - x =
      (σ • y - y) + ((((σ • a : A) : K) : A.valuation.Completion) -
        (((a : A) : K) : A.valuation.Completion)) := by
    rw [hxy, smul_add, hσa]; ring
  rw [hdecomp]
  have h1 : Valued.v (σ • y - y) < 1 := by
    refine lt_of_le_of_lt (Valued.v.map_sub _ _) (max_lt ?_ ha)
    rw [valuation_smul_completion]; exact ha
  have h2 : Valued.v ((((σ • a : A) : K) : A.valuation.Completion) -
      (((a : A) : K) : A.valuation.Completion)) < 1 := by
    rw [← UniformSpace.Completion.coe_sub]
    change Valued.v ((WithVal.toVal A.valuation (((σ • a : A) : K) - ((a : A) : K)) :
      WithVal A.valuation) : A.valuation.Completion) < 1
    rw [Valued.valuedCompletion_apply]
    exact valuation_smul_sub_lt_one_of_mem_inertiaSubgroup A hσ a
  exact lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt h1 h2)

end P2mR1W0inertia

theorem solution
    {F K : Type*} [Field F] [Field K] [Algebra F K] (A : ValuationSubring K)
    [Fact (A.DecompositionIsometric F)]
    {σ : A.decompositionSubgroup F} (hσ : σ ∈ A.inertiaSubgroup F)
    (x : A.valuation.Completion) (hx : Valued.v x ≤ 1) :
    Valued.v (σ • x - x) < 1 :=
  P2mR1W0inertia.valuation_smul_sub_lt_one A hσ x hx

end S_ValuationSubring_valuation_completion_smul_sub_self_lt_one_of_mem_inertiaSubgroup
end P2MW
export P2MW.S_ValuationSubring_valuation_completion_smul_sub_self_lt_one_of_mem_inertiaSubgroup (solution)
