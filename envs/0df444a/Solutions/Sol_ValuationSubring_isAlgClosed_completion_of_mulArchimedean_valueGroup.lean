-- Prove2me | solution 1 for ValuationSubring.isAlgClosed_completion_of_mulArchimedean_valueGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/2d00d357-fef1-5309-9355-29f528b421c7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isAlgClosed_completion_of_mulArchimedean_valueGroup

open scoped Classical
open MonoidWithZeroHom

namespace P2mR1W0kur

section Kurschak

variable {K : Type*} [Field K] (A : ValuationSubring K)

theorem mulArchimedean_valueGroup₀ {L Γ₀ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ₀]
    [MulArchimedean Γ₀] (v : Valuation L Γ₀) : MulArchimedean (ValueGroup₀ (.ofClass v)) := by
  haveI : MulArchimedean (valueGroup (.ofClass v)) :=
    MulArchimedean.comap (valueGroup (.ofClass v)).subtype (Subtype.strictMono_coe _)
  infer_instance

@[reducible] noncomputable def rankOneOfMulArchimedean {L Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] [MulArchimedean Γ₀] (v : Valuation L Γ₀)
    [v.IsNontrivial] : v.RankOne :=
  haveI := mulArchimedean_valueGroup₀ v
  (Valuation.nonempty_rankOne_iff_mulArchimedean.mpr inferInstance).some

theorem isNontrivial_valuation (hA : A ≠ ⊤) : A.valuation.IsNontrivial := by
  obtain ⟨x, hx⟩ : ∃ x : K, x ∉ A := by
    by_contra h
    push Not at h
    exact hA (eq_top_iff.mpr fun x _ => h x)
  refine ⟨x, ?_, ?_⟩
  · intro h0
    rw [Valuation.zero_iff] at h0
    exact hx (h0 ▸ A.zero_mem)
  · intro h1
    exact hx ((A.valuation_le_one_iff x).mp h1.le)

theorem isNontrivial_withVal (hA : A ≠ ⊤) :
    (Valued.v (R := WithVal A.valuation)).IsNontrivial := by
  obtain ⟨x, h0, h1⟩ := isNontrivial_valuation A hA
  exact ⟨WithVal.toVal A.valuation x, h0, h1⟩

theorem isNontrivial_completion (hA : A ≠ ⊤) :
    (Valued.v (R := A.valuation.Completion)).IsNontrivial := by
  obtain ⟨x, h0, h1⟩ := isNontrivial_valuation A hA
  refine ⟨((WithVal.toVal A.valuation x : WithVal A.valuation) : A.valuation.Completion), ?_, ?_⟩
  · rw [Valued.valuedCompletion_apply]; exact h0
  · rw [Valued.valuedCompletion_apply]; exact h1

theorem isAlgClosed_completion [IsAlgClosed K] [CharZero K] [MulArchimedean A.ValueGroup]
    (hA : A ≠ ⊤) :
    IsAlgClosed A.valuation.Completion := by
  haveI := isNontrivial_completion A hA
  letI hr : (Valued.v (R := A.valuation.Completion)).RankOne := rankOneOfMulArchimedean _
  letI : NontriviallyNormedField A.valuation.Completion :=
    Valued.toNontriviallyNormedField A.valuation.Completion A.ValueGroup
  haveI : IsUltrametricDist A.valuation.Completion := inferInstance
  haveI : CompleteSpace A.valuation.Completion := inferInstance
  haveI : CharZero A.valuation.Completion :=
    charZero_of_injective_ringHom
      (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).injective
  haveI : IsAlgClosed (WithVal A.valuation) :=
    IsAlgClosed.of_ringEquiv K (WithVal A.valuation) (WithVal.equiv A.valuation).symm
  exact IsAlgClosed.of_denseRange (K := WithVal A.valuation)
    UniformSpace.Completion.denseRange_coe

end Kurschak

end P2mR1W0kur

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (A : ValuationSubring K) [MulArchimedean A.ValueGroup] (hA : A ≠ ⊤) :
    IsAlgClosed A.valuation.Completion :=
  P2mR1W0kur.isAlgClosed_completion A hA

end S_ValuationSubring_isAlgClosed_completion_of_mulArchimedean_valueGroup
end P2MW
export P2MW.S_ValuationSubring_isAlgClosed_completion_of_mulArchimedean_valueGroup (solution)
