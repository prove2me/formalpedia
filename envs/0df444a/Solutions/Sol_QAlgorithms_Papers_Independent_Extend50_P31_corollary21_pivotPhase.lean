-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.corollary21_pivotPhase
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:10:23.004838+00:00
-- url     : https://prove2.me/submissions/ced6f55d-58f1-43ef-b77b-ef9adc5891f5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition20_eigenmatrices
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_sector_unit_vectors_phase
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Extend50.P31
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq



open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.13, Corollary 21 Eq.(64), with a phase depending on the two pivots. -/
theorem solution (D : Data G A n) (r : Row D) (p q : Fin n × Fin n)
    (hp : 0 < pivotWeight D.U D.F r.1.val r.2 p)
    (hq : 0 < pivotWeight D.U D.F r.1.val r.2 q) :
    ∃ zeta : ℝ, (p = q → zeta = 0) ∧
      normalizedMatrix D.U D.F r.1.val r.2 q =
        phase zeta • normalizedMatrix D.U D.F r.1.val r.2 p := by
  by_cases he : p = q
  · subst q
    exact ⟨0,fun _ => rfl,by simp [phase]⟩
  · obtain ⟨hnp,hfp⟩ := (proposition20_eigenmatrices D).2.1 r p hp
    obtain ⟨hnq,hfq⟩ := (proposition20_eigenmatrices D).2.1 r q hq
    obtain ⟨t,ht⟩ := fine_sector_unit_vectors_phase D r _ _ hnp hnq
      (by simpa using hfp r) (by simpa using hfq r)
    exact ⟨t,fun h => False.elim (he h),ht⟩
