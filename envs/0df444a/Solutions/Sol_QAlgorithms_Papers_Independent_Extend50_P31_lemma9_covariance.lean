-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.lemma9_covariance
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:05:56.411552+00:00
-- url     : https://prove2.me/submissions/f734e179-ea8b-4fae-977b-cc9c5b424eba

import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_row_representative_calculus
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

/-- PDF pp.8--9, Lemma 9 Eq.(32), Appendix A p.34. No CP or MF premise. -/
theorem solution (hG : Finite G) (U : UnitaryIrrep G n) (Phi : EndMat n) :
    IsIrrepCovariant U Phi ↔ rowMatrixRepresentative Phi ∈ representationCommutant (tensorConjugate U) := by
  obtain ⟨ha,hcomp,hsand⟩ := row_representative_calculus n
  have hinj : Function.Injective (rowMatrixRepresentative (n := n)) := by
    intro P Q hPQ
    apply LinearMap.ext
    intro X
    apply (rowVec (d := n) (e := n)).injective
    rw [ha P X, ha Q X, hPQ]
  have hC (g : G) : rowMatrixRepresentative (conjugationMap U g) = tensorConjugate U g := by
    change rowMatrixRepresentative (sandwich (U.rho g) (U.rho g)ᴴ) = _
    rw [hsand]
    rfl
  change (∀ g X, Phi (conjugationMap U g X) = conjugationMap U g (Phi X)) ↔
    ∀ g, rowMatrixRepresentative Phi * tensorConjugate U g =
      tensorConjugate U g * rowMatrixRepresentative Phi
  constructor
  · intro h g
    have hh : Phi.comp (conjugationMap U g) = (conjugationMap U g).comp Phi := by
      apply LinearMap.ext
      intro X
      exact h g X
    have hm := congrArg rowMatrixRepresentative hh
    simpa only [hcomp, hC] using hm
  · intro h g X
    have hh : Phi.comp (conjugationMap U g) = (conjugationMap U g).comp Phi := by
      apply hinj
      rw [hcomp, hcomp, hC]
      exact h g
    exact congrArg (fun P : EndMat n => P X) hh
