-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.corollary14_absent
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:40:46.487287+00:00
-- url     : https://prove2.me/submissions/bdf211e2-4d76-4384-86be-5b8e7feba214

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_central_projector_irrep_action
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_trivial_irrep_occurs
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31 QAlgorithms.Papers.Independent.Information100.P44
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
private lemma central_coordinates (D : Data G A n)
    (T : ((Fin n × Fin n) → ℂ) ≃ₗ[ℂ] ((b : OccurringIrrep D) → Fin (D.F.dim b.val) → ℂ))
    (hT : ∀ g v b, T ((tensorConjugate D.U g).mulVec v) b =
      ((D.F.irrep b.val).rho g).mulVec (T v b)) (a : A) (v : (Fin n × Fin n) → ℂ)
    (b : OccurringIrrep D) :
    T ((centralMatrix D.U D.F a).mulVec v) b =
      if a = b.val then T v b else 0 := by
  have h := congrArg (fun M : Mat (D.F.dim b.val) => M.mulVec (T v b))
    (central_projector_irrep_action D.F a b.val)
  simp only [centralMatrix, Matrix.smul_mulVec, Matrix.sum_mulVec,
    map_smul, map_sum, Finset.sum_apply, Pi.smul_apply, hT]
  split_ifs at h ⊢ <;> simpa only [Matrix.smul_mulVec, Matrix.sum_mulVec, Matrix.one_mulVec,
    Matrix.zero_mulVec] using h

private lemma absent_central (D : Data G A n) (a : A) (ha : a ∉ D.theta) : centralMatrix D.U D.F a = 0 := by
  obtain ⟨T,hT⟩ := D.decomposition
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  apply T.injective
  funext b
  rw [Matrix.toLin'_apply,central_coordinates D T hT,Matrix.toLin'_apply,Matrix.zero_mulVec,map_zero]
  simp only [Pi.zero_apply,ite_eq_right_iff]
  intro he
  exact False.elim (ha (he ▸ b.property))

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

/-- PDF p.11, Corollary 14 Eq.(51), including all absent labels. -/
theorem solution (D : Data G A n) :
    D.F.trivial ∈ D.theta ∧
    ∀ a : A, a ∉ D.theta → centralMatrix D.U D.F a = 0 := by
  exact ⟨trivial_irrep_occurs D, fun a ha => absent_central D a ha⟩
