-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P86.basedRingAntiAutomorphism_unique_factorization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T03:53:36.568765+00:00
-- url     : https://prove2.me/submissions/2ec1b1d8-6148-46ab-8dba-37d8b4775b2d

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P86

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Intake100.P86 in
theorem solution
    {A I : Type*} [Ring A] (H : IntegralHypergroup A I)
    (f : BasedRingAntiAutomorphism H) :
    ∃! g : BasedRingAutomorphism H,
      ∀ a : A, f.equiv a = barredAutomorphism H g a := by
  let e : A ≃+* A :=
    { toFun := fun a => H.bar (f.equiv a)
      invFun := fun a => f.equiv.symm (H.bar a)
      left_inv := fun a => by
        show f.equiv.symm (H.bar (H.bar (f.equiv a))) = a
        rw [H.bar_involutive, AddEquiv.symm_apply_apply]
      right_inv := fun a => by
        show H.bar (f.equiv (f.equiv.symm (H.bar a))) = a
        rw [AddEquiv.apply_symm_apply, H.bar_involutive]
      map_mul' := fun x y => by
        show H.bar (f.equiv (x * y)) = H.bar (f.equiv x) * H.bar (f.equiv y)
        rw [f.map_mul, H.bar_mul]
      map_add' := fun x y => by
        show H.bar (f.equiv (x + y)) = H.bar (f.equiv x) + H.bar (f.equiv y)
        rw [map_add, map_add] }
  have hbarrange : Set.range (fun i => H.bar (H.basis i)) = Set.range H.basis := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := H.bar_basis i
      exact ⟨j, hj.symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := H.bar_basis j
      exact ⟨k, by show H.bar (H.basis k) = H.basis j; rw [← hk, H.bar_involutive]⟩
  have hrange : Set.range (fun i => e (H.basis i)) = Set.range H.basis := by
    show Set.range (fun i => H.bar (f.equiv (H.basis i))) = _
    rw [show (fun i => H.bar (f.equiv (H.basis i))) = H.bar ∘ (fun i => f.equiv (H.basis i))
      from rfl, Set.range_comp, f.basis_image, ← Set.range_comp]
    exact hbarrange
  refine ⟨⟨e, hrange⟩, fun a => ?_, fun g' hg' => ?_⟩
  · show f.equiv a = H.bar (H.bar (f.equiv a))
    rw [H.bar_involutive]
  · obtain ⟨eq', bi'⟩ := g'
    have h : ∀ a, eq' a = e a := by
      intro a
      show eq' a = H.bar (f.equiv a)
      rw [hg' a]
      show eq' a = H.bar (H.bar (eq' a))
      rw [H.bar_involutive]
    have : eq' = e := RingEquiv.ext h
    subst this
    rfl
