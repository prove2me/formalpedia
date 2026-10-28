-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P22.closedProduct_stabilization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:26:34.041201+00:00
-- url     : https://prove2.me/submissions/ad6d0da4-e050-4b73-ae5b-7863dc06bb0e

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P22
noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P22

open scoped BigOperators Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

lemma S170A_sub_closure {n : ℕ} {K : Type*} [Field K] (S : Set (GeometricGL n K)) :
    S ⊆ zariskiClosure S := by
  intro a ha p hp
  have hp' := (MvPolynomial.mem_vanishingIdeal_iff).1 hp _ ⟨a, ha, rfl⟩
  have e : algebraMap K K = RingHom.id K := rfl
  show MvPolynomial.eval₂ (algebraMap K K) _ p = 0
  rw [e]; exact hp'

end QAlgorithms.Papers.Independent.Renew46.P22

open QAlgorithms.Papers.Independent.Renew46.P22
open scoped Pointwise

variable {F K : Type*} [Field F] [hchar : CharZero F] [Field K] [Algebra F K] [hclosure : IsAlgClosure F K]

variable {n : ℕ}

include hchar hclosure in
theorem solution (G1 G2 : Subgroup (GeometricGL n K))
    (hG1 : IsAlgebraicGroup G1) (hG2 : IsAlgebraicGroup G2)
    (hc1 : IsZariskiConnected (G1 : Set (GeometricGL n K)))
    (hc2 : IsZariskiConnected (G2 : Set (GeometricGL n K)))
    (A : Set (GeometricGL n K))
    (hA : A ⊆ (G1 ⊔ G2 : Subgroup (GeometricGL n K))) (h1 : 1 ∈ A)
    (hprod1 : zariskiClosure (A * (G1 : Set (GeometricGL n K))) = A)
    (hprod2 : zariskiClosure (A * (G2 : Set (GeometricGL n K))) = A) :
    A = (G1 ⊔ G2 : Subgroup (GeometricGL n K)) := by
  have m1 : ∀ a ∈ A, ∀ g ∈ G1, a * g ∈ A := fun a ha g hg => by
    rw [← hprod1]; exact S170A_sub_closure _ (Set.mul_mem_mul ha hg)
  have m2 : ∀ a ∈ A, ∀ g ∈ G2, a * g ∈ A := fun a ha g hg => by
    rw [← hprod2]; exact S170A_sub_closure _ (Set.mul_mem_mul ha hg)
  have key : ∀ x ∈ (G1 ⊔ G2 : Subgroup (GeometricGL n K)), ∀ a ∈ A, a * x ∈ A := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction'' with
    | mem x hx =>
      rcases hx with hx | hx
      · exact fun a ha => m1 a ha x hx
      · exact fun a ha => m2 a ha x hx
    | inv_mem x hx =>
      rcases hx with hx | hx
      · exact fun a ha => m1 a ha _ (G1.inv_mem hx)
      · exact fun a ha => m2 a ha _ (G2.inv_mem hx)
    | one => intro a ha; simpa using ha
    | mul x y _ _ ihx ihy =>
      intro a ha; rw [← mul_assoc]; exact ihy _ (ihx a ha)
  refine Set.Subset.antisymm hA fun x hx => ?_
  simpa using key x hx 1 h1

end
