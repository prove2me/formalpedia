-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.isUnit_eq_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:09.360064+00:00
-- url     : https://prove2.me/submissions/89444b53-149d-4c1e-9e73-8dc775476ea0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution {R A : Type*} [CommRing R] [IsDomain R] [AddCommMonoid A] [TwoUniqueSums A]
    {u : AddMonoidAlgebra R A} (hu : IsUnit u) : ∃ a c, IsUnit c ∧ u = single a c := by
  obtain ⟨v, huv⟩ := hu.exists_right_inv
  have coeffInj : ∀ p q : AddMonoidAlgebra R A, p.coeff = q.coeff → p = q := by
    intro p q hpq
    first
    | exact AddMonoidAlgebra.coeff_injective hpq
    | exact AddMonoidAlgebra.coeff_inj.1 hpq
    | exact AddMonoidAlgebra.ext hpq
    | (cases p; cases q; simp_all)
  have key : ∀ a0 b0 : A, UniqueAdd u.coeff.support v.coeff.support a0 b0 →
      (u * v).coeff (a0 + b0) = u.coeff a0 * v.coeff b0 := by
    intro a0 b0 h
    first
    | exact AddMonoidAlgebra.coeff_mul_apply_add_eq_mul_of_uniqueAdd h
    | exact AddMonoidAlgebra.mul_coeff_add_eq_mul_of_uniqueAdd h
    | exact AddMonoidAlgebra.coeff_mul_of_uniqueAdd h
    | exact AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd h
    | exact Finsupp.mul_apply_add_eq_mul_of_uniqueAdd h
  have hone : (u * v).coeff = Finsupp.single 0 1 := by
    rw [huv]
    first
    | (simp [AddMonoidAlgebra.one_def]; done)
    | exact AddMonoidAlgebra.coeff_one
    | rfl
  have hcard : u.coeff.support.card * v.coeff.support.card ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨p1, hp1, p2, hp2, hne, hu1, hu2⟩ := TwoUniqueSums.uniqueAdd_of_one_lt_card hlt
    rw [Finset.mem_product] at hp1 hp2
    have n1 : u.coeff p1.1 * v.coeff p1.2 ≠ 0 :=
      mul_ne_zero (Finsupp.mem_support_iff.1 hp1.1) (Finsupp.mem_support_iff.1 hp1.2)
    have n2 : u.coeff p2.1 * v.coeff p2.2 ≠ 0 :=
      mul_ne_zero (Finsupp.mem_support_iff.1 hp2.1) (Finsupp.mem_support_iff.1 hp2.2)
    have e1 := key _ _ hu1
    have e2 := key _ _ hu2
    rw [hone] at e1 e2
    have s1 : p1.1 + p1.2 = 0 := by
      by_contra hs
      exact n1 (by simpa [Finsupp.single_apply, Ne.symm hs] using e1.symm)
    have s2 : p2.1 + p2.2 = 0 := by
      by_contra hs
      exact n2 (by simpa [Finsupp.single_apply, Ne.symm hs] using e2.symm)
    obtain ⟨q1, q2⟩ := hu1 hp2.1 hp2.2 (s2.trans s1.symm)
    exact hne (Prod.ext q1.symm q2.symm)
  have nz : ∀ p : AddMonoidAlgebra R A, p * v = 1 ∨ u * p = 1 → p.coeff ≠ 0 := by
    intro p hp h0
    have hp0 : p = 0 := coeffInj p 0 (by simpa using h0)
    rcases hp with hp | hp <;> rw [hp0] at hp <;> simp at hp
  have hprod : u.coeff.support.card * v.coeff.support.card = 1 :=
    le_antisymm hcard (Nat.mul_pos (Finsupp.support_nonempty_iff.2 (nz u (Or.inl huv))).card_pos
      (Finsupp.support_nonempty_iff.2 (nz v (Or.inr huv))).card_pos)
  have cu : u.coeff.support.card = 1 := by
    first
    | exact Nat.eq_one_of_mul_eq_one_right hprod
    | exact (mul_eq_one.1 hprod).1
    | nlinarith
  have cv : v.coeff.support.card = 1 := by
    first
    | exact Nat.eq_one_of_mul_eq_one_left hprod
    | exact (mul_eq_one.1 hprod).2
    | nlinarith
  obtain ⟨a, hc0, hca⟩ := Finsupp.card_support_eq_one.1 cu
  obtain ⟨b, hd0, hdb⟩ := Finsupp.card_support_eq_one.1 cv
  have hu' : u = single a (u.coeff a) := coeffInj _ _ (by simpa using hca)
  have hv' : v = single b (v.coeff b) := coeffInj _ _ (by simpa using hdb)
  rw [hu', hv', single_mul_single] at huv
  have hcd : u.coeff a * v.coeff b = 1 := by
    have h3 := congrArg AddMonoidAlgebra.coeff huv
    simp only [AddMonoidAlgebra.one_def] at h3
    have h4 : Finsupp.single (a + b) (u.coeff a * v.coeff b) = Finsupp.single 0 1 := by
      simpa using h3
    rcases (Finsupp.single_eq_single_iff _ _ _ _).1 h4 with h5 | h5
    · exact h5.2
    · exact absurd h5.2 one_ne_zero
  have hcu : IsUnit (u.coeff a) := by
    first
    | exact isUnit_of_mul_eq_one _ _ hcd
    | exact IsUnit.of_mul_eq_one _ hcd
  exact ⟨a, u.coeff a, hcu, hu'⟩
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
