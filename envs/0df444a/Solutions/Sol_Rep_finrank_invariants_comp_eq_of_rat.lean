-- Prove2me | solution 1 for Rep.finrank_invariants_comp_eq_of_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/dbd48557-7acc-5ff4-b97e-20f0324327c6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_finrank_invariants_comp_eq_of_rat

set_option autoImplicit false

namespace P2mS26R

section generic
variable {k G : Type} [CommRing k] [Group G]

def invAddSubgroup (X : Rep k G) : AddSubgroup X where
  carrier := {x | ∀ g : G, X.ρ g x = x}
  zero_mem' g := map_zero _
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g]
  neg_mem' {x} hx g := by rw [map_neg, hx g]

lemma mem_invAddSubgroup_iff (X : Rep k G) (x : X) : x ∈ invAddSubgroup X ↔ ∀ g : G, X.ρ g x = x := Iff.rfl

noncomputable def gcZeroAddEquiv (X : Rep k G) : groupCohomology X 0 ≃+ invAddSubgroup X :=
  (groupCohomology.H0Iso X).toLinearEquiv.toAddEquiv.trans
    { toFun := fun x => ⟨x.1, fun g => (X.ρ.mem_invariants x.1).1 x.2 g⟩
      invFun := fun y => ⟨y.1, (X.ρ.mem_invariants y.1).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

end generic

lemma finrank_int_eq (A : Type) [AddCommGroup A] (i₁ i₂ : Module ℤ A) :
    @Module.finrank ℤ A _ _ i₁ = @Module.finrank ℤ A _ _ i₂ := by
  rw [Subsingleton.elim i₁ i₂]

lemma exists_int_smul_eq {L V : Type} [AddCommGroup L] [AddCommGroup V] [Module ℚ V] (i : L →+ V)
    {v : V} (hv : v ∈ Submodule.span ℚ (Set.range i)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ x : L, (n : ℚ) • v = i x := by
  induction hv using Submodule.span_induction with
  | mem v h =>
    obtain ⟨x, rfl⟩ := h
    exact ⟨1, one_ne_zero, x, by rw [Int.cast_one, one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, 0, by rw [smul_zero, map_zero]⟩
  | add v w _ _ hv hw =>
    obtain ⟨n, hn, x, hx⟩ := hv
    obtain ⟨m, hm, y, hy⟩ := hw
    refine ⟨n * m, mul_ne_zero hn hm, m • x + n • y, ?_⟩
    rw [map_add, map_zsmul, map_zsmul, ← hx, ← hy, Int.cast_mul, smul_add, ← Int.cast_smul_eq_zsmul ℚ m,
      ← Int.cast_smul_eq_zsmul ℚ n, smul_smul, smul_smul, mul_comm (m : ℚ) n]
  | smul c v _ hv =>
    obtain ⟨n, hn, x, hx⟩ := hv
    refine ⟨n * c.den, mul_ne_zero hn (Int.natCast_ne_zero.2 (Nat.pos_iff_ne_zero.1 c.den_pos)), c.num • x, ?_⟩
    rw [map_zsmul, ← hx, ← Int.cast_smul_eq_zsmul ℚ c.num, smul_smul, smul_smul, Int.cast_mul, Int.cast_natCast,
      mul_assoc, Rat.den_mul_eq_num, mul_comm (n : ℚ) (c.num : ℚ)]

end P2mS26R

theorem solution {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (τ : Representation ℚ G V)
    {L : Rep ℤ G} [Module.Finite ℤ L] [Module.Free ℤ L]
    (i : L →+ V) (hi : Function.Injective i) (hiG : ∀ (g : G) (x : L), i (L.ρ g x) = τ g (i x))
    (hfull : Submodule.span ℚ (Set.range i) = ⊤) (H : Subgroup G) :
    Module.finrank ℚ (Representation.invariants (τ.comp H.subtype)) =
      Module.finrank ℤ (groupCohomology (Rep.res H.subtype L) 0) := by
  classical

  let M : AddSubgroup L := P2mS26R.invAddSubgroup (Rep.res H.subtype L)
  let N : Submodule ℤ L := M.toIntSubmodule

  obtain ⟨n, ⟨b⟩⟩ := Submodule.nonempty_basis_of_pid (Module.Free.chooseBasis ℤ L) N
  have hn : Module.finrank ℤ N = n := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

  have h0 : Module.finrank ℤ (groupCohomology (Rep.res H.subtype L) 0) = Module.finrank ℤ N := by
    have e : groupCohomology (Rep.res H.subtype L) 0 ≃+ N := P2mS26R.gcZeroAddEquiv (Rep.res H.subtype L)
    exact (P2mS26R.finrank_int_eq _ _ _).trans (e.toIntLinearEquiv.finrank_eq.trans (P2mS26R.finrank_int_eq _ _ _))

  let j : N →ₗ[ℤ] V := i.toIntLinearMap ∘ₗ N.subtype
  have hj : Function.Injective j := fun x y h => Subtype.val_injective (hi h)
  have hliZ : LinearIndependent ℤ (j ∘ b) := b.linearIndependent.map' j (LinearMap.ker_eq_bot.2 hj)
  have hliQ : LinearIndependent ℚ (j ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hliZ

  have hspan : Submodule.span ℚ (Set.range (j ∘ b)) = Submodule.span ℚ (Set.range j) := by
    apply le_antisymm (Submodule.span_mono (Set.range_comp_subset_range b j))
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    rw [← b.sum_repr m, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hrank : Module.finrank ℚ (Submodule.span ℚ (Set.range j)) = n := by
    rw [← hspan, finrank_span_eq_card hliQ, Fintype.card_fin]

  have hW : Representation.invariants (τ.comp H.subtype) = Submodule.span ℚ (Set.range j) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨c, hc, x, hx⟩ := P2mS26R.exists_int_smul_eq i (hfull ▸ Submodule.mem_top : v ∈ Submodule.span ℚ (Set.range i))
      have hxM : x ∈ N := by
        intro h
        apply hi
        have hvh : τ (h : G) v = v := (Representation.mem_invariants _ _).1 hv h
        change i (L.ρ (h : G) x) = i x
        rw [hiG, ← hx, map_smul, hvh]
      have : v = (c : ℚ)⁻¹ • j ⟨x, hxM⟩ := by
        change v = (c : ℚ)⁻¹ • i x
        rw [← hx, inv_smul_smul₀ (Int.cast_ne_zero.2 hc)]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hxM⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      refine (Representation.mem_invariants _ _).2 fun h => ?_
      change τ (h : G) (i m.1) = i m.1
      rw [← hiG]
      exact congrArg i (m.2 h)
  rw [hW, hrank, h0, hn]

end S_Rep_finrank_invariants_comp_eq_of_rat
end P2MW
export P2MW.S_Rep_finrank_invariants_comp_eq_of_rat (solution)
