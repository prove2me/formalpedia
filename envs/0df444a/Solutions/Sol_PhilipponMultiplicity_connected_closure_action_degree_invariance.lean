-- Prove2me | solution 1 for PhilipponMultiplicity.connected_closure_action_degree_invariance
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T22:41:25.550507+00:00
-- url     : https://prove2.me/submissions/215eb756-ec34-4ea3-a7f0-b515ba7e6260
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_connected_group_points_nsmul_surjective
import Theorems.Thm_PhilipponMultiplicity_closure_action_has_degree_controlling_lattice
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree


set_option autoImplicit false

namespace PhilipponMultiplicity.DivisibleLattice

/-- Every homomorphism from a group with surjective positive power maps to a
finite group is trivial. -/
theorem finite_hom_eq_one {Γ H : Type*} [Group Γ] [Group H] [Finite H]
    (hdiv : ∀ n : ℕ, 0 < n → Function.Surjective (fun g : Γ => g ^ n))
    (f : Γ →* H) (g : Γ) : f g = 1 := by
  obtain ⟨x, hx⟩ := hdiv (Nat.card H) Nat.card_pos g
  rw [← hx, map_pow]
  exact pow_card_eq_one'

/-- Agreement modulo every positive integer detects equality in the integers. -/
theorem int_eq_of_all_positive_zmod {a b : ℤ}
    (h : ∀ n : ℕ, 0 < n → (a : ZMod n) = (b : ZMod n)) : a = b := by
  have hd : ((b-a).natAbs+1 : ℕ) ∣ (b-a).natAbs := by
    have hi := (ZMod.intCast_eq_intCast_iff_dvd_sub a b ((b-a).natAbs+1)).mp
      (h _ (Nat.zero_lt_succ _))
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr hi
  have hz : (b-a).natAbs = 0 :=
    Nat.eq_zero_of_dvd_of_lt hd (Nat.lt_succ_self _)
  exact (sub_eq_zero.mp (Int.natAbs_eq_zero.mp hz)).symm

/-- A divisible group has no nontrivial integral matrix representation of finite
rank: reduce modulo each positive integer and use the finite-group result. -/
theorem int_matrix_hom_eq_one {Γ : Type*} [Group Γ]
    (hdiv : ∀ n : ℕ, 0 < n → Function.Surjective (fun g : Γ => g ^ n))
    (r : ℕ) (ρ : Γ →* Matrix.GeneralLinearGroup (Fin r) ℤ) (g : Γ) :
    ρ g = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply int_eq_of_all_positive_zmod
  intro n hn
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let f : Γ →* Matrix.GeneralLinearGroup (Fin r) (ZMod n) :=
    (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod n))).comp ρ
  have hf : f g = 1 := finite_hom_eq_one hdiv f g
  have hij := congrArg (fun A : Matrix.GeneralLinearGroup (Fin r) (ZMod n) =>
    (A : Matrix (Fin r) (Fin r) (ZMod n)) i j) hf
  simpa [f, Matrix.one_apply] using hij

/-- Additive form used for the point group of a commutative algebraic group. -/
theorem additive_int_matrix_hom_eq_one {A : Type*} [AddGroup A]
    (hdiv : ∀ n : ℕ, 0 < n → Function.Surjective (fun g : A => n • g))
    (r : ℕ) (ρ : Multiplicative A →* Matrix.GeneralLinearGroup (Fin r) ℤ)
    (g : A) : ρ (Multiplicative.ofAdd g) = 1 := by
  apply int_matrix_hom_eq_one (r := r)
  intro n hn x
  obtain ⟨y, hy⟩ := hdiv n hn x.toAdd
  exact ⟨Multiplicative.ofAdd y, congrArg Multiplicative.ofAdd hy⟩

end PhilipponMultiplicity.DivisibleLattice


set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

/-- Divisibility kills the lattice action, and its kernel preserves every degree. -/
theorem degree_invariance_of_divisibility_and_lattice
    (K : Type*) [NontriviallyNormedField K]
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hdiv : ∀ n : ℕ, 0 < n → Function.Surjective (fun g : G.Point => n • g))
    (hlattice : ∃ (r : ℕ) (ρ : Multiplicative G.Point →*
        Matrix.GeneralLinearGroup (Fin r) ℤ),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
      ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
        ρ (Multiplicative.ofAdd g) = 1 →
        SectionThree.locusDegreeValue G.ambient (Subtype.val '' V) D =
      SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D)
    (V : Set (groupProjectiveClosure G))
    (hV : @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V)
    (g : G.Point) (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    SectionThree.locusDegreeValue G.ambient (Subtype.val '' V) D =
      SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D := by
  obtain ⟨r,ρ,hρ⟩ := hlattice
  exact hρ V hV g D hD (DivisibleLattice.additive_int_matrix_hom_eq_one hdiv r ρ g)

end PhilipponMultiplicity

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (hconnected : @_root_.IsConnected _ G.zariskiTopology Set.univ)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (hrestrict : ∀ (g : G.Point) (x : groupProjectiveClosure G) (y : G.Point),
      x.val = G.embedding y → (τ g x).val = G.embedding (g+y))
    (V : Set (groupProjectiveClosure G))
    (hV : @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V)
    (g : G.Point) (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    SectionThree.locusDegreeValue G.ambient (Subtype.val '' V) D =
      SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D := by
  exact degree_invariance_of_divisibility_and_lattice K G τ
    (connected_group_points_nsmul_surjective K hK G hconnected)
    (closure_action_has_degree_controlling_lattice K hK G τ hzero hadd hregular)
    V hV g D hD
