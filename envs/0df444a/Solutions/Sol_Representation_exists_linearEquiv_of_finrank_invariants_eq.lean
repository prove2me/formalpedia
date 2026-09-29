-- Prove2me | solution 1 for Representation.exists_linearEquiv_of_finrank_invariants_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ccc2d1ab-c56e-5efc-bf63-33fa57095f52

import Mathlib
import Theorems.Thm_Nat_eq_of_forall_dvd_sum_divisors_eq
import Theorems.Thm_Polynomial_finrank_torsionBy_X_pow_sub_one_eq_sum_finrank_torsionBy_cyclotomic
import Theorems.Thm_Polynomial_nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_exists_linearEquiv_of_finrank_invariants_eq

set_option autoImplicit false
universe u v
open Polynomial Module
open scoped DirectSum
set_option maxHeartbeats 4000000

noncomputable section

namespace P2mS26W3ib

theorem isTorsionBy_of_X_smul {G : Type u} {U : Type v} [Group G] [Fintype G] [AddCommGroup U] [Module ℚ U]
    [Module ℚ[X] U] (π : Representation ℚ G U) (g : G) (hX : ∀ v : U, (X : ℚ[X]) • v = π g v) :
    Module.IsTorsionBy ℚ[X] U ((X : ℚ[X]) ^ Fintype.card G - 1) := by
  have hpow : ∀ (k : ℕ) (v : U), ((X : ℚ[X]) ^ k) • v = (π g ^ k) v := by
    intro k
    induction k with
    | zero => intro v; rw [pow_zero, one_smul, pow_zero, Module.End.one_apply]
    | succ k ih => intro v; rw [pow_succ', mul_smul, hX, ih, pow_succ', Module.End.mul_apply]
  intro v
  have hgn : π g ^ Fintype.card G = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
  show ((X : ℚ[X]) ^ Fintype.card G - 1) • v = 0
  rw [sub_smul, one_smul, hpow, hgn, Module.End.one_apply, sub_self]

theorem finrank_torsionBy_eq_finrank_invariants {G : Type u} {U : Type v} [Group G] [Fintype G]
    [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U] [Module ℚ[X] U] [IsScalarTower ℚ ℚ[X] U]
    (π : Representation ℚ G U) (g : G) (hX : ∀ v : U, (X : ℚ[X]) • v = π g v) (e : ℕ) :
    Module.finrank ℚ (Submodule.torsionBy ℚ[X] U ((X : ℚ[X]) ^ e - 1)) =
      Module.finrank ℚ (Representation.invariants (π.comp (Subgroup.zpowers (g ^ e)).subtype)) := by
  classical
  have hpow : ∀ (k : ℕ) (v : U), ((X : ℚ[X]) ^ k) • v = (π g ^ k) v := by
    intro k
    induction k with
    | zero => intro v; rw [pow_zero, one_smul, pow_zero, Module.End.one_apply]
    | succ k ih => intro v; rw [pow_succ', mul_smul, hX, ih, pow_succ', Module.End.mul_apply]

  have hinv : ∀ v : U, v ∈ Representation.invariants (π.comp (Subgroup.zpowers (g ^ e)).subtype) ↔ π (g ^ e) v = v := by
    intro v
    rw [Representation.mem_invariants]
    constructor
    · intro hv
      exact hv ⟨g ^ e, Subgroup.mem_zpowers _⟩
    · intro hv s
      let S : Subgroup G :=
        { carrier := {s | π s v = v}
          one_mem' := by show π 1 v = v; rw [map_one, Module.End.one_apply]
          mul_mem' := fun {a b} ha hb => by
            show π (a * b) v = v
            rw [map_mul, Module.End.mul_apply, (hb : π b v = v), (ha : π a v = v)]
          inv_mem' := fun {a} ha => by
            show π a⁻¹ v = v
            have h := congrArg (π a⁻¹) (ha : π a v = v)
            rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, eq_comm] at h }
      have hle : Subgroup.zpowers (g ^ e) ≤ S := (Subgroup.zpowers_le (G := G)).2 hv
      exact hle s.2

  have hmem : ∀ v : U, v ∈ Submodule.torsionBy ℚ[X] U ((X : ℚ[X]) ^ e - 1) ↔
      v ∈ Representation.invariants (π.comp (Subgroup.zpowers (g ^ e)).subtype) := by
    intro v
    rw [hinv, Submodule.mem_torsionBy_iff, sub_smul, one_smul, hpow, sub_eq_zero, map_pow]

  let f : Submodule.torsionBy ℚ[X] U ((X : ℚ[X]) ^ e - 1) ≃ₗ[ℚ] Representation.invariants (π.comp (Subgroup.zpowers (g ^ e)).subtype) :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact f.finrank_eq

end P2mS26W3ib

theorem solution {G V W : Type*} [Group G] [Fintype G] [IsCyclic G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ G V) (τ : Representation ℚ G W)
    (h : ∀ H : Subgroup G, Module.finrank ℚ (Representation.invariants (ρ.comp H.subtype)) =
      Module.finrank ℚ (Representation.invariants (τ.comp H.subtype))) :
    ∃ e : V ≃ₗ[ℚ] W, ∀ (g : G) (v : V), e (ρ g v) = τ g (e v) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hnpos : 0 < Fintype.card G := Fintype.card_pos

  letI : Module ℚ[X] V := Module.compHom V (Polynomial.aeval (ρ g)).toRingHom
  letI : Module ℚ[X] W := Module.compHom W (Polynomial.aeval (τ g)).toRingHom
  have hsmulV : ∀ (p : ℚ[X]) (v : V), p • v = Polynomial.aeval (ρ g) p v := fun _ _ => rfl
  have hsmulW : ∀ (p : ℚ[X]) (w : W), p • w = Polynomial.aeval (τ g) p w := fun _ _ => rfl
  haveI : IsScalarTower ℚ ℚ[X] V := ⟨fun c p v => by
    rw [hsmulV, hsmulV, map_smul, LinearMap.smul_apply]⟩
  haveI : IsScalarTower ℚ ℚ[X] W := ⟨fun c p w => by
    rw [hsmulW, hsmulW, map_smul, LinearMap.smul_apply]⟩
  have hXV : ∀ v : V, (X : ℚ[X]) • v = ρ g v := fun v => by rw [hsmulV, Polynomial.aeval_X]
  have hXW : ∀ w : W, (X : ℚ[X]) • w = τ g w := fun w => by rw [hsmulW, Polynomial.aeval_X]

  have hD : ∀ d, d ∣ Fintype.card G →
      Module.finrank ℚ (Submodule.torsionBy ℚ[X] V (cyclotomic d ℚ)) =
        Module.finrank ℚ (Submodule.torsionBy ℚ[X] W (cyclotomic d ℚ)) := by
    refine Nat.eq_of_forall_dvd_sum_divisors_eq hnpos _ _ fun e he => ?_
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hnpos
    rw [← Polynomial.finrank_torsionBy_X_pow_sub_one_eq_sum_finrank_torsionBy_cyclotomic (M := V) hepos,
      ← Polynomial.finrank_torsionBy_X_pow_sub_one_eq_sum_finrank_torsionBy_cyclotomic (M := W) hepos,
      P2mS26W3ib.finrank_torsionBy_eq_finrank_invariants ρ g hXV e, P2mS26W3ib.finrank_torsionBy_eq_finrank_invariants τ g hXW e]
    exact h _

  obtain ⟨E⟩ := Polynomial.nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq hnpos
    (P2mS26W3ib.isTorsionBy_of_X_smul ρ g hXV) (P2mS26W3ib.isTorsionBy_of_X_smul τ g hXW) hD
  have heg : ∀ v : V, E (ρ g v) = τ g (E v) := fun v => by rw [← hXV, E.map_smul, hXW]
  refine ⟨E.restrictScalars ℚ, fun x v => ?_⟩
  show E (ρ x v) = τ x (E v)

  obtain ⟨k, rfl⟩ : ∃ k : ℕ, g ^ k = x := (mem_powers_iff_mem_zpowers (x := g) (y := x)).2 (hg x)
  induction k generalizing v with
  | zero => simp
  | succ k ih => rw [pow_succ, map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply, ih, heg]

end

end S_Representation_exists_linearEquiv_of_finrank_invariants_eq
end P2MW
export P2MW.S_Representation_exists_linearEquiv_of_finrank_invariants_eq (solution)
