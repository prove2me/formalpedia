-- Prove2me | solution 1 for WeierstrassCurve.exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2d8c82f7-7a83-5b81-be9d-b4d10708df54

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_WeierstrassCurve_Affine_Point_exists_addEquiv_nodeNormalForm_additive_units
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare

set_option maxHeartbeats 12800000
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (n : ℕ) [NeZero n]
    (hnsq : ¬ IsSquare c) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    let W : WeierstrassCurve K := ⟨0, c, 0, 0, 0⟩
    ∃ (δ : AlgebraicClosure K), δ * δ = algebraMap K (AlgebraicClosure K) c ∧
      ∃ et : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n
          ≃ rootsOfUnity n (AlgebraicClosure K),
        (∀ P Q, et (P + Q) = et P * et Q) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (P : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n),
          (σ δ = δ →
            ((et (σ • P) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
            = σ ((et P : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∧
          (σ δ = -δ →
            ((et (σ • P) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
            * σ ((et P : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 1) := by
  letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  set W : WeierstrassCurve K := ⟨0, c, 0, 0, 0⟩ with hWdef

  have hcbar : algebraMap K (AlgebraicClosure K) c ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).mpr hc
  obtain ⟨δ, hδsq⟩ : ∃ δ : AlgebraicClosure K, δ * δ = algebraMap K (AlgebraicClosure K) c := by
    obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap K (AlgebraicClosure K) c) (n := 2) two_pos
    exact ⟨δ, by rw [← sq]; exact hδ⟩
  have hδne : δ ≠ 0 := fun h => hcbar (by rw [← hδsq, h, mul_zero])
  refine ⟨δ, hδsq, ?_⟩

  have hσδ_cases : ∀ σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K), σ δ = δ ∨ σ δ = -δ := by
    intro σ
    have hsq : (σ δ)^2 = δ^2 := by
      rw [← map_pow σ δ 2, sq, hδsq, σ.commutes c, ← hδsq, ← sq]
    have hprod : (σ δ - δ) * (σ δ + δ) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)

  have hW : (W⁄(AlgebraicClosure K))
      = (⟨0, δ * δ, 0, 0, 0⟩ : WeierstrassCurve (AlgebraicClosure K)).toAffine := by
    rw [hWdef]; ext
    · exact _root_.map_zero _
    · show algebraMap K (AlgebraicClosure K) c = δ * δ; exact hδsq.symm
    · exact _root_.map_zero _
    · exact _root_.map_zero _
    · exact _root_.map_zero _

  obtain ⟨e₀, he₀⟩ : ∃ e₀ : (W⁄(AlgebraicClosure K)).Point ≃+ Additive (AlgebraicClosure K)ˣ,
      ∀ x y h, ((Additive.toMul (e₀ (.some x y h)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
        * (y + δ * x) = y - δ * x := by
    rw [hW]; exact exists_addEquiv_nodeNormalForm_additive_units δ hδne

  have hypdx : ∀ x y, (W⁄(AlgebraicClosure K)).Nonsingular x y → y + δ * x ≠ 0 := by
    intro x y h habs
    have hh := he₀ x y h; rw [habs, mul_zero] at hh
    have hy0 : y = 0 := by linear_combination (1/2:AlgebraicClosure K)*habs - (1/2)*hh
    have hx0 : x = 0 := by
      have := habs; rw [hy0, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_left hδne
    subst hy0; subst hx0
    rw [hW, WeierstrassCurve.Affine.nonsingular_iff'] at h
    exact h.2.elim (fun h1 => h1 (by ring)) (fun h2 => h2 (by ring))
  have hymdx : ∀ x y, (W⁄(AlgebraicClosure K)).Nonsingular x y → y - δ * x ≠ 0 := by
    intro x y h habs
    have hh := he₀ x y h; rw [habs] at hh
    exact hypdx x y h ((mul_eq_zero.mp hh).resolve_left (Units.ne_zero _))

  have he₀_gal_eq : ∀ (σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K))
      (P : (W⁄(AlgebraicClosure K)).Point), σ δ = δ →
      ((Additive.toMul (e₀ (σ • P)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
      = σ ((Additive.toMul (e₀ P) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := by
    intro σ P hσδ
    rcases P with _ | ⟨x, y, h⟩
    · show ((Additive.toMul (e₀ (Point.map (↑σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K)
          (0 : (W⁄(AlgebraicClosure K)).Point))) : _) : _)
        = σ ((Additive.toMul (e₀ (0 : (W⁄(AlgebraicClosure K)).Point)) : _) : _)
      simp only [_root_.map_zero, toMul_zero, Units.val_one, _root_.map_one]
    · let σ' : AlgebraicClosure K →ₐ[K] AlgebraicClosure K := ↑σ
      have hσ'eq : ∀ z, σ' z = σ z := fun z => rfl
      rw [show σ • (.some x y h : (W⁄(AlgebraicClosure K)).Point)
            = Point.map σ' (.some x y h) from rfl, map_some (f := σ')]
      have hσypdx : σ' y + δ * σ' x ≠ 0 := by
        rw [hσ'eq, hσ'eq, ← hσδ, ← _root_.map_mul, ← _root_.map_add]
        exact (map_ne_zero_iff _ σ.injective).mpr (hypdx x y h)
      have h2 : σ ((Additive.toMul (e₀ (.some x y h)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
          * (σ' y + δ * σ' x) = σ' y - δ * σ' x := by
        rw [hσ'eq, hσ'eq, ← hσδ, ← _root_.map_mul, ← _root_.map_add, ← _root_.map_mul,
          he₀ x y h, _root_.map_sub, _root_.map_mul, hσδ]
      exact mul_right_cancel₀ hσypdx ((he₀ (σ' x) (σ' y) _).trans h2.symm)
  have he₀_gal_neg : ∀ (σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K))
      (P : (W⁄(AlgebraicClosure K)).Point), σ δ = -δ →
      ((Additive.toMul (e₀ (σ • P)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
      * σ ((Additive.toMul (e₀ P) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 1 := by
    intro σ P hσδ
    rcases P with _ | ⟨x, y, h⟩
    · show ((Additive.toMul (e₀ (Point.map (↑σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K)
          (0 : (W⁄(AlgebraicClosure K)).Point))) : _) : _)
        * σ ((Additive.toMul (e₀ (0 : (W⁄(AlgebraicClosure K)).Point)) : _) : _) = 1
      simp only [_root_.map_zero, toMul_zero, Units.val_one, _root_.map_one, mul_one]
    · let σ' : AlgebraicClosure K →ₐ[K] AlgebraicClosure K := ↑σ
      have hσ'eq : ∀ z, σ' z = σ z := fun z => rfl
      rw [show σ • (.some x y h : (W⁄(AlgebraicClosure K)).Point)
            = Point.map σ' (.some x y h) from rfl, map_some (f := σ')]
      have h2 : σ ((Additive.toMul (e₀ (.some x y h)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
          * (σ' y - δ * σ' x) = σ' y + δ * σ' x := by
        have hh := congrArg (⇑σ) (he₀ x y h)
        simp only [_root_.map_mul, _root_.map_add, _root_.map_sub] at hh
        rw [hσδ, show σ x = σ' x from (hσ'eq x).symm,
          show σ y = σ' y from (hσ'eq y).symm] at hh
        linear_combination hh
      have hσymdx : σ' y - δ * σ' x ≠ 0 := by
        rw [hσ'eq, hσ'eq]; intro habs
        exact hypdx x y h ((map_eq_zero_iff _ σ.injective).mp
          (by rw [_root_.map_add, _root_.map_mul, hσδ]; linear_combination habs))
      have hσypdx : σ' y + δ * σ' x ≠ 0 := by
        rw [hσ'eq, hσ'eq]; intro habs
        exact hymdx x y h ((map_eq_zero_iff _ σ.injective).mp
          (by rw [_root_.map_sub, _root_.map_mul, hσδ]; linear_combination habs))
      refine mul_right_cancel₀ (mul_ne_zero hσypdx hσymdx) ?_
      rw [one_mul, mul_mul_mul_comm, he₀ (σ' x) (σ' y), h2]
      ring

  have hmem : ∀ P : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n,
      Additive.toMul (e₀ ↑P) ∈ rootsOfUnity n (AlgebraicClosure K) := by
    intro P
    rw [mem_rootsOfUnity]
    have hP : (n : ℤ) • (↑P : (W⁄(AlgebraicClosure K)).Point) = 0 :=
      (Submodule.mem_torsionBy_iff _ _).mp P.2
    have hP' : n • (↑P : (W⁄(AlgebraicClosure K)).Point) = 0 := by
      rw [← natCast_zsmul]; exact hP
    calc (Additive.toMul (e₀ ↑P)) ^ n
        = Additive.toMul (n • e₀ ↑P) := toMul_nsmul n (e₀ ↑P)
      _ = Additive.toMul (e₀ (n • ↑P)) := congrArg Additive.toMul (map_nsmul e₀ n ↑P).symm
      _ = Additive.toMul (e₀ 0) := by rw [hP']
      _ = 1 := by rw [_root_.map_zero]; rfl
  have hmem_inv : ∀ ζ : rootsOfUnity n (AlgebraicClosure K),
      e₀.symm (Additive.ofMul (ζ : (AlgebraicClosure K)ˣ))
        ∈ Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n := by
    intro ζ
    rw [Submodule.mem_torsionBy_iff]
    apply e₀.injective
    rw [_root_.map_zsmul, AddEquiv.apply_symm_apply, _root_.map_zero]
    calc (n:ℤ) • Additive.ofMul (ζ:(AlgebraicClosure K)ˣ)
        = Additive.ofMul ((ζ:(AlgebraicClosure K)ˣ)^(n:ℤ)) := (ofMul_zpow ..).symm
      _ = Additive.ofMul ((ζ:(AlgebraicClosure K)ˣ)^n) := by rw [zpow_natCast]
      _ = 0 := by rw [(mem_rootsOfUnity ..).mp ζ.2]; rfl
  refine ⟨⟨fun P => ⟨Additive.toMul (e₀ ↑P), hmem P⟩,
    fun ζ => ⟨e₀.symm (Additive.ofMul (ζ : (AlgebraicClosure K)ˣ)), hmem_inv ζ⟩,
    ?_, ?_⟩, ?_, ?_⟩
  · intro P; refine Subtype.ext ?_
    show e₀.symm (Additive.ofMul (Additive.toMul (e₀ ↑P))) = ↑P
    rw [show Additive.ofMul (Additive.toMul (e₀ ↑P)) = e₀ ↑P from rfl]
    exact e₀.symm_apply_apply ↑P
  · intro ζ; refine Subtype.ext ?_
    show Additive.toMul (e₀ (e₀.symm (Additive.ofMul (ζ:(AlgebraicClosure K)ˣ))))
      = (ζ:(AlgebraicClosure K)ˣ)
    rw [AddEquiv.apply_symm_apply]; rfl
  · intro P Q
    refine Subtype.ext (Units.ext ?_)
    simp only [Equiv.coe_fn_mk, Subgroup.coe_mul, Units.val_mul, Submodule.coe_add,
      _root_.map_add, toMul_add]
  · intro σ P
    simp only [Equiv.coe_fn_mk]
    rw [show (↑(σ • P) : (W⁄(AlgebraicClosure K)).Point) = σ • ↑P from rfl]
    exact ⟨he₀_gal_eq σ ↑P, he₀_gal_neg σ ↑P⟩

end S_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare
end P2MW
export P2MW.S_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare (solution)
