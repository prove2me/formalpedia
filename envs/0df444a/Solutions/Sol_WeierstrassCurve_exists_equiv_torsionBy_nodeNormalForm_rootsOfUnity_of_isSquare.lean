-- Prove2me | solution 1 for WeierstrassCurve.exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f8218990-8c73-52a1-a4be-36cf43fe702a

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_WeierstrassCurve_Affine_Point_exists_addEquiv_nodeNormalForm_additive_units
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_isSquare

set_option maxHeartbeats 12800000
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (n : ℕ) [NeZero n]
    (d : K) (hd : d * d = c) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    let W : WeierstrassCurve K := ⟨0, c, 0, 0, 0⟩
    ∃ et : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n
        ≃ rootsOfUnity n (AlgebraicClosure K),
      (∀ P Q, et (P + Q) = et P * et Q) ∧
      ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (P : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n),
        ((et (σ • P) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
        = σ ((et P : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := by
  letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  set W : WeierstrassCurve K := ⟨0, c, 0, 0, 0⟩ with hWdef
  have hdne : d ≠ 0 := fun h => hc (by rw [← hd, h, mul_zero])
  set dbar := algebraMap K (AlgebraicClosure K) d with hdbar_def
  have hdbarne : dbar ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).mpr hdne
  have hσd : ∀ σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K), σ dbar = dbar := by
    intro σ; rw [hdbar_def]; exact σ.commutes d

  have hW : (W⁄(AlgebraicClosure K))
      = (⟨0, dbar * dbar, 0, 0, 0⟩ : WeierstrassCurve (AlgebraicClosure K)).toAffine := by
    rw [hWdef]
    ext
    · exact _root_.map_zero _
    · show algebraMap K (AlgebraicClosure K) c = dbar * dbar
      rw [← hd, _root_.map_mul]
    · exact _root_.map_zero _
    · exact _root_.map_zero _
    · exact _root_.map_zero _

  obtain ⟨e₀, he₀⟩ : ∃ e₀ : (W⁄(AlgebraicClosure K)).Point ≃+ Additive (AlgebraicClosure K)ˣ,
      ∀ x y h, ((Additive.toMul (e₀ (.some x y h)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
        * (y + dbar * x) = y - dbar * x := by
    rw [hW]; exact exists_addEquiv_nodeNormalForm_additive_units dbar hdbarne

  have hypdx : ∀ x y, (W⁄(AlgebraicClosure K)).Nonsingular x y → y + dbar * x ≠ 0 := by
    intro x y h habs
    have hh := he₀ x y h
    rw [habs, mul_zero] at hh
    have hy0 : y = 0 := by linear_combination (1/2:AlgebraicClosure K)*habs - (1/2)*hh
    have hx0 : x = 0 := by
      have := habs; rw [hy0, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_left hdbarne
    subst hy0; subst hx0
    rw [hW, WeierstrassCurve.Affine.nonsingular_iff'] at h
    obtain ⟨-, hns⟩ := h
    rcases hns with h1 | h2
    · exact h1 (by ring)
    · exact h2 (by ring)

  have he₀_gal : ∀ (σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K))
      (P : (W⁄(AlgebraicClosure K)).Point),
      ((Additive.toMul (e₀ (σ • P)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
      = σ ((Additive.toMul (e₀ P) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := by
    intro σ P
    rcases P with _ | ⟨x, y, h⟩
    · show ((Additive.toMul (e₀ (Point.map (↑σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K)
          (0 : (W⁄(AlgebraicClosure K)).Point))) : _) : _)
        = σ ((Additive.toMul (e₀ (0 : (W⁄(AlgebraicClosure K)).Point)) : _) : _)
      simp only [_root_.map_zero, toMul_zero, Units.val_one, _root_.map_one]
    · let σ' : AlgebraicClosure K →ₐ[K] AlgebraicClosure K := ↑σ
      have hσ'eq : ∀ z, σ' z = σ z := fun z => rfl
      rw [show σ • (.some x y h : (W⁄(AlgebraicClosure K)).Point)
            = Point.map σ' (.some x y h) from rfl,
          map_some (f := σ')]
      have hσypdx : σ' y + dbar * σ' x ≠ 0 := by
        rw [hσ'eq, hσ'eq, ← hσd σ, ← _root_.map_mul, ← _root_.map_add]
        exact (map_ne_zero_iff _ σ.injective).mpr (hypdx x y h)
      have h2 : σ ((Additive.toMul (e₀ (.some x y h)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
          * (σ' y + dbar * σ' x) = σ' y - dbar * σ' x := by
        rw [hσ'eq, hσ'eq, ← hσd σ, ← _root_.map_mul, ← _root_.map_add, ← _root_.map_mul,
          he₀ x y h, _root_.map_sub, _root_.map_mul, hσd σ]
      exact mul_right_cancel₀ hσypdx ((he₀ (σ' x) (σ' y) _).trans h2.symm)

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
  · intro P
    refine Subtype.ext ?_
    show e₀.symm (Additive.ofMul (Additive.toMul (e₀ ↑P))) = ↑P
    rw [show Additive.ofMul (Additive.toMul (e₀ ↑P)) = e₀ ↑P from rfl]
    exact e₀.symm_apply_apply ↑P
  · intro ζ
    refine Subtype.ext ?_
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
    exact he₀_gal σ ↑P

end S_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_isSquare
end P2MW
export P2MW.S_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_isSquare (solution)
