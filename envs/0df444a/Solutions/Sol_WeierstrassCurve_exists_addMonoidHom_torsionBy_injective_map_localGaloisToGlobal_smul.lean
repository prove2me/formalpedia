-- Prove2me | solution 1 for WeierstrassCurve.exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e475fca9-c821-5702-925c-bb5ab0271919

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul

open scoped WeierstrassCurve.Affine Classical
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

noncomputable section

namespace E87GPSI

noncomputable def castPoint {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

theorem castPoint_zero {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    castPoint h 0 = 0 := by subst h; simp [castPoint]

theorem castPoint_some {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂)
    {x y : F} (hns : W₁.toAffine.Nonsingular x y) :
    castPoint h (Point.some x y hns) = Point.some x y (h ▸ hns) := by subst h; simp [castPoint]

variable (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]

theorem curve_eq :
    (W.map (Int.castRingHom ℚ)).baseChange (AlgebraicClosure ℚ_[p]) =
      (W.map (Int.castRingHom ℚ_[p])).baseChange (AlgebraicClosure ℚ_[p]) := by
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1

noncomputable def ψ₀ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point →+
    ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point :=
  (castPoint (curve_eq W p)).toAddMonoidHom.comp
    (Point.map (W' := W.map (Int.castRingHom ℚ)) (padicEmbedding p))

theorem ψ₀_injective : Function.Injective (ψ₀ W p) :=
  (castPoint (curve_eq W p)).injective.comp (Point.map_injective _)

theorem ψ₀_smul (τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) :
    ψ₀ W p ((localGaloisToGlobal p τ) • P) = τ • ψ₀ W p P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.algEquiv_smul_def, Point.algEquiv_smul_def]
    simp only [ψ₀, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
    erw [Point.map_some, Point.map_some]
    try erw [castPoint_some, castPoint_some]
    try erw [Point.map_some]
    congr 1 <;> try exact padicEmbedding_localGaloisToGlobal p τ _
    all_goals exact ((W.map (Int.castRingHom ℚ)).toAffine.baseChange_nonsingular
      (f := ((localGaloisToGlobal p τ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom)
      (AlgEquiv.injective _) x y).mpr h

noncomputable def ψ (n : ℕ) :
    Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point n →+
      Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point n :=
  ((ψ₀ W p).comp (Submodule.torsionBy ℤ _ n).subtype.toAddMonoidHom).codRestrict
    (Submodule.torsionBy ℤ _ n).toAddSubgroup (by
      intro P
      change ψ₀ W p P ∈ Submodule.torsionBy ℤ _ n
      rw [Submodule.mem_torsionBy_iff]
      have hP := (Submodule.mem_torsionBy_iff _ _).mp P.2
      rw [← map_zsmul (ψ₀ W p), hP, _root_.map_zero])

theorem ψ_injective (n : ℕ) : Function.Injective (ψ W p n) := by
  intro P Q h
  apply Subtype.ext
  apply ψ₀_injective W p
  exact congrArg Subtype.val h

theorem ψ_smul (n : ℕ) (τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
    (P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point n) :
    ψ W p n ((localGaloisToGlobal p τ) • P) = τ • ψ W p n P := by
  apply Subtype.ext
  exact ψ₀_smul W p τ P

end E87GPSI

end

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (n : ℕ) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ ψ : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point n →+
          Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point n,
      Function.Injective ψ ∧
      ∀ (τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
        (P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point n),
        ψ ((localGaloisToGlobal p τ) • P) = τ • ψ P :=
  ⟨E87GPSI.ψ W p n, E87GPSI.ψ_injective W p n, E87GPSI.ψ_smul W p n⟩

end S_WeierstrassCurve_exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul (solution)
