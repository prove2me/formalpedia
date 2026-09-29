-- Prove2me | solution 1 for WeierstrassCurve.galois_action_trivial_on_submodule_of_inertia_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8fdc0b0d-28d0-5f0b-9e96-d8b2f87032cd

import Theorems.Thm_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_galois_action_trivial_on_submodule_of_inertia_trivial

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace M3dS11

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Γ" => ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))

theorem stabilizer_point_isOpen (W : WeierstrassCurve ℚ) (P : (W⁄ℚ̄).Point) :
    IsOpen (MulAction.stabilizer Γ P : Set Γ) := by
  haveI : Algebra.IsIntegral ℚ ℚ̄ := by
    have h : @Algebra.IsIntegral ℚ ℚ̄ _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  rcases P with _ | ⟨x, y, h⟩
  · have htop : MulAction.stabilizer Γ (Point.zero : (W⁄ℚ̄).Point) = ⊤ := by
      ext σ
      simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
      rfl
    rw [htop, Subgroup.coe_top]
    exact isOpen_univ
  · apply Subgroup.isOpen_mono (H₁ := MulAction.stabilizer Γ x ⊓ MulAction.stabilizer Γ y)
    · intro σ hσ
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff] at hσ
      rw [MulAction.mem_stabilizer_iff, algEquiv_smul_def, map_some, Point.some.injEq]
      exact hσ
    · rw [Subgroup.coe_inf]
      exact (stabilizer_isOpen_of_isIntegral x).inter (stabilizer_isOpen_of_isIntegral y)

theorem fixer_torsion_isOpen (W : WeierstrassCurve ℚ) (n : ℕ)
    [Finite (Submodule.torsionBy ℤ (W⁄ℚ̄).Point n)] :
    IsOpen ((⨅ x : Submodule.torsionBy ℤ (W⁄ℚ̄).Point n, MulAction.stabilizer Γ x :
      Subgroup Γ) : Set Γ) := by
  rw [Subgroup.coe_iInf]
  apply isOpen_iInter_of_finite
  intro x
  have hx : (MulAction.stabilizer Γ x : Set Γ) = MulAction.stabilizer Γ (x : (W⁄ℚ̄).Point) := by
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [hx]
  exact stabilizer_point_isOpen W x

end M3dS11

open M3dS11 in
theorem solution (W : WeierstrassCurve ℚ) {n : ℕ} [Finite (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n)] (N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n)) (hunr : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ N, σ • x = x) : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ x ∈ N, σ • x = x := by

  let H : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :=
    ⨅ x : N, MulAction.stabilizer ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
      (x : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n)
  have hH : H = ⊤ := by
    apply AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le H
    ·
      apply Subgroup.isOpen_mono _ (fixer_torsion_isOpen W n)
      intro σ hσ
      rw [Subgroup.mem_iInf] at hσ ⊢
      exact fun x => hσ x
    ·
      intro q hq A hA σ hσ
      rw [Subgroup.mem_iInf]
      exact fun x => hunr q hq A hA σ hσ x x.2
  intro σ x hx
  have hσ : σ ∈ H := hH ▸ Subgroup.mem_top σ
  rw [Subgroup.mem_iInf] at hσ
  exact hσ ⟨x, hx⟩

end S_WeierstrassCurve_galois_action_trivial_on_submodule_of_inertia_trivial
end P2MW
export P2MW.S_WeierstrassCurve_galois_action_trivial_on_submodule_of_inertia_trivial (solution)
