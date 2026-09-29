-- Prove2me | solution 1 for TateModule.exists_addEquiv_addMonoidHom_map_proj_one_of_forall_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/10b3bc0f-67c4-55ea-b6bd-3076123520a2

import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateModule_exists_addEquiv_addMonoidHom_map_proj_one_of_forall_smul_mem

set_option autoImplicit false

namespace TateProjHomAux

variable {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]

local notation "π" => TateModule.proj p M 1

theorem apply_eq_of_proj_eq (P : Submodule ℤ_[p] ↥(TateModule p M))
    (hsat : ∀ x : ↥(TateModule p M), (p : ℤ_[p]) • x ∈ P → x ∈ P)
    {N : Type*} [AddCommGroup N] (hN : ∀ y : N, p • y = 0)
    (φ : ↥P →+ N) (x x' : ↥P) (h : π (x : ↥(TateModule p M)) = π (x' : ↥(TateModule p M))) :
    φ x = φ x' := by
  rw [← sub_eq_zero, ← map_sub]
  set d : ↥(TateModule p M) := (x : ↥(TateModule p M)) - x' with hd
  have hd0 : π d = 0 := by rw [hd, map_sub, h, sub_self]
  let y := TateModule.shiftOfProjEqZero 1 d hd0
  have hy : (p : ℤ_[p]) • y = d := by
    have := TateModule.pow_smul_shiftOfProjEqZero 1 d hd0
    rwa [pow_one] at this
  have hyP : y ∈ P := hsat y (by rw [hy, hd]; exact P.sub_mem x.2 x'.2)
  have hxy : x - x' = (p : ℕ) • (⟨y, hyP⟩ : ↥P) := by
    apply Subtype.ext
    show (x : ↥(TateModule p M)) - x' = (((p : ℕ) • (⟨y, hyP⟩ : ↥P) : ↥P) : ↥(TateModule p M))
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul ℤ_[p], hy]
  rw [hxy, map_nsmul, hN]

end TateProjHomAux

theorem solution
    {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    (P : Submodule ℤ_[p] ↥(TateModule p M))
    (hsat : ∀ x : ↥(TateModule p M), (p : ℤ_[p]) • x ∈ P → x ∈ P)
    (N : Type*) [AddCommGroup N] (hN : ∀ y : N, p • y = 0) :
    ∃ ρ : (↥P →+ N) ≃+ (↥((P.toAddSubgroup).map (TateModule.proj p M 1)) →+ N),
      (∀ (φ : ↥P →+ N) (x : ↥P) (a : ↥((P.toAddSubgroup).map (TateModule.proj p M 1))),
        (a : M) = TateModule.proj p M 1 (x : ↥(TateModule p M)) → ρ φ a = φ x) ∧
      (∀ (T : ↥(TateModule p M) →ₗ[ℤ_[p]] ↥(TateModule p M)) (t : M →+ M)
        (hTt : ∀ x : ↥(TateModule p M), TateModule.proj p M 1 (T x) = t (TateModule.proj p M 1 x))
        (hTP : ∀ x ∈ P, T x ∈ P)
        (φ : ↥P →+ N) (a a' : ↥((P.toAddSubgroup).map (TateModule.proj p M 1))),
        (a' : M) = t (a : M) → ρ (φ.comp (T.restrict hTP).toAddMonoidHom) a = ρ φ a') := by
  classical

  have hrep : ∀ a : ↥((P.toAddSubgroup).map (TateModule.proj p M 1)),
      ∃ x : ↥P, TateModule.proj p M 1 (x : ↥(TateModule p M)) = a := fun a => by
    obtain ⟨x, hx, hxa⟩ := a.2
    exact ⟨⟨x, hx⟩, hxa⟩
  choose lift hlift using hrep
  have key := TateProjHomAux.apply_eq_of_proj_eq P hsat hN

  let πP : ↥P →+ ↥((P.toAddSubgroup).map (TateModule.proj p M 1)) :=
    { toFun := fun x => ⟨TateModule.proj p M 1 (x : ↥(TateModule p M)), ⟨x, x.2, rfl⟩⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }

  let ρf : (↥P →+ N) → (↥((P.toAddSubgroup).map (TateModule.proj p M 1)) →+ N) := fun φ =>
    { toFun := fun a => φ (lift a)
      map_zero' := by
        rw [← map_zero φ]
        exact key φ _ _ (by rw [hlift]; simp)
      map_add' := fun a b => by
        rw [← map_add]
        exact key φ _ _ (by rw [hlift, Submodule.coe_add, map_add, hlift, hlift]; rfl) }
  let ρ : (↥P →+ N) ≃+ (↥((P.toAddSubgroup).map (TateModule.proj p M 1)) →+ N) :=
    { toFun := ρf
      invFun := fun ψ => ψ.comp πP
      left_inv := fun φ => by
        ext x
        show φ (lift (πP x)) = φ x
        exact key φ _ _ (by rw [hlift]; rfl)
      right_inv := fun ψ => by
        ext a
        show ψ (πP (lift a)) = ψ a
        congr 1
        exact Subtype.ext (hlift a)
      map_add' := fun φ ψ => by ext a; rfl }
  refine ⟨ρ, fun φ x a hax => ?_, fun T t hTt hTP φ a a' haa' => ?_⟩
  · show φ (lift a) = φ x
    exact key φ _ _ (by rw [hlift, hax])
  · show φ ((T.restrict hTP).toAddMonoidHom (lift a)) = φ (lift a')
    apply key
    show TateModule.proj p M 1 (T (lift a : ↥(TateModule p M))) = TateModule.proj p M 1 (lift a' : ↥(TateModule p M))
    rw [hTt, hlift, hlift, haa']

end S_TateModule_exists_addEquiv_addMonoidHom_map_proj_one_of_forall_smul_mem
end P2MW
export P2MW.S_TateModule_exists_addEquiv_addMonoidHom_map_proj_one_of_forall_smul_mem (solution)
