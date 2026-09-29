-- Prove2me | solution 1 for TateModule.exists_baseChange_pi_torsionBy_ker_eq_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/84086e8a-aa42-53b8-a3fa-242f67ae54a3

import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateModule_exists_baseChange_pi_torsionBy_ker_eq_pow_smul

set_option autoImplicit false

open TensorProduct IsLocalRing

namespace A2TateTorsion

variable {p : ℕ} [Fact p.Prime]

theorem mem_maximalIdeal_pow_smul_top_iff {V : Type*} [AddCommGroup V] [Module ℤ_[p] V] (n : ℕ)
    (x : V) : x ∈ (maximalIdeal ℤ_[p] ^ n) • (⊤ : Submodule ℤ_[p] V) ↔
      ∃ y : V, x = ((p : ℤ_[p]) ^ n) • y := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  constructor
  · intro h
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y, Submodule.mem_top, rfl⟩

end A2TateTorsion

open A2TateTorsion in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M]
    (R : Type) [CommRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    (n : ℕ) :
    ∃ lam : R ⊗[ℤ_[p]] ↥(TateModule p M) →+
        (Fin (Module.finrank ℤ_[p] R) → ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ))),
      (∀ z : R ⊗[ℤ_[p]] ↥(TateModule p M),
        lam z = 0 ↔ ∃ w : R ⊗[ℤ_[p]] ↥(TateModule p M), z = ((p : R) ^ n) • w) ∧
      ∀ (G : Type) [Monoid G] [DistribMulAction G M] (g : G) (z : R ⊗[ℤ_[p]] ↥(TateModule p M))
        (i : Fin (Module.finrank ℤ_[p] R)),
        ((lam ((TateModule.rep p M G g).baseChange R z) i :
            ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ))) : M) =
          g • ((lam z i : ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ))) : M) := by
  classical

  set b := Module.finrank ℤ_[p] R
  let bR : Module.Basis (Fin b) ℤ_[p] R := Module.finBasis ℤ_[p] R
  let κ : R ⊗[ℤ_[p]] ↥(TateModule p M) ≃ₗ[ℤ_[p]] (Fin b → ↥(TateModule p M)) :=
    (TensorProduct.congr bR.repr (LinearEquiv.refl ℤ_[p] _)) ≪≫ₗ
      (TensorProduct.finsuppScalarLeft ℤ_[p] ↥(TateModule p M) (Fin b)) ≪≫ₗ
      (Finsupp.linearEquivFunOnFinite ℤ_[p] ↥(TateModule p M) (Fin b))
  have hκ_tmul : ∀ (a : R) (x : ↥(TateModule p M)) (i : Fin b), κ (a ⊗ₜ x) i = (bR.repr a i) • x := by
    intro a x i
    show Finsupp.linearEquivFunOnFinite ℤ_[p] _ (Fin b)
      (TensorProduct.finsuppScalarLeft ℤ_[p] _ (Fin b)
        (TensorProduct.congr bR.repr (LinearEquiv.refl ℤ_[p] _) (a ⊗ₜ x))) i = _
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, Finsupp.linearEquivFunOnFinite_apply,
      TensorProduct.finsuppScalarLeft_apply_tmul_apply]

  have hκ_nat : ∀ (f : Module.End ℤ_[p] ↥(TateModule p M)) (z : R ⊗[ℤ_[p]] ↥(TateModule p M))
      (i : Fin b), κ (f.baseChange R z) i = f (κ z i) := by
    intro f z i
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, Pi.zero_apply, map_zero]
    | tmul a x => rw [LinearMap.baseChange_tmul, hκ_tmul, hκ_tmul, map_smul]
    | add z z' hz hz' => rw [map_add, map_add, Pi.add_apply, hz, hz', map_add, Pi.add_apply, map_add]

  let lam : R ⊗[ℤ_[p]] ↥(TateModule p M) →+
      (Fin b → ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ))) :=
    { toFun := fun z i => ⟨TateModule.proj p M n (κ z i), TateModule.proj_mem_torsionBy n _⟩
      map_zero' := by
        funext i; apply Subtype.ext
        show TateModule.proj p M n (κ 0 i) = 0
        rw [map_zero, Pi.zero_apply, map_zero]
      map_add' := fun z z' => by
        funext i; apply Subtype.ext
        show TateModule.proj p M n (κ (z + z') i) = TateModule.proj p M n (κ z i) + TateModule.proj p M n (κ z' i)
        rw [map_add, Pi.add_apply, map_add] }
  have hlam : ∀ z i, ((lam z i : ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ))) : M) =
      TateModule.proj p M n (κ z i) := fun _ _ => rfl
  have hpR : ∀ w : R ⊗[ℤ_[p]] ↥(TateModule p M), ((p : R) ^ n) • w = ((p : ℤ_[p]) ^ n) • w :=
    fun w => by rw [← algebraMap_smul R ((p : ℤ_[p]) ^ n) w, map_pow, map_natCast]
  refine ⟨lam, fun z => ?_, ?_⟩
  ·
    constructor
    · intro hz

      have hcoord : ∀ i, ∃ y : ↥(TateModule p M), κ z i = ((p : ℤ_[p]) ^ n) • y := by
        intro i
        have hi : TateModule.proj p M n (κ z i) = 0 := by
          rw [← hlam]
          have := congrArg (fun x : Fin b → ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) =>
            ((x i : ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ))) : M)) hz
          simpa using this
        exact (mem_maximalIdeal_pow_smul_top_iff n _).mp ((TateModule.proj_eq_zero_iff n _).mp hi)
      choose y hy using hcoord
      refine ⟨κ.symm (fun i => y i), ?_⟩
      apply κ.injective
      rw [hpR, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      rw [Pi.smul_apply, hy i]
    · rintro ⟨w, rfl⟩
      funext i; apply Subtype.ext
      rw [hlam, hpR, map_smul, Pi.smul_apply, (TateModule.proj_eq_zero_iff n _).mpr]
      · rfl
      · exact (mem_maximalIdeal_pow_smul_top_iff n _).mpr ⟨κ w i, rfl⟩
  ·
    intro G _ _ g z i
    rw [hlam, hlam, hκ_nat]
    rfl

end S_TateModule_exists_baseChange_pi_torsionBy_ker_eq_pow_smul
end P2MW
export P2MW.S_TateModule_exists_baseChange_pi_torsionBy_ker_eq_pow_smul (solution)
