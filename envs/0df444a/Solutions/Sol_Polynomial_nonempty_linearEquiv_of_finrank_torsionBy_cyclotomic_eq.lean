-- Prove2me | solution 1 for Polynomial.nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fc9d7db4-c50a-5a27-af88-d9cbc5761719

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq

set_option autoImplicit false
universe u v
open Polynomial Module
open scoped DirectSum
set_option maxHeartbeats 4000000

noncomputable section

theorem solution
    {M : Type u} [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M] [IsScalarTower ℚ ℚ[X] M] [FiniteDimensional ℚ M]
    {N : Type v} [AddCommGroup N] [Module ℚ[X] N] [Module ℚ N] [IsScalarTower ℚ ℚ[X] N] [FiniteDimensional ℚ N]
    {n : ℕ} (hn : 0 < n) (hM : Module.IsTorsionBy ℚ[X] M ((X : ℚ[X]) ^ n - 1)) (hN : Module.IsTorsionBy ℚ[X] N ((X : ℚ[X]) ^ n - 1))
    (h : ∀ d, d ∣ n → Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)) =
      Module.finrank ℚ (Submodule.torsionBy ℚ[X] N (cyclotomic d ℚ))) :
    Nonempty (M ≃ₗ[ℚ[X]] N) := by
  classical
  have hprod : ∏ d ∈ n.divisors, cyclotomic d ℚ = (X : ℚ[X]) ^ n - 1 := prod_cyclotomic_eq_X_pow_sub_one hn ℚ
  have hcop : (n.divisors : Set ℕ).Pairwise (Function.onFun IsCoprime fun d => cyclotomic d ℚ) :=
    fun i _ j _ hij => cyclotomic.isCoprime_rat hij

  have hMt : Module.IsTorsionBy ℚ[X] M (∏ d ∈ n.divisors, cyclotomic d ℚ) := by rw [hprod]; exact hM
  have hNt : Module.IsTorsionBy ℚ[X] N (∏ d ∈ n.divisors, cyclotomic d ℚ) := by rw [hprod]; exact hN
  let eM := (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun d : n.divisors =>
      Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)) (Submodule.torsionBy_isInternal hcop hMt)).symm
  let eN := (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun d : n.divisors =>
      Submodule.torsionBy ℚ[X] N (cyclotomic d ℚ)) (Submodule.torsionBy_isInternal hcop hNt)).symm

  have hcomp : ∀ (Φ : ℚ[X]), Irreducible Φ →
      Module.finrank ℚ (Submodule.torsionBy ℚ[X] M Φ) = Module.finrank ℚ (Submodule.torsionBy ℚ[X] N Φ) →
      Nonempty (Submodule.torsionBy ℚ[X] M Φ ≃ₗ[ℚ[X]] Submodule.torsionBy ℚ[X] N Φ) := by
    intro Φ hΦ hfin
    haveI : Fact (Irreducible Φ) := ⟨hΦ⟩
    letI : Module (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] M Φ) :=
      inferInstanceAs (Module (ℚ[X] ⧸ Ideal.span {Φ}) (Submodule.torsionBy ℚ[X] M Φ))
    letI : Module (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] N Φ) :=
      inferInstanceAs (Module (ℚ[X] ⧸ Ideal.span {Φ}) (Submodule.torsionBy ℚ[X] N Φ))
    have hmkM : ∀ (r : ℚ[X]) (x : Submodule.torsionBy ℚ[X] M Φ), (AdjoinRoot.mk Φ r) • x = r • x := fun _ _ => rfl
    have hmkN : ∀ (r : ℚ[X]) (x : Submodule.torsionBy ℚ[X] N Φ), (AdjoinRoot.mk Φ r) • x = r • x := fun _ _ => rfl
    haveI : IsScalarTower ℚ (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] M Φ) := ⟨fun c k x => by
      obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective k
      rw [AdjoinRoot.smul_mk, hmkM, hmkM, smul_assoc]⟩
    haveI : IsScalarTower ℚ (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] N Φ) := ⟨fun c k x => by
      obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective k
      rw [AdjoinRoot.smul_mk, hmkN, hmkN, smul_assoc]⟩
    haveI : Module.Finite ℚ (AdjoinRoot Φ) := (AdjoinRoot.powerBasis hΦ.ne_zero).finite
    haveI : Module.Finite ℚ (Submodule.torsionBy ℚ[X] M Φ) :=
      Module.Finite.of_injective ((Submodule.torsionBy ℚ[X] M Φ).subtype.restrictScalars ℚ) Subtype.val_injective
    haveI : Module.Finite ℚ (Submodule.torsionBy ℚ[X] N Φ) :=
      Module.Finite.of_injective ((Submodule.torsionBy ℚ[X] N Φ).subtype.restrictScalars ℚ) Subtype.val_injective
    haveI : Module.Finite (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] M Φ) :=
      Module.Finite.of_restrictScalars_finite ℚ (AdjoinRoot Φ) _
    haveI : Module.Finite (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] N Φ) :=
      Module.Finite.of_restrictScalars_finite ℚ (AdjoinRoot Φ) _

    have hKpos : 0 < Module.finrank ℚ (AdjoinRoot Φ) := Module.finrank_pos
    have hdim : Module.finrank (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] M Φ) =
        Module.finrank (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] N Φ) := by
      have h1 := Module.finrank_mul_finrank ℚ (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] M Φ)
      have h2 := Module.finrank_mul_finrank ℚ (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] N Φ)
      rw [hfin, ← h2] at h1
      exact Nat.eq_of_mul_eq_mul_left hKpos h1
    let eK := LinearEquiv.ofFinrankEq (Submodule.torsionBy ℚ[X] M Φ) (Submodule.torsionBy ℚ[X] N Φ) hdim

    let f : Submodule.torsionBy ℚ[X] M Φ →ₗ[ℚ[X]] Submodule.torsionBy ℚ[X] N Φ :=
      { toFun := eK
        map_add' := fun x y => eK.map_add x y
        map_smul' := fun r x => by
          show eK (r • x) = r • eK x
          rw [← hmkM r x, eK.map_smul, hmkN] }
    exact ⟨LinearEquiv.ofBijective f eK.bijective⟩
  let ed := fun d : n.divisors => (hcomp (cyclotomic d ℚ) (cyclotomic.irreducible_rat (Nat.pos_of_mem_divisors d.2))
    (h d (Nat.dvd_of_mem_divisors d.2))).some
  exact ⟨eM ≪≫ₗ (DFinsupp.mapRange.linearEquiv ed) ≪≫ₗ eN.symm⟩

end

end S_Polynomial_nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq
end P2MW
export P2MW.S_Polynomial_nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq (solution)
