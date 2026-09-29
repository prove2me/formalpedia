-- Prove2me | solution 1 for TateModule.nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/366fea0a-9e3b-5a11-b564-141d91460491

import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_TateModule_nonempty_basis_of_card_torsionBy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateModule_nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq

set_option autoImplicit false

namespace HTTORIC

open Submodule

variable (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [∀ i : ℕ, HasEnoughRootsOfUnity L (p ^ i)]

theorem natCard_torsionBy_units (n : ℕ) :
    Nat.card (torsionBy ℤ (Additive Lˣ) ((p ^ n : ℕ) : ℤ)) = p ^ n := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have e : torsionBy ℤ (Additive Lˣ) ((p ^ n : ℕ) : ℤ) ≃ rootsOfUnity (p ^ n) L :=
    ⟨fun u => ⟨Additive.toMul u.1, by
        have hu := u.2
        rw [mem_torsionBy_iff, natCast_zsmul] at hu
        rw [mem_rootsOfUnity]
        exact congrArg Additive.toMul hu⟩,
     fun ζ => ⟨Additive.ofMul ζ.1, by
        have hζ := ζ.2
        rw [mem_rootsOfUnity] at hζ
        rw [mem_torsionBy_iff, natCast_zsmul]
        exact congrArg Additive.ofMul hζ⟩,
     fun u => rfl, fun ζ => rfl⟩
  rw [Nat.card_congr e, HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ n)]

variable (ι : Type) [Finite ι]

def torsionByPiEquiv (n : ℕ) :
    torsionBy ℤ (ι → Additive Lˣ) ((p ^ n : ℕ) : ℤ) ≃ (ι → torsionBy ℤ (Additive Lˣ) ((p ^ n : ℕ) : ℤ)) where
  toFun f := fun i => ⟨f.1 i, by
    have hf := f.2
    rw [mem_torsionBy_iff] at hf ⊢
    exact congrFun hf i⟩
  invFun g := ⟨fun i => (g i).1, by
    rw [mem_torsionBy_iff]
    funext i
    exact (mem_torsionBy_iff _ _).1 (g i).2⟩
  left_inv f := rfl
  right_inv g := rfl

theorem natCard_torsionBy_pi_units (n : ℕ) :
    Nat.card (torsionBy ℤ (ι → Additive Lˣ) ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ Nat.card ι := by
  rw [Nat.card_congr (torsionByPiEquiv p L ι n), Nat.card_fun, natCard_torsionBy_units]

theorem nonempty_basis :
    Nonempty (Module.Basis ι ℤ_[p] (TateModule p (ι → Additive Lˣ))) := by
  obtain ⟨b⟩ := TateModule.nonempty_basis_of_card_torsionBy p (Nat.card ι)
    (natCard_torsionBy_pi_units p L ι)
  exact ⟨b.reindex (Finite.equivFin ι).symm⟩

variable {p L ι}

private def _root_.HTTORIC.val (t : TateModule p (ι → Additive Lˣ)) (v : ℕ) (i : ι) : L :=
  ((Additive.toMul ((t : ℕ → ι → Additive Lˣ) v i) : Lˣ) : L)

p2m_export "HTTORIC" "val"
omit [Fact p.Prime] [∀ i : ℕ, HasEnoughRootsOfUnity L (p ^ i)] [Finite ι] in
theorem val_pow (t : TateModule p (ι → Additive Lˣ)) (v : ℕ) (i : ι) : val t v i ^ (p ^ v) = 1 := by
  have h := TateModule.torsion t v
  rw [natCast_zsmul] at h
  have hi : (p ^ v) • ((t : ℕ → ι → Additive Lˣ) v i) = 0 := by
    have := congrFun h i
    exact this
  have h' : (Additive.toMul ((t : ℕ → ι → Additive Lˣ) v i)) ^ (p ^ v) = 1 := congrArg Additive.toMul hi
  rw [val, ← Units.val_pow_eq_pow_val, h', Units.val_one]

omit [∀ i : ℕ, HasEnoughRootsOfUnity L (p ^ i)] [Finite ι] in
theorem val_smul (a : ℤ_[p]) (t : TateModule p (ι → Additive Lˣ)) (v : ℕ) (i : ι) :
    val (a • t) v i = val t v i ^ (a.appr v) := by
  rw [val, TateModule.smul_apply, Pi.smul_apply, toMul_zsmul, Units.val_zpow_eq_zpow_val, zpow_natCast]
  rfl

omit [Fact p.Prime] [∀ i : ℕ, HasEnoughRootsOfUnity L (p ^ i)] [Finite ι] in
theorem ext_val {s t : TateModule p (ι → Additive Lˣ)} (h : ∀ v i, val s v i = val t v i) : s = t := by
  refine Subtype.ext (funext fun v => funext fun i => ?_)
  exact congrArg Additive.ofMul (Units.ext (h v i))

omit [Finite ι] in

theorem eq_smul_of_val_eq (σ : L ≃+* L) (s t : TateModule p (ι → Additive Lˣ))
    (hst : ∀ v i, val s v i = σ (val t v i)) :
    s = ((cyclotomicCharacter L p σ : ℤ_[p]ˣ) : ℤ_[p]) • t := by
  refine ext_val fun v i => ?_
  rw [hst, val_smul]
  have hspec := cyclotomicCharacter.spec p (n := v) σ (val t v i) (val_pow t v i)
  have hval : (((cyclotomicCharacter L p σ).val.toZModPow v).val) =
      ((cyclotomicCharacter L p σ : ℤ_[p]ˣ) : ℤ_[p]).appr v := by
    rw [TateModule.toZModPow_eq_appr, ZMod.val_natCast, Nat.mod_eq_of_lt (PadicInt.appr_lt _ _)]
  rw [hval] at hspec
  exact hspec

end HTTORIC

theorem solution
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [∀ i : ℕ, HasEnoughRootsOfUnity L (p ^ i)]
    (ι : Type) [Finite ι] :
    Nonempty (Module.Basis ι ℤ_[p] (TateModule p (ι → Additive Lˣ))) ∧
    ∀ (σ : L ≃+* L) (s t : TateModule p (ι → Additive Lˣ)),
      (∀ (v : ℕ) (i : ι), ((Additive.toMul ((s : ℕ → ι → Additive Lˣ) v i) : Lˣ) : L) =
          σ (((Additive.toMul ((t : ℕ → ι → Additive Lˣ) v i) : Lˣ) : L))) →
      s = ((cyclotomicCharacter L p σ : ℤ_[p]ˣ) : ℤ_[p]) • t :=
  ⟨HTTORIC.nonempty_basis p L ι, fun σ s t hst => HTTORIC.eq_smul_of_val_eq σ s t hst⟩

end S_TateModule_nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq
end P2MW
export P2MW.S_TateModule_nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq (solution)
