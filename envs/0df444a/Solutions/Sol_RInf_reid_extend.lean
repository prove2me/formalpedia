-- Prove2me | solution 1 for RInf.reid_extend
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:11:01.709448+00:00
-- url     : https://prove2.me/submissions/2cda6a25-9b88-4e38-8650-d56eb5aa5ac5

import Mathlib
import Definitions.Def_RInf_alg
import Definitions.Def_RInf_braid
open RInf

abbrev g74p_H := Multiplicative (ℕ → ℤ)
abbrev g74p_G := Multiplicative (ℕ → ℚ)

noncomputable def g74p_inj : g74p_H →* g74p_G :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.compLeft (Int.castAddHom ℚ) ℕ)

theorem g74p_inj_apply (x : g74p_H) (n : ℕ) :
    Multiplicative.toAdd (g74p_inj x) n = ((Multiplicative.toAdd x n : ℤ) : ℚ) := rfl

theorem g74p_H_reid : ReidInf (MulEquiv.inv g74p_H).toMonoidHom := by
  refine ⟨fun i => Multiplicative.ofAdd (Pi.single i (1 : ℤ)), fun i j hij ⟨z, hz⟩ => ?_⟩
  have h := congrFun (congrArg Multiplicative.toAdd hz) i
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.inv_apply, inv_inv, toAdd_mul, toAdd_ofAdd,
    Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij] at h
  omega

theorem g74p_G_not (f : ℕ → g74p_G) :
    TwistedConj (MulEquiv.inv g74p_G).toMonoidHom (f 0) (f 1) := by
  refine ⟨Multiplicative.ofAdd ((Multiplicative.toAdd (f 0) - Multiplicative.toAdd (f 1)) / 2), ?_⟩
  apply Multiplicative.toAdd.injective
  funext t
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.inv_apply, inv_inv, toAdd_mul, toAdd_ofAdd,
    Pi.add_apply, Pi.div_apply, Pi.sub_apply, Pi.ofNat_apply]
  ring

theorem solution : ¬ (∀ {H G : Type} [Group H] [Group G]
    (inj : H →* G) (hinj : ∀ x y : H, inj x = inj y → x = y)
    (hnorm : ∀ (g : G) (x : H), ∃ y : H, inj y = g * inj x * g⁻¹)
    (α : G ≃* G) (β : H ≃* H) (hcomm : ∀ x : H, inj (β x) = α (inj x))
    (hβ : ReidInf β.toMonoidHom), ReidInf α.toMonoidHom) := by
  intro hall
  have := hall g74p_inj
    (fun x y hxy => by
      apply Multiplicative.toAdd.injective
      funext n
      have := congrFun (congrArg Multiplicative.toAdd hxy) n
      rw [g74p_inj_apply, g74p_inj_apply] at this
      exact_mod_cast this)
    (fun g x => ⟨x, by rw [mul_comm g, mul_inv_cancel_right]⟩)
    (MulEquiv.inv g74p_G) (MulEquiv.inv g74p_H)
    (fun x => by simp [map_inv])
    g74p_H_reid
  obtain ⟨f, hf⟩ := this
  exact hf 0 1 (by norm_num) (g74p_G_not f)
