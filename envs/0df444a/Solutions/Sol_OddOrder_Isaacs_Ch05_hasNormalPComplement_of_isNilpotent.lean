-- Prove2me | solution 1 for OddOrder.Isaacs.Ch05.hasNormalPComplement_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:30:04.13212+00:00
-- url     : https://prove2.me/submissions/b84a01b9-5db1-4bd6-beef-bc2f849c36f2

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch05_Transfer/NilpotentPComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Mathlib.GroupTheory.Nilpotent

-- ===== OddOrder/Isaacs/Ch05_Transfer/NilpotentPComplement.lean =====
namespace OddOrder.Isaacs.Ch05

open scoped Pointwise

section

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]

/-- A finite group with `p ∤ |H|` has a (trivial) normal `p`-complement: `⊤`. -/
theorem hasNormalPComplement_of_not_dvd_card (hnd : ¬ p ∣ Nat.card H) :
    HasNormalPComplement p H := by
  refine ⟨⊤, inferInstance, fun P => ?_⟩
  have hP_bot : (P : Subgroup H) = ⊥ := by
    have hcard := P.card_eq_multiplicity
    rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero] at hcard
    exact Subgroup.card_eq_one.mp hcard
  rw [hP_bot]
  exact Subgroup.isComplement'_top_left.mpr rfl

/-- **A finite nilpotent group has a normal `p`-complement for every prime `p`**
(Isaacs p. 196, used in the proof of Thm 6.24).

The complement is the kernel of the projection of the Sylow direct-product decomposition
(`Sylow.directProductOfNormal`) onto the `p`-component. -/
theorem _root_.solution [Group.IsNilpotent H] :
    HasNormalPComplement p H := by
  classical
  by_cases hpH : p ∣ Nat.card H
  swap
  · exact hasNormalPComplement_of_not_dvd_card hpH
  have hcard_ne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hp_mem : p ∈ (Nat.card H).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp.out, hpH, hcard_ne⟩
  let e := Sylow.directProductOfNormal (G := H) fun {q} _ Q => inferInstance
  set P : Sylow p H := default with hP_def
  let π₁ : (∀ q : (Nat.card H).primeFactors, ∀ Q : Sylow (q : ℕ) H, ↥(Q : Subgroup H)) →*
      (∀ Q : Sylow p H, ↥(Q : Subgroup H)) :=
    Pi.evalMonoidHom (fun q : (Nat.card H).primeFactors =>
      ∀ Q : Sylow (q : ℕ) H, ↥(Q : Subgroup H)) ⟨p, hp_mem⟩
  let π₂ : (∀ Q : Sylow p H, ↥(Q : Subgroup H)) →* ↥(P : Subgroup H) :=
    Pi.evalMonoidHom (fun Q : Sylow p H => ↥(Q : Subgroup H)) P
  let f : H →* ↥(P : Subgroup H) := (π₂.comp π₁).comp e.symm.toMonoidHom
  -- `f` is surjective (hit `y` from `e (mulSingle (mulSingle y))`)
  have hf_surj : Function.Surjective f := by
    intro y
    set v₂ : ∀ Q : Sylow p H, ↥(Q : Subgroup H) := Pi.mulSingle P y with hv₂
    set v₁ : ∀ q : (Nat.card H).primeFactors, ∀ Q : Sylow (q : ℕ) H, ↥(Q : Subgroup H) :=
      Pi.mulSingle ⟨p, hp_mem⟩ v₂ with hv₁
    refine ⟨e v₁, ?_⟩
    change π₂ (π₁ (e.symm (e v₁))) = y
    rw [MulEquiv.symm_apply_apply]
    change v₁ ⟨p, hp_mem⟩ P = y
    rw [hv₁, Pi.mulSingle_eq_same, hv₂, Pi.mulSingle_eq_same]
  -- the kernel of `f` complements the (unique) Sylow `p`-subgroup
  refine ⟨f.ker, inferInstance, fun Q => ?_⟩
  have : Subsingleton (Sylow p H) := by
    have := Sylow.unique_of_normal P inferInstance
    infer_instance
  rw [Subsingleton.elim Q P]
  -- coprime cardinalities: `[H : ker f] = |P|` is the full `p`-part
  have hindex : (f.ker).index = Nat.card ↥(P : Subgroup H) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf_surj]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hmul : Nat.card f.ker * Nat.card ↥(P : Subgroup H) = Nat.card H := by
    rw [← hindex]
    exact Subgroup.card_mul_index (H := f.ker)
  have hnd : ¬ p ∣ Nat.card f.ker := by
    intro hdvd
    have hpow : p ^ ((Nat.card H).factorization p + 1) ∣ Nat.card H := by
      conv_rhs => rw [← hmul, P.card_eq_multiplicity]
      rw [pow_succ, mul_comm (p ^ _) p]
      exact mul_dvd_mul hdvd dvd_rfl
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp.out hcard_ne).mp hpow
    omega
  refine Subgroup.isComplement'_of_coprime hmul ?_
  rw [P.card_eq_multiplicity]
  exact Nat.Coprime.pow_right _ ((hp.out.coprime_iff_not_dvd.mpr hnd).symm)

end

end OddOrder.Isaacs.Ch05
