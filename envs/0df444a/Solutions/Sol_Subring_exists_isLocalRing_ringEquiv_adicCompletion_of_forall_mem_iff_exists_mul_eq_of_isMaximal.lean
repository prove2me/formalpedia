-- Prove2me | solution 1 for Subring.exists_isLocalRing_ringEquiv_adicCompletion_of_forall_mem_iff_exists_mul_eq_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/946c823a-e782-5579-b4b9-88f674495c16

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subring_exists_isLocalRing_ringEquiv_adicCompletion_of_forall_mem_iff_exists_mul_eq_of_isMaximal

set_option autoImplicit false

open IsLocalRing

namespace Ws48LocSubring

section Generic

variable {B O : Type} [CommRing B] [CommRing O] (φ : B →+* O) (P : Ideal B) (m : Ideal O)
  (hle : ∀ n : ℕ, P ^ n ≤ (m ^ n).comap φ) (hge : ∀ n : ℕ, (m ^ n).comap φ ≤ P ^ n)
  (hsurj : ∀ (n : ℕ) (z : O), ∃ b : B, z - φ b ∈ m ^ n)

def levelMap (n : ℕ) : B ⧸ P ^ n →+* O ⧸ m ^ n := Ideal.quotientMap _ φ (hle n)

theorem levelMap_mk (n : ℕ) (b : B) : levelMap φ P m hle n (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (φ b) :=
  Ideal.quotientMap_mk

include hge in
theorem levelMap_injective (n : ℕ) : Function.Injective (levelMap φ P m hle n) :=
  Ideal.quotientMap_injective' (hge n)

include hsurj in
theorem levelMap_surjective (n : ℕ) : Function.Surjective (levelMap φ P m hle n) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, hb⟩ := hsurj n z
  refine ⟨Ideal.Quotient.mk _ b, ?_⟩
  rw [levelMap_mk, Ideal.Quotient.eq, ← neg_sub]
  exact (Ideal.neg_mem_iff _).2 hb

noncomputable def levelEquiv (n : ℕ) : (B ⧸ P ^ n) ≃+* (O ⧸ m ^ n) :=
  RingEquiv.ofBijective (levelMap φ P m hle n)
    ⟨levelMap_injective φ P m hle hge n, levelMap_surjective φ P m hle hsurj n⟩

theorem levelEquiv_mk (n : ℕ) (b : B) :
    levelEquiv φ P m hle hge hsurj n (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (φ b) :=
  levelMap_mk φ P m hle n b

theorem factorPow_levelEquiv {k n : ℕ} (hkn : k ≤ n) (x : B ⧸ P ^ n) :
    Ideal.Quotient.factorPow m hkn (levelEquiv φ P m hle hge hsurj n x) =
      levelEquiv φ P m hle hge hsurj k (Ideal.Quotient.factorPow P hkn x) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [levelEquiv_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, levelEquiv_mk]

theorem factorPow_levelEquiv_symm {k n : ℕ} (hkn : k ≤ n) (y : O ⧸ m ^ n) :
    Ideal.Quotient.factorPow P hkn ((levelEquiv φ P m hle hge hsurj n).symm y) =
      (levelEquiv φ P m hle hge hsurj k).symm (Ideal.Quotient.factorPow m hkn y) := by
  apply (levelEquiv φ P m hle hge hsurj k).injective
  rw [← factorPow_levelEquiv, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem factorPow_evalₐ {R : Type} [CommRing R] (I : Ideal R) {k n : ℕ} (hkn : k ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hkn (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x := by
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hkn f

noncomputable def fwdFamily (n : ℕ) : AdicCompletion P B →+* O ⧸ m ^ n :=
  (levelEquiv φ P m hle hge hsurj n).toRingHom.comp (AdicCompletion.evalₐ P n).toRingHom

theorem fwdFamily_apply (n : ℕ) (x : AdicCompletion P B) :
    fwdFamily φ P m hle hge hsurj n x = levelEquiv φ P m hle hge hsurj n (AdicCompletion.evalₐ P n x) := rfl

theorem fwd_compat {k n : ℕ} (hkn : k ≤ n) :
    (Ideal.Quotient.factorPow m hkn).comp (fwdFamily φ P m hle hge hsurj n) = fwdFamily φ P m hle hge hsurj k := by
  ext x
  rw [RingHom.comp_apply, fwdFamily_apply, fwdFamily_apply, factorPow_levelEquiv, factorPow_evalₐ]

noncomputable def fwd : AdicCompletion P B →+* AdicCompletion m O :=
  AdicCompletion.liftRingHom m (fwdFamily φ P m hle hge hsurj) (fun hkn => fwd_compat φ P m hle hge hsurj hkn)

theorem evalₐ_fwd (n : ℕ) (x : AdicCompletion P B) :
    AdicCompletion.evalₐ m n (fwd φ P m hle hge hsurj x) =
      levelEquiv φ P m hle hge hsurj n (AdicCompletion.evalₐ P n x) := by
  rw [fwd, AdicCompletion.evalₐ_liftRingHom, fwdFamily_apply]

noncomputable def bwdFamily (n : ℕ) : AdicCompletion m O →+* B ⧸ P ^ n :=
  (levelEquiv φ P m hle hge hsurj n).symm.toRingHom.comp (AdicCompletion.evalₐ m n).toRingHom

theorem bwdFamily_apply (n : ℕ) (y : AdicCompletion m O) :
    bwdFamily φ P m hle hge hsurj n y = (levelEquiv φ P m hle hge hsurj n).symm (AdicCompletion.evalₐ m n y) := rfl

theorem bwd_compat {k n : ℕ} (hkn : k ≤ n) :
    (Ideal.Quotient.factorPow P hkn).comp (bwdFamily φ P m hle hge hsurj n) = bwdFamily φ P m hle hge hsurj k := by
  ext y
  rw [RingHom.comp_apply, bwdFamily_apply, bwdFamily_apply, factorPow_levelEquiv_symm, factorPow_evalₐ]

noncomputable def bwd : AdicCompletion m O →+* AdicCompletion P B :=
  AdicCompletion.liftRingHom P (bwdFamily φ P m hle hge hsurj) (fun hkn => bwd_compat φ P m hle hge hsurj hkn)

theorem evalₐ_bwd (n : ℕ) (y : AdicCompletion m O) :
    AdicCompletion.evalₐ P n (bwd φ P m hle hge hsurj y) =
      (levelEquiv φ P m hle hge hsurj n).symm (AdicCompletion.evalₐ m n y) := by
  rw [bwd, AdicCompletion.evalₐ_liftRingHom, bwdFamily_apply]

theorem bwd_fwd (x : AdicCompletion P B) : bwd φ P m hle hge hsurj (fwd φ P m hle hge hsurj x) = x :=
  AdicCompletion.ext_evalₐ fun n => by rw [evalₐ_bwd, evalₐ_fwd, RingEquiv.symm_apply_apply]

theorem fwd_bwd (y : AdicCompletion m O) : fwd φ P m hle hge hsurj (bwd φ P m hle hge hsurj y) = y :=
  AdicCompletion.ext_evalₐ fun n => by rw [evalₐ_fwd, evalₐ_bwd, RingEquiv.apply_symm_apply]

noncomputable def complEquiv : AdicCompletion P B ≃+* AdicCompletion m O :=
  { toFun := fwd φ P m hle hge hsurj
    invFun := bwd φ P m hle hge hsurj
    left_inv := bwd_fwd φ P m hle hge hsurj
    right_inv := fwd_bwd φ P m hle hge hsurj
    map_mul' := (fwd φ P m hle hge hsurj).map_mul
    map_add' := (fwd φ P m hle hge hsurj).map_add }

theorem complEquiv_algebraMap (b : B) :
    complEquiv φ P m hle hge hsurj (algebraMap B (AdicCompletion P B) b) =
      algebraMap O (AdicCompletion m O) (φ b) := by
  show fwd φ P m hle hge hsurj _ = _
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_fwd]
  rw [show algebraMap B (AdicCompletion P B) b = AdicCompletion.of P B b from rfl,
    show algebraMap O (AdicCompletion m O) (φ b) = AdicCompletion.of m O (φ b) from rfl,
    AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, levelEquiv_mk]

end Generic

section Loc

variable {B : Type} [CommRing B] (P : Ideal B) (hP : P.IsMaximal)

include hP in

theorem exists_mul_sub_one_mem_pow {h : B} (hh : h ∉ P) (n : ℕ) : ∃ t : B, h * t - 1 ∈ P ^ n := by
  have hsup : P ⊔ Ideal.span {h} = ⊤ := by
    refine hP.1.2 _ ?_
    refine lt_of_le_of_ne le_sup_left fun heq => hh ?_
    rw [heq]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self h)
  have htop : P ^ n ⊔ Ideal.span {h} = ⊤ := Ideal.pow_sup_eq_top hsup
  have h1 : (1 : B) ∈ P ^ n ⊔ Ideal.span {h} := htop ▸ Submodule.mem_top
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 h1
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  refine ⟨t, ?_⟩
  have : h * t - 1 = -a := by rw [← hac]; ring
  rw [this]
  exact (P ^ n).neg_mem ha

end Loc

end Ws48LocSubring

open Ws48LocSubring in
theorem solution
    (K : Type) [Field K] (B : Subring K) (P : Ideal ↥B) (hP : P.IsMaximal)
    (O : Subring K)
    (hO : ∀ f : K, f ∈ O ↔ ∃ g h : ↥B, h ∉ P ∧ f * (h : K) = (g : K)) :
    ∃ (hBO : ∀ b : ↥B, (b : K) ∈ O) (_ : IsLocalRing ↥O),
      (∀ b : ↥B, (⟨(b : K), hBO b⟩ : ↥O) ∈ maximalIdeal ↥O ↔ b ∈ P) ∧
      (IsNoetherianRing ↥B → IsNoetherianRing ↥O) ∧
      (∀ (f : K) (hf : f ∈ O), ∃ (g h : ↥B), h ∉ P ∧ (⟨f, hf⟩ : ↥O) * ⟨(h : K), hBO h⟩ = ⟨(g : K), hBO g⟩) ∧
      ∃ T : AdicCompletion P ↥B ≃+* AdicCompletion (maximalIdeal ↥O) ↥O,
        ∀ b : ↥B, T (algebraMap ↥B (AdicCompletion P ↥B) b) =
          algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨(b : K), hBO b⟩ := by
  classical

  have hP1 : (1 : ↥B) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hBO : ∀ b : ↥B, (b : K) ∈ O := fun b => (hO b).2 ⟨b, 1, hP1, by simp⟩
  have hle' : B ≤ O := fun x hx => hBO ⟨x, hx⟩
  set φ : ↥B →+* ↥O := Subring.inclusion hle' with hφ
  have hφ_apply : ∀ b : ↥B, φ b = ⟨(b : K), hBO b⟩ := fun b => rfl
  have hφ_inj : Function.Injective φ := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  letI : Algebra ↥B ↥O := φ.toAlgebra
  have halg : ∀ b : ↥B, algebraMap ↥B ↥O b = φ b := fun b => rfl

  haveI hprime : P.IsPrime := hP.isPrime
  haveI hloc : IsLocalization.AtPrime ↥O P := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      have hy' : (y : ↥B) ∉ P := hy
      have hy0 : ((y : ↥B) : K) ≠ 0 := by
        intro h0
        apply hy'
        have : (y : ↥B) = 0 := Subtype.ext h0
        rw [this]; exact P.zero_mem
      have hinv : ((y : ↥B) : K)⁻¹ ∈ O := (hO _).2 ⟨1, y, hy', by rw [inv_mul_cancel₀ hy0]; simp⟩
      refine isUnit_iff_exists_inv.2 ⟨⟨((y : ↥B) : K)⁻¹, hinv⟩, ?_⟩
      rw [halg]
      exact Subtype.ext (mul_inv_cancel₀ hy0)
    · intro z
      obtain ⟨g, h, hh, hz⟩ := (hO z).1 z.2
      refine ⟨(g, ⟨h, hh⟩), ?_⟩
      rw [halg, halg]
      exact Subtype.ext hz
    · intro a b hab
      refine ⟨1, ?_⟩
      rw [halg, halg] at hab
      rw [hφ_inj hab]
  haveI hlocal : IsLocalRing ↥O := IsLocalization.AtPrime.isLocalRing ↥O P
  have hcomap : (maximalIdeal ↥O).comap (algebraMap ↥B ↥O) = P := IsLocalization.AtPrime.comap_maximalIdeal ↥O P
  have hmap : Ideal.map (algebraMap ↥B ↥O) P = maximalIdeal ↥O := IsLocalization.AtPrime.map_eq_maximalIdeal P ↥O
  have hmem : ∀ b : ↥B, φ b ∈ maximalIdeal ↥O ↔ b ∈ P := fun b => by
    rw [← hcomap, Ideal.mem_comap, halg]

  have hle : ∀ n : ℕ, P ^ n ≤ (maximalIdeal ↥O ^ n).comap φ := fun n => by
    rw [← hcomap]
    exact Ideal.le_comap_pow _ n
  have hge : ∀ n : ℕ, (maximalIdeal ↥O ^ n).comap φ ≤ P ^ n := fun n b hb => by
    rw [Ideal.mem_comap, ← hmap, ← Ideal.map_pow] at hb
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl ↥O).1 hb
    simp only [halg] at h
    have hbs : b * s = a := by
      apply hφ_inj
      rw [map_mul]
      exact h
    have hs' : s ∉ P := hs
    obtain ⟨t, ht⟩ := exists_mul_sub_one_mem_pow P hP hs' n
    have : b = b * s * t - b * (s * t - 1) := by ring
    rw [this]
    refine (P ^ n).sub_mem ?_ (Ideal.mul_mem_left _ _ ht)
    rw [hbs]
    exact Ideal.mul_mem_right _ _ ha
  have hsurj : ∀ (n : ℕ) (z : ↥O), ∃ b : ↥B, z - φ b ∈ maximalIdeal ↥O ^ n := fun n z => by
    obtain ⟨g, h, hh, hz⟩ := (hO z).1 z.2
    obtain ⟨t, ht⟩ := exists_mul_sub_one_mem_pow P hP hh n
    refine ⟨g * t, ?_⟩
    have hzφ : z * φ h = φ g := Subtype.ext hz
    have : z - φ (g * t) = -(z * φ (h * t - 1)) := by
      rw [map_mul, map_sub, map_mul, map_one, ← hzφ]; ring
    rw [this]
    refine (maximalIdeal ↥O ^ n).neg_mem (Ideal.mul_mem_left _ _ ?_)
    rw [← hmap, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ht
  refine ⟨hBO, hlocal, fun b => (hmem b), fun hN => IsLocalization.isNoetherianRing P.primeCompl ↥O hN,
    fun f hf => ?_, complEquiv φ P (maximalIdeal ↥O) hle hge hsurj, fun b => ?_⟩
  · obtain ⟨g, h, hh, hz⟩ := (hO f).1 hf
    exact ⟨g, h, hh, Subtype.ext hz⟩
  · exact complEquiv_algebraMap φ P (maximalIdeal ↥O) hle hge hsurj b

end S_Subring_exists_isLocalRing_ringEquiv_adicCompletion_of_forall_mem_iff_exists_mul_eq_of_isMaximal
end P2MW
export P2MW.S_Subring_exists_isLocalRing_ringEquiv_adicCompletion_of_forall_mem_iff_exists_mul_eq_of_isMaximal (solution)
