-- Prove2me | solution 1 for RingHom.exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/abd56dfb-3660-55e6-9ec5-d86682bb49de

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow

set_option autoImplicit false

universe u

namespace AdicIso

open Ideal Ideal.Quotient AdicCompletion

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

theorem factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hle a

theorem exists_ringEquiv (e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
    (he : ∀ {m n : ℕ} (hle : m ≤ n) (x : R ⧸ I ^ n),
      e m (Ideal.Quotient.factorPow I hle x) = Ideal.Quotient.factorPow J hle (e n x)) :
    ∃ E : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ (n : ℕ) (x : AdicCompletion I R), AdicCompletion.evalₐ J n (E x) = e n (AdicCompletion.evalₐ I n x) := by
  have he' : ∀ {m n : ℕ} (hle : m ≤ n) (y : S ⧸ J ^ n),
      (e m).symm (Ideal.Quotient.factorPow J hle y) = Ideal.Quotient.factorPow I hle ((e n).symm y) := by
    intro m n hle y
    apply (e m).injective
    rw [RingEquiv.apply_symm_apply, he, RingEquiv.apply_symm_apply]
  let F : AdicCompletion I R →+* AdicCompletion J S :=
    AdicCompletion.liftRingHom J (fun n => (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom) (by
      intro m n hle
      ext x
      show Ideal.Quotient.factorPow J hle (e n (AdicCompletion.evalₐ I n x)) = e m (AdicCompletion.evalₐ I m x)
      rw [← he, factorPow_evalₐ])
  let G : AdicCompletion J S →+* AdicCompletion I R :=
    AdicCompletion.liftRingHom I (fun n => (e n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom) (by
      intro m n hle
      ext y
      show Ideal.Quotient.factorPow I hle ((e n).symm (AdicCompletion.evalₐ J n y)) =
        (e m).symm (AdicCompletion.evalₐ J m y)
      rw [← he', factorPow_evalₐ])
  have hF : ∀ n x, AdicCompletion.evalₐ J n (F x) = e n (AdicCompletion.evalₐ I n x) :=
    fun n x => AdicCompletion.evalₐ_liftRingHom J _ _ n x
  have hG : ∀ n y, AdicCompletion.evalₐ I n (G y) = (e n).symm (AdicCompletion.evalₐ J n y) :=
    fun n y => AdicCompletion.evalₐ_liftRingHom I _ _ n y
  refine ⟨RingEquiv.ofRingHom F G (RingHom.ext fun y => ?_) (RingHom.ext fun x => ?_), hF⟩
  · apply AdicCompletion.ext_evalₐ
    intro n
    rw [RingHom.comp_apply, hF, hG, RingEquiv.apply_symm_apply, RingHom.id_apply]
  · apply AdicCompletion.ext_evalₐ
    intro n
    rw [RingHom.comp_apply, hG, hF, RingEquiv.symm_apply_apply, RingHom.id_apply]

theorem apply_of_eq_of (e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n) (E : AdicCompletion I R ≃+* AdicCompletion J S)
    (hE : ∀ (n : ℕ) (x : AdicCompletion I R), AdicCompletion.evalₐ J n (E x) = e n (AdicCompletion.evalₐ I n x))
    (θ : R → S) (hθ : ∀ (n : ℕ) (r : R), e n (Ideal.Quotient.mk (I ^ n) r) = Ideal.Quotient.mk (J ^ n) (θ r)) (r : R) :
    E (AdicCompletion.of I R r) = AdicCompletion.of J S (θ r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [hE, AdicCompletion.evalₐ_of, hθ, AdicCompletion.evalₐ_of]

end AdicIso

open AdicIso in
theorem solution
    {B C : Type u} [CommRing B] [CommRing C] (θ : B →+* C) (hθ : Function.Surjective θ)
    (𝔪 : Ideal C) (hker : ∀ n : ℕ, RingHom.ker θ ≤ (Ideal.comap θ 𝔪) ^ n) :
    ∃ e : AdicCompletion (Ideal.comap θ 𝔪) B ≃+* AdicCompletion 𝔪 C,
      ∀ b : B, e (algebraMap B (AdicCompletion (Ideal.comap θ 𝔪) B) b) = algebraMap C (AdicCompletion 𝔪 C) (θ b) := by
  classical

  have hcomap : ∀ n : ℕ, Ideal.comap θ (𝔪 ^ n) = (Ideal.comap θ 𝔪) ^ n := by
    intro n
    have h1 : Ideal.map θ ((Ideal.comap θ 𝔪) ^ n) = 𝔪 ^ n := by
      rw [Ideal.map_pow, Ideal.map_comap_of_surjective θ hθ]
    rw [← h1, Ideal.comap_map_of_surjective θ hθ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr (hker n)
  have hker' : ∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk (𝔪 ^ n)).comp θ) = (Ideal.comap θ 𝔪) ^ n := by
    intro n
    rw [← RingHom.comap_ker, Ideal.mk_ker, hcomap]
  have hvan : ∀ (n : ℕ) (b : B), b ∈ (Ideal.comap θ 𝔪) ^ n → ((Ideal.Quotient.mk (𝔪 ^ n)).comp θ) b = 0 := by
    intro n b hb
    rw [← RingHom.mem_ker, hker']
    exact hb
  let g : ∀ n : ℕ, B ⧸ (Ideal.comap θ 𝔪) ^ n →+* C ⧸ 𝔪 ^ n := fun n =>
    Ideal.Quotient.lift ((Ideal.comap θ 𝔪) ^ n) ((Ideal.Quotient.mk (𝔪 ^ n)).comp θ) (hvan n)
  have hg : ∀ (n : ℕ) (b : B), g n (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk (𝔪 ^ n) (θ b) := fun n b => rfl
  let e : ∀ n : ℕ, B ⧸ (Ideal.comap θ 𝔪) ^ n ≃+* C ⧸ 𝔪 ^ n := fun n =>
    RingEquiv.ofBijective (g n)
      ⟨(Ideal.injective_lift_iff (hvan n)).mpr (hker' n),
        Ideal.Quotient.lift_surjective_of_surjective _ (hvan n)
          (Ideal.Quotient.mk_surjective.comp hθ)⟩
  have he_mk : ∀ (n : ℕ) (b : B), e n (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk (𝔪 ^ n) (θ b) := fun n b => rfl
  have he : ∀ {m n : ℕ} (hle : m ≤ n) (x : B ⧸ (Ideal.comap θ 𝔪) ^ n),
      e m (Ideal.Quotient.factorPow _ hle x) = Ideal.Quotient.factorPow 𝔪 hle (e n x) := by
    intro m n hle x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.factor_mk, he_mk, he_mk, Ideal.Quotient.factor_mk]
  obtain ⟨E, hE⟩ := exists_ringEquiv (Ideal.comap θ 𝔪) 𝔪 e he
  refine ⟨E, fun b => ?_⟩
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, Algebra.algebraMap_self,
    RingHom.id_apply, RingHom.id_apply]
  exact apply_of_eq_of _ _ e E hE θ he_mk b

end S_RingHom_exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow
end P2MW
export P2MW.S_RingHom_exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow (solution)
