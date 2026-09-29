-- Prove2me | solution 1 for Subring.exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/cf983ee9-b699-574c-98f5-67417571eb2c

import Mathlib
import Theorems.Thm_Ideal_exists_mem_forall_not_mem_of_forall_not_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subring_exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring

set_option autoImplicit false
set_option maxHeartbeats 0

open IsLocalRing

theorem solution
    {k K : Type} [Field k] [Field K] [Algebra k K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (V : ValuationSubring K) (hBV : ∀ f : K, f ∈ B → f ∈ V)
    (hp : ∃ (b : K) (hb : b ∈ B), b ≠ 0 ∧ (⟨b, hBV b hb⟩ : ↥V) ∈ maximalIdeal ↥V)
    (E : Finset (Subring K)) (hEloc : ∀ O ∈ E, IsLocalRing ↥O) (hBE : ∀ O ∈ E, ∀ f : K, f ∈ B → f ∈ O)
    (hEG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ O ∈ E, ∃ O' ∈ E, ∀ f : K, f ∈ O' ↔ σ f ∈ O)
    (hsep : ∀ (O : Subring K) (hO : O ∈ E), ∃ (b : K) (hb : b ∈ B),
      (⟨b, hBV b hb⟩ : ↥V) ∈ maximalIdeal ↥V ∧ IsUnit (⟨b, hBE O hO b hb⟩ : ↥O)) :
    ∃ f : K, (∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f) ∧ (∀ O ∈ E, f ∈ O) ∧ f ∉ V := by
  classical
  haveI := hGfin
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  haveI : IsDomain ↥B := inferInstance

  let toV : ↥B →+* ↥V :=
    { toFun := fun b => ⟨(b : K), hBV b b.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let toO : ∀ (O : Subring K), O ∈ E → (↥B →+* ↥O) := fun O hO =>
    { toFun := fun b => ⟨(b : K), hBE O hO b b.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }

  let J : Ideal ↥B := (maximalIdeal ↥V).comap toV
  let mO : {O // O ∈ E} → Ideal ↥B := fun O =>
    (@maximalIdeal ↥(O.1) _ (hEloc O.1 O.2)).comap (toO O.1 O.2)
  have hmOprime : ∀ O : {O // O ∈ E}, (mO O).IsPrime := by
    intro O
    haveI := hEloc O.1 O.2
    exact Ideal.comap_isPrime (toO O.1 O.2) (maximalIdeal ↥(O.1))
  have hmOmem : ∀ (O : {O // O ∈ E}) (b : ↥B), b ∈ mO O ↔ ¬ IsUnit (⟨(b : K), hBE O.1 O.2 b b.2⟩ : ↥(O.1)) := by
    intro O b
    haveI := hEloc O.1 O.2
    change (toO O.1 O.2 b) ∈ maximalIdeal ↥(O.1) ↔ _
    exact IsLocalRing.mem_maximalIdeal _

  let S : Finset (Ideal ↥B) := insert ⊥ (Finset.univ.image (fun O : {O // O ∈ E} => mO ⟨O.1, O.2⟩))
  have hSprime : ∀ P ∈ S, P.IsPrime := by
    intro P hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact Ideal.bot_prime
    · obtain ⟨O, -, rfl⟩ := Finset.mem_image.mp hP
      exact hmOprime _
  have hJ : ∀ P ∈ S, ¬ J ≤ P := by
    intro P hP hle
    rcases Finset.mem_insert.mp hP with rfl | hP
    · obtain ⟨b, hb, hb0, hbm⟩ := hp
      have : (⟨b, hb⟩ : ↥B) ∈ J := hbm
      have h0 := hle this
      rw [Ideal.mem_bot] at h0
      exact hb0 (congrArg Subtype.val h0)
    · obtain ⟨O, -, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨b, hb, hbm, hbu⟩ := hsep O.1 O.2
      have : (⟨b, hb⟩ : ↥B) ∈ J := hbm
      exact ((hmOmem _ _).mp (hle this)) hbu
  obtain ⟨b₀, hb₀J, hb₀S⟩ := Ideal.exists_mem_forall_not_mem_of_forall_not_le J S hSprime hJ
  have hb₀0 : (b₀ : K) ≠ 0 := by
    intro h
    apply hb₀S ⊥ (Finset.mem_insert_self _ _)
    rw [Ideal.mem_bot]; exact Subtype.ext h
  have hb₀u : ∀ (O : Subring K) (hO : O ∈ E), IsUnit (⟨(b₀ : K), hBE O hO b₀ b₀.2⟩ : ↥O) := by
    intro O hO
    have := hb₀S (mO ⟨O, hO⟩) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨O, hO⟩, Finset.mem_univ _, rfl⟩))
    rwa [hmOmem, not_not] at this

  let b : K := ∏ σ : ↥G, (σ : K ≃ₐ[k] K) (b₀ : K)
  have hbB : b ∈ B := prod_mem (fun σ _ => hBG σ σ.2 _ b₀.2)
  have hb0 : b ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun σ _ => by
    rw [map_ne_zero_iff _ (σ : K ≃ₐ[k] K).injective]; exact hb₀0)
  have hbinv : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ b = b := by
    intro τ hτ
    change τ (∏ σ : ↥G, (σ : K ≃ₐ[k] K) (b₀ : K)) = ∏ σ : ↥G, (σ : K ≃ₐ[k] K) (b₀ : K)
    rw [map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft ⟨τ, hτ⟩) _ _ (fun σ => rfl)

  have hbV : (⟨b, hBV b hbB⟩ : ↥V) ∈ maximalIdeal ↥V := by
    have hsplit : b = (b₀ : K) * ∏ σ ∈ (Finset.univ : Finset ↥G).erase 1, (σ : K ≃ₐ[k] K) (b₀ : K) := by
      change ∏ σ : ↥G, (σ : K ≃ₐ[k] K) (b₀ : K) = _
      rw [← Finset.mul_prod_erase Finset.univ (fun σ : ↥G => (σ : K ≃ₐ[k] K) (b₀ : K)) (Finset.mem_univ 1)]
      rfl
    have hrestB : (∏ σ ∈ (Finset.univ : Finset ↥G).erase 1, (σ : K ≃ₐ[k] K) (b₀ : K)) ∈ B :=
      prod_mem (fun σ _ => hBG σ σ.2 _ b₀.2)
    have : (⟨b, hBV b hbB⟩ : ↥V) = ⟨(b₀ : K), hBV _ b₀.2⟩ * ⟨_, hBV _ hrestB⟩ := Subtype.ext hsplit
    rw [this]
    exact Ideal.mul_mem_right _ _ hb₀J

  have hbu : ∀ (O : Subring K) (hO : O ∈ E), IsUnit (⟨b, hBE O hO b hbB⟩ : ↥O) := by
    intro O hO
    haveI := hEloc O hO
    by_contra hnu
    have hmem : (⟨b, hBE O hO b hbB⟩ : ↥O) ∈ maximalIdeal ↥O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hcoe : (⟨b, hBE O hO b hbB⟩ : ↥O) = ∏ σ : ↥G, (⟨(σ : K ≃ₐ[k] K) (b₀ : K), hBE O hO _ (hBG σ σ.2 _ b₀.2)⟩ : ↥O) := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_finsetProd]
    rw [hcoe, Ideal.IsPrime.prod_mem_iff] at hmem
    obtain ⟨σ, -, hσ⟩ := hmem
    apply (IsLocalRing.mem_maximalIdeal _).mp hσ

    obtain ⟨O', hO', hO'mem⟩ := hEG σ σ.2 O hO
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp (hb₀u O' hO')
    refine isUnit_iff_exists_inv.mpr ⟨⟨(σ : K ≃ₐ[k] K) (c : K), (hO'mem _).mp c.2⟩, Subtype.ext ?_⟩
    change (σ : K ≃ₐ[k] K) (b₀ : K) * (σ : K ≃ₐ[k] K) (c : K) = 1
    rw [← map_mul]
    have := congrArg Subtype.val hc
    change (b₀ : K) * (c : K) = 1 at this
    rw [this, map_one]

  refine ⟨b⁻¹, fun τ hτ => by rw [map_inv₀, hbinv τ hτ], fun O hO => ?_, fun hV => ?_⟩
  · obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp (hbu O hO)
    have hc' : b * (c : K) = 1 := by
      have := congrArg Subtype.val hc
      exact this
    rw [inv_eq_of_mul_eq_one_right hc']; exact c.2
  · have h1 : (⟨b, hBV b hbB⟩ : ↥V) * ⟨b⁻¹, hV⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hb0)
    exact (IsLocalRing.mem_maximalIdeal _).mp hbV (isUnit_iff_exists_inv.mpr ⟨_, h1⟩)

end S_Subring_exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring
end P2MW
export P2MW.S_Subring_exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring (solution)
