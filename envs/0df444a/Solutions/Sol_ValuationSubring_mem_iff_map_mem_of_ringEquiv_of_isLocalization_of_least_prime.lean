-- Prove2me | solution 1 for ValuationSubring.mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/077f113d-00c0-5dc5-bb74-7f71135b94bb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime

set_option autoImplicit false

namespace IValAux

theorem map_mem_maximalIdeal
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (C B : Subalgebra R K) (hCB : C ≤ B) (W : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (y : Ideal ↥C) (ϖ : R) (hϖy : algebraMap R ↥C ϖ ∈ y)
    (hcen : ∀ b : ↥C, b ∈ y ↔ ∃ hb : (b : K) ∈ W, (⟨(b : K), hb⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W)
    (hleast : ∀ Q : Ideal ↥B, Q.IsPrime → algebraMap R ↥B ϖ ∈ Q →
      (∀ b : ↥C, (⟨(b : K), hCB b.2⟩ : ↥B) ∈ Q ↔ b ∈ y) →
      ∀ b : ↥B, (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W → b ∈ Q)
    (ρ : K ≃+* K)
    (hC : ∀ a : K, a ∈ C → ρ a ∈ C)
    (hB : ∀ f : K, f ∈ B → ρ f ∈ B)
    (hy : ∀ (b : ↥C) (hb : ρ (b : K) ∈ C), b ∈ y ↔ (⟨ρ (b : K), hb⟩ : ↥C) ∈ y)
    (b : ↥B) (hb : (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W) :
    (⟨ρ (b : K), hBW _ (hB _ b.2)⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W := by
  classical

  let φ : ↥B →+* ↥W :=
    { toFun := fun b => ⟨ρ (b : K), hBW _ (hB _ b.2)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hφ : ∀ b : ↥B, (φ b : ↥W) = ⟨ρ (b : K), hBW _ (hB _ b.2)⟩ := fun _ => rfl
  let Q : Ideal ↥B := Ideal.comap φ (IsLocalRing.maximalIdeal ↥W)
  have hQp : Q.IsPrime := Ideal.comap_isPrime φ _
  have hϖQ : algebraMap R ↥B ϖ ∈ Q := by
    rw [Ideal.mem_comap, hφ]
    have h1 : ρ ((algebraMap R ↥C ϖ : ↥C) : K) ∈ C := hC _ (algebraMap R ↥C ϖ).2
    have h2 := (hy (algebraMap R ↥C ϖ) h1).mp hϖy
    obtain ⟨hb', hm⟩ := (hcen _).mp h2
    have hcoe : ((algebraMap R ↥B ϖ : ↥B) : K) = ((algebraMap R ↥C ϖ : ↥C) : K) := by
      simp [Subalgebra.algebraMap_eq]
    convert hm using 2
    rfl
  have hQC : ∀ b : ↥C, (⟨(b : K), hCB b.2⟩ : ↥B) ∈ Q ↔ b ∈ y := by
    intro b
    rw [Ideal.mem_comap, hφ]
    have h1 : ρ (b : K) ∈ C := hC _ b.2
    rw [hy b h1, hcen ⟨ρ (b : K), h1⟩]
    constructor
    · intro hm; exact ⟨_, hm⟩
    · rintro ⟨_, hm⟩; exact hm
  have := hleast Q hQp hϖQ hQC b hb
  rw [Ideal.mem_comap, hφ] at this
  exact this

theorem mem_of_mem
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (C B : Subalgebra R K) (hCB : C ≤ B) (W : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (y : Ideal ↥C) (ϖ : R) (hϖy : algebraMap R ↥C ϖ ∈ y)
    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : K), hBW _ h.2⟩ : ↥W) ∉ IsLocalRing.maximalIdeal ↥W ∧ f * (h : K) = (g : K))
    (hcen : ∀ b : ↥C, b ∈ y ↔ ∃ hb : (b : K) ∈ W, (⟨(b : K), hb⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W)
    (hleast : ∀ Q : Ideal ↥B, Q.IsPrime → algebraMap R ↥B ϖ ∈ Q →
      (∀ b : ↥C, (⟨(b : K), hCB b.2⟩ : ↥B) ∈ Q ↔ b ∈ y) →
      ∀ b : ↥B, (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W → b ∈ Q)
    (ρ : K ≃+* K)
    (hC : ∀ a : K, a ∈ C → ρ a ∈ C) (hC' : ∀ a : K, a ∈ C → ρ.symm a ∈ C)
    (hB : ∀ f : K, f ∈ B → ρ f ∈ B) (hB' : ∀ f : K, f ∈ B → ρ.symm f ∈ B)
    (hy : ∀ (b : ↥C) (hb : ρ (b : K) ∈ C), b ∈ y ↔ (⟨ρ (b : K), hb⟩ : ↥C) ∈ y)
    (f : K) (hf : f ∈ W) : ρ f ∈ W := by
  classical

  have hy' : ∀ (b : ↥C) (hb : ρ.symm (b : K) ∈ C), b ∈ y ↔ (⟨ρ.symm (b : K), hb⟩ : ↥C) ∈ y := by
    intro b hb
    have h1 : ρ ((⟨ρ.symm (b : K), hb⟩ : ↥C) : K) ∈ C := by simp
    have h2 := hy ⟨ρ.symm (b : K), hb⟩ h1
    have h3 : (⟨ρ ((⟨ρ.symm (b : K), hb⟩ : ↥C) : K), h1⟩ : ↥C) = b := by ext; simp
    rw [h3] at h2
    exact h2.symm
  obtain ⟨g, h, hh, hfh⟩ := (hloc f).mp hf
  refine (hloc (ρ f)).mpr ⟨⟨ρ (g : K), hB _ g.2⟩, ⟨ρ (h : K), hB _ h.2⟩, ?_, ?_⟩
  · intro hm
    have := map_mem_maximalIdeal C B hCB W hBW y ϖ hϖy hcen hleast ρ.symm hC' hB' hy' ⟨ρ (h : K), hB _ h.2⟩ hm
    apply hh
    convert this using 2
    simp
  · simp only
    rw [← map_mul, hfh]

end IValAux

theorem solution
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (C B : Subalgebra R K) (hCB : C ≤ B) (W : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (y : Ideal ↥C) (ϖ : R) (hϖy : algebraMap R ↥C ϖ ∈ y)

    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : K), hBW _ h.2⟩ : ↥W) ∉ IsLocalRing.maximalIdeal ↥W ∧ f * (h : K) = (g : K))

    (hcen : ∀ b : ↥C, b ∈ y ↔ ∃ hb : (b : K) ∈ W, (⟨(b : K), hb⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W)

    (hleast : ∀ Q : Ideal ↥B, Q.IsPrime → algebraMap R ↥B ϖ ∈ Q →
      (∀ b : ↥C, (⟨(b : K), hCB b.2⟩ : ↥B) ∈ Q ↔ b ∈ y) →
      ∀ b : ↥B, (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W → b ∈ Q)

    (τ : K ≃+* K)
    (hC : ∀ a : K, a ∈ C → τ a ∈ C) (hC' : ∀ a : K, a ∈ C → τ.symm a ∈ C)
    (hB : ∀ f : K, f ∈ B → τ f ∈ B) (hB' : ∀ f : K, f ∈ B → τ.symm f ∈ B)
    (hy : ∀ (b : ↥C) (hb : τ (b : K) ∈ C), b ∈ y ↔ (⟨τ (b : K), hb⟩ : ↥C) ∈ y) :
    ∀ f : K, f ∈ W ↔ τ f ∈ W := by
  intro f
  constructor
  · exact IValAux.mem_of_mem C B hCB W hBW y ϖ hϖy hloc hcen hleast τ hC hC' hB hB' hy f
  · intro hf
    have hy' : ∀ (b : ↥C) (hb : τ.symm (b : K) ∈ C), b ∈ y ↔ (⟨τ.symm (b : K), hb⟩ : ↥C) ∈ y := by
      intro b hb
      have h1 : τ ((⟨τ.symm (b : K), hb⟩ : ↥C) : K) ∈ C := by simp
      have h2 := hy ⟨τ.symm (b : K), hb⟩ h1
      have h3 : (⟨τ ((⟨τ.symm (b : K), hb⟩ : ↥C) : K), h1⟩ : ↥C) = b := by ext; simp
      rw [h3] at h2
      exact h2.symm
    have := IValAux.mem_of_mem C B hCB W hBW y ϖ hϖy hloc hcen hleast τ.symm hC' (by simpa using hC) hB' (by simpa using hB) hy' (τ f) hf
    simpa using this

end S_ValuationSubring_mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime
end P2MW
export P2MW.S_ValuationSubring_mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime (solution)
