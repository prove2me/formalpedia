-- Prove2me | solution 1 for ValuationSubring.henselianLocalRing_comap_of_forall_comap_eq_imp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/37d75189-8824-5a5a-9b52-6189ba6310f2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_henselianLocalRing_comap_of_forall_comap_eq_imp_eq

set_option autoImplicit false

universe u

open Polynomial

namespace UEHAux

theorem exists_sub_mem_nonunits_of_prod_mem_nonunits {Ω : Type*} [Field Ω] (A : ValuationSubring Ω)
    (c : Ω) (hc : c ∈ A) (s : Multiset Ω) (hs : ∀ x ∈ s, x ∈ A)
    (h : (s.map (c - ·)).prod ∈ A.nonunits) : ∃ x ∈ s, c - x ∈ A.nonunits := by
  induction s using Multiset.induction_on with
  | empty =>
      exfalso
      rw [Multiset.map_zero, Multiset.prod_zero, ValuationSubring.mem_nonunits_iff, map_one] at h
      exact lt_irrefl _ h
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons] at h
      by_cases ha : c - a ∈ A.nonunits
      · exact ⟨a, Multiset.mem_cons_self _ _, ha⟩
      · have haA : c - a ∈ A := sub_mem hc (hs a (Multiset.mem_cons_self _ _))
        have h1 : A.valuation (c - a) = 1 :=
          le_antisymm ((A.valuation_le_one_iff _).mpr haA) (not_lt.mp (fun hlt => ha (A.mem_nonunits_iff.mpr hlt)))
        have hrest : (s.map (c - ·)).prod ∈ A.nonunits := by
          rw [ValuationSubring.mem_nonunits_iff, map_mul, h1, one_mul] at h
          exact A.mem_nonunits_iff.mpr h
        obtain ⟨x, hx, hxn⟩ := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx)) hrest
        exact ⟨x, Multiset.mem_cons_of_mem hx, hxn⟩

theorem mul_mem_nonunits_of_mem {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {x y : Ω}
    (hx : x ∈ A.nonunits) (hy : y ∈ A) : x * y ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [map_mul]
  calc A.valuation x * A.valuation y ≤ A.valuation x * 1 :=
        mul_le_mul_right ((A.valuation_le_one_iff _).mpr hy) _
    _ = A.valuation x := mul_one _
    _ < 1 := hx

theorem eval_derivative_eq_zero_of_sq_dvd {R : Type*} [CommRing R] {p : R[X]} {a : R}
    (h : (X - C a) ^ 2 ∣ p) : p.derivative.eval a = 0 := by
  obtain ⟨g, rfl⟩ := h
  simp [derivative_mul, derivative_pow]

end UEHAux

set_option maxHeartbeats 6400000 in
theorem solution
    {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (hAtop : A ≠ ⊤)
    (huniq : ∀ B : ValuationSubring Ω,
      B.comap (algebraMap K Ω) = A.comap (algebraMap K Ω) → B = A) :
    HenselianLocalRing ↥(A.comap (algebraMap K Ω)) := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI halg : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic

  have hιinj : Function.Injective (algebraMap K Ω) := (algebraMap K Ω).injective
  have hmemR : ∀ x : K, x ∈ A.comap (algebraMap K Ω) ↔ algebraMap K Ω x ∈ A := fun x => ValuationSubring.mem_comap
  have hnu : ∀ x : K, x ∈ (A.comap (algebraMap K Ω)).nonunits ↔ algebraMap K Ω x ∈ A.nonunits := by
    intro x
    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, hmemR, map_inv₀,
      map_eq_zero_iff _ hιinj]
  have hmaxR : ∀ r : ↥(A.comap (algebraMap K Ω)),
      r ∈ IsLocalRing.maximalIdeal ↥(A.comap (algebraMap K Ω)) ↔ algebraMap K Ω (r : K) ∈ A.nonunits := by
    intro r; rw [← ValuationSubring.coe_mem_nonunits_iff, hnu]

  let φA : ↥(A.comap (algebraMap K Ω)) →+* ↥A :=
    { toFun := fun r => ⟨algebraMap K Ω (r : K), (hmemR _).mp r.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let φ : ↥(A.comap (algebraMap K Ω)) →+* Ω := A.subtype.comp φA
  have hφ : ∀ r, φ r = algebraMap K Ω (r : K) := fun r => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    rw [hφ, hφ] at hab
    exact Subtype.ext (hιinj hab)
  refine { is_henselian := ?_ }
  intro f hf a₀ h₁ h₂

  set F : (Polynomial Ω) := f.map φ with hF
  have hFA : F = (f.map φA).map A.subtype := by rw [hF, Polynomial.map_map]
  have hFm : F.Monic := hf.map φ
  have hF0 : F ≠ 0 := hFm.ne_zero
  have hFs : F.Splits := IsAlgClosed.splits F
  have hrootA : ∀ α ∈ F.roots, α ∈ A := by
    intro α hα
    have hroot : F.eval α = 0 := (mem_roots hF0).mp hα
    have hint : IsIntegral ↥A α := by
      refine ⟨f.map φA, hf.map φA, ?_⟩
      rw [← eval_map]
      show ((f.map φA).map A.subtype).eval α = 0
      rw [← hFA]; exact hroot
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := Ω)).mp hint
    rw [← hy]; exact y.2

  set c : Ω := algebraMap K Ω (a₀ : K) with hc
  have hcA : c ∈ A := (hmemR _).mp a₀.2
  have hFc : F.eval c ∈ A.nonunits := by
    have : F.eval c = φ (f.eval a₀) := by rw [hF, hc, ← hφ, eval_map, eval₂_at_apply]
    rw [this, hφ]
    exact (hmaxR _).mp h₁

  obtain ⟨α, hαr, hα⟩ : ∃ α ∈ F.roots, c - α ∈ A.nonunits := by
    apply UEHAux.exists_sub_mem_nonunits_of_prod_mem_nonunits A c hcA F.roots hrootA
    rw [← hFs.eval_eq_prod_roots_of_monic hFm]; exact hFc
  have hαA : α ∈ A := hrootA α hαr

  have hder : F.derivative.eval α ∈ A ∧ F.derivative.eval α ∉ A.nonunits := by

    set G : (↥A)[X] := f.derivative.map φA with hG
    have hGeval : ∀ y : ↥A, ((G.eval y : ↥A) : Ω) = F.derivative.eval (y : Ω) := by
      intro y
      rw [hG, hF, derivative_map, ← Polynomial.map_map]
      show A.subtype ((f.derivative.map φA).eval y) = _
      rw [← eval₂_at_apply, ← eval_map]
      rfl
    have hunit₀ : IsUnit (G.eval (φA a₀)) := by
      rw [hG, eval_map, eval₂_at_apply]; exact h₂.map φA
    obtain ⟨t, ht⟩ := Polynomial.sub_dvd_eval_sub (⟨α, hαA⟩ : ↥A) (φA a₀) G
    have hm : (⟨α, hαA⟩ : ↥A) - φA a₀ ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      show α - c ∈ A.nonunits
      rw [← neg_sub]; exact A.nonunits.neg_mem hα
    have hunit : IsUnit (G.eval ⟨α, hαA⟩) := by
      by_contra hnu'
      have h1 : G.eval ⟨α, hαA⟩ ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hnu'
      have h2 : G.eval ⟨α, hαA⟩ - G.eval (φA a₀) ∈ IsLocalRing.maximalIdeal ↥A := by
        rw [ht]; exact Ideal.mul_mem_right _ _ hm
      have h3 : G.eval (φA a₀) ∈ IsLocalRing.maximalIdeal ↥A := by
        have := Ideal.sub_mem _ h1 h2
        rwa [sub_sub_cancel] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp h3 hunit₀
    refine ⟨?_, ?_⟩
    · rw [← hGeval ⟨α, hαA⟩]; exact (G.eval ⟨α, hαA⟩).2
    · rw [← hGeval ⟨α, hαA⟩, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun h => h hunit

  have huniqα : ∀ β ∈ F.roots, c - β ∈ A.nonunits → β = α := by
    intro β hβr hβ
    by_contra hne
    have hβe : β ∈ F.roots.erase α := (Multiset.mem_erase_of_ne hne).mpr hβr
    have hprod := hFs.eval_root_derivative hFm hαr
    have hfac : α - β ∈ (F.roots.erase α).map (α - ·) := Multiset.mem_map_of_mem _ hβe
    have hsplit := Multiset.prod_erase hfac
    have hαβ : α - β ∈ A.nonunits := by
      have : α - β = (c - β) - (c - α) := by ring
      rw [this]; exact A.nonunits.sub_mem hβ hα
    have hrestA : (((F.roots.erase α).map (α - ·)).erase (α - β)).prod ∈ A := by
      apply multiset_prod_mem
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_mem_erase hx)
      exact sub_mem hαA (hrootA y (Multiset.mem_of_mem_erase hy))
    apply hder.2
    rw [hprod, ← hsplit]
    exact UEHAux.mul_mem_nonunits_of_mem A hαβ hrestA

  have hσA : ∀ (σ : Ω ≃ₐ[K] Ω) (x : Ω), σ x ∈ A ↔ x ∈ A := by
    intro σ x
    have hB := huniq (A.comap (σ : Ω →+* Ω)) (by
      ext y
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, ValuationSubring.mem_comap]
      show σ (algebraMap K Ω y) ∈ A ↔ algebraMap K Ω y ∈ A
      rw [AlgEquiv.commutes])
    have := SetLike.ext_iff.mp hB x
    rwa [ValuationSubring.mem_comap] at this
  have hσnu : ∀ (σ : Ω ≃ₐ[K] Ω) (x : Ω), σ x ∈ A.nonunits ↔ x ∈ A.nonunits := by
    intro σ x
    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀, hσA,
      map_eq_zero_iff _ σ.injective]
  have hFσ : ∀ σ : Ω ≃ₐ[K] Ω, F.map (σ : Ω →+* Ω) = F := by
    intro σ
    rw [hF, Polynomial.map_map]
    congr 1
    ext r
    show σ (φ r) = φ r
    rw [hφ, AlgEquiv.commutes]
  have hfix : ∀ σ : Ω ≃ₐ[K] Ω, σ α = α := by
    intro σ
    apply huniqα
    · rw [mem_roots hF0, IsRoot, ← hFσ σ, eval_map]
      show eval₂ (σ : Ω →+* Ω) ((σ : Ω →+* Ω) α) F = 0
      rw [eval₂_at_apply]
      show σ (F.eval α) = 0
      rw [(mem_roots hF0).mp hαr, map_zero]
    · have : c - σ α = σ (c - α) := by rw [map_sub, hc, AlgEquiv.commutes]
      rw [this, hσnu]; exact hα

  have hαint : IsIntegral K α := (halg.isAlgebraic α).isIntegral
  set m := minpoly K α with hm
  set M : (Polynomial Ω) := m.map (algebraMap K Ω) with hM
  have hMm : M.Monic := (minpoly.monic hαint).map _
  have hMs : M.Splits := IsAlgClosed.splits M
  have hMroots : ∀ x ∈ M.roots, x = α := by
    intro x hx
    have hev : aeval x (minpoly K α) = 0 := by
      rw [aeval_def, ← eval_map]; exact (mem_roots hMm.ne_zero).mp hx
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (halg.isAlgebraic α) hev
    rw [← hσ, hfix σ]
  have hMeq : M = (X - C α) ^ M.natDegree := by
    conv_lhs => rw [hMs.eq_prod_roots_of_monic hMm]
    rw [(Multiset.eq_replicate (n := M.natDegree) (a := α)).mpr ⟨(hMs.natDegree_eq_card_roots).symm, hMroots⟩,
      Multiset.map_replicate, Multiset.prod_replicate]
  have hMdvd : M ∣ F := by
    have h1 : minpoly K α ∣ f.map (A.comap (algebraMap K Ω)).subtype := by
      apply minpoly.dvd
      rw [aeval_def, ← eval_map, Polynomial.map_map]
      show (f.map φ).eval α = 0
      exact (mem_roots hF0).mp hαr
    have h2 := Polynomial.map_dvd (algebraMap K Ω) h1
    rw [Polynomial.map_map] at h2
    exact h2
  have hdeg : m.natDegree = 1 := by
    have hpos : 0 < m.natDegree := minpoly.natDegree_pos hαint
    have hMdeg : M.natDegree = m.natDegree := (minpoly.monic hαint).natDegree_map _
    by_contra hne
    have h2 : 2 ≤ M.natDegree := by rw [hMdeg]; omega
    have hsq : (X - C α) ^ 2 ∣ F := (pow_dvd_pow _ h2).trans (hMeq ▸ hMdvd)
    exact hder.2 (by rw [UEHAux.eval_derivative_eq_zero_of_sq_dvd hsq]; exact A.nonunits.zero_mem)
  obtain ⟨k, hk⟩ := minpoly.natDegree_eq_one_iff.mp hdeg

  have hkR : k ∈ A.comap (algebraMap K Ω) := by rw [hmemR, hk]; exact hαA
  refine ⟨⟨k, hkR⟩, ?_, ?_⟩
  · apply hφinj
    rw [map_zero, ← eval₂_at_apply, ← eval_map]
    show F.eval (algebraMap K Ω k) = 0
    rw [hk]; exact (mem_roots hF0).mp hαr
  · rw [hmaxR]
    show algebraMap K Ω (k - (a₀ : K)) ∈ A.nonunits
    rw [map_sub, hk, ← hc, ← neg_sub]
    exact A.nonunits.neg_mem hα

end S_ValuationSubring_henselianLocalRing_comap_of_forall_comap_eq_imp_eq
end P2MW
export P2MW.S_ValuationSubring_henselianLocalRing_comap_of_forall_comap_eq_imp_eq (solution)
