-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P21.corner_extremal_submodules
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:56:08.821878+00:00
-- url     : https://prove2.me/submissions/ce9455b1-41f6-4f13-8fff-3d3d8d90411d

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P21
open QAlgorithms.Papers.Independent.Renew46.P21

universe u v w

theorem solution {K : Type u} {A : Type v} {M : Type w}
    [CommRing K] [NonUnitalRing A] [Module K A] [AddCommGroup M] [Module K M]
    (hleft : ∀ (k : K) (a b : A), (k • a) * b = k • (a * b))
    (hright : ∀ (k : K) (a b : A), a * (k • b) = k • (a * b))
    (rho : RightAlgebraAction K A M) (e : A) (he : e * e = e) :
    AlgebraInvariant rho (cornerAnnihilator rho e) ∧
    (∀ m : M, m ∈ cornerAnnihilator rho e ↔ ∀ a : A, rho.act (a * e) m = 0) ∧
    (∀ m ∈ cornerAnnihilator rho e, rho.act e m = 0) ∧
    (∀ U : Submodule K M, AlgebraInvariant rho U →
      (∀ m ∈ U, rho.act e m = 0) → U ≤ cornerAnnihilator rho e) ∧
    AlgebraInvariant rho (cornerGenerated rho e) ∧
    rho.act e '' (cornerGenerated rho e : Set M) = Set.range (rho.act e) ∧
    (∀ U : Submodule K M, AlgebraInvariant rho U →
      rho.act e '' (U : Set M) = Set.range (rho.act e) → cornerGenerated rho e ≤ U) ∧
    (∀ (P : Type w) [AddCommGroup P] [Module K P]
      (sigma : RightAlgebraAction K A P) (f : M →ₗ[K] P),
      (∀ (a : A) (m : M), f (rho.act a m) = sigma.act a (f m)) →
      (∀ m ∈ cornerAnnihilator rho e, f m ∈ cornerAnnihilator sigma e) ∧
      (∀ m ∈ cornerGenerated rho e, f m ∈ cornerGenerated sigma e)) := by
  have memN : ∀ m : M, m ∈ cornerAnnihilator rho e ↔ ∀ a : A, rho.act (a * e) m = 0 := by
    intro m
    simp [cornerAnnihilator, Submodule.mem_iInf, LinearMap.mem_ker]
  have memNs : ∀ {P : Type w} [AddCommGroup P] [Module K P] (sigma : RightAlgebraAction K A P)
      (m : P), m ∈ cornerAnnihilator sigma e ↔ ∀ a : A, sigma.act (a * e) m = 0 := by
    intro P _ _ sigma m
    simp [cornerAnnihilator, Submodule.mem_iInf, LinearMap.mem_ker]
  have genL : ∀ (a : A) (m : M), rho.act a (rho.act e m) ∈ cornerGenerated rho e := fun a m =>
    Submodule.subset_span ⟨(m, a), rfl⟩
  have invL : AlgebraInvariant rho (cornerGenerated rho e) := by
    intro b m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨m', a⟩, rfl⟩ := hx
      simp only
      rw [← rho.mul_apply]
      exact genL _ _
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  refine ⟨?_, memN, ?_, ?_, invL, ?_, ?_, ?_⟩
  · intro b m hm
    rw [memN] at hm ⊢
    intro a
    rw [← rho.mul_apply, ← mul_assoc]
    exact hm _
  · intro m hm
    have := (memN m).1 hm e
    rwa [he] at this
  · intro U hU hk m hm
    rw [memN]
    intro a
    rw [rho.mul_apply]
    exact hk _ (hU a m hm)
  · ext x
    constructor
    · rintro ⟨y, _, rfl⟩; exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨rho.act e y, ?_, ?_⟩
      · have h1 := genL e y
        rw [← rho.mul_apply, he] at h1
        exact h1
      · rw [← rho.mul_apply, he]
  · intro U hU hrange
    rw [cornerGenerated, Submodule.span_le]
    rintro _ ⟨⟨m, a⟩, rfl⟩
    have : rho.act e m ∈ rho.act e '' (U : Set M) := by rw [hrange]; exact ⟨m, rfl⟩
    obtain ⟨u, hu, hue⟩ := this
    simp only
    rw [← hue]
    exact hU a _ (hU e u hu)
  · intro P _ _ sigma f hf
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [memNs]
      intro a
      rw [← hf, (memN m).1 hm a, map_zero]
    · intro m hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨m', a⟩, rfl⟩ := hx
        simp only
        rw [hf, hf]
        exact Submodule.subset_span ⟨(f m', a), rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
