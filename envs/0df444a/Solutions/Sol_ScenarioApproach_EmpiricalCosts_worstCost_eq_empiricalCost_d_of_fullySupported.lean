-- Prove2me | solution 1 for ScenarioApproach.EmpiricalCosts.worstCost_eq_empiricalCost_d_of_fullySupported
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:10:51.853584+00:00
-- url     : https://prove2.me/submissions/70320a0e-8c08-4d50-8c11-3b034c6b355b

import Mathlib
import Definitions.Def_ScenarioApproach_EmpiricalCosts_scenarioProgram
import Definitions.Def_ScenarioApproach_EmpiricalCosts_empiricalCost
import Definitions.Def_ScenarioApproach_EmpiricalCosts_supportConstraint



namespace ScenarioApproach.EmpiricalCosts

lemma fs_le_sup {m : ℕ} (c : Fin m → ℝ) (i : Fin m) : c i ≤ ⨆ j, c j :=
  le_ciSup (Set.finite_range c).bddAbove i

lemma fs_active {n m : ℕ} {Δ : Type*} (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    (hconv : ∀ δ, ConvexOn ℝ Set.univ fun ν => ℓ ν δ) (hm : 1 ≤ m)
    (ω : Fin m → Δ) (ν : EuclideanSpace ℝ (Fin n)) (hν : IsSolution ℓ ω ν) (i : Fin m)
    (hi : IsSupportConstraint ℓ ω ν i) : ℓ ν (ω i) = worstCost ℓ ω ν := by
  have hle : ℓ ν (ω i) ≤ worstCost ℓ ω ν := fs_le_sup (fun j => ℓ ν (ω j)) i
  refine le_antisymm hle ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨ν', t, ht, htW⟩ := hi
  set W := worstCost ℓ ω ν with hW
  set a := ℓ ν (ω i)
  set b := ℓ ν' (ω i)
  set lam := (W - a) / (W - a + |b - a| + 1) with hlam
  have hden : 0 < W - a + |b - a| + 1 := by have := abs_nonneg (b - a); linarith
  have hlam0 : 0 < lam := div_pos (by linarith) hden
  have hlam1 : lam < 1 := by
    rw [hlam, div_lt_one hden]; have := abs_nonneg (b - a); linarith
  have hkey : lam * (b - a) < W - a := by
    have h1 : lam * (b - a) ≤ lam * |b - a| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hlam0.le
    have h2 : lam * (W - a + |b - a| + 1) = W - a := by
      rw [hlam]; field_simp
    nlinarith
  set νl := (1 - lam) • ν + lam • ν'
  have hall : ∀ j, ℓ νl (ω j) < W := by
    intro j
    have hc := (hconv (ω j)).2 (Set.mem_univ ν) (Set.mem_univ ν') (by linarith : (0:ℝ) ≤ 1 - lam)
      hlam0.le (by ring)
    simp only [smul_eq_mul] at hc
    by_cases hj : j = i
    · subst hj
      have : (1 - lam) * a + lam * b < W := by nlinarith
      linarith
    · have h1 := ht j hj
      have h2 : ℓ ν (ω j) ≤ W := fs_le_sup (fun j => ℓ ν (ω j)) j
      have : (1 - lam) * ℓ ν (ω j) + lam * ℓ ν' (ω j) < W := by nlinarith
      linarith
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨j0, hj0⟩ := exists_eq_ciSup_of_finite (f := fun j => ℓ νl (ω j))
  have h3 : W ≤ worstCost ℓ ω νl := hν νl
  have h4 : worstCost ℓ ω νl = ℓ νl (ω j0) := hj0.symm
  linarith [hall j0]

lemma fs_kth {m : ℕ} (c : Fin m → ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ m)
    (hcard : k ≤ (Finset.univ.filter fun i => c i = ⨆ j, c j).card) :
    kthLargest c k = ⨆ j, c j := by
  unfold kthLargest
  rw [dif_pos ⟨hk1, hkm⟩]
  set p : Fin m := ⟨m - k, by omega⟩ with hp
  refine le_antisymm (fs_le_sup c _) ?_
  by_contra hlt
  push_neg at hlt
  have hmono := Tuple.monotone_sort c
  set σ := Tuple.sort c
  have hinj : Set.InjOn (fun i => σ.symm i)
      ↑(Finset.univ.filter fun i => c i = ⨆ j, c j) := by
    intro x _ y _ h; exact σ.symm.injective h
  have hmaps : ∀ x ∈ (Finset.univ.filter fun i => c i = ⨆ j, c j),
      (fun i => σ.symm i) x ∈ Finset.Ioi p := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_Ioi]
    by_contra hcon
    push_neg at hcon
    have := hmono hcon
    simp only [Function.comp, Equiv.apply_symm_apply] at this
    linarith [hx.2]
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Fin.card_Ioi] at this
  simp [hp] at this
  omega

theorem fs_core {n N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    (hconv : ∀ δ, ConvexOn ℝ Set.univ fun ν => ℓ ν δ)
    (hfs : FullySupported P ℓ)
    (νstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin n))
    (hνstar : ∀ ω, IsSolution ℓ ω (νstar ω))
    (hN : n + 1 ≤ N) :
    ∀ᵐ ω ∂(MeasureTheory.Measure.pi fun _ : Fin N => P),
      worstCost ℓ ω (νstar ω) = empiricalCost ℓ ω (νstar ω) (n + 1) := by
  classical
  filter_upwards [hfs N hN] with ω hω
  have hcnt := hω (νstar ω) (hνstar ω)
  unfold numSupportConstraints at hcnt
  unfold empiricalCost
  symm
  apply fs_kth _ _ (by omega) hN
  rw [← hcnt]
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  exact fs_active ℓ hconv (by omega) ω (νstar ω) (hνstar ω) i hi.2

end ScenarioApproach.EmpiricalCosts

open ScenarioApproach.EmpiricalCosts


theorem solution
    {n N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    -- standing assumption (p. 6): `ℓ(ν, δ)` is convex in `ν` for every `δ`
    (hconv : ∀ δ, ConvexOn ℝ Set.univ fun ν => ℓ ν δ)
    -- measurability, glossed over in the book (p. 6, footnote 1; p. 33)
    (hmeas : Measurable (Function.uncurry ℓ))
    -- Assumption 3.6 for (1.4): existence and uniqueness for every `m ≥ 1` and every sample
    (hexu : ∀ m : ℕ, 1 ≤ m → ∀ ω : Fin m → Δ, ∃! ν, IsSolution ℓ ω ν)
    -- Definition 5.4 for (1.4)
    (hfs : FullySupported P ℓ)
    -- `νstar ω` is the solution `ν*` of the scenario program with the `N` scenarios `ω`
    (νstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin n))
    (hνstar : ∀ ω, IsSolution ℓ ω (νstar ω)) (hνstar_meas : Measurable νstar)
    (hN : n + 1 ≤ N) :
    ∀ᵐ ω ∂(MeasureTheory.Measure.pi fun _ : Fin N => P),
      worstCost ℓ ω (νstar ω) = empiricalCost ℓ ω (νstar ω) (n + 1) := by
  exact fs_core P ℓ hconv hfs νstar hνstar hN
