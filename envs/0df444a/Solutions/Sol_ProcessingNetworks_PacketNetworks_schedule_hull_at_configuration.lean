-- Prove2me | solution 1 for ProcessingNetworks.PacketNetworks.schedule_hull_at_configuration
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:04:50.322261+00:00
-- url     : https://prove2.me/submissions/c6ec57ef-7a65-41e0-b6f2-35b500b56751

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion

set_option autoImplicit false

open ProcessingNetworks.PacketNetworks in
/-- The link used by activity `j`. -/
noncomputable def SHC7e2b_link {J K : ℕ} (cfg : LinkConfigData J K) (j : Fin J) : Fin K :=
  (cfg.hA j).exists.choose

open ProcessingNetworks.PacketNetworks in
theorem SHC7e2b_A_eq {J K : ℕ} (cfg : LinkConfigData J K) (k : Fin K) (j : Fin J) :
    cfg.A k j = if SHC7e2b_link cfg j = k then 1 else 0 := by
  have hspec : cfg.A (SHC7e2b_link cfg j) j = 1 := (cfg.hA j).exists.choose_spec
  split_ifs with h
  · rw [← h]; exact hspec
  · apply cfg.hA0
    intro h1
    exact h ((cfg.hA j).unique hspec h1)

open ProcessingNetworks.PacketNetworks in
theorem SHC7e2b_mulVec {J K : ℕ} (cfg : LinkConfigData J K) (x : Fin J → ℝ) (k : Fin K) :
    (cfg.A.mulVec x) k = ∑ j, if SHC7e2b_link cfg j = k then x j else 0 := by
  simp only [Matrix.mulVec, dotProduct, SHC7e2b_A_eq]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

open ProcessingNetworks.PacketNetworks in
theorem schedule_hull_at_configuration_aux
    {J K : ℕ} (cfg : LinkConfigData J K) (c : Fin K → ℕ) (Sc : Finset (Fin J → ℕ))
    (hSc : IsScheduleSetAt cfg c Sc) :
    hullFinset Sc = {x : Fin J → ℝ | (∀ j, 0 ≤ x j) ∧ ∀ k, (cfg.A.mulVec x) k ≤ (c k : ℝ)} := by
  classical
  set link := SHC7e2b_link cfg with hlink_def
  apply Set.Subset.antisymm
  · -- hull ⊆ polytope
    apply convexHull_min
    · rintro _ ⟨s, hs, rfl⟩
      have hs' := (hSc s).1 hs
      refine ⟨fun j => by simp [realize], fun k => ?_⟩
      exact hs' k
    · intro x hx y hy a b ha hb hab
      refine ⟨fun j => ?_, fun k => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hx.1 j; have := hy.1 j; positivity
      · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h1 := hx.2 k; have h2 := hy.2 k
        calc a * cfg.A.mulVec x k + b * cfg.A.mulVec y k
            ≤ a * (c k : ℝ) + b * (c k : ℝ) := by gcongr
          _ = c k := by rw [← add_mul, hab, one_mul]
  · -- polytope ⊆ hull
    rintro x ⟨hx0, hxA⟩
    -- per-link weights
    let w : Fin K → Option (Fin J) → ℝ := fun k o =>
      match o with
      | none => 1 - ∑ j, (if link j = k then x j / (c k : ℝ) else 0)
      | some j => if link j = k then x j / (c k : ℝ) else 0
    let pt : (Fin K → Option (Fin J)) → (Fin J → ℕ) := fun σ j =>
      if σ (link j) = some j then c (link j) else 0
    have hsumk : ∀ k, (∑ j, (if link j = k then x j / (c k : ℝ) else 0))
        = (∑ j, (if link j = k then x j else 0)) / (c k : ℝ) := by
      intro k
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    have hw0 : ∀ k o, 0 ≤ w k o := by
      intro k o
      cases o with
      | none =>
        simp only [w]
        rw [hsumk]
        have hle : (∑ j, (if link j = k then x j else 0)) ≤ (c k : ℝ) := by
          have := hxA k
          rwa [SHC7e2b_mulVec] at this
        have := div_le_one_of_le₀ hle (Nat.cast_nonneg (c k))
        linarith
      | some j =>
        simp only [w]
        split_ifs
        · exact div_nonneg (hx0 j) (Nat.cast_nonneg _)
        · exact le_refl 0
    have hw1 : ∀ k, ∑ o, w k o = 1 := by
      intro k
      rw [Fintype.sum_option]
      simp only [w]
      ring
    have hpt : ∀ σ, pt σ ∈ Sc := by
      intro σ
      rw [hSc]
      intro k
      rw [SHC7e2b_mulVec]
      have : ∀ j, (if link j = k then ((pt σ j : ℕ) : ℝ) else 0)
          = if σ k = some j ∧ link j = k then (c k : ℝ) else 0 := by
        intro j
        simp only [pt]
        by_cases h1 : link j = k
        · subst h1
          by_cases h2 : σ (link j) = some j <;> simp [h2]
        · simp [h1]
      refine (Finset.sum_congr rfl (fun j _ => this j)).trans_le ?_
      cases hσ : σ k with
      | none => simp
      | some j0 =>
        simp only [Option.some.injEq]
        rw [Finset.sum_eq_single j0]
        · split_ifs <;> simp
        · intro j _ hj
          rw [if_neg]
          rintro ⟨h, _⟩
          exact hj h.symm
        · intro h; exact absurd (Finset.mem_univ j0) h
    -- the convex combination
    let W : (Fin K → Option (Fin J)) → ℝ := fun σ => ∏ k, w k (σ k)
    have hW0 : ∀ σ ∈ (Finset.univ : Finset (Fin K → Option (Fin J))), 0 ≤ W σ := by
      intro σ _
      exact Finset.prod_nonneg (fun k _ => hw0 k (σ k))
    have hW1 : ∑ σ ∈ (Finset.univ : Finset (Fin K → Option (Fin J))), W σ = 1 := by
      simp only [W]
      rw [← Fintype.prod_sum]
      simp [hw1]
    have hmean : x = ∑ σ ∈ (Finset.univ : Finset (Fin K → Option (Fin J))),
        W σ • realize (pt σ) := by
      funext j
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, realize, W, pt]
      set l := link j with hl
      let f : Option (Fin J) → ℝ := fun o => if o = some j then (c l : ℝ) else 0
      let g : Fin K → Option (Fin J) → ℝ := fun k o => w k o * (if k = l then f o else 1)
      have hterm : ∀ σ : Fin K → Option (Fin J),
          (∏ k, w k (σ k)) * (((if σ l = some j then c l else 0 : ℕ)) : ℝ)
            = ∏ k, g k (σ k) := by
        intro σ
        simp only [g]
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
        simp only [Finset.mem_univ, if_true, f]
        congr 1
        split_ifs <;> simp
      simp only [hterm]
      rw [← Fintype.prod_sum]
      rw [Finset.prod_eq_single l]
      · simp only [g, if_true, mul_ite, mul_one]
        simp only [f, mul_ite, mul_zero]
        rw [Fintype.sum_option]
        simp only [reduceCtorEq, if_false, Option.some.injEq, zero_add]
        rw [Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true, w, hl, if_true]
        by_cases hc : (c l : ℝ) = 0
        · have hxj : x j = 0 := by
            have hle := hxA l
            rw [SHC7e2b_mulVec, hc] at hle
            have hnn : ∀ i ∈ Finset.univ, 0 ≤ (if link i = l then x i else 0) := by
              intro i _; split_ifs; exact hx0 i; exact le_refl 0
            have := Finset.single_le_sum hnn (Finset.mem_univ j)
            simp only [← hl, if_true] at this
            linarith [hx0 j]
          rw [hc, hxj]; simp
        · rw [div_mul_cancel₀ _ hc]
      · intro k _ hk
        simp only [g, if_neg hk, mul_one]
        exact hw1 k
      · intro h; exact absurd (Finset.mem_univ l) h
    rw [hmean]
    apply (convex_convexHull ℝ _).sum_mem hW0 hW1
    intro σ _
    apply subset_convexHull
    exact ⟨pt σ, hpt σ, rfl⟩

open ProcessingNetworks.PacketNetworks in
theorem solution
    {J K : ℕ} (cfg : LinkConfigData J K) (c : Fin K → ℕ) (Sc : Finset (Fin J → ℕ))
    (hSc : IsScheduleSetAt cfg c Sc) :
    hullFinset Sc = {x : Fin J → ℝ | (∀ j, 0 ≤ x j) ∧ ∀ k, (cfg.A.mulVec x) k ≤ (c k : ℝ)} := by
  exact schedule_hull_at_configuration_aux cfg c Sc hSc
