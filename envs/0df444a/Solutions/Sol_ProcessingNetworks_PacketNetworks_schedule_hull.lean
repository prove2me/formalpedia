-- Prove2me | solution 1 for ProcessingNetworks.PacketNetworks.schedule_hull
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:00:32.34217+00:00
-- url     : https://prove2.me/submissions/3bc46eae-2fa2-411b-ad02-ddd2b6e20a61

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion

set_option autoImplicit false

open ProcessingNetworks.PacketNetworks in
lemma shull6d_realize_inj {J : ℕ} : Function.Injective (realize (J := J)) := by
  intro a b h
  funext j
  have := congrFun h j
  simpa [realize] using this

open ProcessingNetworks.PacketNetworks in
lemma shull6d_hullC {K : ℕ} (C : Finset (Fin K → ℕ)) (chat : Fin K → ℝ)
    (h : chat ∈ hullFinset C) :
    ∃ μ : (Fin K → ℕ) → ℝ, (∀ c ∈ C, 0 ≤ μ c) ∧ ∑ c ∈ C, μ c = 1 ∧
      ∑ c ∈ C, μ c • realize c = chat := by
  classical
  unfold hullFinset at h
  rw [← Finset.coe_image, Finset.mem_convexHull'] at h
  obtain ⟨w, hw0, hw1, hwx⟩ := h
  refine ⟨fun c => w (realize c), fun c hc => hw0 _ (Finset.mem_image_of_mem _ hc), ?_, ?_⟩
  · rw [Finset.sum_image (fun a _ b _ hab => shull6d_realize_inj hab)] at hw1
    exact hw1
  · rw [Finset.sum_image (fun a _ b _ hab => shull6d_realize_inj hab)] at hwx
    exact hwx

open ProcessingNetworks.PacketNetworks in
lemma shull6d_A_eq {J K : ℕ} (cfg : LinkConfigData J K) (link : Fin J → Fin K)
    (hlink : ∀ j, cfg.A (link j) j = 1) (k : Fin K) (j : Fin J) :
    cfg.A k j = if link j = k then 1 else 0 := by
  split_ifs with h
  · subst h; exact hlink j
  · apply cfg.hA0
    intro h1
    obtain ⟨k0, _, huniq⟩ := cfg.hA j
    exact h ((huniq _ (hlink j)).trans (huniq _ h1).symm)

open ProcessingNetworks.PacketNetworks in
lemma shull6d_mulVec {J K : ℕ} (cfg : LinkConfigData J K) (link : Fin J → Fin K)
    (hlink : ∀ j, cfg.A (link j) j = 1) (v : Fin J → ℝ) (k : Fin K) :
    cfg.A.mulVec v k = ∑ j, if link j = k then v j else 0 := by
  simp only [Matrix.mulVec, dotProduct, shull6d_A_eq cfg link hlink]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

open ProcessingNetworks.PacketNetworks in
theorem solution
    {J K : ℕ} (cfg : LinkConfigData J K) (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S) :
    hullFinset S =
      {x : Fin J → ℝ | (∀ j, 0 ≤ x j) ∧ ∃ chat ∈ hullFinset cfg.C,
        ∀ k, (cfg.A.mulVec x) k ≤ chat k} := by
  classical
  apply Set.Subset.antisymm
  · unfold hullFinset
    apply convexHull_min
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨c, hc, hav⟩ := (hS s).1 (Finset.mem_coe.1 hs)
      rw [Set.mem_setOf_eq]
      refine ⟨fun j => by simp [realize], realize c, subset_convexHull ℝ _ ⟨c, hc, rfl⟩,
        fun k => ?_⟩
      exact hav k
    · rintro x ⟨hx0, c1, hc1, hx1⟩ y ⟨hy0, c2, hc2, hy1⟩ a b ha hb hab
      rw [Set.mem_setOf_eq]
      refine ⟨fun j => ?_, a • c1 + b • c2, convex_convexHull ℝ _ hc1 hc2 ha hb hab, fun k => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg ha (hx0 j)) (mul_nonneg hb (hy0 j))
      · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hx1 k) ha)
          (mul_le_mul_of_nonneg_left (hy1 k) hb)
  · rintro x ⟨hx0, chat, hchat, hAx⟩
    obtain ⟨μ, hμ0, hμ1, hμx⟩ := shull6d_hullC cfg.C chat hchat
    choose link hlink _ using cfg.hA
    have hMV := shull6d_mulVec cfg link hlink
    have hchatk : ∀ k, chat k = ∑ c ∈ cfg.C, μ c * (c k : ℝ) := by
      intro k
      rw [← hμx, Finset.sum_apply]
      simp [realize]
    have hchat0 : ∀ k, 0 ≤ chat k := by
      intro k
      rw [hchatk]
      exact Finset.sum_nonneg fun c hc => mul_nonneg (hμ0 c hc) (Nat.cast_nonneg _)
    set q : Fin J → ℝ := fun j => x j / chat (link j) with hq
    have hq0 : ∀ j, 0 ≤ q j := fun j => div_nonneg (hx0 j) (hchat0 _)
    have hxq : ∀ j, chat (link j) * q j = x j := by
      intro j
      by_cases h : chat (link j) = 0
      · have h1 : x j ≤ cfg.A.mulVec x (link j) := by
          rw [hMV]
          have := Finset.single_le_sum (f := fun j' => if link j' = link j then x j' else 0)
            (fun j' _ => by
              show 0 ≤ (if link j' = link j then x j' else 0)
              split_ifs
              · exact hx0 j'
              · exact le_refl 0) (Finset.mem_univ j)
          simpa using this
        have : x j = 0 := le_antisymm (by linarith [hAx (link j)]) (hx0 j)
        simp [hq, this]
      · simp only [hq]
        field_simp
    have hsumk : ∀ k, ∑ j, (if link j = k then q j else 0) ≤ 1 := by
      intro k
      by_cases h : chat k = 0
      · have : ∀ j, (if link j = k then q j else 0) = 0 := by
          intro j
          split_ifs with hj
          · simp [hq, hj, h]
          · rfl
        simp [this]
      · have hpos : 0 < chat k := lt_of_le_of_ne (hchat0 k) (Ne.symm h)
        have : ∑ j, (if link j = k then q j else 0) = (cfg.A.mulVec x k) / chat k := by
          rw [hMV, Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs with hj
          · simp [hq, hj]
          · simp
        rw [this, div_le_one hpos]
        exact hAx k
    let wk : Fin K → Option (Fin J) → ℝ := fun k o =>
      Option.elim o (1 - ∑ j, if link j = k then q j else 0)
        (fun j => if link j = k then q j else 0)
    have hwk0 : ∀ k o, 0 ≤ wk k o := by
      intro k o
      cases o with
      | none => simp only [wk, Option.elim]; linarith [hsumk k]
      | some j =>
        simp only [wk, Option.elim]
        split_ifs
        · exact hq0 j
        · exact le_refl 0
    have hwk1 : ∀ k, ∑ o, wk k o = 1 := by
      intro k
      rw [Fintype.sum_option]
      simp only [wk, Option.elim]
      ring
    let sch : (Fin K → ℕ) → (Fin K → Option (Fin J)) → (Fin J → ℕ) := fun c f j =>
      if f (link j) = some j then c (link j) else 0
    have hsch : ∀ c ∈ cfg.C, ∀ f, sch c f ∈ S := by
      intro c hc f
      refine (hS _).2 ⟨c, hc, ?_⟩
      intro k
      rw [hMV]
      refine le_trans (Finset.sum_le_sum fun j _ => ?_)
        (?_ : ∑ j, (if f k = some j then (c k : ℝ) else 0) ≤ c k)
      · split_ifs with h1 h2 h2
        · subst h1; simp [sch, h2]
        · subst h1; simp [sch, h2]
        · positivity
        · exact le_refl 0
      · cases hfk : f k with
        | none => simp
        | some j0 => simp [Finset.sum_ite_eq]
    -- the inner product-of-sums identity
    have key : ∀ (j : Fin J) (c : Fin K → ℕ), ∑ f : Fin K → Option (Fin J),
        ((∏ k, wk k (f k)) * (if f (link j) = some j then (c (link j) : ℝ) else 0))
          = (c (link j) : ℝ) * q j := by
      intro j c
      have e : ∀ f : Fin K → Option (Fin J),
          (∏ k, wk k (f k)) * (if f (link j) = some j then (c (link j) : ℝ) else 0)
            = (c (link j) : ℝ) * ∏ k, (wk k (f k) *
                (if k = link j then (if f k = some j then (1 : ℝ) else 0) else 1)) := by
        intro f
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ (link j)]
        simp only [Finset.mem_univ, if_true]
        split_ifs <;> ring
      simp only [e, ← Finset.mul_sum]
      congr 1
      rw [← Fintype.prod_sum (fun k o => wk k o *
          (if k = link j then (if o = some j then (1 : ℝ) else 0) else 1))]
      rw [Finset.prod_eq_single (link j)]
      · rw [Fintype.sum_option]
        simp [wk]
      · intro k _ hk
        simp only [hk, if_false, mul_one]
        exact hwk1 k
      · simp
    unfold hullFinset
    refine mem_convexHull_of_exists_fintype (ι := ↥cfg.C × (Fin K → Option (Fin J)))
      (fun p => μ p.1 * ∏ k, wk k (p.2 k))
      (fun p => realize (sch p.1 p.2)) ?_ ?_ ?_ ?_
    · intro p
      exact mul_nonneg (hμ0 _ p.1.2) (Finset.prod_nonneg fun k _ => hwk0 k _)
    · rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ← Fintype.prod_sum, hwk1, Finset.prod_const_one, mul_one]
      rw [Finset.sum_coe_sort cfg.C μ]
      exact hμ1
    · intro p
      exact ⟨sch p.1 p.2, Finset.mem_coe.2 (hsch _ p.1.2 _), rfl⟩
    · funext j
      rw [Finset.sum_apply, Fintype.sum_prod_type]
      have step : ∀ c : ↥cfg.C, ∑ f : Fin K → Option (Fin J),
          ((μ c.1 * ∏ k, wk k (f k)) • realize (sch c.1 f)) j
            = μ c.1 * ((c.1 (link j) : ℝ) * q j) := by
        intro c
        rw [← key j c.1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, realize, sch]
        push_cast
        ring
      simp only [step]
      rw [Finset.sum_coe_sort cfg.C (fun c => μ c * ((c (link j) : ℝ) * q j))]
      rw [← hxq j, hchatk (link j), Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
