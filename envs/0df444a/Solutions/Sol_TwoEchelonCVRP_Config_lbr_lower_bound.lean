-- Prove2me | solution 1 for TwoEchelonCVRP.Config.lbr_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:45:09.616003+00:00
-- url     : https://prove2.me/submissions/23841df5-3b58-4d0e-a67b-faa3ec431c89

import Mathlib
import Definitions.Def_TwoEchelonCVRP_Config_Bounds

set_option autoImplicit false

open TwoEchelonCVRP.Config

lemma tec_weak {I : Instance} (RS : RouteSystem I) (K : Finset (Fin I.ns)) (hK : K.Nonempty)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (X : RS.SR → ℕ)
    (hcover : ∀ i, ∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ K ∧ i ∈ RS.tour2 l), X l = 1)
    (hmk : ∀ k ∈ K, ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), X l ≤ I.m k)
    (hm2 : ∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ K), X l ≤ I.m2) :
    ∑ i, K.inf' hK (fun k => β i k) + ∑ i, lam i + ∑ k ∈ K, (I.m k : ℝ) * μ k
        + (I.m2 : ℝ) * μ0 ≤
      ∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ K), RS.c l * (X l : ℝ) := by
  set F : Finset RS.SR := Finset.univ.filter (fun l => RS.sat l ∈ K) with hF
  have hx0 : ∀ l, (0 : ℝ) ≤ (X l : ℝ) := fun l => Nat.cast_nonneg _
  -- a i l = indicator
  have ha : ∀ i l, (RS.a i l : ℝ) = if i ∈ RS.tour2 l then 1 else 0 := by
    intro i l
    unfold RouteSystem.a
    by_cases h : i ∈ RS.tour2 l
    · rw [if_pos h, List.count_eq_one_of_mem (RS.tour2_nodup l) h]; simp
    · rw [if_neg h, List.count_eq_zero.2 h]; simp
  -- step 1: pointwise penalty bound
  have h1 : ∑ l ∈ F, (X l : ℝ) * (∑ i, (RS.a i l : ℝ) * (β i (RS.sat l) + lam i)
      + μ (RS.sat l) + μ0) ≤ ∑ l ∈ F, RS.c l * (X l : ℝ) := by
    apply Finset.sum_le_sum
    intro l _
    have := hβ l
    have e : ∑ i, (RS.a i l : ℝ) * (β i (RS.sat l) + lam i)
        = ∑ i, (RS.a i l : ℝ) * β i (RS.sat l) + ∑ i, (RS.a i l : ℝ) * lam i := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intros; ring
    rw [e, mul_comm (RS.c l)]
    apply mul_le_mul_of_nonneg_left _ (hx0 l)
    linarith
  -- step 2: split
  have hsplit : ∑ l ∈ F, (X l : ℝ) * (∑ i, (RS.a i l : ℝ) * (β i (RS.sat l) + lam i)
      + μ (RS.sat l) + μ0)
      = ∑ i, ∑ l ∈ F, (X l : ℝ) * ((RS.a i l : ℝ) * (β i (RS.sat l) + lam i))
        + ∑ l ∈ F, (X l : ℝ) * μ (RS.sat l) + μ0 * ∑ l ∈ F, (X l : ℝ) := by
    have e1 : ∑ l ∈ F, (X l : ℝ) * (∑ i, (RS.a i l : ℝ) * (β i (RS.sat l) + lam i)
        + μ (RS.sat l) + μ0)
        = ∑ l ∈ F, (X l : ℝ) * (∑ i, (RS.a i l : ℝ) * (β i (RS.sat l) + lam i))
          + ∑ l ∈ F, (X l : ℝ) * μ (RS.sat l) + ∑ l ∈ F, (X l : ℝ) * μ0 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intros; ring
    have e2 : ∑ l ∈ F, (X l : ℝ) * (∑ i, (RS.a i l : ℝ) * (β i (RS.sat l) + lam i))
        = ∑ i, ∑ l ∈ F, (X l : ℝ) * ((RS.a i l : ℝ) * (β i (RS.sat l) + lam i)) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    have e3 : ∑ l ∈ F, (X l : ℝ) * μ0 = μ0 * ∑ l ∈ F, (X l : ℝ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    rw [e1, e2, e3]
  -- step 3a
  have hA : ∀ i, K.inf' hK (fun k => β i k) + lam i ≤
      ∑ l ∈ F, (X l : ℝ) * ((RS.a i l : ℝ) * (β i (RS.sat l) + lam i)) := by
    intro i
    have hterm : ∀ l ∈ F, (if i ∈ RS.tour2 l then (X l : ℝ) * (K.inf' hK (fun k => β i k) + lam i)
        else 0) ≤ (X l : ℝ) * ((RS.a i l : ℝ) * (β i (RS.sat l) + lam i)) := by
      intro l hl
      have hlK : RS.sat l ∈ K := (Finset.mem_filter.1 hl).2
      rw [ha]
      by_cases h : i ∈ RS.tour2 l
      · simp only [h, if_true, one_mul]
        apply mul_le_mul_of_nonneg_left _ (hx0 l)
        have h' : K.inf' hK (fun k => β i k) ≤ β i (RS.sat l) := Finset.inf'_le (fun k => β i k) hlK
        linarith
      · simp [h]
    refine le_trans ?_ (Finset.sum_le_sum hterm)
    rw [← Finset.sum_filter, Finset.filter_filter]
    have hc : ∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ K ∧ i ∈ RS.tour2 l), (X l : ℝ) = 1 := by
      exact_mod_cast hcover i
    rw [← Finset.sum_mul, hc, one_mul]
  -- step 3b
  have hB : ∑ k ∈ K, (I.m k : ℝ) * μ k ≤ ∑ l ∈ F, (X l : ℝ) * μ (RS.sat l) := by
    have hfib : ∑ l ∈ F, (X l : ℝ) * μ (RS.sat l)
        = ∑ k ∈ K, ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), (X l : ℝ) * μ k := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := F) (t := K) (g := RS.sat)
        (fun l hl => (Finset.mem_filter.1 hl).2)]
      apply Finset.sum_congr rfl
      intro k hk
      have : F.filter (fun l => RS.sat l = k) = Finset.univ.filter (fun l => RS.sat l = k) := by
        ext l
        simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; exact h.2
        · intro h; exact ⟨h ▸ hk, h⟩
      rw [this]
      apply Finset.sum_congr rfl
      intro l hl
      rw [(Finset.mem_filter.1 hl).2]
    rw [hfib]
    apply Finset.sum_le_sum
    intro k hk
    rw [← Finset.sum_mul]
    have h2 : (∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), (X l : ℝ)) ≤ (I.m k : ℝ) := by
      exact_mod_cast hmk k hk
    nlinarith [hμ k]
  -- step 3c
  have hC : (I.m2 : ℝ) * μ0 ≤ μ0 * ∑ l ∈ F, (X l : ℝ) := by
    have h2 : (∑ l ∈ F, (X l : ℝ)) ≤ (I.m2 : ℝ) := by exact_mod_cast hm2
    nlinarith
  have hA' : ∑ i, K.inf' hK (fun k => β i k) + ∑ i, lam i ≤
      ∑ i, ∑ l ∈ F, (X l : ℝ) * ((RS.a i l : ℝ) * (β i (RS.sat l) + lam i)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => hA i)
  linarith

theorem solution (I : Instance) (RS : RouteSystem I) (hns : 0 < I.ns)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (s : SolF RS) (hs : IsFeasibleF RS s) :
    LBR hns β lam μ μ0 ≤ secondLevelCost RS s := by
  obtain ⟨hcov, hmk, hm2, _⟩ := hs
  have hK : (Finset.univ : Finset (Fin I.ns)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hns⟩⟩
  have := tec_weak RS Finset.univ hK β lam μ μ0 hμ hμ0 hβ (fun l => (s.x l).toNat)
    (by intro i; simpa using hcov i) (by intro k _; exact hmk k) (by simpa using hm2)
  simpa [LBR, secondLevelCost] using this
