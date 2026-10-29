-- Prove2me | solution 1 for PochetWolsey.BacklogStartup.startup_stock_inequality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:16:10.29903+00:00
-- url     : https://prove2.me/submissions/c071cefc-da9f-4f3e-b0ec-6931e39c41ea

import Mathlib
import Definitions.Def_PochetWolsey_BacklogStartup_StartupModel

open PochetWolsey.BacklogStartup

theorem solution {n : ℕ} (y0 : ℝ) (hy0 : y0 = 0 ∨ y0 = 1) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t)
    (M : ℝ) (hM : demandSum d 1 n ≤ M) (p : StartupPoint n) (x : Fin n → ℝ)
    (hp : LSStartup y0 d M p x) (k l : ℕ) (hk : 1 ≤ k) (hkl : k ≤ l) (hl : l ≤ n) :
    startupStockRHS d p k l ≤ stock p.1 (k - 1) := by
  obtain ⟨hs, hx, ⟨hyb, hzb, hc⟩, hbal⟩ := hp
  have nn : ∀ (v : Fin n → ℝ), (∀ i, 0 ≤ v i) → ∀ i, 0 ≤ period v i := by
    intro v hv i
    unfold period
    split_ifs
    · exact hv _
    · exact le_refl _
  have binNN : ∀ (v : Fin n → ℝ), Binary v → ∀ i, 0 ≤ v i := by
    intro v hv i; rcases hv i with h | h <;> rw [h] <;> norm_num
  have bin01 : ∀ (v : Fin n → ℝ), Binary v → ∀ i, period v i = 0 ∨ period v i = 1 := by
    intro v hv i
    unfold period
    split_ifs
    · exact hv _
    · exact Or.inl rfl
  have hyN := nn _ (binNN _ hyb)
  have hzN := nn _ (binNN _ hzb)
  have hxN := nn _ hx
  have hdN := nn _ hd
  have hsN : ∀ t, 0 ≤ stock p.1 t := by
    intro t; unfold stock; split_ifs
    · exact hs _
    · exact le_refl _
  set y := p.2.1 with hy
  set z := p.2.2 with hz
  set s := p.1 with hsdef
  unfold startupStockRHS
  rcases bin01 y hyb k with hyk | hyk
  swap
  · -- y_k = 1: all coefficients ≤ 0
    have : ∑ u ∈ Finset.Icc k l,
        period d u * (1 - period y k - ∑ j ∈ Finset.Icc (k + 1) u, period z j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro u _
      rw [hyk]
      have : 0 ≤ ∑ j ∈ Finset.Icc (k + 1) u, period z j := Finset.sum_nonneg (fun j _ => hzN j)
      nlinarith [hdN u]
    linarith [hsN (k - 1)]
  -- y_k = 0
  have Q : ∀ m, k + m ≤ n →
      ((∑ j ∈ Finset.Icc (k + 1) (k + m), period z j = 0 →
          period y (k + m) = 0 ∧
          ∑ u ∈ Finset.Icc k (k + m),
            period d u * (1 - ∑ j ∈ Finset.Icc (k + 1) u, period z j)
            ≤ stock s (k - 1) - stock s (k + m)) ∧
        ∑ u ∈ Finset.Icc k (k + m),
            period d u * (1 - ∑ j ∈ Finset.Icc (k + 1) u, period z j)
            ≤ stock s (k - 1)) := by
    intro m
    induction m with
    | zero =>
      intro hkn
      simp only [add_zero, Finset.Icc_self, Finset.sum_singleton]
      have hb := hbal k (Finset.mem_Icc.mpr ⟨hk, by omega⟩)
      have hx0 : period x k = 0 := by
        have := hb.2; rw [hyk, mul_zero] at this; linarith [hxN k]
      have hb1 := hb.1
      rw [hx0] at hb1
      have e : Finset.Icc (k + 1) k = ∅ := Finset.Icc_eq_empty (by omega)
      rw [e, Finset.sum_empty]
      have := hsN k
      constructor
      · intro _; exact ⟨hyk, by linarith⟩
      · linarith
    | succ m ih =>
      intro hkn
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hsplitZ : ∑ j ∈ Finset.Icc (k + 1) (k + (m + 1)), period z j
          = ∑ j ∈ Finset.Icc (k + 1) (k + m), period z j + period z (k + m + 1) := by
        rw [show k + (m + 1) = (k + m) + 1 by omega]
        exact Finset.sum_Icc_succ_top (by omega) _
      have hsplitR : ∑ u ∈ Finset.Icc k (k + (m + 1)),
            period d u * (1 - ∑ j ∈ Finset.Icc (k + 1) u, period z j)
          = ∑ u ∈ Finset.Icc k (k + m),
            period d u * (1 - ∑ j ∈ Finset.Icc (k + 1) u, period z j)
            + period d (k + m + 1) * (1 -
                ∑ j ∈ Finset.Icc (k + 1) (k + (m + 1)), period z j) := by
        rw [show k + (m + 1) = (k + m) + 1 by omega]
        exact Finset.sum_Icc_succ_top (by omega) _
      rw [hsplitR]
      have hS0 : 0 ≤ ∑ j ∈ Finset.Icc (k + 1) (k + m), period z j :=
        Finset.sum_nonneg (fun j _ => hzN j)
      have hzl := hzN (k + m + 1)
      by_cases hZ : ∑ j ∈ Finset.Icc (k + 1) (k + (m + 1)), period z j = 0
      · have hA : ∑ j ∈ Finset.Icc (k + 1) (k + m), period z j = 0 := by linarith
        have hzl0 : period z (k + m + 1) = 0 := by linarith
        obtain ⟨hyprev, hR⟩ := ih1 hA
        have hcon := (hc (k + m + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).1
        have hss : setupState y0 y (k + m + 1 - 1) = 0 := by
          unfold setupState
          rw [if_neg (by omega)]
          simpa using hyprev
        rw [hss, hzl0] at hcon
        have hyl : period y (k + m + 1) = 0 := by linarith [hyN (k + m + 1)]
        have hb := hbal (k + m + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hx0 : period x (k + m + 1) = 0 := by
          have := hb.2; rw [hyl, mul_zero] at this; linarith [hxN (k + m + 1)]
        have hb1 := hb.1
        rw [hx0, show k + m + 1 - 1 = k + m by omega] at hb1
        rw [hZ]
        have := hsN (k + m + 1)
        rw [show k + (m + 1) = k + m + 1 by omega]
        constructor
        · intro _; exact ⟨hyl, by linarith⟩
        · linarith
      · have hge : 1 ≤ ∑ j ∈ Finset.Icc (k + 1) (k + (m + 1)), period z j := by
          obtain ⟨j, hj, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hZ
          have h1 : period z j = 1 := (bin01 z hzb j).resolve_left hjne
          have := Finset.single_le_sum (f := fun j => period z j) (fun j _ => hzN j) hj
          linarith
        constructor
        · intro h; exact absurd h hZ
        · have := hdN (k + m + 1)
          nlinarith
  rw [hyk]; simp only [sub_zero]
  have := (Q (l - k) (by omega)).2
  rwa [show k + (l - k) = l by omega] at this
