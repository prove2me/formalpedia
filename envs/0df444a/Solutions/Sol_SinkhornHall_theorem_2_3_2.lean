-- Prove2me | solution 1 for SinkhornHall.theorem_2_3_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T00:09:57.669143+00:00
-- url     : https://prove2.me/submissions/35db68cb-41f5-40a4-8af6-18f794fff66e

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Theorems.Thm_SinkhornHall_lemma_1_1
import Theorems.Thm_SinkhornHall_lemma_2_4

open Finset Filter Topology SinkhornHall

private lemma log_le_sub_one_232 {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1 := by
  have h := Real.log_le_log hx (by linarith [Real.add_one_le_exp (x - 1)] : x ≤ Real.exp (x - 1))
  rwa [Real.log_exp] at h

private noncomputable def skRow {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) : ℕ → ι → ℝ
  | 0 => fun _ => 1
  | t + 1 => rowNorm A r (colNorm A c (skRow A r c t))

private lemma skRow_pos {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j)
    (hcol : ∀ j, ∃ i, 0 < A i j) (r : ι → ℝ) (c : κ → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) :
    ∀ t : ℕ, (∀ i, 0 < skRow A r c t i) ∧ (∀ j, 0 < colNorm A c (skRow A r c t) j)
  | 0 => by
      have hx0 : ∀ i : ι, 0 < skRow A r c 0 i := fun _ => zero_lt_one
      refine ⟨hx0, fun j => ?_⟩
      obtain ⟨i₀, hi₀⟩ := hcol j
      have ht_pos : 0 < ∑ i, A i j * skRow A r c 0 i :=
        (mul_pos hi₀ (hx0 i₀)).trans_le
          (Finset.single_le_sum (f := fun i => A i j * skRow A r c 0 i)
            (fun i _ => mul_nonneg (hA i j) (hx0 i).le) (Finset.mem_univ i₀))
      exact div_pos (hc j) ht_pos
  | t + 1 => by
      obtain ⟨_, hy_pos⟩ := skRow_pos A hA hrow hcol r c hr hc t
      have hx1 : ∀ i, 0 < skRow A r c (t + 1) i := by
        intro i
        obtain ⟨j₀, hj₀⟩ := hrow i
        have hs_pos : 0 < ∑ j, A i j * colNorm A c (skRow A r c t) j :=
          (mul_pos hj₀ (hy_pos j₀)).trans_le
            (Finset.single_le_sum (f := fun j => A i j * colNorm A c (skRow A r c t) j)
              (fun j _ => mul_nonneg (hA i j) (hy_pos j).le) (Finset.mem_univ j₀))
        exact div_pos (hr i) hs_pos
      refine ⟨hx1, fun j => ?_⟩
      obtain ⟨i₀, hi₀⟩ := hcol j
      have ht_pos : 0 < ∑ i, A i j * skRow A r c (t + 1) i :=
        (mul_pos hi₀ (hx1 i₀)).trans_le
          (Finset.single_le_sum (f := fun i => A i j * skRow A r c (t + 1) i)
            (fun i _ => mul_nonneg (hA i j) (hx1 i).le) (Finset.mem_univ i₀))
      exact div_pos (hc j) ht_pos

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j)
    (hcol : ∀ j, ∃ i, 0 < A i j)
    (r : ι → ℝ) (c : κ → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hRC : ∑ i, r i = ∑ j, c j) :
    ApproxScalable A r c ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ι → ℝ) (y : κ → ℝ), (∀ i, 0 < x i) → (∀ j, 0 < y j) →
        δ ≤ kappa A r c x y := by
  have hne_κ : Nonempty κ := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    obtain ⟨j₀, _⟩ := hrow i₀
    exact ⟨j₀⟩
  let R : ℝ := ∑ i, r i
  let C : ℝ := ∑ j, c j
  have hR_pos : 0 < R := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  have hC_pos : 0 < C := Finset.sum_pos (fun j _ => hc j) Finset.univ_nonempty
  constructor
  · intro happrox
    have hex_seq : ∀ m : ℕ, ∃ (x : ι → ℝ) (y : κ → ℝ),
        (∀ i, 0 < x i) ∧ (∀ j, 0 < y j) ∧
        (∑ i, |(∑ j, A i j * x i * y j) - r i|) +
          (∑ j, |(∑ i, A i j * x i * y j) - c j|) < 1 / ((m : ℝ) + 1) := by
      intro m
      exact happrox (1 / ((m : ℝ) + 1)) (div_pos zero_lt_one (by positivity))
    choose xm ym hxm hym herr using hex_seq
    let Bm : ℕ → ι × κ → ℝ := fun m p => A p.1 p.2 * xm m p.1 * ym m p.2
    have hBm_nn : ∀ m p, 0 ≤ Bm m p :=
      fun m p => mul_nonneg (mul_nonneg (hA p.1 p.2) (hxm m p.1).le) (hym m p.2).le
    have hBm_ub : ∀ m p, Bm m p ≤ R + 1 := by
      intro m p
      have h1 : Bm m p ≤ ∑ j, A p.1 j * xm m p.1 * ym m j :=
        Finset.single_le_sum (f := fun j => A p.1 j * xm m p.1 * ym m j)
          (fun j _ => hBm_nn m (p.1, j)) (Finset.mem_univ p.2)
      have herr_le1 : 1 / ((m : ℝ) + 1) ≤ 1 :=
        div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) m]) (by positivity)
      have hrow_err : |(∑ j, A p.1 j * xm m p.1 * ym m j) - r p.1| ≤
          ∑ i, |(∑ j, A i j * xm m i * ym m j) - r i| :=
        Finset.single_le_sum (f := fun i => |(∑ j, A i j * xm m i * ym m j) - r i|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ p.1)
      have hcol_nn : 0 ≤ ∑ j, |(∑ i, A i j * xm m i * ym m j) - c j| :=
        Finset.sum_nonneg fun j _ => abs_nonneg _
      have hr_le_R : r p.1 ≤ R :=
        Finset.single_le_sum (f := r) (fun i _ => (hr i).le) (Finset.mem_univ p.1)
      have habs := le_abs_self ((∑ j, A p.1 j * xm m p.1 * ym m j) - r p.1)
      linarith [herr m]
    let box : Set (ι × κ → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) (R + 1)
    have hbox_compact : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
    have hBm_mem : ∀ m, Bm m ∈ box := fun m p _ => ⟨hBm_nn m p, hBm_ub m p⟩
    obtain ⟨B, hB_mem, φ, hφ_mono, hφ_lim⟩ := hbox_compact.tendsto_subseq hBm_mem
    have hB_nn : ∀ p, 0 ≤ B p := fun p => (hB_mem p trivial).1
    have hB_zero : ∀ p : ι × κ, A p.1 p.2 = 0 → B p = 0 := by
      intro p hp0
      have hlim_p : Tendsto (fun k => Bm (φ k) p) atTop (𝓝 (B p)) :=
        (continuous_apply p).continuousAt.tendsto.comp hφ_lim
      have hconst : (fun k => Bm (φ k) p) = fun _ => (0 : ℝ) := by
        ext k
        simp [Bm, hp0]
      rw [hconst] at hlim_p
      exact tendsto_nhds_unique hlim_p tendsto_const_nhds
    have hB_row : ∀ i : ι, ∑ j, B (i, j) = r i := by
      intro i
      have hcont : Continuous (fun M : ι × κ → ℝ => |(∑ j : κ, M (i, j)) - r i|) :=
        ((continuous_finsetSum _ fun j _ => continuous_apply (i, j)).sub continuous_const).abs
      have hlim_i : Tendsto (fun k => |(∑ j, Bm (φ k) (i, j)) - r i|) atTop
          (𝓝 |(∑ j, B (i, j)) - r i|) := hcont.continuousAt.tendsto.comp hφ_lim
      have hle_zero : |(∑ j, B (i, j)) - r i| ≤ 0 := by
        by_contra hpos
        push Not at hpos
        let η : ℝ := |(∑ j, B (i, j)) - r i| / 2
        have hη_pos : 0 < η := half_pos hpos
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
        have hev : ∀ᶠ k in atTop, |(∑ j, Bm (φ k) (i, j)) - r i| ≤ η := by
          refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
          have hφk : N ≤ φ k := hk.trans (hφ_mono.id_le k)
          have hφk_real : (1 / η) < ((φ k : ℝ) + 1) := by
            have : (N : ℝ) ≤ (φ k : ℝ) := Nat.cast_le.mpr hφk
            linarith
          have hdiv_lt : 1 / ((φ k : ℝ) + 1) < η := by
            rw [div_lt_iff₀ (by positivity)]
            rw [div_lt_iff₀ hη_pos] at hφk_real
            linarith
          have hrow_le : |(∑ j, Bm (φ k) (i, j)) - r i| ≤
              ∑ i', |(∑ j, Bm (φ k) (i', j)) - r i'| :=
            Finset.single_le_sum (f := fun i' => |(∑ j, Bm (φ k) (i', j)) - r i'|)
              (fun i' _ => abs_nonneg _) (Finset.mem_univ i)
          have hcol_nn : 0 ≤ ∑ j, |(∑ i', Bm (φ k) (i', j)) - c j| :=
            Finset.sum_nonneg fun j _ => abs_nonneg _
          have herr_φ := herr (φ k)
          dsimp [Bm] at hrow_le hcol_nn ⊢
          linarith
        have hle_η : |(∑ j, B (i, j)) - r i| ≤ η := le_of_tendsto hlim_i hev
        dsimp [η] at hle_η
        linarith
      have habs0 : |(∑ j, B (i, j)) - r i| = 0 := le_antisymm hle_zero (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp habs0)
    have hB_col : ∀ j : κ, ∑ i, B (i, j) = c j := by
      intro j
      have hcont : Continuous (fun M : ι × κ → ℝ => |(∑ i : ι, M (i, j)) - c j|) :=
        ((continuous_finsetSum _ fun i _ => continuous_apply (i, j)).sub continuous_const).abs
      have hlim_j : Tendsto (fun k => |(∑ i, Bm (φ k) (i, j)) - c j|) atTop
          (𝓝 |(∑ i, B (i, j)) - c j|) := hcont.continuousAt.tendsto.comp hφ_lim
      have hle_zero : |(∑ i, B (i, j)) - c j| ≤ 0 := by
        by_contra hpos
        push Not at hpos
        let η : ℝ := |(∑ i, B (i, j)) - c j| / 2
        have hη_pos : 0 < η := half_pos hpos
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
        have hev : ∀ᶠ k in atTop, |(∑ i, Bm (φ k) (i, j)) - c j| ≤ η := by
          refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
          have hφk : N ≤ φ k := hk.trans (hφ_mono.id_le k)
          have hφk_real : (1 / η) < ((φ k : ℝ) + 1) := by
            have : (N : ℝ) ≤ (φ k : ℝ) := Nat.cast_le.mpr hφk
            linarith
          have hdiv_lt : 1 / ((φ k : ℝ) + 1) < η := by
            rw [div_lt_iff₀ (by positivity)]
            rw [div_lt_iff₀ hη_pos] at hφk_real
            linarith
          have hcol_le : |(∑ i, Bm (φ k) (i, j)) - c j| ≤
              ∑ j', |(∑ i, Bm (φ k) (i, j')) - c j'| :=
            Finset.single_le_sum (f := fun j' => |(∑ i, Bm (φ k) (i, j')) - c j'|)
              (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
          have hrow_nn : 0 ≤ ∑ i, |(∑ j', Bm (φ k) (i, j')) - r i| :=
            Finset.sum_nonneg fun i _ => abs_nonneg _
          have herr_φ := herr (φ k)
          dsimp [Bm] at hcol_le hrow_nn ⊢
          linarith
        have hle_η : |(∑ i, B (i, j)) - c j| ≤ η := le_of_tendsto hlim_j hev
        dsimp [η] at hle_η
        linarith
      have habs0 : |(∑ i, B (i, j)) - c j| = 0 := le_antisymm hle_zero (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp habs0)
    classical
    let SB : Finset (ι × κ) := Finset.univ.filter (fun p : ι × κ => 0 < B p)
    have hSB_Apos : ∀ p ∈ SB, 0 < A p.1 p.2 := by
      intro p hp
      have hBp : 0 < B p := (Finset.mem_filter.mp hp).2
      rcases eq_or_lt_of_le (hA p.1 p.2) with h0 | hpos
      · exfalso
        exact hBp.ne' (hB_zero p h0.symm)
      · exact hpos
    have hsum_SB_eq : ∀ f : ι × κ → ℝ, ∑ p ∈ SB, B p * f p = ∑ p : ι × κ, B p * f p := by
      intro f
      have hsp := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun p : ι × κ => 0 < B p) (fun p => B p * f p)
      have h0 : ∑ p ∈ Finset.univ.filter (fun p : ι × κ => ¬ 0 < B p), B p * f p = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hnp := (Finset.mem_filter.mp hp).2
        have hBp0 : B p = 0 := le_antisymm (not_lt.mp hnp) (hB_nn p)
        simp [hBp0]
      change (∑ p ∈ SB, B p * f p) + _ = _ at hsp
      linarith
    have hsum_B : ∑ p ∈ SB, B p = R := by
      have h1 := hsum_SB_eq (fun _ => 1)
      simp only [mul_one] at h1
      rw [h1, Fintype.sum_prod_type]
      simp_rw [hB_row]
      rfl
    have hw_sum : ∑ p ∈ SB, B p / R = 1 := by
      rw [← Finset.sum_div, hsum_B, div_self hR_pos.ne']
    let δ : ℝ := R * Real.exp (∑ p ∈ SB, (B p / R) * Real.log (A p.1 p.2 / B p))
    refine ⟨δ, mul_pos hR_pos (Real.exp_pos _), fun x y hx hy => ?_⟩
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    obtain ⟨j₀, hj₀⟩ := hrow i₀
    let N : ℝ := ∑ i, ∑ j, A i j * x i * y j
    have hN_pos : 0 < N := by
      have hrow0 : 0 < ∑ j, A i₀ j * x i₀ * y j :=
        (mul_pos (mul_pos hj₀ (hx i₀)) (hy j₀)).trans_le
          (Finset.single_le_sum (f := fun j => A i₀ j * x i₀ * y j)
            (fun j _ => mul_nonneg (mul_nonneg (hA i₀ j) (hx i₀).le) (hy j).le)
            (Finset.mem_univ j₀))
      exact hrow0.trans_le
        (Finset.single_le_sum (f := fun i => ∑ j, A i j * x i * y j)
          (fun i _ => Finset.sum_nonneg fun j _ =>
            mul_nonneg (mul_nonneg (hA i j) (hx i).le) (hy j).le)
          (Finset.mem_univ i₀))
    let Dx : ℝ := ∏ i, x i ^ (r i / R)
    let Dy : ℝ := ∏ j, y j ^ (c j / C)
    have hDx_pos : 0 < Dx := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _
    have hDy_pos : 0 < Dy := Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hy j) _
    have hκ_pos : 0 < kappa A r c x y := div_pos hN_pos (mul_pos hDx_pos hDy_pos)
    let z : ι × κ → ℝ := fun p => (A p.1 p.2 * x p.1 * y p.2 / N) / (B p / R)
    have hz_pos : ∀ p ∈ SB, 0 < z p := by
      intro p hp
      have hBp : 0 < B p := (Finset.mem_filter.mp hp).2
      exact div_pos (div_pos (mul_pos (mul_pos (hSB_Apos p hp) (hx p.1)) (hy p.2)) hN_pos)
        (div_pos hBp hR_pos)
    have hle_zero : ∑ p ∈ SB, (B p / R) * Real.log (z p) ≤ 0 := by
      have h1 : ∑ p ∈ SB, (B p / R) * Real.log (z p) ≤ ∑ p ∈ SB, (B p / R) * (z p - 1) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hBp : 0 < B p := (Finset.mem_filter.mp hp).2
        exact mul_le_mul_of_nonneg_left (log_le_sub_one_232 (hz_pos p hp))
          (div_pos hBp hR_pos).le
      have h2 : ∑ p ∈ SB, (B p / R) * (z p - 1) =
          (∑ p ∈ SB, A p.1 p.2 * x p.1 * y p.2) / N - 1 := by
        have hcancel : ∀ p ∈ SB, (B p / R) * (z p - 1) =
            (A p.1 p.2 * x p.1 * y p.2) / N - B p / R := by
          intro p hp
          have hBp : B p ≠ 0 := ((Finset.mem_filter.mp hp).2).ne'
          have hRne : R ≠ 0 := hR_pos.ne'
          dsimp [z]
          rw [mul_sub, mul_one, mul_div_cancel₀ _ (div_ne_zero hBp hRne)]
        rw [Finset.sum_congr rfl hcancel, Finset.sum_sub_distrib, ← Finset.sum_div, hw_sum]
      have h3 : ∑ p ∈ SB, A p.1 p.2 * x p.1 * y p.2 ≤ N := by
        have hle_univ : ∑ p ∈ SB, A p.1 p.2 * x p.1 * y p.2 ≤
            ∑ p : ι × κ, A p.1 p.2 * x p.1 * y p.2 :=
          Finset.sum_le_univ_sum_of_nonneg fun p =>
            mul_nonneg (mul_nonneg (hA p.1 p.2) (hx p.1).le) (hy p.2).le
        rwa [Fintype.sum_prod_type] at hle_univ
      have hdiv_le : (∑ p ∈ SB, A p.1 p.2 * x p.1 * y p.2) / N ≤ 1 :=
        (div_le_one hN_pos).mpr h3
      linarith
    have hlog_expand : ∑ p ∈ SB, (B p / R) * Real.log (z p) =
        (∑ p ∈ SB, (B p / R) * Real.log (A p.1 p.2 / B p)) +
          Real.log Dx + Real.log Dy + Real.log R - Real.log N := by
      have hpt : ∀ p ∈ SB, (B p / R) * Real.log (z p) =
          (B p / R) * Real.log (A p.1 p.2 / B p) +
            (B p / R) * Real.log (x p.1) +
            (B p / R) * Real.log (y p.2) +
            (B p / R) * (Real.log R - Real.log N) := by
        intro p hp
        have hBp : 0 < B p := (Finset.mem_filter.mp hp).2
        have hAp : 0 < A p.1 p.2 := hSB_Apos p hp
        have hz_eq : z p = (A p.1 p.2 / B p) * x p.1 * y p.2 * (R / N) := by
          dsimp [z]
          have hBne : B p ≠ 0 := hBp.ne'
          have hRne : R ≠ 0 := hR_pos.ne'
          have hNne : N ≠ 0 := hN_pos.ne'
          field_simp [hBne, hRne, hNne]
        rw [hz_eq,
          Real.log_mul (mul_pos (mul_pos (div_pos hAp hBp) (hx p.1)) (hy p.2)).ne'
            (div_pos hR_pos hN_pos).ne',
          Real.log_mul (mul_pos (div_pos hAp hBp) (hx p.1)).ne' (hy p.2).ne',
          Real.log_mul (div_pos hAp hBp).ne' (hx p.1).ne',
          Real.log_div hR_pos.ne' hN_pos.ne']
        ring
      rw [Finset.sum_congr rfl hpt]
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hw_sum, one_mul]
      have hx_term : ∑ p ∈ SB, (B p / R) * Real.log (x p.1) = Real.log Dx := by
        have h1 : ∑ p ∈ SB, (B p / R) * Real.log (x p.1) =
            ∑ p ∈ SB, B p * (Real.log (x p.1) / R) :=
          Finset.sum_congr rfl fun p _ => by ring
        rw [h1, hsum_SB_eq, Fintype.sum_prod_type]
        have h2 : ∀ i : ι, ∑ j : κ, B (i, j) * (Real.log (x i) / R) =
            (r i / R) * Real.log (x i) := by
          intro i
          rw [← Finset.sum_mul, hB_row i]
          ring
        simp_rw [h2]
        dsimp [Dx]
        rw [Real.log_prod fun i _ => (Real.rpow_pos_of_pos (hx i) _).ne']
        exact Finset.sum_congr rfl fun i _ => by rw [Real.log_rpow (hx i), mul_comm]
      have hy_term : ∑ p ∈ SB, (B p / R) * Real.log (y p.2) = Real.log Dy := by
        have h1 : ∑ p ∈ SB, (B p / R) * Real.log (y p.2) =
            ∑ p ∈ SB, B p * (Real.log (y p.2) / R) :=
          Finset.sum_congr rfl fun p _ => by ring
        rw [h1, hsum_SB_eq, Fintype.sum_prod_type, Finset.sum_comm]
        have h2 : ∀ j : κ, ∑ i : ι, B (i, j) * (Real.log (y j) / R) =
            (c j / C) * Real.log (y j) := by
          intro j
          rw [← Finset.sum_mul, hB_col j]
          dsimp [R, C]
          rw [hRC]
          ring
        simp_rw [h2]
        dsimp [Dy]
        rw [Real.log_prod fun j _ => (Real.rpow_pos_of_pos (hy j) _).ne']
        exact Finset.sum_congr rfl fun j _ => by rw [Real.log_rpow (hy j), mul_comm]
      rw [hx_term, hy_term]
      ring
    rw [hlog_expand] at hle_zero
    have hlog_δ : Real.log δ = Real.log R + ∑ p ∈ SB, (B p / R) * Real.log (A p.1 p.2 / B p) := by
      dsimp [δ]
      rw [Real.log_mul hR_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    have hlog_κ : Real.log (kappa A r c x y) = Real.log N - Real.log Dx - Real.log Dy := by
      have hk : kappa A r c x y = N / (Dx * Dy) := rfl
      rw [hk, Real.log_div hN_pos.ne' (mul_pos hDx_pos hDy_pos).ne',
        Real.log_mul hDx_pos.ne' hDy_pos.ne']
      ring
    have hlog_le : Real.log δ ≤ Real.log (kappa A r c x y) := by linarith
    exact (Real.log_le_log_iff (mul_pos hR_pos (Real.exp_pos _)) hκ_pos).mp hlog_le
  · rintro ⟨δ, hδ_pos, hδ_le⟩ ε hε
    by_contra hnot
    push Not at hnot
    let xT : ℕ → ι → ℝ := skRow A r c
    let yT : ℕ → κ → ℝ := fun t => colNorm A c (xT t)
    have hxy_pos : ∀ t, (∀ i, 0 < xT t i) ∧ (∀ j, 0 < yT t j) :=
      fun t => skRow_pos A hA hrow hcol r c hr hc t
    have hcol_exact : ∀ t j, ∑ i, A i j * xT t i * yT t j = c j := by
      intro t j
      obtain ⟨i₀, hi₀⟩ := hcol j
      have ht_pos : 0 < ∑ i, A i j * xT t i :=
        (mul_pos hi₀ ((hxy_pos t).1 i₀)).trans_le
          (Finset.single_le_sum (f := fun i => A i j * xT t i)
            (fun i _ => mul_nonneg (hA i j) ((hxy_pos t).1 i).le) (Finset.mem_univ i₀))
      rw [← Finset.sum_mul]
      dsimp [yT, colNorm]
      exact mul_div_cancel₀ (c j) ht_pos.ne'
    have hrow_ge_ε : ∀ t : ℕ, ε ≤ ∑ i, |r i - ∑ j, A i j * xT t i * yT t j| := by
      intro t
      have ht := hnot (xT t) (yT t) (hxy_pos t).1 (hxy_pos t).2
      have hcol0 : ∑ j, |(∑ i, A i j * xT t i * yT t j) - c j| = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hcol_exact t j, sub_self, abs_zero]
      rw [hcol0, add_zero] at ht
      have heq : ∑ i, |(∑ j, A i j * xT t i * yT t j) - r i| =
          ∑ i, |r i - ∑ j, A i j * xT t i * yT t j| :=
        Finset.sum_congr rfl fun i _ => abs_sub_comm _ (r i)
      rwa [heq] at ht
    let η : ℝ := ε ^ 2 / (2 * R ^ 2)
    have hη_pos : 0 < η := div_pos (sq_pos_of_pos hε) (mul_pos zero_lt_two (sq_pos_of_pos hR_pos))
    have hstep_dec : ∀ t : ℕ,
        Real.log (kappa A r c (xT (t + 1)) (yT (t + 1))) -
          Real.log (kappa A r c (xT t) (yT t)) ≤ -η := by
      intro t
      let p : ι → ℝ := fun i => ∑ j, A i j * xT t i * yT t j
      let q : κ → ℝ := fun j => ∑ i, A i j * xT (t + 1) i * yT t j
      have hp_pos : ∀ i, 0 < p i := by
        intro i
        obtain ⟨j₀, hj₀⟩ := hrow i
        exact (mul_pos (mul_pos hj₀ ((hxy_pos t).1 i)) ((hxy_pos t).2 j₀)).trans_le
          (Finset.single_le_sum (f := fun j => A i j * xT t i * yT t j)
            (fun j _ => mul_nonneg (mul_nonneg (hA i j) ((hxy_pos t).1 i).le)
              ((hxy_pos t).2 j).le) (Finset.mem_univ j₀))
      have hq_pos : ∀ j, 0 < q j := by
        intro j
        obtain ⟨i₀, hi₀⟩ := hcol j
        exact (mul_pos (mul_pos hi₀ ((hxy_pos (t + 1)).1 i₀)) ((hxy_pos t).2 j)).trans_le
          (Finset.single_le_sum (f := fun i => A i j * xT (t + 1) i * yT t j)
            (fun i _ => mul_nonneg (mul_nonneg (hA i j) ((hxy_pos (t + 1)).1 i).le)
              ((hxy_pos t).2 j).le) (Finset.mem_univ i₀))
      have hrow_exact_next : ∀ i, ∑ j, A i j * xT (t + 1) i * yT t j = r i := by
        intro i
        obtain ⟨j₀, hj₀⟩ := hrow i
        have hs_pos : 0 < ∑ j, A i j * yT t j :=
          (mul_pos hj₀ ((hxy_pos t).2 j₀)).trans_le
            (Finset.single_le_sum (f := fun j => A i j * yT t j)
              (fun j _ => mul_nonneg (hA i j) ((hxy_pos t).2 j).le) (Finset.mem_univ j₀))
        have hmul : ∑ j, A i j * xT (t + 1) i * yT t j = xT (t + 1) i * ∑ j, A i j * yT t j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hmul]
        change rowNorm A r (yT t) i * (∑ j, A i j * yT t j) = r i
        exact div_mul_cancel₀ (r i) hs_pos.ne'
      have hp_sum : ∑ i, r i = ∑ i, p i := by
        dsimp [p]
        rw [Finset.sum_comm]
        simp_rw [hcol_exact t]
        exact hRC
      have hq_sum : ∑ j, c j = ∑ j, q j := by
        dsimp [q]
        rw [Finset.sum_comm]
        simp_rw [hrow_exact_next]
        exact hRC.symm
      have hno_rp : ¬ ∃ i, p i = 0 ∧ 0 < r i := fun ⟨i, hp0, _⟩ => (hp_pos i).ne' hp0
      have hno_cq : ¬ ∃ j, q j = 0 ∧ 0 < c j := fun ⟨j, hq0, _⟩ => (hq_pos j).ne' hq0
      have h24 := lemma_2_4 A hA hrow hcol r c hr hc hRC (xT t) (hxy_pos t).1
      change ((Real.log (kappa A r c (xT (t + 1)) (yT (t + 1))) -
          Real.log (kappa A r c (xT t) (yT t)) : ℝ) : EReal) =
        -(klDiv r p) / ((R : ℝ) : EReal) - klDiv c q / ((C : ℝ) : EReal) at h24
      rw [klDiv, if_neg hno_rp, klDiv, if_neg hno_cq] at h24
      have hreal_eq : Real.log (kappa A r c (xT (t + 1)) (yT (t + 1))) -
          Real.log (kappa A r c (xT t) (yT t)) =
          -(∑ i, r i * Real.log (r i / p i)) / R -
            (∑ j, c j * Real.log (c j / q j)) / C := EReal.coe_eq_coe_iff.mp h24
      have hp11 := lemma_1_1 r p (fun i => (hr i).le) (fun i => (hp_pos i).le) hp_sum
      rw [klDiv, if_neg hno_rp, EReal.coe_le_coe_iff] at hp11
      have hq11 := lemma_1_1 c q (fun j => (hc j).le) (fun j => (hq_pos j).le) hq_sum
      rw [klDiv, if_neg hno_cq, EReal.coe_le_coe_iff] at hq11
      have hkl_cq_nn : 0 ≤ (∑ j, c j * Real.log (c j / q j)) / C := by
        have h0 : 0 ≤ (∑ j, |c j - q j|) ^ 2 / (2 * ∑ j, c j) :=
          div_nonneg (sq_nonneg _) (mul_nonneg zero_le_two hC_pos.le)
        exact div_nonneg (h0.trans hq11) hC_pos.le
      have hkl_rp_lb : η ≤ (∑ i, r i * Real.log (r i / p i)) / R := by
        have hge : ε ≤ ∑ i, |r i - p i| := hrow_ge_ε t
        have hsq : ε ^ 2 ≤ (∑ i, |r i - p i|) ^ 2 := by nlinarith [hge, hε]
        have h1 : ε ^ 2 / (2 * R) ≤ ∑ i, r i * Real.log (r i / p i) := by
          have : ε ^ 2 / (2 * R) ≤ (∑ i, |r i - p i|) ^ 2 / (2 * ∑ i, r i) :=
            div_le_div_of_nonneg_right hsq (mul_nonneg zero_le_two hR_pos.le)
          exact this.trans hp11
        have h2 := div_le_div_of_nonneg_right h1 hR_pos.le
        have hrew : (ε ^ 2 / (2 * R)) / R = η := by
          dsimp [η]
          have hRne : R ≠ 0 := hR_pos.ne'
          field_simp [hRne]
        rwa [hrew] at h2
      rw [hreal_eq, neg_div]
      linarith
    have hind : ∀ T : ℕ, Real.log (kappa A r c (xT T) (yT T)) ≤
        Real.log (kappa A r c (xT 0) (yT 0)) - (T : ℝ) * η := by
      intro T
      induction T with
      | zero => simp
      | succ T ih =>
          have hst := hstep_dec T
          push_cast
          linarith
    obtain ⟨T, hT⟩ := exists_nat_gt
      ((Real.log (kappa A r c (xT 0) (yT 0)) - Real.log δ) / η)
    have hT_mul : Real.log (kappa A r c (xT 0) (yT 0)) - Real.log δ < (T : ℝ) * η :=
      (div_lt_iff₀ hη_pos).mp hT
    have hδT := hδ_le (xT T) (yT T) (hxy_pos T).1 (hxy_pos T).2
    have hlog_δT : Real.log δ ≤ Real.log (kappa A r c (xT T) (yT T)) :=
      Real.log_le_log hδ_pos hδT
    linarith [hind T]
