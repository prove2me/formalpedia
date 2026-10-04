-- Prove2me | solution 1 for SennottDP.ResidualLife.common_distributions_bmrl
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:23:19.681985+00:00
-- url     : https://prove2.me/submissions/99ee2d33-12d7-49ba-a949-460fb1e3d981

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist
import Definitions.Def_SennottDP_ResidualLife_Distributions

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife.CDB

theorem cdb_shift (g : ℕ → ℝ≥0∞) (s : ℕ) :
    ∑' y, (if s ≤ y then g y else 0) = ∑' i, g (s + i) := by
  have hsupp : Function.support (fun y => if s ≤ y then g y else 0) ⊆ Set.range (fun i => i + s) := by
    intro y hy
    by_cases h : s ≤ y
    · exact ⟨y - s, Nat.sub_add_cancel h⟩
    · rw [Function.mem_support] at hy; exact (hy (by simp [h])).elim
  rw [← (add_left_injective s).tsum_eq hsupp]
  refine tsum_congr fun i => ?_
  rw [if_pos (Nat.le_add_left s i), add_comm]

theorem cdb_tail_eq (u : ℕ → ℝ≥0∞) (n : ℕ) : tail u n = ∑' i, u (n + 1 + i) := by
  unfold tail
  rw [← cdb_shift u (n + 1)]
  refine tsum_congr fun w => ?_
  by_cases h : n < w
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem cdb_tail_anti (u : ℕ → ℝ≥0∞) {s t : ℕ} (h : s ≤ t) : tail u t ≤ tail u s := by
  unfold tail
  refine ENNReal.tsum_le_tsum fun w => ?_
  split_ifs with h1 h2 <;> first | exact le_rfl | exact bot_le | omega

theorem cdb_tail_sum (u : ℕ → ℝ≥0∞) (s : ℕ) :
    ∑' i, tail u (s + i) = ∑' y : ℕ, (y : ℝ≥0∞) * u (s + y) := by
  unfold tail
  rw [ENNReal.tsum_comm]
  have h1 : ∀ w, ∑' i, (if s + i < w then u w else 0) = ((w - s : ℕ) : ℝ≥0∞) * u w := by
    intro w
    rw [tsum_eq_sum (s := Finset.range (w - s))]
    · rw [Finset.sum_congr rfl (fun i hi => if_pos (by
        have := Finset.mem_range.mp hi; omega)), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · intro i hi
      rw [if_neg]
      intro h; exact hi (Finset.mem_range.mpr (by omega))
  simp_rw [h1]
  have h2 : ∀ w, ((w - s : ℕ) : ℝ≥0∞) * u w = if s ≤ w then ((w - s : ℕ) : ℝ≥0∞) * u w else 0 := by
    intro w
    split_ifs with h
    · rfl
    · rw [show w - s = 0 by omega]; simp
  rw [tsum_congr h2]
  rw [cdb_shift (fun w => ((w - s : ℕ) : ℝ≥0∞) * u w) s]
  refine tsum_congr fun i => ?_
  rw [Nat.add_sub_cancel_left]

theorem cdb_resid (u : ℕ → ℝ≥0∞) (s : ℕ) :
    residualMoment u s 1 = (∑' i, tail u (s + i)) * (tail u s)⁻¹ := by
  rw [cdb_tail_sum, ← ENNReal.tsum_mul_right]
  unfold residualMoment moment residualDist
  refine tsum_congr fun y => ?_
  split_ifs with hy
  · rw [pow_one, div_eq_mul_inv, mul_assoc]
  · rw [show y = 0 by omega]; simp

/-- Ratio criterion: if `u (n+1) ≤ ρ u n` for `n ≥ N` with `ρ < 1`, all `u n` are finite and
`u (N+1) > 0`, then `u` is BMRL. -/
theorem cdb_ratio (u : ℕ → ℝ≥0∞) (N : ℕ) (ρ : ℝ≥0) (hρ : ρ < 1)
    (hratio : ∀ n, N ≤ n → u (n + 1) ≤ ρ * u n) (hfin : ∀ n, u n ≠ ⊤) (hpos : 0 < u (N + 1)) :
    IsBMRLDist u := by
  have hρ' : (ρ : ℝ≥0∞) < 1 := by exact_mod_cast hρ
  have hgeo_ne : (1 - (ρ : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hρ').ne'
  -- geometric decay of `u` beyond `N`
  have hu_geo : ∀ j, u (N + j) ≤ (ρ : ℝ≥0∞) ^ j * u N := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc u (N + (j + 1)) = u (N + j + 1) := by rw [Nat.add_assoc]
        _ ≤ ρ * u (N + j) := hratio _ (Nat.le_add_right _ _)
        _ ≤ ρ * ((ρ : ℝ≥0∞) ^ j * u N) := by gcongr
        _ = (ρ : ℝ≥0∞) ^ (j + 1) * u N := by ring
  -- total mass is finite
  have hsum : ∑' n, u n ≠ ⊤ := by
    rw [← Summable.sum_add_tsum_nat_add' (f := u) (k := N) ENNReal.summable]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun n _ => hfin n, ?_⟩
    refine ne_top_of_le_ne_top (b := ∑' j, (ρ : ℝ≥0∞) ^ j * u N) ?_ ?_
    · rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      exact ENNReal.mul_ne_top hgeo_ne (hfin N)
    · exact ENNReal.tsum_le_tsum fun j => by rw [add_comm]; exact hu_geo j
  have htail_fin : ∀ n, tail u n ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp)
  -- tail ratio
  have htail_ratio : ∀ n, N ≤ n → tail u (n + 1) ≤ ρ * tail u n := by
    intro n hn
    rw [cdb_tail_eq, cdb_tail_eq, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [show n + 1 + 1 + i = (n + 1 + i) + 1 by omega]
    exact hratio _ (by omega)
  have htail_geo : ∀ s, N ≤ s → ∀ i, tail u (s + i) ≤ (ρ : ℝ≥0∞) ^ i * tail u s := by
    intro s hs i
    induction i with
    | zero => simp
    | succ i ih =>
      calc tail u (s + (i + 1)) = tail u (s + i + 1) := by rw [Nat.add_assoc]
        _ ≤ ρ * tail u (s + i) := htail_ratio _ (by omega)
        _ ≤ ρ * ((ρ : ℝ≥0∞) ^ i * tail u s) := by gcongr
        _ = (ρ : ℝ≥0∞) ^ (i + 1) * tail u s := by ring
  have htN : 0 < tail u N := by
    rw [cdb_tail_eq]
    exact lt_of_lt_of_le hpos (ENNReal.le_tsum 0)
  -- the constant for small `s`
  set K : ℝ≥0∞ := ∑' i, tail u i with hK
  have hK_fin : K ≠ ⊤ := by
    rw [hK, ← Summable.sum_add_tsum_nat_add' (f := tail u) (k := N) ENNReal.summable]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun n _ => htail_fin n, ?_⟩
    refine ne_top_of_le_ne_top (b := ∑' j, (ρ : ℝ≥0∞) ^ j * tail u N) ?_ ?_
    · rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      exact ENNReal.mul_ne_top hgeo_ne (htail_fin N)
    · exact ENNReal.tsum_le_tsum fun j => by rw [add_comm]; exact htail_geo N le_rfl j
  set B : ℝ≥0∞ := max ((1 - (ρ : ℝ≥0∞))⁻¹) (K * (tail u N)⁻¹) with hB
  have hB_fin : B ≠ ⊤ :=
    max_ne_top hgeo_ne (ENNReal.mul_ne_top hK_fin (ENNReal.inv_ne_top.mpr htN.ne'))
  refine ⟨B.toNNReal, fun s hs => ?_⟩
  rw [ENNReal.coe_toNNReal hB_fin, cdb_resid]
  rcases le_or_gt N s with hNs | hsN
  · refine le_trans ?_ (le_max_left _ _)
    calc (∑' i, tail u (s + i)) * (tail u s)⁻¹
        ≤ (∑' i, (ρ : ℝ≥0∞) ^ i * tail u s) * (tail u s)⁻¹ := by
          gcongr with i; exact htail_geo s hNs i
      _ = (1 - (ρ : ℝ≥0∞))⁻¹ := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_assoc,
            ENNReal.mul_inv_cancel hs.ne' (htail_fin s), mul_one]
  · refine le_trans ?_ (le_max_right _ _)
    gcongr
    · exact ENNReal.tsum_le_tsum fun i => cdb_tail_anti u (Nat.le_add_left i s)
    · exact cdb_tail_anti u hsN.le

theorem cdb_geom (μ : ℝ) (h0 : 0 < μ) (h1 : μ < 1) : IsBMRLDist (geomTrials μ) := by
  refine cdb_ratio _ 1 (Real.toNNReal (1 - μ)) (Real.toNNReal_lt_one.mpr (by linarith)) ?_ ?_ ?_
  · intro n hn
    show geomTrials μ (n + 1) ≤ ENNReal.ofReal (1 - μ) * geomTrials μ n
    unfold geomTrials
    rw [if_pos (by omega), if_pos hn, ← ENNReal.ofReal_mul (by linarith)]
    apply le_of_eq; congr 1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  · intro n; unfold geomTrials; split_ifs <;> simp
  · unfold geomTrials
    rw [if_pos (by norm_num)]
    exact ENNReal.ofReal_pos.mpr (by simp only [Nat.reduceAdd, Nat.add_one_sub_one, pow_one]; exact mul_pos h0 (by linarith))

theorem cdb_negbin (μ : ℝ) (h0 : 0 < μ) (h1 : μ < 1) (r : ℕ) (hr : 1 ≤ r) :
    IsBMRLDist (negBinTrials μ r) := by
  set N : ℕ := ⌈2 * (r : ℝ) / μ⌉₊ + r with hN
  refine cdb_ratio _ N (Real.toNNReal (1 - μ / 2)) (Real.toNNReal_lt_one.mpr (by linarith)) ?_ ?_ ?_
  · intro n hn
    show negBinTrials μ r (n + 1) ≤ ENNReal.ofReal (1 - μ / 2) * negBinTrials μ r n
    have hrn : r ≤ n := by omega
    have hnμ : 2 * (r : ℝ) / μ ≤ n := by
      have := Nat.le_ceil (2 * (r : ℝ) / μ)
      have h' : ((⌈2 * (r : ℝ) / μ⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (show ⌈2 * (r : ℝ) / μ⌉₊ ≤ n by omega)
      linarith
    have hrμ : (r : ℝ) ≤ n * μ / 2 := by
      rw [div_le_iff₀ h0] at hnμ; linarith
    unfold negBinTrials
    rw [if_pos (by omega), if_pos hrn, ← ENNReal.ofReal_mul (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    set k := r - 1 with hk
    set A : ℝ := ((n.choose k : ℕ) : ℝ) with hA
    set c : ℝ := (((n - 1).choose k : ℕ) : ℝ) with hc
    have hc0 : 0 ≤ c := Nat.cast_nonneg _
    have hkn : k < n := by omega
    have hid : c * n = A * ((n : ℝ) - k) := by
      have h := Nat.choose_mul_succ_eq (n - 1) k
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
      have h' : ((((n - 1).choose k * n : ℕ)) : ℝ) = ((n.choose k * (n - k) : ℕ) : ℝ) := by rw [h]
      push_cast [Nat.cast_sub hkn.le] at h'
      rw [hc, hA]; linarith
    have hk' : (k : ℝ) = r - 1 := by rw [hk]; push_cast [Nat.cast_sub hr]; ring
    have hgap : 0 ≤ (n : ℝ) * μ / 2 - k * (1 - μ / 2) := by
      rw [hk']; nlinarith
    have hnk : (0 : ℝ) < n - k := by
      have : (k : ℝ) < n := by exact_mod_cast hkn
      linarith
    have key : A * (1 - μ) ≤ (1 - μ / 2) * c := by
      have e : (1 - μ / 2) * c * (n - k) - A * (1 - μ) * (n - k) =
          c * ((n : ℝ) * μ / 2 - k * (1 - μ / 2)) := by linear_combination (1 - μ) * hid
      have : A * (1 - μ) * (n - k) ≤ (1 - μ / 2) * c * (n - k) := by nlinarith [mul_nonneg hc0 hgap]
      exact le_of_mul_le_mul_right this hnk
    have hP : 0 ≤ μ ^ r * (1 - μ) ^ (n - r) := by
      have : 0 ≤ 1 - μ := by linarith
      positivity
    rw [show n + 1 - 1 = n by omega, show n + 1 - r = n - r + 1 by omega, pow_succ]
    calc A * μ ^ r * ((1 - μ) ^ (n - r) * (1 - μ))
        = (A * (1 - μ)) * (μ ^ r * (1 - μ) ^ (n - r)) := by ring
      _ ≤ ((1 - μ / 2) * c) * (μ ^ r * (1 - μ) ^ (n - r)) := mul_le_mul_of_nonneg_right key hP
      _ = (1 - μ / 2) * (c * μ ^ r * (1 - μ) ^ (n - r)) := by ring
  · intro n; unfold negBinTrials; split_ifs <;> simp
  · unfold negBinTrials
    rw [if_pos (by omega)]
    refine ENNReal.ofReal_pos.mpr ?_
    have hch : 0 < (N + 1 - 1).choose (r - 1) := Nat.choose_pos (by omega)
    have h1μ : 0 < 1 - μ := by linarith
    have : (0 : ℝ) < ((N + 1 - 1).choose (r - 1) : ℕ) := by exact_mod_cast hch
    positivity

theorem cdb_poisson (lam : ℝ) (h0 : 0 < lam) : IsBMRLDist (truncPoisson lam) := by
  set E : ℝ := Real.exp (-lam) / (1 - Real.exp (-lam)) with hE
  have hE0 : 0 < E := by
    have : Real.exp (-lam) < 1 := Real.exp_lt_one_iff.mpr (by linarith) |>.trans_le' le_rfl
    exact div_pos (Real.exp_pos _) (by linarith)
  set N : ℕ := ⌈2 * lam⌉₊ + 1 with hN
  refine cdb_ratio _ N (Real.toNNReal (1 / 2)) (Real.toNNReal_lt_one.mpr (by norm_num)) ?_ ?_ ?_
  · intro n hn
    show truncPoisson lam (n + 1) ≤ ENNReal.ofReal (1 / 2) * truncPoisson lam n
    have hn2 : 2 * lam ≤ n := by
      have := Nat.le_ceil (2 * lam)
      have h' : ((⌈2 * lam⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (show ⌈2 * lam⌉₊ ≤ n by omega)
      linarith
    unfold truncPoisson
    rw [if_pos (by omega), if_pos (by omega), ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [← hE]
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hq : lam / (n + 1) ≤ 1 / 2 := by rw [div_le_iff₀ hn1]; linarith
    have hb : 0 ≤ E * lam ^ n / n.factorial := by positivity
    calc E * lam ^ (n + 1) / ((n + 1).factorial : ℝ)
        = (E * lam ^ n / n.factorial) * (lam / (n + 1)) := by
          rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]; push_cast; field_simp
      _ ≤ (E * lam ^ n / n.factorial) * (1 / 2) := mul_le_mul_of_nonneg_left hq hb
      _ = 1 / 2 * (E * lam ^ n / n.factorial) := by ring
  · intro n; unfold truncPoisson; split_ifs <;> simp
  · unfold truncPoisson
    rw [if_pos (by omega)]
    refine ENNReal.ofReal_pos.mpr ?_
    rw [← hE]
    have : (0 : ℝ) < ((N + 1).factorial : ℕ) := by exact_mod_cast Nat.factorial_pos _
    positivity

end SennottDP.ResidualLife.CDB

open SennottDP.ResidualLife SennottDP.ResidualLife.CDB in
theorem solution :
    (∀ μ : ℝ, 0 < μ → μ < 1 → IsBMRLDist (geomTrials μ)) ∧
    (∀ μ : ℝ, 0 < μ → μ < 1 → ∀ r : ℕ, 2 ≤ r → IsBMRLDist (negBinTrials μ r)) ∧
    (∀ lam : ℝ, 0 < lam → IsBMRLDist (truncPoisson lam)) :=
  ⟨fun μ h0 h1 => cdb_geom μ h0 h1, fun μ h0 h1 r hr => cdb_negbin μ h0 h1 r (by omega),
    fun lam h0 => cdb_poisson lam h0⟩


