-- Prove2me | solution 1 for OracleRO.ApproxFPL.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:45:57.038766+00:00
-- url     : https://prove2.me/submissions/cdeec653-66b8-497a-8696-1621f3afadd3

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_IsApproxLinOracle
import Definitions.Def_OracleRO_ApproxFPL_FPL

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

/-- `∏ (L - d_i)_+ ≥ L^k (1 - L⁻¹ ∑ d_i)` for `d_i ≥ 0`, with the side facts `0 ≤ ∏ ≤ L^k`. -/
theorem fpl6_prod_trunc {ι : Type*} (s : Finset ι) (L : ℝ) (hL : 0 < L) (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) :
    0 ≤ ∏ i ∈ s, max (L - d i) 0 ∧ ∏ i ∈ s, max (L - d i) 0 ≤ L ^ s.card ∧
    L ^ s.card - ∏ i ∈ s, max (L - d i) 0 ≤ L ^ s.card * L⁻¹ * ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj, Finset.sum_insert hj, pow_succ]
    set y := ∏ i ∈ s, max (L - d i) 0
    set x := L ^ s.card
    set S := ∑ i ∈ s, d i
    have hm0 : 0 ≤ max (L - d j) 0 := le_max_right _ _
    have hm1 : max (L - d j) 0 ≤ L := max_le (by linarith [hd j]) hL.le
    have hm2 : L - d j ≤ max (L - d j) 0 := le_max_left _ _
    refine ⟨mul_nonneg hm0 h0, ?_, ?_⟩
    · calc max (L - d j) 0 * y ≤ L * x := mul_le_mul hm1 h1 h0 hL.le
        _ = x * L := mul_comm _ _
    · have e1 : L * (x - y) ≤ x * S := by
        have := mul_le_mul_of_nonneg_left h2 hL.le
        calc L * (x - y) ≤ L * (x * L⁻¹ * S) := this
          _ = x * S := by field_simp
      have e2 : (L - max (L - d j) 0) * y ≤ d j * x :=
        mul_le_mul (by linarith) h1 h0 (hd j)
      have hx : x * L * L⁻¹ = x := by field_simp
      rw [hx]
      nlinarith [e1, e2]

open OracleRO.ApproxFPL in
theorem fpl6_perturb_integral {n : ℕ} (η : ℝ) (h : (Fin n → ℝ) → ℝ) :
    ∫ p, h p ∂(perturbLaw n η) =
      ((volume (Set.Icc (0 : Fin n → ℝ) (fun _ => η⁻¹)))⁻¹).toReal *
        ∫ p in Set.Icc (0 : Fin n → ℝ) (fun _ => η⁻¹), h p := by
  rw [perturbLaw, ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul]

theorem fpl6_integral_shift {n : ℕ} (c a : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ) :
    ∫ p in Set.Icc (0 : Fin n → ℝ) c, g (a + p) = ∫ u in Set.Icc a (a + c), g u := by
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
  have : (Set.Icc (0 : Fin n → ℝ) c).indicator (fun p => g (a + p)) =
      fun p => (Set.Icc a (a + c)).indicator g (a + p) := by
    funext p
    by_cases hp : p ∈ Set.Icc (0 : Fin n → ℝ) c
    · have hp' : a + p ∈ Set.Icc a (a + c) :=
        ⟨le_add_of_nonneg_right hp.1, (add_le_add_iff_left a).mpr hp.2⟩
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp']
    · have hp' : a + p ∉ Set.Icc a (a + c) := fun h =>
        hp ⟨(le_add_iff_nonneg_right a).mp h.1, (add_le_add_iff_left a).mp h.2⟩
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
  rw [this, integral_add_left_eq_self]

theorem fpl6_vol_box {n : ℕ} (L : ℝ) (hL : 0 < L) (a : Fin n → ℝ) :
    volume.real (Set.Icc a (a + fun _ => L)) = L ^ n := by
  rw [measureReal_def, Real.volume_Icc_pi_toReal (by intro i; simp [hL.le])]
  simp

theorem fpl6_vol_inter {n : ℕ} (L : ℝ) (a d : Fin n → ℝ) :
    volume.real (Set.Icc a (a + fun _ => L) ∩ Set.Icc (a + d) (a + d + fun _ => L)) =
      ∏ i, max (L - |d i|) 0 := by
  rw [Set.Icc_inter_Icc, measureReal_def, Real.volume_Icc_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_ofReal']
  congr 1
  simp only [Pi.add_apply, Pi.inf_apply, Pi.sup_apply]
  rcases le_total 0 (d i) with h | h
  · rw [abs_of_nonneg h, min_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, min_eq_right (by linarith), max_eq_left (by linarith)]; ring

theorem fpl6_shift_bound {n : ℕ} (L : ℝ) (hL : 0 < L) (g : (Fin n → ℝ) → ℝ)
    (hg : Measurable g) (R : ℝ) (hgR : ∀ u v, g u - g v ≤ R) (a d : Fin n → ℝ) :
    (∫ u in Set.Icc (a + d) (a + d + fun _ => L), g u) -
        (∫ u in Set.Icc a (a + fun _ => L), g u) ≤ R * (L ^ n * L⁻¹ * ∑ i, |d i|) := by
  set A := Set.Icc a (a + fun _ => L) with hA
  set B := Set.Icc (a + d) (a + d + fun _ => L) with hB
  have hbdd : BddBelow (Set.range g) := ⟨g 0 - R, by rintro _ ⟨u, rfl⟩; linarith [hgR 0 u]⟩
  set m := ⨅ u, g u
  have hm1 : ∀ u, m ≤ g u := fun u => ciInf_le hbdd u
  have hm2 : ∀ u, g u ≤ m + R := fun u => by
    have : g u - R ≤ m := le_ciInf (fun v => by linarith [hgR u v])
    linarith
  have hR0 : 0 ≤ R := by linarith [hgR 0 0]
  have hAf : volume A < ⊤ := isCompact_Icc.measure_lt_top
  have hBf : volume B < ⊤ := isCompact_Icc.measure_lt_top
  have hint : ∀ s : Set (Fin n → ℝ), volume s ≠ ⊤ → IntegrableOn g s := fun s hs =>
    Measure.integrableOn_of_bounded (M := |m| + R) hs hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hm1 u, hm2 u, neg_abs_le m, le_abs_self m])
  have hcst : ∀ (s : Set (Fin n → ℝ)) (k : ℝ), volume s ≠ ⊤ →
      IntegrableOn (fun _ => k) s := fun s k hs =>
    Measure.integrableOn_of_bounded (M := ‖k‖) hs aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun _ => le_rfl)
  have hBAf : volume (B \ A) ≠ ⊤ := ((measure_mono Set.sdiff_subset).trans_lt hBf).ne
  have hABf : volume (A \ B) ≠ ⊤ := ((measure_mono Set.sdiff_subset).trans_lt hAf).ne
  have e1 := integral_inter_add_sdiff (s := B) (t := A) (f := g) (μ := volume)
    measurableSet_Icc (hint B hBf.ne)
  have e2 := integral_inter_add_sdiff (s := A) (t := B) (f := g) (μ := volume)
    measurableSet_Icc (hint A hAf.ne)
  rw [Set.inter_comm] at e1
  have hBA : ∫ u in B \ A, g u ≤ volume.real (B \ A) * (m + R) := by
    have := setIntegral_mono_on (hint _ hBAf) (hcst _ (m + R) hBAf)
      (measurableSet_Icc.diff measurableSet_Icc) (fun u _ => hm2 u)
    rwa [setIntegral_const, smul_eq_mul] at this
  have hAB : volume.real (A \ B) * m ≤ ∫ u in A \ B, g u := by
    have := setIntegral_mono_on (hcst _ m hABf) (hint _ hABf)
      (measurableSet_Icc.diff measurableSet_Icc) (fun u _ => hm1 u)
    rwa [setIntegral_const, smul_eq_mul] at this
  have v1 := measureReal_inter_add_sdiff (μ := volume) (s := A) (t := B) measurableSet_Icc hAf.ne
  have v2 := measureReal_inter_add_sdiff (μ := volume) (s := B) (t := A) measurableSet_Icc hBf.ne
  rw [Set.inter_comm] at v2
  have vA : volume.real A = L ^ n := fpl6_vol_box L hL a
  have vB : volume.real B = L ^ n := by
    rw [hB]; exact fpl6_vol_box L hL (a + d)
  have vI : volume.real (A ∩ B) = ∏ i, max (L - |d i|) 0 := fpl6_vol_inter L a d
  have hP := (fpl6_prod_trunc Finset.univ L hL (fun i => |d i|) (fun i => abs_nonneg _)).2.2
  rw [Finset.card_univ, Fintype.card_fin] at hP
  have hW : volume.real (B \ A) = L ^ n - ∏ i, max (L - |d i|) 0 := by linarith
  have hW' : volume.real (A \ B) = L ^ n - ∏ i, max (L - |d i|) 0 := by linarith
  rw [hW] at hBA
  rw [hW'] at hAB
  have : (∫ u in B, g u) - (∫ u in A, g u) = (∫ u in B \ A, g u) - (∫ u in A \ B, g u) := by
    linarith
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left hP hR0]

open OracleRO.ApproxFPL in
theorem fpl6_btl {n : ℕ} (K : Set (Fin n → ℝ)) (ε : ℝ)
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsApproxLinOracle K ε M)
    (f : ℕ → Fin n → ℝ) (p : Fin n → ℝ) (N : ℕ) :
    ∀ x ∈ K, (prefixSum f N + p) ⬝ᵥ x - (N + 1) * ε ≤
      p ⬝ᵥ M p + ∑ t ∈ Finset.Icc 1 N, f t ⬝ᵥ M (prefixSum f t + p) := by
  induction N with
  | zero =>
    intro x hx
    have h0 : prefixSum f 0 = 0 := by simp [prefixSum]
    have := (hM p).2 x hx
    simp [h0]
    linarith
  | succ N ih =>
    intro x hx
    have hS : prefixSum f (N + 1) = prefixSum f N + f (N + 1) := by
      unfold prefixSum
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [Finset.sum_Icc_succ_top (by omega)]
    set y := M (prefixSum f (N + 1) + p)
    have hy : y ∈ K := (hM _).1
    have h1 := ih y hy
    have h2 := (hM (prefixSum f (N + 1) + p)).2 x hx
    have h3 : (prefixSum f (N + 1) + p) ⬝ᵥ y = (prefixSum f N + p) ⬝ᵥ y + f (N + 1) ⬝ᵥ y := by
      rw [hS, add_dotProduct, add_dotProduct, add_dotProduct]; ring
    push_cast
    linarith

open OracleRO.ApproxFPL in
theorem fpl6_prefix_succ {n : ℕ} (f : ℕ → Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    prefixSum f t = prefixSum f (t - 1) + f t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold prefixSum
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem fpl6_dot_meas {n : ℕ} (v : Fin n → ℝ) : Continuous (fun x : Fin n → ℝ => v ⬝ᵥ x) := by
  unfold dotProduct
  fun_prop

open OracleRO.ApproxFPL in
theorem solution {n : ℕ} (K : Set (Fin n → ℝ)) (ε : ℝ) (hε : 0 < ε)
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsApproxLinOracle K ε M) (hMmeas : Measurable M)
    (f : ℕ → Fin n → ℝ) (T : ℕ) (hT : 1 ≤ T) (D R A : ℝ)
    (hD0 : 0 < D) (hR0 : 0 < R) (hA0 : 0 < A)
    (hD : ∀ x ∈ K, ∀ y ∈ K, ∑ i, |x i - y i| ≤ D)
    (hR : ∀ t ∈ Finset.Icc 1 T, ∀ x ∈ K, ∀ y ∈ K, |f t ⬝ᵥ x - f t ⬝ᵥ y| ≤ R)
    (hA : ∀ t ∈ Finset.Icc 1 T, ∑ i, |f t i| ≤ A) :
    ∀ xStar ∈ K, (∑ t ∈ Finset.Icc 1 T, f t ⬝ᵥ xStar) -
        fplExpectedReward M f (Real.sqrt (D / (R * A * T))) T ≤
      2 * Real.sqrt (D * R * A * T) + 2 * ε * T := by
  intro xStar hx
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  set η := Real.sqrt (D / (R * A * T)) with hη
  have hη0 : 0 < η := Real.sqrt_pos.mpr (by positivity)
  set s := Real.sqrt (D * R * A * T) with hs
  have hηs : η * s = D := by
    rw [hη, hs, ← Real.sqrt_mul (by positivity)]
    have : D / (R * A * T) * (D * R * A * T) = D * D := by field_simp
    rw [this, Real.sqrt_mul_self hD0.le]
  have hηR : η * (R * A * T) = s := by
    have h1 : (η * (R * A * T)) ^ 2 = D * R * A * T := by
      rw [mul_pow, hη, Real.sq_sqrt (by positivity)]
      field_simp
    rw [hs, ← h1, Real.sqrt_sq (by positivity)]
  set L := η⁻¹ with hLdef
  have hL : 0 < L := inv_pos.mpr hη0
  have hLD : L * D = s := by
    rw [hLdef, ← hηs]; field_simp
  set Q := Set.Icc (0 : Fin n → ℝ) (fun _ => L) with hQ
  have hQf : volume Q < ⊤ := isCompact_Icc.measure_lt_top
  have hVol : volume.real Q = L ^ n := by
    have := fpl6_vol_box (n := n) L hL 0
    simpa using this
  have hκ : ((volume Q)⁻¹).toReal = (L ^ n)⁻¹ := by
    rw [ENNReal.toReal_inv, ← measureReal_def, hVol]
  have hLn : 0 < L ^ n := pow_pos hL n
  -- the expected reward as a sum of normalized set integrals
  have hE : fplExpectedReward M f η T = ∑ t ∈ Finset.Icc 1 T,
      (L ^ n)⁻¹ * ∫ p in Q, f t ⬝ᵥ M (prefixSum f (t - 1) + p) := by
    unfold fplExpectedReward
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [fpl6_perturb_integral, ← hLdef, hκ]
  -- measurability / integrability of the round rewards
  have hmeas : ∀ t (a : Fin n → ℝ), Measurable (fun p : Fin n → ℝ => f t ⬝ᵥ M (a + p)) :=
    fun t a => (fpl6_dot_meas (f t)).measurable.comp (hMmeas.comp (measurable_const_add a))
  have hint : ∀ t ∈ Finset.Icc 1 T, ∀ a : Fin n → ℝ,
      IntegrableOn (fun p : Fin n → ℝ => f t ⬝ᵥ M (a + p)) Q := by
    intro t ht a
    refine Measure.integrableOn_of_bounded (M := |f t ⬝ᵥ xStar| + R) hQf.ne
      (hmeas t a).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    have h1 := hR t ht _ (hM (a + p)).1 xStar hx
    rw [Real.norm_eq_abs]
    calc |f t ⬝ᵥ M (a + p)| = |(f t ⬝ᵥ M (a + p) - f t ⬝ᵥ xStar) + f t ⬝ᵥ xStar| := by ring_nf
      _ ≤ |f t ⬝ᵥ M (a + p) - f t ⬝ᵥ xStar| + |f t ⬝ᵥ xStar| := abs_add_le _ _
      _ ≤ |f t ⬝ᵥ xStar| + R := by linarith
  -- (2) stability: one-step shift of the perturbed leader
  have hstab : ∀ t ∈ Finset.Icc 1 T,
      (L ^ n)⁻¹ * (∫ p in Q, f t ⬝ᵥ M (prefixSum f t + p)) -
        (L ^ n)⁻¹ * (∫ p in Q, f t ⬝ᵥ M (prefixSum f (t - 1) + p)) ≤ R * η * A := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    have hg : Measurable (fun u : Fin n → ℝ => f t ⬝ᵥ M u) :=
      (fpl6_dot_meas (f t)).measurable.comp hMmeas
    have hgR : ∀ u v, f t ⬝ᵥ M u - f t ⬝ᵥ M v ≤ R := fun u v =>
      (abs_le.mp (hR t ht _ (hM u).1 _ (hM v).1)).2
    have key := fpl6_shift_bound L hL (fun u => f t ⬝ᵥ M u) hg R hgR (prefixSum f (t - 1)) (f t)
    rw [hQ, fpl6_integral_shift (fun _ => L) (prefixSum f t) (fun u => f t ⬝ᵥ M u),
      fpl6_integral_shift (fun _ => L) (prefixSum f (t - 1)) (fun u => f t ⬝ᵥ M u),
      fpl6_prefix_succ f t ht1]
    rw [← mul_sub]
    have hA' := hA t ht
    calc (L ^ n)⁻¹ * ((∫ u in Set.Icc (prefixSum f (t - 1) + f t)
            (prefixSum f (t - 1) + f t + fun _ => L), f t ⬝ᵥ M u) -
          (∫ u in Set.Icc (prefixSum f (t - 1)) (prefixSum f (t - 1) + fun _ => L), f t ⬝ᵥ M u))
        ≤ (L ^ n)⁻¹ * (R * (L ^ n * L⁻¹ * ∑ i, |f t i|)) :=
          mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hLn.le)
      _ = R * η * ∑ i, |f t i| := by rw [hLdef, inv_inv]; field_simp
      _ ≤ R * η * A := mul_le_mul_of_nonneg_left hA' (by positivity)
  -- (1) be-the-leader, integrated
  have hbtl : (∑ t ∈ Finset.Icc 1 T, f t ⬝ᵥ xStar) - (L * D + (T + 1) * ε) ≤
      ∑ t ∈ Finset.Icc 1 T, (L ^ n)⁻¹ * ∫ p in Q, f t ⬝ᵥ M (prefixSum f t + p) := by
    rw [← Finset.mul_sum, ← integral_finsetSum _ (fun t ht => hint t ht _)]
    set C := (∑ t ∈ Finset.Icc 1 T, f t ⬝ᵥ xStar) - (L * D + (T + 1) * ε)
    have hcst : IntegrableOn (fun _ : Fin n → ℝ => C) Q :=
      Measure.integrableOn_of_bounded (M := ‖C‖) hQf.ne aestronglyMeasurable_const
        (Filter.Eventually.of_forall fun _ => le_rfl)
    have hmono := setIntegral_mono_on hcst (integrable_finsetSum _ (fun t ht => hint t ht _))
      measurableSet_Icc (fun p hp => by
        have hb := fpl6_btl K ε M hM f p T xStar hx
        have hpd : p ⬝ᵥ M p - p ⬝ᵥ xStar ≤ L * D := by
          rw [← dotProduct_sub]
          unfold dotProduct
          calc ∑ i, p i * (M p - xStar) i ≤ ∑ i, L * |M p i - xStar i| := by
                refine Finset.sum_le_sum fun i _ => ?_
                have hp0 : 0 ≤ p i := hp.1 i
                have hp1 : p i ≤ L := hp.2 i
                calc p i * (M p - xStar) i ≤ |p i * (M p - xStar) i| := le_abs_self _
                  _ = p i * |M p i - xStar i| := by
                      rw [abs_mul, abs_of_nonneg hp0, Pi.sub_apply]
                  _ ≤ L * |M p i - xStar i| :=
                      mul_le_mul_of_nonneg_right hp1 (abs_nonneg _)
            _ = L * ∑ i, |M p i - xStar i| := by rw [Finset.mul_sum]
            _ ≤ L * D := mul_le_mul_of_nonneg_left (hD _ (hM p).1 _ hx) hL.le
        have hsum : prefixSum f T ⬝ᵥ xStar = ∑ t ∈ Finset.Icc 1 T, f t ⬝ᵥ xStar := by
          unfold prefixSum; rw [sum_dotProduct]
        rw [add_dotProduct, hsum] at hb
        show C ≤ _
        simp only [C]
        linarith)
    rw [setIntegral_const, smul_eq_mul, hVol] at hmono
    calc C = (L ^ n)⁻¹ * (L ^ n * C) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hLn.le)
  -- combine
  rw [hE]
  have hsumstab := Finset.sum_le_sum hstab
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsumstab
  have hTc : ((T + 1 - 1 : ℕ) : ℝ) = T := by rw [Nat.add_sub_cancel]
  rw [hTc] at hsumstab
  have hfin : (T : ℝ) * (R * η * A) = s := by rw [← hηR]; ring
  nlinarith [hbtl, hsumstab, hfin, hLD, hε, hT1]
