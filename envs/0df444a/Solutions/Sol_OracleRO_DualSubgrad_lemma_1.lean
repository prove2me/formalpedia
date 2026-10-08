-- Prove2me | solution 1 for OracleRO.DualSubgrad.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:21:22.087711+00:00
-- url     : https://prove2.me/submissions/a38bedef-50b3-4b62-92e6-e9ff697c142b

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto

set_option autoImplicit false

open scoped RealInnerProductSpace in
theorem a9a39405_proj_nonexp {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hK : Convex ℝ K) (hP : SpectralProjGrad.Shared.IsProjOnto K P)
    (z y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ K) :
    ‖P z - y‖ ^ 2 ≤ ‖z - y‖ ^ 2 := by
  set p := P z with hp
  have hpK : p ∈ K := (hP z).1
  have hvi : ⟪z - p, y - p⟫ ≤ 0 := by
    by_contra hcon
    push Not at hcon
    set a := ⟪z - p, y - p⟫ with ha
    set b := ‖y - p‖ ^ 2 with hb'
    have hb : 0 ≤ b := by positivity
    set s : ℝ := min 1 (a / (b + 1)) with hsdef
    have hs0 : 0 < s := lt_min one_pos (div_pos hcon (by linarith))
    have hs1 : s ≤ 1 := min_le_left _ _
    have hs2 : s ≤ a / (b + 1) := min_le_right _ _
    have hw : p + s • (y - p) ∈ K := by
      have := hK hpK hy (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
      convert this using 1
      rw [smul_sub, sub_smul, one_smul]; abel
    have hmin := (hP z).2 _ hw
    have h1 : ‖z - p‖ ^ 2 ≤ ‖z - (p + s • (y - p))‖ ^ 2 := by
      have h0 : 0 ≤ ‖z - p‖ := norm_nonneg _
      exact pow_le_pow_left₀ h0 hmin 2
    have h2 : ‖z - (p + s • (y - p))‖ ^ 2 = ‖z - p‖ ^ 2 - 2 * s * a + s ^ 2 * b := by
      have : z - (p + s • (y - p)) = (z - p) - s • (y - p) := by abel
      rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
      ring
    have h3 : 2 * a ≤ s * b := by
      have : s * (2 * a) ≤ s * (s * b) := by nlinarith
      exact le_of_mul_le_mul_left this hs0
    have h4 : s * b ≤ a / (b + 1) * b := mul_le_mul_of_nonneg_right hs2 hb
    have h5 : a / (b + 1) * b < a := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  have hexp : z - y = (z - p) + (p - y) := by abel
  rw [hexp, norm_add_sq_real]
  have : ⟪z - p, p - y⟫ = -⟪z - p, y - p⟫ := by
    rw [← inner_neg_right, neg_sub]
  nlinarith [sq_nonneg ‖z - p‖, this, hvi]

open scoped RealInnerProductSpace in
theorem a9a39405_concave_grad {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {g x y : EuclideanSpace ℝ (Fin n)}
    (hF : ConcaveOn ℝ K F) (hg : HasGradientAt F g x) (hx : x ∈ K) (hy : y ∈ K) :
    F y - F x ≤ ⟪g, y - x⟫ := by
  have hfd := (hasGradientAt_iff_hasFDerivAt.mp hg).hasLineDerivAt (y - x)
  have ht := hfd.tendsto_slope_zero_right
  rw [InnerProductSpace.toDual_apply_apply] at ht
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 from one_pos)] with s hs
  obtain ⟨hs0, hs1⟩ := hs
  have hc := hF.2 hx hy (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
  have heq : (1 - s) • x + s • y = x + s • (y - x) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [heq, smul_eq_mul, smul_eq_mul] at hc
  rw [smul_eq_mul, le_inv_mul_iff₀ hs0]
  linarith

open scoped RealInnerProductSpace in
theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (g : ℕ → EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (T : ℕ) (D G : ℝ)
    (hK : Convex ℝ K) (hP : SpectralProjGrad.Shared.IsProjOnto K P)
    (hT : 1 ≤ T) (hD : 0 < D) (hG : 0 < G)
    (hdiam : ∀ y ∈ K, ∀ z ∈ K, ‖y - z‖ ≤ D)
    (hconc : ∀ t ∈ Finset.Icc 1 T, ConcaveOn ℝ K (f t))
    (hgrad : ∀ t ∈ Finset.Icc 1 T, HasGradientAt (f t) (g t) (x t))
    (hgradG : ∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ G)
    (hx1 : x 1 ∈ K)
    (hstep : ∀ t ∈ Finset.Ico 1 T, x (t + 1) = P (x t + (D / (G * Real.sqrt T)) • g t)) :
    ∀ xs ∈ K, ∑ t ∈ Finset.Icc 1 T, f t xs - ∑ t ∈ Finset.Icc 1 T, f t (x t)
      ≤ G * D * Real.sqrt T := by
  intro xs hxs
  set η : ℝ := D / (G * Real.sqrt T) with hη
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hsq2 : Real.sqrt T ^ 2 = T := Real.sq_sqrt hTpos.le
  have hηpos : 0 < η := div_pos hD (mul_pos hG hsq)
  -- iterates lie in K
  have hmem : ∀ t ∈ Finset.Icc 1 T, x t ∈ K := by
    intro t ht
    rcases Finset.mem_Icc.mp ht with ⟨h1, h2⟩
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · rw [← h]; exact hx1
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      rw [hstep s (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]
      exact (hP _).1
  set a : ℕ → ℝ := fun t => ‖x t - xs‖ ^ 2 with ha
  set b : ℕ → ℝ := fun t => ‖P (x t + η • g t) - xs‖ ^ 2 with hb
  -- per-step bound
  have hper : ∀ t ∈ Finset.Icc 1 T,
      f t xs - f t (x t) ≤ (a t - b t) / (2 * η) + η * G ^ 2 / 2 := by
    intro t ht
    have hc := a9a39405_concave_grad (hconc t ht) (hgrad t ht) (hmem t ht) hxs
    have hne := a9a39405_proj_nonexp hK hP (x t + η • g t) xs hxs
    have hexp : ‖x t + η • g t - xs‖ ^ 2
        = a t + 2 * η * ⟪g t, x t - xs⟫ + η ^ 2 * ‖g t‖ ^ 2 := by
      have : x t + η • g t - xs = (x t - xs) + η • g t := by abel
      rw [this, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, real_inner_comm]
      simp only [ha]
      ring
    have hgG : ‖g t‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hgradG t ht) 2
    have hinner : ⟪g t, xs - x t⟫ = -⟪g t, x t - xs⟫ := by
      rw [← inner_neg_right, neg_sub]
    have hkey : 2 * η * ⟪g t, xs - x t⟫ ≤ a t - b t + η ^ 2 * G ^ 2 := by
      have : b t ≤ a t + 2 * η * ⟪g t, x t - xs⟫ + η ^ 2 * ‖g t‖ ^ 2 := by
        simp only [hb]; rw [← hexp]; exact hne
      rw [hinner]
      nlinarith [sq_nonneg η]
    have h2η : 0 < 2 * η := by positivity
    rw [div_add' _ _ _ h2η.ne', le_div_iff₀ h2η]
    nlinarith
  -- telescoping
  have htel : ∀ m, 1 ≤ m → m ≤ T →
      ∑ t ∈ Finset.Icc 1 m, (a t - b t) = a 1 - b m := by
    intro m hm1 hmT
    induction m with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · rw [Finset.sum_Icc_succ_top (by omega), ih hk (by omega)]
        have : b k = a (k + 1) := by
          simp only [ha, hb]
          rw [hstep k (Finset.mem_Ico.mpr ⟨hk, by omega⟩)]
        rw [this]; ring
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, ← Finset.sum_div, htel T hT le_rfl, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul] at hsum
  rw [← Finset.sum_sub_distrib]
  have ha1 : a 1 ≤ D ^ 2 := by
    simp only [ha]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdiam _ hx1 _ hxs) 2
  have hb0 : 0 ≤ b T := by simp only [hb]; positivity
  have hfin : (a 1 - b T) / (2 * η) + ((T + 1 - 1 : ℕ) : ℝ) * (η * G ^ 2 / 2)
      ≤ G * D * Real.sqrt T := by
    have hcast : ((T + 1 - 1 : ℕ) : ℝ) = T := by simp
    rw [hcast]
    have h1 : (a 1 - b T) / (2 * η) ≤ D ^ 2 / (2 * η) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : D ^ 2 / (2 * η) + (T:ℝ) * (η * G ^ 2 / 2) = G * D * Real.sqrt T := by
      have aux : ∀ r : ℝ, 0 < r →
          D ^ 2 / (2 * (D / (G * r))) + r ^ 2 * (D / (G * r) * G ^ 2 / 2) = G * D * r := by
        intro r hr
        field_simp
        ring
      have := aux (Real.sqrt T) hsq
      rw [hsq2] at this
      rw [hη]
      exact this
    linarith
  linarith
