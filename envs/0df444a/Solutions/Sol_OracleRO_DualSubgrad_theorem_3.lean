-- Prove2me | solution 1 for OracleRO.DualSubgrad.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:31:31.701186+00:00
-- url     : https://prove2.me/submissions/c349ef76-d53f-46f4-94ae-6dedae90e637

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_OracleRO_DualSubgrad_Problem
import Definitions.Def_OracleRO_DualSubgrad_Algorithm1

set_option autoImplicit false


open scoped RealInnerProductSpace in
theorem p72856194_proj_nonexp {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
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
theorem p72856194_concave_grad {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
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
theorem p72856194_regret {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
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
    have hc := p72856194_concave_grad (hconc t ht) (hgrad t ht) (hmem t ht) hxs
    have hne := p72856194_proj_nonexp hK hP (x t + η • g t) xs hxs
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



open OracleRO.DualSubgrad in
theorem p72856194_eq6
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto U P) (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (hO : IsApproxOracle Dom U f ε O)
    (xbar : EuclideanSpace ℝ (Fin n))
    (hout : alg1Output gradU P O G D ε u0 x0 = some xbar) :
    ∀ i, (1 / (alg1T G D ε : ℝ)) * ∑ t ∈ Finset.Icc 1 (alg1T G D ε),
      f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i) ≤ ε := by
  intro i
  set T := alg1T G D ε with hT
  have hnone : ∀ t ∈ Finset.Icc 1 T, O (alg1U gradU P O G D ε u0 x0 t) ≠ none := by
    intro t ht hc
    unfold alg1Output at hout
    rw [if_pos ⟨t, ht, hc⟩] at hout
    cases hout
  have hbound : ∀ t ∈ Finset.Icc 1 T,
      f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i) ≤ ε := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hU : ∀ j, alg1U gradU P O G D ε u0 x0 (s + 1) j ∈ U := by
      intro j
      simp only [alg1U, alg1State]
      exact (hP _).1
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp (hnone _ ht)
    have hX : alg1X gradU P O G D ε u0 x0 (s + 1) = x := by
      have : alg1X gradU P O G D ε u0 x0 (s + 1)
          = (O (alg1U gradU P O G D ε u0 x0 (s + 1))).getD x0 := by
        simp only [alg1X, alg1U, alg1State]
      rw [this, hx]; rfl
    rw [hX]
    exact ((hO _ hU).1 x hx).2 i
  have hsum : ∑ t ∈ Finset.Icc 1 T,
      f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i) ≤ (T : ℝ) * ε := by
    calc _ ≤ ∑ t ∈ Finset.Icc 1 T, ε := Finset.sum_le_sum hbound
      _ = (T : ℝ) * ε := by simp
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · rw [h0]; simp; exact hε.le
  · have hTpos : (0 : ℝ) < T := by exact_mod_cast hpos
    rw [one_div, inv_mul_le_iff₀ hTpos]
    exact hsum


open OracleRO.DualSubgrad in
theorem p72856194_iter_mem
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O) (t : ℕ) :
    alg1X gradU P O G D ε u0 x0 t ∈ Dom := by
  cases t with
  | zero => simpa [alg1X, alg1State] using hx0
  | succ k =>
    simp only [alg1X, alg1State]
    set u' : Fin m → EuclideanSpace ℝ (Fin d) := fun i =>
      P ((alg1State gradU P O (alg1Eta G D ε) u0 x0 k).1 i + alg1Eta G D ε •
        gradU i (alg1State gradU P O (alg1Eta G D ε) u0 x0 k).2
          ((alg1State gradU P O (alg1Eta G D ε) u0 x0 k).1 i)) with hu'
    have hU : ∀ i, u' i ∈ U := fun i => (hP _).1
    rcases h : O u' with _ | x
    · simpa using hx0
    · simpa using ((hO u' hU).1 x h).1

open OracleRO.DualSubgrad in
theorem p72856194_cvx_step
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hDom : Convex ℝ Dom) (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hconv : ∀ i, ∀ u ∈ U, ConvexOn ℝ Dom (fun x => f i x u))
    (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O)
    (xbar : EuclideanSpace ℝ (Fin n))
    (hout : alg1Output gradU P O G D ε u0 x0 = some xbar) :
    ∀ i, ∀ u ∈ U, f i xbar u ≤ (1 / (alg1T G D ε : ℝ)) *
      ∑ t ∈ Finset.Icc 1 (alg1T G D ε), f i (alg1X gradU P O G D ε u0 x0 t) u := by
  intro i u hu
  have hT : 0 < (alg1T G D ε : ℝ) := by
    have : 0 < G ^ 2 * D ^ 2 / ε ^ 2 := by positivity
    have h1 : 0 < alg1T G D ε := by
      unfold alg1T
      exact Nat.ceil_pos.mpr this
    exact_mod_cast h1
  have hxbar : xbar = (1 / (alg1T G D ε : ℝ)) •
      ∑ t ∈ Finset.Icc 1 (alg1T G D ε), alg1X gradU P O G D ε u0 x0 t := by
    unfold alg1Output at hout
    split_ifs at hout
    exact (Option.some.inj hout).symm
  have hcard : ((Finset.Icc 1 (alg1T G D ε)).card : ℝ) = (alg1T G D ε : ℝ) := by
    simp
  have key := (hconv i u hu).map_sum_le (t := Finset.Icc 1 (alg1T G D ε))
    (w := fun _ => 1 / (alg1T G D ε : ℝ)) (p := fun t => alg1X gradU P O G D ε u0 x0 t)
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul, hcard]; field_simp)
    (fun t _ => p72856194_iter_mem Dom U f gradU P O ε D G u0 x0
      hP hx0 hO t)
  rw [hxbar, Finset.smul_sum]
  refine key.trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  simp [smul_eq_mul]


open OracleRO.DualSubgrad in
theorem p72856194_U_mem {m n d : ℕ} (U : Set (EuclideanSpace ℝ (Fin d)))
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto U P) (t : ℕ) (ht : 1 ≤ t) (i : Fin m) :
    alg1U gradU P O G D ε u0 x0 t i ∈ U := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [alg1U, alg1State]
  exact (hP _).1

open OracleRO.DualSubgrad in
theorem solution
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hDom : Convex ℝ Dom) (hU : Convex ℝ U) (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hconv : ∀ i, ∀ u ∈ U, ConvexOn ℝ Dom (fun x => f i x u))
    (hconc : ∀ i, ∀ x ∈ Dom, ConcaveOn ℝ U (f i x))
    (hgrad : ∀ i, ∀ x ∈ Dom, ∀ u ∈ U, HasGradientAt (f i x) (gradU i x u) u)
    (hgradG : ∀ i, ∀ x ∈ Dom, ∀ u ∈ U, ‖gradU i x u‖ ≤ G)
    (hdiam : ∀ u ∈ U, ∀ v ∈ U, ‖u - v‖ ≤ D)
    (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (hu0 : ∀ i, u0 i ∈ U) (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O) :
    (alg1Output gradU P O G D ε u0 x0 = none → ¬ RobustFeasible Dom U f) ∧
    (∀ xbar, alg1Output gradU P O G D ε u0 x0 = some xbar →
      IsApproxSolution Dom U f (2 * ε) xbar) ∧
    alg1Calls gradU P O G D ε u0 x0 ≤ ⌈G ^ 2 * D ^ 2 / ε ^ 2⌉₊ := by
  have hTnat : 0 < alg1T G D ε := by
    have : 0 < G ^ 2 * D ^ 2 / ε ^ 2 := by positivity
    unfold alg1T
    exact Nat.ceil_pos.mpr this
  refine ⟨?_, ?_, ?_⟩
  · -- infeasibility branch
    intro hnone hfeas
    unfold alg1Output at hnone
    split_ifs at hnone with h
    obtain ⟨t, ht, hOt⟩ := h
    have hmem : ∀ i, alg1U gradU P O G D ε u0 x0 t i ∈ U := fun i =>
      p72856194_U_mem U gradU P O ε D G u0 x0 hP t (Finset.mem_Icc.mp ht).1 i
    obtain ⟨x, hx, hall⟩ := hfeas
    exact (hO _ hmem).2 hOt ⟨x, hx, fun i => hall i _ (hmem i)⟩
  · -- approximate solution branch
    intro xbar hout
    set T := alg1T G D ε with hTdef
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hTnat
    have hxbar : xbar = (1 / (T : ℝ)) •
        ∑ t ∈ Finset.Icc 1 T, alg1X gradU P O G D ε u0 x0 t := by
      unfold alg1Output at hout
      split_ifs at hout
      exact (Option.some.inj hout).symm
    have hXmem : ∀ t, alg1X gradU P O G D ε u0 x0 t ∈ Dom := fun t =>
      p72856194_iter_mem Dom U f gradU P O ε D G u0 x0 hP hx0 hO t
    refine ⟨?_, ?_⟩
    · rw [hxbar, Finset.smul_sum]
      refine hDom.sum_mem (fun _ _ => by positivity) ?_ (fun t _ => hXmem t)
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp only [Nat.add_sub_cancel]
      field_simp
    · intro i u hu
      have h1 := p72856194_cvx_step Dom U f gradU P O ε D G u0 x0 hDom hP hconv hε hD hG hx0 hO
        xbar hout i u hu
      have h2 := p72856194_eq6 Dom U f gradU P O ε D G u0 x0 hP hε hD hG hO xbar hout i
      have h3 := p72856194_regret U P
        (fun t => f i (alg1X gradU P O G D ε u0 x0 t))
        (fun t => gradU i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i))
        (fun t => alg1U gradU P O G D ε u0 x0 t i) T D G hU hP hTnat hD hG hdiam
        (fun t _ => hconc i _ (hXmem t))
        (fun t ht => hgrad i _ (hXmem t) _
          (p72856194_U_mem U gradU P O ε D G u0 x0 hP t (Finset.mem_Icc.mp ht).1 i))
        (fun t ht => hgradG i _ (hXmem t) _
          (p72856194_U_mem U gradU P O ε D G u0 x0 hP t (Finset.mem_Icc.mp ht).1 i))
        (p72856194_U_mem U gradU P O ε D G u0 x0 hP 1 le_rfl i)
        (by
          intro t ht
          simp only [alg1U, alg1X, alg1State, alg1Eta, hTdef])
        u hu
      -- G D √T ≤ ε T
      have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
      have hTge : G ^ 2 * D ^ 2 / ε ^ 2 ≤ (T : ℝ) := Nat.le_ceil _
      have hGD : G * D ≤ ε * Real.sqrt T := by
        have hle : (G * D) ^ 2 ≤ (ε * Real.sqrt T) ^ 2 := by
          rw [mul_pow ε, Real.sq_sqrt hTpos.le]
          rw [div_le_iff₀ (by positivity)] at hTge
          nlinarith
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hle
      have hreg : G * D * Real.sqrt T ≤ ε * T := by
        have := mul_le_mul_of_nonneg_right hGD hsq.le
        rw [mul_assoc ε, Real.mul_self_sqrt hTpos.le] at this
        exact this
      set S1 := ∑ t ∈ Finset.Icc 1 T, f i (alg1X gradU P O G D ε u0 x0 t) u
      set S2 := ∑ t ∈ Finset.Icc 1 T,
        f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i)
      have h2' : S2 ≤ ε * T := by
        rw [one_div, inv_mul_le_iff₀ hTpos] at h2; linarith
      have h1' : f i xbar u * T ≤ S1 := by
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hTpos] at h1; exact h1
      have : f i xbar u * T ≤ 2 * ε * T := by linarith
      exact le_of_mul_le_mul_right this hTpos
  · -- call count
    show alg1Calls gradU P O G D ε u0 x0 ≤ alg1T G D ε
    unfold alg1Calls
    split_ifs with h
    · exact (Nat.find_spec h).2.1
    · exact le_rfl
