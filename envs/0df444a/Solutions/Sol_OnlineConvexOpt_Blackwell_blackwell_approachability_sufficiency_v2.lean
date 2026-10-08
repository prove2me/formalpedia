-- Prove2me | solution 1 for OnlineConvexOpt.Blackwell.blackwell_approachability_sufficiency_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:09:30.711964+00:00
-- url     : https://prove2.me/submissions/8142d14e-9aba-46dc-9dc9-278e50e52c11

import Mathlib
import Definitions.Def_OnlineConvexOpt_Blackwell_Approachability



namespace OnlineConvexOpt.Blackwell

/-- Blackwell's strategy: state = (current play, cumulative payoff). -/
noncomputable def bwX {E1 E2 F : Type*} [AddCommGroup F] [Module ℝ F]
    (u : E1 → E2 → F) (g : F → E1) (y : ℕ → E2) : ℕ → E1 × F
  | 0 => (g 0, 0)
  | n + 1 => (g ((n:ℝ)⁻¹ • (bwX u g y n).2),
      (bwX u g y n).2 + u (g ((n:ℝ)⁻¹ • (bwX u g y n).2)) (y (n + 1)))

lemma bwX_dep {E1 E2 F : Type*} [AddCommGroup F] [Module ℝ F]
    (u : E1 → E2 → F) (g : F → E1) (y y' : ℕ → E2) :
    ∀ n, (∀ s, s ≤ n → y s = y' s) → bwX u g y n = bwX u g y' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    have := ih (fun s hs => h s (by omega))
    simp only [bwX, this, h (n+1) le_rfl]

lemma bwX_sum {E1 E2 F : Type*} [AddCommGroup F] [Module ℝ F]
    (u : E1 → E2 → F) (g : F → E1) (y : ℕ → E2) :
    ∀ T, ∑ t ∈ Finset.Icc 1 T, u (bwX u g y t).1 (y t) = (bwX u g y T).2 := by
  intro T
  induction T with
  | zero => simp [bwX]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [bwX]

theorem bw_core
    {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2]
    [NormedSpace ℝ E2] {d : ℕ}
    (K1 : Set E1) (K2 : Set E2) (u : E1 → E2 → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSconv : Convex ℝ S) (hSbdd : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hK1cpt : IsCompact K1) (hK1conv : Convex ℝ K1) (hK1ne : K1.Nonempty)
    (hK2cpt : IsCompact K2) (hK2conv : Convex ℝ K2) (hK2ne : K2.Nonempty)
    (hucont : ContinuousOn (fun p : E1 × E2 => u p.1 p.2) (K1 ×ˢ K2))
    (huaffx : ∀ y ∈ K2, ∀ x₁ ∈ K1, ∀ x₂ ∈ K1, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      u (a • x₁ + b • x₂) y = a • u x₁ y + b • u x₂ y)
    (huaffy : ∀ x ∈ K1, ∀ y₁ ∈ K2, ∀ y₂ ∈ K2, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      u x (a • y₁ + b • y₂) = a • u x y₁ + b • u x y₂)
    (hcond : ∀ y ∈ K2, ∃ x ∈ K1, u x y ∈ S) :
    IsApproachable K1 K2 u S := by
  obtain ⟨y0, hy0⟩ := hK2ne
  obtain ⟨x0, hx0⟩ := hK1ne
  have hSne : S.Nonempty := by
    obtain ⟨x, _, hx⟩ := hcond y0 hy0; exact ⟨_, hx⟩
  -- nearest point map
  have hPex := exists_norm_eq_iInf_of_complete_convex hSne hSclosed.isComplete hSconv
  choose P hPS hP using hPex
  have hPdist : ∀ a, Metric.infDist a S = ‖a - P a‖ := by
    intro a
    rw [hP a, Metric.infDist_eq_iInf]
    simp only [dist_eq_norm]
  have hPproj : ∀ a, ∀ s ∈ S, inner ℝ (a - P a) (s - P a) ≤ (0:ℝ) :=
    fun a => (norm_eq_iInf_iff_real_inner_le_zero hSconv (hPS a)).1 (hP a)
  -- continuity in each variable
  have hcx : ∀ y ∈ K2, ContinuousOn (fun x => u x y) K1 := by
    intro y hy
    exact hucont.comp (Continuous.continuousOn (continuous_id.prodMk continuous_const))
      (fun x hx => ⟨hx, hy⟩)
  have hcy : ∀ x ∈ K1, ContinuousOn (fun y => u x y) K2 := by
    intro x hx
    exact hucont.comp (Continuous.continuousOn (continuous_const.prodMk continuous_id))
      (fun y hy => ⟨hx, hy⟩)
  -- oracle via Sion's minimax theorem
  have horacle : ∀ a, ∃ x ∈ K1, ∀ y ∈ K2, inner ℝ (a - P a) (u x y - P a) ≤ (0:ℝ) := by
    intro a
    set w := a - P a
    let φ : E1 → E2 → ℝ := fun x y => inner ℝ w (u x y)
    have hfy : ∀ y ∈ K2, LowerSemicontinuousOn (fun x => φ x y) K1 := fun y hy =>
      (ContinuousOn.inner continuousOn_const (hcx y hy)).lowerSemicontinuousOn
    have hfx : ∀ x ∈ K1, UpperSemicontinuousOn (fun y => φ x y) K2 := fun x hx =>
      (ContinuousOn.inner continuousOn_const (hcy x hx)).upperSemicontinuousOn
    have hfy' : ∀ y ∈ K2, QuasiconvexOn ℝ K1 (fun x => φ x y) := by
      intro y hy
      refine ConvexOn.quasiconvexOn ⟨hK1conv, ?_⟩
      intro x₁ hx₁ x₂ hx₂ a b ha hb hab
      apply le_of_eq
      simp only [φ, huaffx y hy x₁ hx₁ x₂ hx₂ a b ha hb hab, inner_add_right, inner_smul_right,
        smul_eq_mul]
    have hfx' : ∀ x ∈ K1, QuasiconcaveOn ℝ K2 (fun y => φ x y) := by
      intro x hx
      refine ConcaveOn.quasiconcaveOn ⟨hK2conv, ?_⟩
      intro y₁ hy₁ y₂ hy₂ a b ha hb hab
      apply le_of_eq
      simp only [φ, huaffy x hx y₁ hy₁ y₂ hy₂ a b ha hb hab, inner_add_right, inner_smul_right,
        smul_eq_mul]
    obtain ⟨xs, hxs, ys, hys, hsad⟩ := Sion.exists_isSaddlePointOn ⟨x0, hx0⟩ hK1conv hK1cpt hfy hfy'
      hK2conv ⟨y0, hy0⟩ hK2cpt hfx hfx'
    refine ⟨xs, hxs, fun y hy => ?_⟩
    obtain ⟨x1, hx1, hx1S⟩ := hcond ys hys
    have h1 := hsad x1 hx1 y hy
    have h2 := hPproj a _ hx1S
    simp only [φ] at h1
    rw [inner_sub_right] at h2 ⊢
    linarith
  choose g hgK hg using horacle
  -- bounds
  obtain ⟨M, hM⟩ := hSbdd.exists_norm_le
  obtain ⟨B, hB⟩ := ((hK1cpt.prod hK2cpt).image_of_continuousOn hucont).isBounded.exists_norm_le
  have hB' : ∀ x ∈ K1, ∀ y ∈ K2, ‖u x y‖ ≤ B := fun x hx y hy =>
    hB _ ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  set C := B + M with hC
  have hCv : ∀ x ∈ K1, ∀ y ∈ K2, ∀ s ∈ S, ‖u x y - s‖ ≤ C := by
    intro x hx y hy s hs
    calc ‖u x y - s‖ ≤ ‖u x y‖ + ‖s‖ := norm_sub_le _ _
      _ ≤ B + M := add_le_add (hB' x hx y hy) (hM s hs)
  refine ⟨fun y t => (bwX u g y t).1, ?_, ?_, ?_⟩
  · intro y t _
    cases t with
    | zero => exact hgK _
    | succ n => exact hgK _
  · intro y y' t h
    cases t with
    | zero => rfl
    | succ n =>
      simp only [bwX, bwX_dep u g y y' n (fun s hs => h s (by omega))]
  · intro y hy
    simp only [bwX_sum]
    set U := fun n => (bwX u g y n).2 with hU
    set D := fun n : ℕ => Metric.infDist ((n:ℝ)⁻¹ • U n) S with hD
    have hD0 : ∀ n, 0 ≤ D n := fun n => Metric.infDist_nonneg
    have hrec : ∀ n : ℕ, ((n:ℝ) * D n) ^ 2 ≤ n * C ^ 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        set a := (n:ℝ)⁻¹ • U n with ha
        set p := P a
        have hUa : U n = (n:ℝ) • a := by
          rcases Nat.eq_zero_or_pos n with h | h
          · subst h; simp [hU, bwX]
          · rw [ha, smul_smul, mul_inv_cancel₀ (by exact_mod_cast h.ne'), one_smul]
        set v := u (g a) (y (n+1)) with hv
        have hUs : U (n+1) = (n:ℝ) • a + v := by
          rw [← hUa]; simp only [hU, bwX]; rfl
        have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
        have hdist : ((n+1:ℕ):ℝ) * D (n+1) ≤ ‖(n:ℝ) • (a - p) + (v - p)‖ := by
          have h1 : D (n+1) ≤ ‖((n+1:ℕ):ℝ)⁻¹ • U (n+1) - p‖ := by
            rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem (hPS a)
          have h2 : ((n+1:ℕ):ℝ)⁻¹ • U (n+1) - p = ((n:ℝ)+1)⁻¹ • ((n:ℝ) • (a - p) + (v - p)) := by
            have e : (n:ℝ) • (a - p) + (v - p) = ((n:ℝ) • a + v) - ((n:ℝ) + 1) • p := by
              rw [add_smul, one_smul, smul_sub]; abel
            rw [e, ← hUs, smul_sub, smul_smul ((n:ℝ)+1)⁻¹ ((n:ℝ)+1) p, inv_mul_cancel₀ hn1.ne', one_smul]
            push_cast; rfl
          rw [h2, norm_smul, Real.norm_of_nonneg (by positivity)] at h1
          push_cast
          rw [← le_div_iff₀' hn1, div_eq_inv_mul]; exact h1
        have hip : inner ℝ ((n:ℝ) • (a - p)) (v - p) ≤ (0:ℝ) := by
          rw [inner_smul_left, RCLike.conj_to_real]
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (hg a (y (n+1)) (hy _ (by omega)))
        have hvp : ‖v - p‖ ≤ C := hCv _ (hgK a) _ (hy _ (by omega)) _ (hPS a)
        have hap : ‖a - p‖ = D n := by simp only [hD]; rw [hPdist]
        have hsq := norm_add_sq_real ((n:ℝ) • (a - p)) (v - p)
        rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg n), hap] at hsq
        have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hvp
        have hlhs : 0 ≤ ((n+1:ℕ):ℝ) * D (n+1) := mul_nonneg (by positivity) (hD0 _)
        have := pow_le_pow_left₀ hlhs hdist 2
        push_cast at this ⊢
        nlinarith [norm_nonneg (v - p)]
    have hbound : ∀ n : ℕ, 1 ≤ n → D n ≤ Real.sqrt (C ^ 2 / n) := by
      intro n hn
      have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      rw [← Real.sqrt_sq (hD0 n)]
      apply Real.sqrt_le_sqrt
      rw [le_div_iff₀ hnpos]
      have := hrec n
      nlinarith
    have hlim : Filter.Tendsto (fun n : ℕ => Real.sqrt (C ^ 2 / n)) Filter.atTop (nhds 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (C ^ 2)).sqrt
      simpa using this
    apply squeeze_zero' (Filter.Eventually.of_forall hD0) _ hlim
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact hbound n hn

end OnlineConvexOpt.Blackwell

open OnlineConvexOpt.Blackwell


theorem solution
    {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2]
    [NormedSpace ℝ E2] {d : ℕ}
    (K1 : Set E1) (K2 : Set E2) (u : E1 → E2 → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSconv : Convex ℝ S) (hSbdd : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hK1cpt : IsCompact K1) (hK1conv : Convex ℝ K1) (hK1ne : K1.Nonempty)
    (hK2cpt : IsCompact K2) (hK2conv : Convex ℝ K2) (hK2ne : K2.Nonempty)
    (hucont : ContinuousOn (fun p : E1 × E2 => u p.1 p.2) (K1 ×ˢ K2))
    (huaffx : ∀ y ∈ K2, ∀ x₁ ∈ K1, ∀ x₂ ∈ K1, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      u (a • x₁ + b • x₂) y = a • u x₁ y + b • u x₂ y)
    (huaffy : ∀ x ∈ K1, ∀ y₁ ∈ K2, ∀ y₂ ∈ K2, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      u x (a • y₁ + b • y₂) = a • u x y₁ + b • u x y₂)
    (hcond : ∀ y ∈ K2, ∃ x ∈ K1, u x y ∈ S) :
    IsApproachable K1 K2 u S := by
  exact bw_core K1 K2 u S hSconv hSbdd hSclosed hK1cpt hK1conv hK1ne hK2cpt hK2conv hK2ne hucont huaffx huaffy hcond
