-- Prove2me | solution 1 for OnlineConvexOpt.OnlineBoosting.smoothed_regret_comparison_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T03:57:25.780537+00:00
-- url     : https://prove2.me/submissions/2a1c0918-3385-4b94-86e1-b90bfe71e7fd

import Mathlib
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_SmoothOn
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_WOCL_v2

set_option autoImplicit false

namespace P57cc6451

/-- First-order condition for a convex function with a gradient. -/
theorem first_order {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g p q : E} (hf : ConvexOn ℝ Set.univ f) (hg : HasGradientAt f g p) :
    inner ℝ g (q - p) ≤ f q - f p := by
  set φ : ℝ → ℝ := fun s => f (p + s • (q - p)) with hφ
  have hφc : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have e : a • (p + x • (q - p)) + b • (p + y • (q - p))
        = (a + b) • p + (a * x + b * y) • (q - p) := by module
    rw [hab, one_smul] at e
    simp only [hφ, smul_eq_mul]
    rw [← e]
    exact hf.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have h1 : HasDerivAt (fun s : ℝ => p + s • (q - p)) ((1 : ℝ) • (q - p)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const (q - p)).const_add p
  have hg' : HasGradientAt f g (p + (0 : ℝ) • (q - p)) := by simpa using hg
  have hd := hg'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have hd' : HasDerivAt φ (inner ℝ g (q - p)) 0 := by
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using hd
  have := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd'
  simpa [slope_def_field, hφ] using this

/-- A Lipschitz function has gradient of norm at most the Lipschitz constant. -/
theorem grad_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g p : E} {G : ℝ} (hG : 0 ≤ G) (hg : HasGradientAt f g p)
    (hL : ∀ x y, |f x - f y| ≤ G * dist x y) : ‖g‖ ≤ G := by
  have := hg.hasFDerivAt.le_of_lip' hG (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, ← dist_eq_norm]; exact hL x p)
  simpa using this

/-- The Frank–Wolfe style recursion. -/
theorem recursion (Δ η : ℕ → ℝ) (c E : ℝ) (hc : 0 ≤ c) (N : ℕ)
    (hη : ∀ i : ℕ, 1 ≤ i → η i = min (2 / (i : ℝ)) 1)
    (hstep : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      Δ i ≤ (1 - η i) * Δ (i - 1) + η i * E + η i ^ 2 * c / 2) :
    ∀ i : ℕ, 1 ≤ i → i ≤ N → Δ i ≤ 2 * c / i + E := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro h1N
    have h := hstep 1 le_rfl h1N
    have e1 : η 1 = 1 := by rw [hη 1 le_rfl]; norm_num
    rw [e1] at h
    simp only [Nat.cast_one]
    nlinarith
  | succ i hi ih =>
    intro hiN
    have hprev := ih (by omega)
    have h := hstep (i + 1) (by omega) hiN
    have hm : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    have eη : η (i + 1) = 2 / ((i : ℝ) + 1) := by
      rw [hη (i + 1) (by omega)]; push_cast
      apply min_eq_left
      rw [div_le_one (by positivity)]; linarith
    rw [eη] at h
    simp only [Nat.add_sub_cancel] at h
    have hnn : 0 ≤ 1 - 2 / ((i : ℝ) + 1) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have h2 := mul_le_mul_of_nonneg_left hprev hnn
    have key : (1 - 2 / ((i : ℝ) + 1)) * (2 * c / i + E) + 2 / ((i : ℝ) + 1) * E
        + (2 / ((i : ℝ) + 1)) ^ 2 * c / 2
        = 2 * c / ((i : ℝ) + 1) + E - 2 * c / ((i : ℝ) * ((i : ℝ) + 1) ^ 2) := by
      field_simp; ring
    have hpos : 0 ≤ 2 * c / ((i : ℝ) * ((i : ℝ) + 1) ^ 2) := by positivity
    push_cast
    linarith

end P57cc6451

open OnlineConvexOpt.OnlineBoosting in
theorem solution
    {n : ℕ} {A : Type*} (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K)
    (h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K)
    (D γ : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (hγpos : 0 < γ) (hγ1 : γ ≤ 1)
    (N T : ℕ) (hN : 0 < N) (hT : 0 < T)
    (fhat : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (β Ghat : ℝ) (hβpos : 0 < β) (hGhatpos : 0 < Ghat)
    (ghat : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hghat : ∀ t x, HasGradientAt (fhat t) (ghat t x) x)
    (hfconv : ∀ t, ConvexOn ℝ Set.univ (fhat t))
    (hsmooth : ∀ t, SmoothOn Set.univ (fhat t) (ghat t) β)
    (hLip : ∀ t, ∀ x y, |fhat t x - fhat t y| ≤ Ghat * dist x y)
    (η : ℕ → ℝ) (hη : ∀ i : ℕ, 1 ≤ i → η i = min (2 / (i : ℝ)) 1)
    (a : ℕ → A) (H : Set (A → EuclideanSpace ℝ (Fin n))) (hHne : H.Nonempty)
    (hHK : ∀ h ∈ H, ∀ c : A, h c ∈ K)
    (W x : ℕ → ℕ → EuclideanSpace ℝ (Fin n)) (hW : ∀ t i, W t i ∈ K)
    (hx0 : ∀ t : ℕ, 1 ≤ t → t ≤ T → x t 0 = 0)
    (hxstep : ∀ t i : ℕ, 1 ≤ t → t ≤ T → 1 ≤ i → i ≤ N →
      x t i = (1 - η i) • x t (i - 1) + η i • ((1 / γ) • W t i))
    (fstage : ℕ → ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfstage : ∀ t i : ℕ, 1 ≤ t → t ≤ T → 1 ≤ i → i ≤ N →
      fstage t i = fun y => inner ℝ (ghat t (x t (i - 1))) y)
    (RegretBoundW : ℝ)
    (hWOCL : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      IsGammaWOCL K γ T a H (fun t => W t i) (fun t y => fstage t i y / (Ghat * D)) RegretBoundW)
    (hstar : A → EuclideanSpace ℝ (Fin n)) (hstar_mem : hstar ∈ convexHull ℝ H) :
    (∑ t ∈ Finset.Icc 1 T, fhat t (x t N)) - ∑ t ∈ Finset.Icc 1 T, fhat t (hstar (a t)) ≤
      (2 * β * D ^ 2 * T) / (γ ^ 2 * N) + (Ghat * D / γ) * RegretBoundW := by
  -- basic facts on η
  have hη01 : ∀ i : ℕ, 1 ≤ i → 0 ≤ η i ∧ η i ≤ 1 := by
    intro i hi
    rw [hη i hi]
    exact ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have hGD : 0 < Ghat * D := mul_pos hGhatpos hDpos
  -- iterates scaled by γ stay in K
  have hmem : ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ i : ℕ, i ≤ N → γ • x t i ∈ K := by
    intro t ht1 htT i
    induction i with
    | zero => intro _; rw [hx0 t ht1 htT, smul_zero]; exact h0K
    | succ i ih =>
      intro hiN
      have hs := hxstep t (i + 1) ht1 htT (by omega) hiN
      simp only [Nat.add_sub_cancel] at hs
      rw [hs]
      have e : γ • ((1 - η (i + 1)) • x t i + η (i + 1) • ((1 / γ) • W t (i + 1)))
          = (1 - η (i + 1)) • (γ • x t i) + η (i + 1) • W t (i + 1) := by
        rw [smul_add, smul_comm γ (1 - η (i + 1)), smul_comm γ (η (i + 1)), smul_smul γ (1 / γ),
          mul_one_div_cancel hγpos.ne', one_smul]
      rw [e]
      obtain ⟨h0, h1⟩ := hη01 (i + 1) (by omega)
      exact hKconv (ih (by omega)) (hW t (i + 1)) (by linarith) h0 (by ring)
  -- gradient norm bound
  have hgn : ∀ t p, ‖ghat t p‖ ≤ Ghat := fun t p =>
    P57cc6451.grad_norm_le hGhatpos.le (hghat t p) (hLip t)
  -- WOCL consequence at stage i
  have hwocl : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      ∑ t ∈ Finset.Icc 1 T, (inner ℝ (ghat t (x t (i - 1))) ((1 / γ) • W t i)
        - inner ℝ (ghat t (x t (i - 1))) (hstar (a t))) ≤ Ghat * D / γ * RegretBoundW := by
    intro i hi1 hiN
    set L : (A → EuclideanSpace ℝ (Fin n)) → ℝ :=
      fun h => ∑ t ∈ Finset.Icc 1 T, inner ℝ (ghat t (x t (i - 1))) (h (a t)) / (Ghat * D) with hL
    have hfl : ∀ t ∈ Finset.Icc 1 T, ∀ y, fstage t i y / (Ghat * D)
        = inner ℝ (ghat t (x t (i - 1))) y / (Ghat * D) := by
      intro t ht y
      rw [Finset.mem_Icc] at ht
      rw [hfstage t i ht.1 ht.2 hi1 hiN]
    have hpre : ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ u ∈ K, ∀ v ∈ K,
        fstage t i u / (Ghat * D) - fstage t i v / (Ghat * D) ≤ 1 := by
      intro t ht1 htT u hu v hv
      rw [hfstage t i ht1 htT hi1 hiN, div_sub_div_same, div_le_one hGD, ← inner_sub_right]
      refine (real_inner_le_norm _ _).trans ?_
      rw [← dist_eq_norm]
      exact mul_le_mul (hgn _ _) (hD u hu v hv) dist_nonneg hGhatpos.le
    have hW' := hWOCL i hi1 hiN hpre
    simp only at hW'
    set S := (fun h => ∑ t ∈ Finset.Icc 1 T, fstage t i (h (a t)) / (Ghat * D)) '' H with hS
    have hSL : ∀ h, ∑ t ∈ Finset.Icc 1 T, fstage t i (h (a t)) / (Ghat * D) = L h := by
      intro h
      exact Finset.sum_congr rfl fun t ht => hfl t ht _
    have hbdd : BddBelow S := by
      refine ⟨∑ t ∈ Finset.Icc 1 T, (-1 : ℝ), ?_⟩
      rintro _ ⟨h, hh, rfl⟩
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_Icc.mp ht
      have := hpre t ht'.1 ht'.2 0 h0K (h (a t)) (hHK h hh (a t))
      rw [hfstage t i ht'.1 ht'.2 hi1 hiN] at this ⊢
      simp only [inner_zero_right, zero_div, zero_sub] at this
      linarith
    have hsub : H ⊆ {h | sInf S ≤ L h} := by
      intro h hh
      show sInf S ≤ L h
      rw [← hSL]
      exact csInf_le hbdd ⟨h, hh, rfl⟩
    have hconv : Convex ℝ {h : A → EuclideanSpace ℝ (Fin n) | sInf S ≤ L h} := by
      intro h1 hh1 h2 hh2 p q hp hq hpq
      simp only [Set.mem_ofPred_eq] at hh1 hh2 ⊢
      have e : L (p • h1 + q • h2) = p * L h1 + q * L h2 := by
        simp only [hL, Pi.add_apply, Pi.smul_apply, inner_add_right, inner_smul_right, add_div,
          Finset.sum_add_distrib, Finset.mul_sum, mul_div_assoc]
      rw [e]
      have : sInf S = p * sInf S + q * sInf S := by rw [← add_mul, hpq, one_mul]
      rw [this]
      exact add_le_add (mul_le_mul_of_nonneg_left hh1 hp) (mul_le_mul_of_nonneg_left hh2 hq)
    have hstarL : sInf S ≤ L hstar := convexHull_min hsub hconv hstar_mem
    -- hW' : L-type sum for W ≤ γ * sInf S + R
    have hWsum : ∑ t ∈ Finset.Icc 1 T, fstage t i (W t i) / (Ghat * D)
        = (∑ t ∈ Finset.Icc 1 T, inner ℝ (ghat t (x t (i - 1))) (W t i)) / (Ghat * D) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun t ht => hfl t ht _
    have hLs : L hstar
        = (∑ t ∈ Finset.Icc 1 T, inner ℝ (ghat t (x t (i - 1))) (hstar (a t))) / (Ghat * D) := by
      rw [hL, Finset.sum_div]
    rw [hWsum] at hW'
    rw [hLs] at hstarL
    have e2 : ∑ t ∈ Finset.Icc 1 T, (inner ℝ (ghat t (x t (i - 1))) ((1 / γ) • W t i)
        - inner ℝ (ghat t (x t (i - 1))) (hstar (a t)))
        = Ghat * D / γ * ((∑ t ∈ Finset.Icc 1 T, inner ℝ (ghat t (x t (i - 1))) (W t i)) / (Ghat * D)
          - γ * ((∑ t ∈ Finset.Icc 1 T, inner ℝ (ghat t (x t (i - 1))) (hstar (a t))) / (Ghat * D))) := by
      simp only [inner_smul_right, Finset.sum_sub_distrib, ← Finset.mul_sum]
      field_simp
    rw [e2]
    have hcoef : 0 ≤ Ghat * D / γ := by positivity
    apply mul_le_mul_of_nonneg_left _ hcoef
    have := mul_le_mul_of_nonneg_left hstarL hγpos.le
    linarith
  -- per-round inequality
  set c : ℝ := β * D ^ 2 * T / γ ^ 2 with hc
  set E : ℝ := Ghat * D / γ * RegretBoundW with hE
  set Δ : ℕ → ℝ := fun i => ∑ t ∈ Finset.Icc 1 T, (fhat t (x t i) - fhat t (hstar (a t))) with hΔ
  have hstep : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      Δ i ≤ (1 - η i) * Δ (i - 1) + η i * E + η i ^ 2 * c / 2 := by
    intro i hi1 hiN
    obtain ⟨hη0, hη1⟩ := hη01 i hi1
    have hpt : ∀ t ∈ Finset.Icc 1 T,
        fhat t (x t i) - fhat t (hstar (a t)) ≤
          (1 - η i) * (fhat t (x t (i - 1)) - fhat t (hstar (a t)))
          + η i * (inner ℝ (ghat t (x t (i - 1))) ((1 / γ) • W t i)
              - inner ℝ (ghat t (x t (i - 1))) (hstar (a t)))
          + η i ^ 2 * (β * D ^ 2 / γ ^ 2) / 2 := by
      intro t ht
      have ht' := Finset.mem_Icc.mp ht
      set p := x t (i - 1) with hp
      set y := (1 / γ) • W t i with hy
      set z := hstar (a t) with hz
      set g := ghat t p with hg
      have hxi : x t i - p = η i • (y - p) := by
        rw [hxstep t i ht'.1 ht'.2 hi1 hiN]; module
      have hsm := hsmooth t p (Set.mem_univ _) (x t i) (Set.mem_univ _)
      rw [← hg, hxi, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hsm
      have hco := P57cc6451.first_order (q := z) (hfconv t) (hghat t p)
      rw [← hg] at hco
      have hnorm : ‖y - p‖ ≤ D / γ := by
        have hpm := hmem t ht'.1 ht'.2 (i - 1) (by omega)
        have : y - p = (1 / γ) • (W t i - γ • p) := by
          rw [hy, smul_sub, smul_smul, one_div_mul_cancel hγpos.ne', one_smul]
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← dist_eq_norm]
        rw [one_div_mul_eq_div]
        exact div_le_div_of_nonneg_right (hD _ (hW t i) _ hpm) hγpos.le
      have hn2 : ‖y - p‖ ^ 2 ≤ (D / γ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have hsplit : inner ℝ g (y - p) = (inner ℝ g y - inner ℝ g z) + inner ℝ g (z - p) := by
        rw [inner_sub_right, inner_sub_right]; ring
      rw [hsplit] at hsm
      have h3 := mul_le_mul_of_nonneg_left hco hη0
      have h4 : η i ^ 2 * ‖y - p‖ ^ 2 ≤ η i ^ 2 * (D / γ) ^ 2 :=
        mul_le_mul_of_nonneg_left hn2 (by positivity)
      have e5 : η i ^ 2 * (β * D ^ 2 / γ ^ 2) / 2 = β / 2 * (η i ^ 2 * (D / γ) ^ 2) := by
        rw [div_pow]; ring
      rw [e5]
      have h6 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ β / 2)
      nlinarith
    calc Δ i ≤ ∑ t ∈ Finset.Icc 1 T,
          ((1 - η i) * (fhat t (x t (i - 1)) - fhat t (hstar (a t)))
          + η i * (inner ℝ (ghat t (x t (i - 1))) ((1 / γ) • W t i)
              - inner ℝ (ghat t (x t (i - 1))) (hstar (a t)))
          + η i ^ 2 * (β * D ^ 2 / γ ^ 2) / 2) := Finset.sum_le_sum hpt
      _ = (1 - η i) * Δ (i - 1) + η i * ∑ t ∈ Finset.Icc 1 T,
            (inner ℝ (ghat t (x t (i - 1))) ((1 / γ) • W t i)
              - inner ℝ (ghat t (x t (i - 1))) (hstar (a t))) + η i ^ 2 * c / 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hc, hΔ]
          simp only [Nat.add_sub_cancel]
          ring
      _ ≤ (1 - η i) * Δ (i - 1) + η i * E + η i ^ 2 * c / 2 := by
          have := mul_le_mul_of_nonneg_left (hwocl i hi1 hiN) hη0
          rw [hE]; linarith
  have hc0 : 0 ≤ c := by positivity
  have hfin := P57cc6451.recursion Δ η c E hc0 N hη hstep N hN le_rfl
  have hlhs : (∑ t ∈ Finset.Icc 1 T, fhat t (x t N)) - ∑ t ∈ Finset.Icc 1 T, fhat t (hstar (a t))
      = Δ N := by simp only [hΔ, Finset.sum_sub_distrib]
  rw [hlhs]
  have e : 2 * c / (N : ℝ) = (2 * β * D ^ 2 * T) / (γ ^ 2 * N) := by
    rw [hc]; field_simp
  rw [← e]
  exact hfin
