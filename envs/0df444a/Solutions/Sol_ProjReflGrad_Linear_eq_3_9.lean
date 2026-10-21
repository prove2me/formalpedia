-- Prove2me | solution 1 for ProjReflGrad.Linear.eq_3_9
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:29:09.187377+00:00
-- url     : https://prove2.me/submissions/f4a89a8e-e340-46f2-b4b6-9a769c5f11b4

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

set_option autoImplicit false

theorem prl_y_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {C : Set H} {F : H → H} {lam : ℝ} {x y : ℕ → H}
    (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (n : ℕ) (hn : 1 ≤ n) :
    y n = (2 : ℝ) • x n - x (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using (hrun.2 k).2

theorem prl_proj_char {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hCcl : IsClosed C) (hCcv : Convex ℝ C) (hne : C.Nonempty) (z : H) :
    ProjReflGrad.Weak.proj C z ∈ C ∧
      ∀ w ∈ C, inner ℝ (z - ProjReflGrad.Weak.proj C z) (w - ProjReflGrad.Weak.proj C z) ≤ 0 := by
  have hex : ∃ p, ProjReflGrad.Weak.IsProj C z p := by
    obtain ⟨v, hv, hvn⟩ := exists_norm_eq_iInf_of_complete_convex hne hCcl.isComplete hCcv z
    refine ⟨v, hv, fun q hq => ?_⟩
    rw [hvn]
    exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨q, hq⟩ : C)
  have hp : ProjReflGrad.Weak.proj C z = hex.choose := by
    unfold ProjReflGrad.Weak.proj; rw [dif_pos hex]
  have hs := hex.choose_spec
  rw [hp]
  refine ⟨hs.1, ?_⟩
  have : ‖z - hex.choose‖ = ⨅ w : C, ‖z - w‖ := by
    apply le_antisymm
    · haveI : Nonempty C := hne.to_subtype
      exact le_ciInf (fun q => hs.2 q q.2)
    · exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨hex.choose, hs.1⟩ : C)
  exact (norm_eq_iInf_iff_real_inner_le_zero hCcv hs.1).mp this

theorem prl_exp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (a p z f : H) (lam : ℝ) :
    ‖a - lam • f - z‖ ^ 2 - ‖a - lam • f - p‖ ^ 2 =
      ‖a - z‖ ^ 2 - ‖p - a‖ ^ 2 - 2 * lam * inner ℝ f (p - z) := by
  have e1 : a - lam • f - z = (a - z) - lam • f := by abel
  have e2 : a - lam • f - p = (a - p) - lam • f := by abel
  have e4 : inner ℝ (a - z) f - inner ℝ (a - p) f = inner ℝ (p - z) f := by
    rw [← inner_sub_left]; congr 1; abel
  rw [e1, e2, norm_sub_sq_real (a - z), norm_sub_sq_real (a - p), norm_sub_rev p a,
    real_inner_comm (p - z) f]
  simp only [inner_smul_right]
  linear_combination (-2 * lam) * e4

theorem prl_key {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u v : H) :
    ‖(2 : ℝ) • u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 - ‖v‖ ^ 2 + 2 * ‖u - v‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, inner_smul_left]
  simp only [Real.norm_ofNat, RCLike.conj_to_real]
  ring

theorem prl_34 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (w d g : H) (lam : ℝ)
    (h1 : inner ℝ (w - lam • g) d ≤ 0) (h2 : inner ℝ (w - lam • g) w ≤ 0) :
    2 * lam * inner ℝ g (-w - d) ≤ ‖d‖ ^ 2 - ‖w‖ ^ 2 - ‖d + w‖ ^ 2 := by
  rw [norm_add_sq_real]
  have c1 := real_inner_comm w d
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_neg_right,
    real_inner_self_eq_norm_sq, RCLike.conj_to_real] at h1 h2 ⊢
  nlinarith

theorem prl_amgm (r A B s : ℝ) (hr : r ^ 2 = 2) (hr1 : 1 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s) :
    2 * (A + B) * s ≤ (1 + r) * A ^ 2 + B ^ 2 + r * s ^ 2 := by
  have h1 : 0 ≤ (r - 1) * ((r + 1) * A - s) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : (r - 1) * ((r + 1) * A - s) ^ 2 =
      (r + 1) * A ^ 2 - 2 * A * s + (r - 1) * s ^ 2 := by
    linear_combination ((r + 1) * A ^ 2 - 2 * A * s) * hr
  nlinarith [sq_nonneg (B - s)]

theorem prl_L32 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (lam : ℝ)
    (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (z : H) (hz : z ∈ C) :
    ∀ n : ℕ,
      ‖x (n + 1) - z‖ ^ 2 ≤
          ‖x n - lam • F (y n) - z‖ ^ 2 - ‖x n - lam • F (y n) - x (n + 1)‖ ^ 2 ∧
        ‖x n - lam • F (y n) - z‖ ^ 2 - ‖x n - lam • F (y n) - x (n + 1)‖ ^ 2 =
          ‖x n - z‖ ^ 2 - ‖x (n + 1) - x n‖ ^ 2 - 2 * lam * inner ℝ (F (y n)) (x (n + 1) - z) := by
  intro n
  have hp : x (n + 1) = ProjReflGrad.Weak.proj C (x n - lam • F (y n)) := (hrun.2 n).1
  obtain ⟨-, hvi⟩ := prl_proj_char hCcl hCcv ⟨z, hz⟩ (x n - lam • F (y n))
  rw [← hp] at hvi
  have h := hvi z hz
  refine ⟨?_, prl_exp (x n) (x (n + 1)) z (F (y n)) lam⟩
  generalize x (n + 1) = p at h
  generalize x n - lam • F (y n) = u at h
  have e : u - z = (u - p) + (p - z) := by abel
  have e2 : p - z = -(z - p) := by abel
  have h3 : ‖u - z‖ ^ 2 = ‖u - p‖ ^ 2 + 2 * inner ℝ (u - p) (p - z) + ‖p - z‖ ^ 2 := by
    rw [e, norm_add_sq_real]
  have h4 : inner ℝ (u - p) (p - z) = - inner ℝ (u - p) (z - p) := by
    rw [e2, inner_neg_right]
  nlinarith

theorem prl_L34 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (hne : C.Nonempty) (F : H → H) (lam : ℝ)
    (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) :
    ∀ n : ℕ, 2 ≤ n →
      2 * lam * inner ℝ (F (y (n - 1))) (y n - x (n + 1)) ≤
        ‖x (n + 1) - x n‖ ^ 2 - ‖x n - y n‖ ^ 2 - ‖x (n + 1) - y n‖ ^ 2 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : k + 2 - 1 = k + 1 := by omega
  rw [hk]
  have hyn : y (k + 2) = (2 : ℝ) • x (k + 2) - x (k + 1) := (hrun.2 (k + 1)).2
  have hb : x (k + 2) = ProjReflGrad.Weak.proj C (x (k + 1) - lam • F (y (k + 1))) := (hrun.2 (k + 1)).1
  obtain ⟨hbC, hvi⟩ := prl_proj_char hCcl hCcv hne (x (k + 1) - lam • F (y (k + 1)))
  rw [← hb] at hbC hvi
  have haC : x (k + 1) ∈ C := by
    have := (prl_proj_char hCcl hCcv hne (x k - lam • F (y k))).1
    rwa [← (hrun.2 k).1] at this
  have hcC : x (k + 3) ∈ C := by
    have := (prl_proj_char hCcl hCcv hne (x (k + 2) - lam • F (y (k + 2)))).1
    rwa [← (hrun.2 (k + 2)).1] at this
  have h1 := hvi _ hcC
  have h2 := hvi _ haC
  have := prl_34 (x (k + 1) - x (k + 2)) (x (k + 3) - x (k + 2)) (F (y (k + 1))) lam
    (by have e : x (k + 1) - x (k + 2) - lam • F (y (k + 1)) = x (k + 1) - lam • F (y (k + 1)) - x (k + 2) := by abel
        rw [e]; exact h1)
    (by have e : x (k + 1) - x (k + 2) - lam • F (y (k + 1)) = x (k + 1) - lam • F (y (k + 1)) - x (k + 2) := by abel
        have e' : x (k + 1) - x (k + 2) = x (k + 1) - x (k + 2) := rfl
        rw [e]; exact h2)
  have e1 : y (k + 2) - x (k + 2 + 1) = -(x (k + 1) - x (k + 2)) - (x (k + 3) - x (k + 2)) := by
    rw [hyn]; module
  have e2 : x (k + 2) - y (k + 2) = x (k + 1) - x (k + 2) := by rw [hyn]; module
  have e3 : x (k + 2 + 1) - y (k + 2) = (x (k + 3) - x (k + 2)) + (x (k + 1) - x (k + 2)) := by
    rw [hyn]; module
  rw [e1, e2, e3]
  exact this

theorem prl_L35 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (F : H → H) (L lam : ℝ) (hL : 0 < L) (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L) (hlam0 : 0 < lam)
    (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) :
    ∀ n : ℕ, 1 ≤ n →
      2 * lam * inner ℝ (F (y n) - F (y (n - 1))) (y n - x (n + 1)) ≤
        lam * L * (1 + Real.sqrt 2) * ‖y n - x n‖ ^ 2 + lam * L * ‖x n - y (n - 1)‖ ^ 2
          + Real.sqrt 2 * lam * L * ‖x (n + 1) - y n‖ ^ 2 := by
  intro n _
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : 1 ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  set A := ‖y n - x n‖
  set B := ‖x n - y (n - 1)‖
  set s := ‖x (n + 1) - y n‖
  have hkey := prl_amgm (Real.sqrt 2) A B s hr hr1 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have hd : y n - y (n - 1) = (y n - x n) + (x n - y (n - 1)) := by abel
  have h1 : ‖F (y n) - F (y (n - 1))‖ ≤ L * (A + B) := by
    calc ‖F (y n) - F (y (n - 1))‖ ≤ L * ‖y n - y (n - 1)‖ := hC3 _ _
      _ ≤ L * (A + B) := by
        apply mul_le_mul_of_nonneg_left _ hL.le
        rw [hd]; exact norm_add_le _ _
  have h2 : inner ℝ (F (y n) - F (y (n - 1))) (y n - x (n + 1)) ≤ L * (A + B) * s := by
    calc _ ≤ ‖F (y n) - F (y (n - 1))‖ * ‖y n - x (n + 1)‖ := real_inner_le_norm _ _
      _ ≤ L * (A + B) * s := by
        rw [norm_sub_rev (y n) (x (n + 1))]
        exact mul_le_mul h1 le_rfl (norm_nonneg _) (by positivity)
  have h3 : 2 * lam * inner ℝ (F (y n) - F (y (n - 1))) (y n - x (n + 1)) ≤
      2 * lam * (L * (A + B) * s) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : lam * L * (2 * (A + B) * s) ≤ lam * L * ((1 + Real.sqrt 2) * A ^ 2 + B ^ 2 + Real.sqrt 2 * s ^ 2) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  nlinarith [h3, h4]

theorem prl_L38 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (F : H → H) (m lam : ℝ) (hm : 0 < m) (hC2s : ProjReflGrad.Linear.IsStronglyMonotoneMap F m)
    (hlam0 : 0 < lam) (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (z : H) :
    ∀ m1 : ℝ, 0 < m1 → m1 ≤ m → ∀ n : ℕ, 1 ≤ n →
      2 * lam * (inner ℝ (F (y n) - F z) (y n - z) - m * ‖y n - z‖ ^ 2) ≤
        2 * lam * (inner ℝ (F (y n) - F z) (y n - z)
          - m1 * (2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2)) ∧
      0 ≤ 2 * lam * (inner ℝ (F (y n) - F z) (y n - z) - m * ‖y n - z‖ ^ 2) := by
  intro m1 hm1 hm1m n hn
  have hmon := hC2s (y n) z
  have h1 : y n - z = (2 : ℝ) • (x n - z) - (x (n - 1) - z) := by
    rw [prl_y_eq hrun n hn]; module
  have h2 : x n - z - (x (n - 1) - z) = x n - x (n - 1) := by abel
  have h3 : ‖y n - z‖ ^ 2 = 2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2 + 2 * ‖x n - x (n - 1)‖ ^ 2 := by
    rw [h1, prl_key, h2]
  set Q := 2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2 with hQ
  have hQy : Q ≤ ‖y n - z‖ ^ 2 := by rw [h3]; nlinarith [sq_nonneg ‖x n - x (n - 1)‖]
  have hy0 : 0 ≤ ‖y n - z‖ ^ 2 := sq_nonneg _
  have h4 : m1 * Q ≤ m * ‖y n - z‖ ^ 2 := by
    rcases le_total Q 0 with hq | hq
    · nlinarith
    · nlinarith
  refine ⟨?_, ?_⟩
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  · apply mul_nonneg (by positivity)
    linarith

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (L lam m : ℝ)
    (hm : 0 < m) (hC2s : ProjReflGrad.Linear.IsStronglyMonotoneMap F m) (hL : 0 < L) (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L)
    (hlam0 : 0 < lam) (hlam1 : lam < (Real.sqrt 2 - 1) / L)
    (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (z : H) (hz : z ∈ ProjReflGrad.Weak.solSet C F) :
    ∀ m1 : ℝ, 0 < m1 → m1 ≤ m → ∀ n : ℕ, 2 ≤ n →
      ‖x (n + 1) - z‖ ^ 2 + (1 - Real.sqrt 2 * lam * L) * ‖x (n + 1) - y n‖ ^ 2
          + 4 * lam * inner ℝ (F z) (x n - z) ≤
        (1 - 4 * lam * m1) * ‖x n - z‖ ^ 2 + 2 * lam * m1 * ‖x (n - 1) - z‖ ^ 2
          + max (lam * L / (1 - Real.sqrt 2 * lam * L)) (1 / 2)
            * ((1 - Real.sqrt 2 * lam * L) * ‖x n - y (n - 1)‖ ^ 2
              + 4 * lam * inner ℝ (F z) (x (n - 1) - z)) := by
  intro m1 hm1 hm1m n hn
  have hne : C.Nonempty := ⟨z, hz.1⟩
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : 1 ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  set r := Real.sqrt 2 with hrdef
  have hlL : lam * L < r - 1 := by
    rw [lt_div_iff₀ hL] at hlam1; linarith
  have hpos : 0 < 1 - r * lam * L := by nlinarith
  have hcoef : 0 ≤ 1 - lam * L * (1 + r) := by nlinarith
  -- membership of x (n-1) in C
  have hxC : x (n - 1) ∈ C := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hk : k + 2 - 1 = k + 1 := by omega
    rw [hk]
    have := (prl_proj_char hCcl hCcv hne (x k - lam • F (y k))).1
    rwa [← (hrun.2 k).1] at this
  have hK : 0 ≤ inner ℝ (F z) (x (n - 1) - z) := hz.2 _ hxC
  obtain ⟨h32, h32'⟩ := prl_L32 C hCcl hCcv F lam x y hrun z hz.1 n
  have h34 := prl_L34 C hCcl hCcv hne F lam x y hrun n hn
  have h35 := prl_L35 C F L lam hL hC3 hlam0 x y hrun n (by omega)
  obtain ⟨h38a, h38b⟩ := prl_L38 C F m lam hm hC2s hlam0 x y hrun z m1 hm1 hm1m n (by omega)
  have h38 : 0 ≤ inner ℝ (F (y n) - F z) (y n - z) - m1 * (2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2) := by
    have := le_trans h38b h38a
    have h2 : 0 < 2 * lam := by positivity
    exact (mul_nonneg_iff_of_pos_left h2).mp this
  -- decomposition of the inner product
  have hdec : inner ℝ (F (y n)) (x (n + 1) - z) =
      inner ℝ (F (y n) - F z) (y n - z) + (2 * inner ℝ (F z) (x n - z) - inner ℝ (F z) (x (n - 1) - z))
        - inner ℝ (F (y n) - F (y (n - 1))) (y n - x (n + 1)) - inner ℝ (F (y (n - 1))) (y n - x (n + 1)) := by
    have hyz : y n - z = (2 : ℝ) • (x n - z) - (x (n - 1) - z) := by
      rw [prl_y_eq hrun n (by omega)]; module
    have e : inner ℝ (F z) (y n - z) = 2 * inner ℝ (F z) (x n - z) - inner ℝ (F z) (x (n - 1) - z) := by
      rw [hyz, inner_sub_right, inner_smul_right]
    simp only [inner_sub_left, inner_sub_right] at e ⊢
    linarith
  rw [norm_sub_rev (x n) (y n)] at h34
  rw [h32', hdec] at h32
  have hβ1 : lam * L ≤ max (lam * L / (1 - r * lam * L)) (1 / 2) * (1 - r * lam * L) := by
    have := le_max_left (lam * L / (1 - r * lam * L)) (1 / 2)
    rw [div_le_iff₀ hpos] at this; exact this
  have hβ2 : 1 / 2 ≤ max (lam * L / (1 - r * lam * L)) (1 / 2) := le_max_right _ _
  set β := max (lam * L / (1 - r * lam * L)) (1 / 2) with hβ
  have f1 := mul_nonneg hlam0.le h38
  have f2 := mul_nonneg hcoef (sq_nonneg ‖y n - x n‖)
  have f3 := mul_nonneg (sub_nonneg.2 hβ1) (sq_nonneg ‖x n - y (n - 1)‖)
  have f4 := mul_nonneg (sub_nonneg.2 hβ2) (mul_nonneg hlam0.le hK)
  nlinarith [f1, f2, f3, f4, h32, h34, h35]
