-- Prove2me | solution 1 for Orabona2019.theorem_6_11_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:31:36.202961+00:00
-- url     : https://prove2.me/submissions/3962154e-39ea-42c8-a0db-8677bd90f32a

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting
import Definitions.Def_ModernOnlineLearning_OMD_Defs

open ModernOnlineLearning.OMD

namespace OM85

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "B" => BeckTeboulleMD.EMDA.bregman

/-- a function vanishing at 0, nonnegative on (0,1], has nonnegative right derivative at 0 -/
theorem nonneg_deriv {h : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt h d 0) (h0 : h 0 = 0)
    (hpos : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ h s) : 0 ≤ d := by
  have ht := hd.tendsto_slope_zero_right
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with s hs
  simp only [zero_add, h0, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hs.1.le) (hpos s hs.1 hs.2.le)

theorem hasDerivAt_line {ψ : E → ℝ} {y v : E} (hd : DifferentiableAt ℝ ψ y) :
    HasDerivAt (fun s : ℝ => ψ (y + s • v)) (fderiv ℝ ψ y v) 0 := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
  have hF : HasFDerivAt ψ (fderiv ℝ ψ y) (y + (0:ℝ) • v) := by
    simpa using hd.hasFDerivAt
  exact hF.comp_hasDerivAt (0:ℝ) hl

/-- strong convexity gives a quadratic lower bound on the Bregman divergence -/
theorem sc_breg {V : Set E} {lam : ℝ} {ψ : E → ℝ} (hsc : StrongConvexOn V lam ψ)
    {x y : E} (hx : x ∈ V) (hy : y ∈ V) (hd : DifferentiableAt ℝ ψ x) :
    lam / 2 * ‖y - x‖ ^ 2 ≤ B ψ y x := by
  set r := ‖y - x‖
  let h : ℝ → ℝ := fun s => s * (ψ y - ψ x - lam / 2 * r ^ 2) + s ^ 2 * (lam / 2 * r ^ 2)
    - (ψ (x + s • (y - x)) - ψ x)
  have hder : HasDerivAt h ((ψ y - ψ x - lam / 2 * r ^ 2) - fderiv ℝ ψ x (y - x)) 0 := by
    have h1 := ((hasDerivAt_id' (0:ℝ)).mul_const (ψ y - ψ x - lam / 2 * r ^ 2)).add
      ((hasDerivAt_pow 2 (0:ℝ)).mul_const (lam / 2 * r ^ 2))
    have h2 := (hasDerivAt_line (v := y - x) hd).sub_const (ψ x)
    exact (h1.sub h2).congr_deriv (by simp)
  have h0 : h 0 = 0 := by simp [h]
  have hpos : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ h s := by
    intro s hs0 hs1
    have := hsc.2 hx hy (show (0:ℝ) ≤ 1 - s by linarith) hs0.le (by ring)
    have e : (1 - s) • x + s • y = x + s • (y - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e, smul_eq_mul, smul_eq_mul, norm_sub_rev] at this
    simp only [h]
    nlinarith
  have := nonneg_deriv hder h0 hpos
  unfold BeckTeboulleMD.EMDA.bregman
  linarith

/-- first-order optimality of the mirror step, three-point form -/
theorem three_point {V : Set E} (hV : Convex ℝ V) {ψ : E → ℝ} {η : ℝ} (hη : 0 < η)
    {g : E →L[ℝ] ℝ} {x y : E} (hx : DifferentiableAt ℝ ψ x) (hy : DifferentiableAt ℝ ψ y)
    (hyV : y ∈ V)
    (hmin : ∀ z ∈ V, g y + (1 / η) * B ψ y x ≤ g z + (1 / η) * B ψ z x)
    {u : E} (hu : u ∈ V) :
    η * g (y - u) ≤ B ψ u x - B ψ u y - B ψ y x := by
  let h : ℝ → ℝ := fun s => s * g (u - y) + (1 / η) * (ψ (y + s • (u - y)) - ψ y
    - s * fderiv ℝ ψ x (u - y))
  have hder : HasDerivAt h (g (u - y) + (1 / η) * (fderiv ℝ ψ y (u - y) - fderiv ℝ ψ x (u - y))) 0 := by
    have h1 := (hasDerivAt_id' (0:ℝ)).mul_const (g (u - y))
    have h2 := (((hasDerivAt_line (v := u - y) hy).sub_const (ψ y)).sub
      ((hasDerivAt_id' (0:ℝ)).mul_const (fderiv ℝ ψ x (u - y)))).const_mul (1 / η)
    exact (h1.add h2).congr_deriv (by simp)
  have h0 : h 0 = 0 := by simp [h]
  have hpos : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ h s := by
    intro s hs0 hs1
    have hz : y + s • (u - y) ∈ V := hV.add_smul_sub_mem hyV hu ⟨hs0.le, hs1⟩
    have := hmin _ hz
    unfold BeckTeboulleMD.EMDA.bregman at this
    have e1 : y + s • (u - y) - x = (y - x) + s • (u - y) := by abel
    rw [e1, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
    simp only [h]
    nlinarith
  have := nonneg_deriv hder h0 hpos
  have key : 0 ≤ η * g (u - y) + (fderiv ℝ ψ y (u - y) - fderiv ℝ ψ x (u - y)) := by
    have := mul_nonneg hη.le this
    rw [mul_add, ← mul_assoc, mul_one_div_cancel hη.ne', one_mul] at this
    exact this
  unfold BeckTeboulleMD.EMDA.bregman
  have e2 : u - x = (u - y) + (y - x) := by abel
  have e3 : y - u = -(u - y) := by abel
  rw [e2, map_add, e3, map_neg]
  linarith

/-- weak form (no differentiability at the new point) -/
theorem two_point {V : Set E} {ψ : E → ℝ} {η : ℝ} (hη : 0 < η)
    {g : E →L[ℝ] ℝ} {x y : E}
    (hmin : ∀ z ∈ V, g y + (1 / η) * B ψ y x ≤ g z + (1 / η) * B ψ z x)
    {u : E} (hu : u ∈ V) :
    η * g (y - u) ≤ B ψ u x - B ψ y x := by
  have := mul_le_mul_of_nonneg_left (hmin u hu) hη.le
  rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, mul_one_div_cancel hη.ne', one_mul, one_mul]
    at this
  rw [map_sub]
  linarith

theorem young {a r η lam : ℝ} (hη : 0 < η) (hl : 0 < lam) :
    a * r - lam / 2 * r ^ 2 / η ≤ η * a ^ 2 / (2 * lam) := by
  have : 0 ≤ (η * a - lam * r) ^ 2 / (2 * lam * η) := by positivity
  have e : (η * a - lam * r) ^ 2 / (2 * lam * η) = η * a ^ 2 / (2 * lam) - (a * r - lam / 2 * r ^ 2 / η) := by
    field_simp; ring
  linarith

theorem tele_ineq (b η : ℕ → ℝ) (D : ℝ) (T : ℕ)
    (hb : ∀ t, 1 ≤ t → t ≤ T → b t ≤ D) (hη : ∀ t, 1 ≤ t → t ≤ T → 0 < η t)
    (hmono : ∀ t : ℕ, 1 ≤ t → t < T → η (t + 1) ≤ η t) :
    ∀ m, m + 1 ≤ T →
      ∑ t ∈ Finset.Icc 1 m, (b t - b (t + 1)) / η t + b (m + 1) / η (m + 1) ≤ D / η (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro hT
    simp only [Finset.Icc_self, zero_add, Finset.Icc_eq_empty_of_lt one_pos, Finset.sum_empty]
    have := hη 1 le_rfl hT
    have := hb 1 le_rfl hT
    simp only [zero_add] at *
    exact div_le_div_of_nonneg_right (by assumption) (le_of_lt (by assumption))
  | succ n ih =>
    intro hT
    have ih' := ih (by omega)
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := hη (n + 1) (by omega) (by omega)
    have h2 := hη (n + 1 + 1) (by omega) (by omega)
    have hm := hmono (n + 1) (by omega) (by omega)
    have hbd := hb (n + 1 + 1) (by omega) (by omega)
    have hinv : 1 / η (n + 1) ≤ 1 / η (n + 1 + 1) := one_div_le_one_div_of_le h2 hm
    have : (D - b (n + 1 + 1)) * (1 / η (n + 1)) ≤ (D - b (n + 1 + 1)) * (1 / η (n + 1 + 1)) :=
      mul_le_mul_of_nonneg_left hinv (by linarith)
    have e1 : (b (n + 1) - b (n + 1 + 1)) / η (n + 1) = b (n + 1) / η (n + 1)
      - b (n + 1 + 1) * (1 / η (n + 1)) := by ring
    have e2 : D / η (n + 1) = D * (1 / η (n + 1)) := by ring
    have e3 : D / η (n + 1 + 1) = D * (1 / η (n + 1 + 1)) := by ring
    have e4 : b (n + 1 + 1) / η (n + 1 + 1) = b (n + 1 + 1) * (1 / η (n + 1 + 1)) := by ring
    rw [e1, e3, e4]
    rw [e2] at ih'
    nlinarith

theorem tele_eq (b : ℕ → ℝ) (m : ℕ) :
    ∑ t ∈ Finset.Icc 1 m, (b t - b (t + 1)) + b (m + 1) = b 1 := by
  induction m with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega)]; linarith

end OM85

open OM85 in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X V : Set E) (ψ : E → ℝ) (lam : ℝ)
    (hsetting : IsOMDSetting X V ψ lam)
    (T : ℕ) (hT : 1 ≤ T) (η : ℕ → ℝ) (ℓ : ℕ → E → ℝ)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ)
    (hrun : IsOMDRun T X V ψ η ℓ x g)
    (hmono : ∀ t : ℕ, 1 ≤ t → t < T → η (t + 1) ≤ η t) :
    (∀ u ∈ V,
      (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
        bregmanMax T hT ψ u x / η T +
          (1 / (2 * lam)) * ∑ t ∈ Finset.Icc 1 T, η t * ‖g t‖ ^ 2) ∧
    (∀ η₀ : ℝ, (∀ t ∈ Finset.Icc 1 T, η t = η₀) → ∀ u ∈ V,
      (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
        BeckTeboulleMD.EMDA.bregman ψ u (x 1) / η₀ +
          (η₀ / (2 * lam)) * ∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2) := by
  obtain ⟨hlam, -, -, hdiff, -, -, -, hVc, -, -, hsc⟩ := hsetting
  obtain ⟨-, hrun⟩ := hrun
  have hdA : ∀ t ∈ Finset.Icc 1 T, DifferentiableAt ℝ ψ (x t) := fun t ht =>
    (hdiff _ (hrun t ht).1.2).differentiableAt (isOpen_interior.mem_nhds (hrun t ht).1.2)
  have hηpos : ∀ t ∈ Finset.Icc 1 T, 0 < η t := fun t ht => (hrun t ht).2.2.2.1
  have round : ∀ u ∈ V, ∀ t ∈ Finset.Icc 1 T,
      ℓ t (x t) - ℓ t u ≤ (BeckTeboulleMD.EMDA.bregman ψ u (x t) -
        (if t < T then BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) else 0)) / η t
        + (1 / (2 * lam)) * (η t * ‖g t‖ ^ 2) := by
    intro u hu t ht
    obtain ⟨⟨hxV, -⟩, -, hsub, hstep⟩ := hrun t ht
    obtain ⟨hη, -, hdx, hyV, hmin⟩ := hstep
    have h1 : ℓ t (x t) - ℓ t u ≤ g t (x t - u) := by
      have := hsub u hu
      rw [show u - x t = -(x t - u) by abel, map_neg] at this
      linarith
    have h2 : η t * g t (x (t + 1) - u) ≤ BeckTeboulleMD.EMDA.bregman ψ u (x t) -
        (if t < T then BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) else 0) -
        BeckTeboulleMD.EMDA.bregman ψ (x (t + 1)) (x t) := by
      split_ifs with hlt
      · have ht1 : t + 1 ∈ Finset.Icc 1 T := by simp at ht ⊢; omega
        exact three_point hVc hη hdx (hdA _ ht1) hyV hmin hu
      · have := two_point hη hmin hu; linarith
    have h3 := sc_breg hsc hxV hyV hdx
    have h4 : g t (x t - x (t + 1)) ≤ ‖g t‖ * ‖x (t + 1) - x t‖ := by
      rw [norm_sub_rev]
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using (g t).le_opNorm (x t - x (t + 1)))
    have h5 := young (a := ‖g t‖) (r := ‖x (t + 1) - x t‖) hη hlam
    set c := (if t < T then BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) else 0)
    set r := ‖x (t + 1) - x t‖
    have h2' : g t (x (t + 1) - u) ≤ (BeckTeboulleMD.EMDA.bregman ψ u (x t) - c) / η t
        - lam / 2 * r ^ 2 / η t := by
      rw [div_sub_div_same, le_div_iff₀ hη]; linarith
    have e : g t (x t - u) = g t (x t - x (t + 1)) + g t (x (t + 1) - u) := by
      rw [← map_add]; congr 1; abel
    have e2 : (1 / (2 * lam)) * (η t * ‖g t‖ ^ 2) = η t * ‖g t‖ ^ 2 / (2 * lam) := by ring
    rw [e2]
    linarith
  have main : ∀ u ∈ V, (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
      ∑ t ∈ Finset.Icc 1 T, (BeckTeboulleMD.EMDA.bregman ψ u (x t) -
        (if t < T then BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) else 0)) / η t
        + (1 / (2 * lam)) * ∑ t ∈ Finset.Icc 1 T, η t * ‖g t‖ ^ 2 := by
    intro u hu
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (round u hu)
  obtain ⟨m, rfl⟩ : ∃ m, T = m + 1 := ⟨T - 1, by omega⟩
  have split : ∀ u : E, ∀ η' : ℕ → ℝ, ∑ t ∈ Finset.Icc 1 (m + 1), (BeckTeboulleMD.EMDA.bregman ψ u (x t) -
        (if t < m + 1 then BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) else 0)) / η' t =
      ∑ t ∈ Finset.Icc 1 m, (BeckTeboulleMD.EMDA.bregman ψ u (x t) -
        BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1))) / η' t +
        BeckTeboulleMD.EMDA.bregman ψ u (x (m + 1)) / η' (m + 1) := by
    intro u η'
    rw [Finset.sum_Icc_succ_top (by omega), if_neg (lt_irrefl _), sub_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    simp at ht
    rw [if_pos (by omega)]
  refine ⟨fun u hu => ?_, fun η₀ hη₀ u hu => ?_⟩
  · refine (main u hu).trans ?_
    rw [split]
    have := tele_ineq (fun t => BeckTeboulleMD.EMDA.bregman ψ u (x t)) η (bregmanMax (m + 1) hT ψ u x)
      (m + 1) (fun t h1 h2 => by
        unfold bregmanMax
        exact Finset.le_sup' (fun t => BeckTeboulleMD.EMDA.bregman ψ u (x t))
          (by simp; omega))
      (fun t h1 h2 => hηpos t (by simp; omega)) hmono m le_rfl
    linarith
  · refine (main u hu).trans (le_of_eq ?_)
    rw [split]
    have e1 : ∀ t ∈ Finset.Icc 1 m, (BeckTeboulleMD.EMDA.bregman ψ u (x t) -
        BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1))) / η t = (BeckTeboulleMD.EMDA.bregman ψ u (x t) -
        BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1))) / η₀ := by
      intro t ht; rw [hη₀ t (by simp at ht ⊢; omega)]
    have e2 : ∀ t ∈ Finset.Icc 1 (m + 1), η t * ‖g t‖ ^ 2 = η₀ * ‖g t‖ ^ 2 := by
      intro t ht; rw [hη₀ t ht]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum,
      hη₀ (m + 1) (by simp), ← Finset.sum_div, ← add_div,
      tele_eq (fun t => BeckTeboulleMD.EMDA.bregman ψ u (x t)) m]
    ring
