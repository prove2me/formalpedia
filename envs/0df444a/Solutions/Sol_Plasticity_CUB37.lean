-- Prove2me | solution 1 for Plasticity.CUB37
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T09:11:27.615023+00:00
-- url     : https://prove2.me/submissions/9e2531f5-cfee-4abb-8aa0-1eb0a468e96d

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_Plasticity_CUB37_normal_form
import Theorems.Thm_Plasticity_CUB37_rigidity

/-!
# CUB37: nonexpansive bijections between balls of spaces between c₀₀ and c₀

Reduction to the two child cards `Plasticity.CUB37.normal_form` (Proposition 1 of
`expositions/c0_between_spaces.md`) and `Plasticity.CUB37.rigidity` (Theorem 3 there).
The normal form gives a bijection `σ : Γ ≃ Δ` and signs `α`; the signed bijection
`A x (σ n) = α n * x n` transports `Y` back to a space `X' = A⁻¹(Y)` between `c00 Γ` and
`c0 Γ`, and `H = A⁻¹ ∘ F` is an inward nonexpansive bijection of `ballIn X` onto `ballIn X'`.
Every point is matched (Corollary 4 (i), (ii)), so rigidity gives `H = id`.
-/

open Plasticity Filter Topology

namespace Sol_Plasticity_CUB37

variable {Γ Δ : Type*}

theorem sperm_memℓp (e : Γ ≃ Δ) (β : Γ → ℝ) (hβ : ∀ n, |β n| ≤ 1) (y : Linf Δ) :
    Memℓp (fun n => β n * y (e n) : Γ → ℝ) ⊤ := by
  rw [memℓp_infty_iff]
  refine ⟨‖y‖, ?_⟩
  rintro _ ⟨n, rfl⟩
  have h1 := lp.norm_apply_le_norm (p := ⊤) ENNReal.top_ne_zero y (e n)
  simp only [Real.norm_eq_abs] at h1 ⊢
  rw [abs_mul]
  calc |β n| * |y (e n)| ≤ 1 * |y (e n)| :=
        mul_le_mul_of_nonneg_right (hβ n) (abs_nonneg _)
    _ ≤ ‖y‖ := by rw [one_mul]; exact h1

/-- The signed permutation `y ↦ (n ↦ β n * y (e n))`, a linear map ℓ∞(Δ) → ℓ∞(Γ). -/
def sperm (e : Γ ≃ Δ) (β : Γ → ℝ) (hβ : ∀ n, |β n| ≤ 1) : Linf Δ →ₗ[ℝ] Linf Γ where
  toFun y := ⟨fun n => β n * y (e n), sperm_memℓp e β hβ y⟩
  map_add' y z := by
    apply lp.ext; funext n
    show β n * (y + z) (e n) = β n * y (e n) + β n * z (e n)
    rw [lp.coeFn_add, Pi.add_apply]; ring
  map_smul' c y := by
    apply lp.ext; funext n
    show β n * (c • y) (e n) = c • (β n * y (e n))
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]; ring

theorem sperm_apply (e : Γ ≃ Δ) (β : Γ → ℝ) (hβ : ∀ n, |β n| ≤ 1) (y : Linf Δ) (n : Γ) :
    sperm e β hβ y n = β n * y (e n) := rfl

theorem sperm_norm_le (e : Γ ≃ Δ) (β : Γ → ℝ) (hβ : ∀ n, |β n| ≤ 1) (y : Linf Δ) :
    ‖sperm e β hβ y‖ ≤ ‖y‖ := by
  refine lp.norm_le_of_forall_le (norm_nonneg y) fun n => ?_
  have h1 := lp.norm_apply_le_norm (p := ⊤) ENNReal.top_ne_zero y (e n)
  rw [sperm_apply]
  simp only [Real.norm_eq_abs] at h1 ⊢
  rw [abs_mul]
  calc |β n| * |y (e n)| ≤ 1 * |y (e n)| :=
        mul_le_mul_of_nonneg_right (hβ n) (abs_nonneg _)
    _ ≤ ‖y‖ := by rw [one_mul]; exact h1

theorem mem_ballIn {X : Submodule ℝ (Linf Γ)} {x : Linf Γ} :
    x ∈ ballIn X ↔ x ∈ X ∧ ‖x‖ ≤ 1 := by
  simp only [ballIn, Set.mem_inter_iff, SetLike.mem_coe, Metric.mem_closedBall,
    dist_zero_right]

/-- Finite support transfers along a bijection of coordinates that preserves moduli. -/
theorem mem_c00_of_abs_eq (e : Γ ≃ Δ) {u : Linf Γ} {v : Linf Δ}
    (h : ∀ n, |u n| = |v (e n)|) (hv : v ∈ c00 Δ) : u ∈ c00 Γ := by
  have hv' : (Function.support (⇑v)).Finite := hv
  show (Function.support (⇑u)).Finite
  have key : Function.support (⇑u) = e ⁻¹' Function.support (⇑v) := by
    ext n
    simp only [Function.mem_support, Set.mem_preimage, ne_eq]
    rw [← abs_eq_zero, h n, abs_eq_zero]
  rw [key]
  exact Set.Finite.preimage e.injective.injOn hv'

/-- Vanishing at infinity transfers along a bijection of coordinates that preserves moduli. -/
theorem mem_c0_of_abs_eq (e : Γ ≃ Δ) {u : Linf Γ} {v : Linf Δ}
    (h : ∀ n, |u n| = |v (e n)|) (hv : v ∈ c0 Δ) : u ∈ c0 Γ := by
  have hv' : Tendsto (⇑v) cofinite (𝓝 0) := hv
  show Tendsto (⇑u) cofinite (𝓝 0)
  have h2 : Tendsto (⇑v ∘ e) cofinite (𝓝 0) := hv'.comp e.injective.tendsto_cofinite
  rw [tendsto_zero_iff_norm_tendsto_zero] at h2 ⊢
  have h3 : (fun n => ‖u n‖) = fun n => ‖(⇑v ∘ e) n‖ := by
    funext n; simp only [Real.norm_eq_abs, Function.comp_apply, h n]
  rw [h3]; exact h2

/-- An element of c₀(Γ) has countable support. -/
theorem countable_support_of_mem_c0 {x : Linf Γ} (hx : x ∈ c0 Γ) :
    (Function.support (⇑x)).Countable := by
  have hx' : Tendsto (⇑x) cofinite (𝓝 0) := hx
  have hsub : Function.support (⇑x) ⊆ ⋃ k : ℕ, {i | ¬ (|x i| < 1 / ((k : ℝ) + 1))} := by
    intro i hi
    have hpos : 0 < |x i| := abs_pos.2 hi
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    exact Set.mem_iUnion.2 ⟨k, by simp only [Set.mem_ofPred_eq, not_lt]; exact hk.le⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun k => ?_)
  apply Set.Finite.countable
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hev : ∀ᶠ i in cofinite, |x i| < 1 / ((k : ℝ) + 1) := by
    have h := (tendsto_zero_iff_norm_tendsto_zero.1 hx').eventually (gt_mem_nhds hk)
    simpa only [Real.norm_eq_abs] using h
  exact Filter.eventually_cofinite.1 hev

end Sol_Plasticity_CUB37

open Sol_Plasticity_CUB37 in
theorem solution {Γ Δ : Type*} (X : Submodule ℝ (Linf Γ)) (Y : Submodule ℝ (Linf Δ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hY0 : c00 Δ ≤ Y) (hY1 : Y ≤ c0 Δ)
    (hmatch : X = c00 Γ ∨ RealizesSignPatterns Y)
    (F : Linf Γ → Linf Δ)
    (hbij : Set.BijOn F (ballIn X) (ballIn Y))
    (hlip : LipschitzOnWith 1 F (ballIn X)) :
    ∃ σ : Γ ≃ Δ, ∃ α : Γ → ℝ, (∀ n, α n = 1 ∨ α n = -1) ∧
      ∀ x ∈ ballIn X, ∀ n, F x (σ n) = α n * x n := by
  classical
  -- Step 1: the normal form.
  obtain ⟨σ, α, hα, hN⟩ := Plasticity.CUB37.normal_form X Y hX0 hX1 hY0 hY1 F hbij hlip
  have hαabs : ∀ n, |α n| = 1 := fun n => by rcases hα n with h | h <;> simp [h]
  have hα1 : ∀ n, |α n| ≤ 1 := fun n => (hαabs n).le
  have hαsq : ∀ n, α n * α n = 1 := fun n => by rcases hα n with h | h <;> simp [h]
  -- Step 2: the signed bijection `A` and its inverse `B`.
  let A : Linf Γ →ₗ[ℝ] Linf Δ := sperm σ.symm (fun m => α (σ.symm m)) (fun m => hα1 _)
  let B : Linf Δ →ₗ[ℝ] Linf Γ := sperm σ α hα1
  have hAapp : ∀ x m, A x m = α (σ.symm m) * x (σ.symm m) := fun _ _ => rfl
  have hBapp : ∀ y n, B y n = α n * y (σ n) := fun _ _ => rfl
  have hAB : ∀ y, A (B y) = y := fun y => by
    apply lp.ext; funext m
    rw [hAapp, hBapp, Equiv.apply_symm_apply, ← mul_assoc, hαsq, one_mul]
  have hBA : ∀ x, B (A x) = x := fun x => by
    apply lp.ext; funext n
    rw [hBapp, hAapp, Equiv.symm_apply_apply, ← mul_assoc, hαsq, one_mul]
  have hAnorm : ∀ x, ‖A x‖ ≤ ‖x‖ := fun x => sperm_norm_le _ _ _ x
  have hBnorm : ∀ y, ‖B y‖ ≤ ‖y‖ := fun y => sperm_norm_le _ _ _ y
  let X' : Submodule ℝ (Linf Γ) := Submodule.comap A Y
  have hmemX' : ∀ x, x ∈ X' ↔ A x ∈ Y := fun x => Iff.rfl
  have hX'0 : c00 Γ ≤ X' := by
    intro x hx
    rw [hmemX']
    apply hY0
    exact mem_c00_of_abs_eq σ.symm (u := A x) (v := x)
      (fun m => by rw [hAapp, abs_mul, hαabs, one_mul]) hx
  have hX'1 : X' ≤ c0 Γ := by
    intro x hx
    rw [hmemX'] at hx
    exact mem_c0_of_abs_eq σ (u := x) (v := A x)
      (fun n => by rw [hAapp, abs_mul, Equiv.symm_apply_apply, hαabs, one_mul]) (hY1 hx)
  -- Step 3: the map `H = A⁻¹ ∘ F`.
  let H : Linf Γ → Linf Γ := fun x => B (F x)
  have hHapp : ∀ x n, H x n = α n * F x (σ n) := fun _ _ => rfl
  have hHbij : Set.BijOn H (ballIn X) (ballIn X') := by
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun z hz => ?_⟩
    · have hFx := hbij.mapsTo hx
      rw [mem_ballIn] at hFx ⊢
      refine ⟨?_, (hBnorm _).trans hFx.2⟩
      rw [hmemX']
      show A (B (F x)) ∈ Y
      rw [hAB]; exact hFx.1
    · apply hbij.injOn hx hy
      have h1 : A (B (F x)) = A (B (F y)) := congrArg A hxy
      rwa [hAB, hAB] at h1
    · rw [mem_ballIn, hmemX'] at hz
      have hAz : A z ∈ ballIn Y := mem_ballIn.2 ⟨hz.1, (hAnorm z).trans hz.2⟩
      obtain ⟨x, hx, hFx⟩ := hbij.surjOn hAz
      refine ⟨x, hx, ?_⟩
      show B (F x) = z
      rw [hFx, hBA]
  have hHlip : LipschitzOnWith 1 H (ballIn X) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have h := hlip.dist_le_mul x hx y hy
    calc dist (H x) (H y) = ‖B (F x - F y)‖ := by
          rw [dist_eq_norm, map_sub]
      _ ≤ ‖F x - F y‖ := hBnorm _
      _ = dist (F x) (F y) := (dist_eq_norm _ _).symm
      _ ≤ _ := h
  have hHN1 : ∀ x ∈ ballIn X, ∀ n, (0 ≤ x n → 0 ≤ H x n ∧ H x n ≤ x n) ∧
      (x n ≤ 0 → x n ≤ H x n ∧ H x n ≤ 0) := fun x hx n => hN x hx n
  -- Step 4: every point of the ball is matched.
  have hHmatched : ∀ x ∈ ballIn X, (Function.support (H x)).Finite →
      ∃ w ∈ X', ∀ i, x i ≠ 0 → 0 < w i * x i := by
    intro x hx _
    rw [mem_ballIn] at hx
    rcases hmatch with hXc | hRSP
    · have hx00 : x ∈ c00 Γ := hXc ▸ hx.1
      exact ⟨x, hX'0 hx00, fun i hi => mul_self_pos.2 hi⟩
    · have hcount : (Function.support (⇑x)).Countable := countable_support_of_mem_c0 (hX1 hx.1)
      obtain ⟨v, hvY, hv⟩ := hRSP (σ.symm ⁻¹' Function.support (⇑x))
        (hcount.preimage σ.symm.injective)
        (fun d => α (σ.symm d) * (if 0 < x (σ.symm d) then 1 else -1))
        (fun d _ => by
          beta_reduce
          rcases hα (σ.symm d) with h | h <;> split_ifs <;> norm_num [h])
      refine ⟨B v, ?_, fun i hi => ?_⟩
      · rw [hmemX', hAB]; exact hvY
      · have hmem : σ i ∈ σ.symm ⁻¹' Function.support (⇑x) := by
          simp only [Set.mem_preimage, Equiv.symm_apply_apply, Function.mem_support]; exact hi
        have h := hv (σ i) hmem
        simp only [Equiv.symm_apply_apply] at h
        rw [hBapp]
        rcases lt_or_gt_of_ne hi with hneg | hpos
        · rw [if_neg (not_lt.2 hneg.le)] at h
          nlinarith
        · rw [if_pos hpos] at h
          nlinarith
  -- Step 5: rigidity.
  have hrig := Plasticity.CUB37.rigidity X X' hX0 hX1 hX'0 hX'1 H hHbij hHlip hHN1 hHmatched
  refine ⟨σ, α, hα, fun x hx n => ?_⟩
  have h1 : H x n = x n := by rw [hrig x hx]
  rw [hHapp] at h1
  calc F x (σ n) = α n * (α n * F x (σ n)) := by rw [← mul_assoc, hαsq, one_mul]
    _ = α n * x n := by rw [h1]
