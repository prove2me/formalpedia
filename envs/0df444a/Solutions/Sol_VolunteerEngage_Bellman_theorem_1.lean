-- Prove2me | solution 1 for VolunteerEngage.Bellman.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:08:50.421981+00:00
-- url     : https://prove2.me/submissions/6d8513a7-d5b1-4d24-bedd-8469ffff74d3

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

open Filter Topology Set

namespace VolBellSol

open VolunteerEngage.Bellman

variable (M : Model)

lemma theta_succ (k : ℕ) : M.θ (k + 1) = M.θ k + M.η (k + 1) := by
  unfold Model.θ
  rw [Finset.sum_Icc_succ_top (by omega)]
  ring

lemma theta0_le (hM : M.Standing) (m : ℕ) (hm : m ≤ M.L) : M.θ0 ≤ M.θ m := by
  unfold Model.θ
  have : 0 ≤ ∑ i ∈ Finset.Icc 1 m, M.η i := by
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact (hM.2.2.1 i (by rw [Finset.mem_Icc]; omega)).le
  linarith

lemma theta_pred_le (hM : M.Standing) (l : ℕ) (hl : l ∈ Finset.Icc 1 M.L) :
    M.θ (l - 1) ≤ M.θ l := by
  rw [Finset.mem_Icc] at hl
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [theta_succ]
  have := hM.2.2.1 (k + 1) (by rw [Finset.mem_Icc]; omega)
  linarith

lemma c_pos (hM : M.Standing) : ∀ l, 1 ≤ l → l ≤ M.L → 0 < M.c l := by
  intro l h1 h2
  induction l with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; exact hM.2.2.2.1
    · have := ih hk (by omega)
      have := hM.2.2.2.2.1 k (by rw [Finset.mem_Ico]; omega)
      linarith

lemma cost_nonneg (hM : M.Standing) (x : ℝ) : 0 ≤ cost M x := by
  unfold cost
  apply Finset.sum_nonneg
  intro l hl
  have hc := c_pos M hM l (Finset.mem_Icc.1 hl).1 (Finset.mem_Icc.1 hl).2
  have := theta_pred_le M hM l hl
  apply mul_nonneg hc.le
  have : M.θ (l - 1) ≤ min (M.θ l) (max (M.θ (l - 1)) x) := le_min this (le_max_left _ _)
  linarith

lemma cost_theta0 (hM : M.Standing) : cost M M.θ0 = 0 := by
  unfold cost
  apply Finset.sum_eq_zero
  intro l hl
  have h1 := theta_pred_le M hM l hl
  have h2 := theta0_le M hM (l - 1) (by have := (Finset.mem_Icc.1 hl).2; omega)
  rw [max_eq_left h2, min_eq_right h1]
  ring

/-- the Lipschitz constant used -/
noncomputable def CL : ℝ := max |M.θ0| |M.θ M.L|

lemma CL_nonneg : 0 ≤ CL M := le_max_of_le_left (abs_nonneg _)

lemma abs_le_CL {x : ℝ} (hx : x ∈ Icc M.θ0 (M.θ M.L)) : |x| ≤ CL M :=
  abs_le_max_abs_abs hx.1 hx.2

lemma A_nonempty (hM : M.Standing) : (Icc M.θ0 (M.θ M.L)).Nonempty :=
  ⟨M.θ0, le_rfl, theta0_le M hM M.L le_rfl⟩

lemma bdd (hM : M.Standing) (y : ℝ) :
    BddAbove ((fun x => y * x - cost M x) '' Icc M.θ0 (M.θ M.L)) := by
  refine ⟨|y| * CL M, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := cost_nonneg M hM x
  have h2 : y * x ≤ |y| * CL M := by
    calc y * x ≤ |y * x| := le_abs_self _
      _ = |y| * |x| := abs_mul _ _
      _ ≤ |y| * CL M := mul_le_mul_of_nonneg_left (abs_le_CL M hx) (abs_nonneg _)
  simp only
  linarith

lemma le_phi (hM : M.Standing) (y : ℝ) {x : ℝ} (hx : x ∈ Icc M.θ0 (M.θ M.L)) :
    y * x - cost M x ≤ phi M y :=
  le_csSup (bdd M hM y) (mem_image_of_mem _ hx)

lemma phi_le (hM : M.Standing) (y b : ℝ) (h : ∀ x ∈ Icc M.θ0 (M.θ M.L), y * x - cost M x ≤ b) :
    phi M y ≤ b := by
  apply csSup_le ((A_nonempty M hM).image _)
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

lemma phi_lip_le (hM : M.Standing) (y₁ y₂ : ℝ) : phi M y₁ ≤ phi M y₂ + CL M * |y₁ - y₂| := by
  apply phi_le M hM
  intro x hx
  have h1 := le_phi M hM y₂ hx
  have h2 : (y₁ - y₂) * x ≤ CL M * |y₁ - y₂| := by
    calc (y₁ - y₂) * x ≤ |(y₁ - y₂) * x| := le_abs_self _
      _ = |y₁ - y₂| * |x| := abs_mul _ _
      _ ≤ |y₁ - y₂| * CL M := mul_le_mul_of_nonneg_left (abs_le_CL M hx) (abs_nonneg _)
      _ = CL M * |y₁ - y₂| := mul_comm _ _
  nlinarith

lemma phi_lip (hM : M.Standing) (y₁ y₂ : ℝ) : |phi M y₁ - phi M y₂| ≤ CL M * |y₁ - y₂| := by
  rw [abs_le]
  have h1 := phi_lip_le M hM y₁ y₂
  have h2 := phi_lip_le M hM y₂ y₁
  rw [abs_sub_comm] at h2
  constructor <;> linarith

lemma phi_zero (hM : M.Standing) : phi M 0 = 0 := by
  apply le_antisymm
  · apply phi_le M hM
    intro x _
    have := cost_nonneg M hM x
    linarith
  · have := le_phi M hM 0 (x := M.θ0) ⟨le_rfl, theta0_le M hM M.L le_rfl⟩
    rw [cost_theta0 M hM] at this
    linarith

lemma phi_ge (hM : M.Standing) (y : ℝ) : M.θ0 * y ≤ phi M y := by
  have := le_phi M hM y (x := M.θ0) ⟨le_rfl, theta0_le M hM M.L le_rfl⟩
  rw [cost_theta0 M hM] at this
  linarith

lemma phi_abs_le (hM : M.Standing) (y : ℝ) : |phi M y| ≤ CL M * |y| := by
  have := phi_lip M hM y 0
  rwa [phi_zero M hM, sub_zero, sub_zero] at this

lemma phi_continuous (hM : M.Standing) : Continuous (phi M) := by
  have : LipschitzWith (Real.toNNReal (CL M)) (phi M) := by
    apply LipschitzWith.of_dist_le_mul
    intro y₁ y₂
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (CL_nonneg M)]
    exact phi_lip M hM y₁ y₂
  exact this.continuous

end VolBellSol

namespace VolBellSol

structure Hyp (κ p σ θ0 C : ℝ) (φ : ℝ → ℝ) : Prop where
  hκ : 0 < κ
  hp : 0 < p
  hσ : 0 < σ
  hθ0 : θ0 < 0
  hC : 0 ≤ C
  lip : ∀ y₁ y₂, |φ y₁ - φ y₂| ≤ C * |y₁ - y₂|
  zero : φ 0 = 0
  ge : ∀ y, θ0 * y ≤ φ y
  cont : Continuous φ

/-- abstract IVP solution -/
def Sol (κ p σ : ℝ) (φ : ℝ → ℝ) (β : ℝ) (v v' : ℝ → ℝ) : Prop :=
  ContinuousOn v' (Set.Ici 0) ∧
  (∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt v (v' x) (Set.Ici 0) x) ∧
  (∀ x : ℝ, 0 ≤ x → β = σ ^ 2 / 2 * v' x + x * κ * (p - v x) - φ (p - v x)) ∧
  v 0 = 0

/-- the vector field -/
noncomputable def F (κ p σ : ℝ) (φ : ℝ → ℝ) (β t y : ℝ) : ℝ :=
  2 / σ ^ 2 * (β - t * κ * (p - y) + φ (p - y))

section

variable {κ p σ θ0 C : ℝ} {φ : ℝ → ℝ}

lemma F_lip (H : Hyp κ p σ θ0 C φ) (β : ℝ) {t X : ℝ} (ht0 : 0 ≤ t) (htX : t ≤ X) (y₁ y₂ : ℝ) :
    |F κ p σ φ β t y₁ - F κ p σ φ β t y₂| ≤ 2 / σ ^ 2 * (X * κ + C) * |y₁ - y₂| := by
  have ha : 0 < 2 / σ ^ 2 := by have := H.hσ; positivity
  unfold F
  have e : 2 / σ ^ 2 * (β - t * κ * (p - y₁) + φ (p - y₁)) -
      2 / σ ^ 2 * (β - t * κ * (p - y₂) + φ (p - y₂)) =
      2 / σ ^ 2 * (t * κ * (y₁ - y₂) + (φ (p - y₁) - φ (p - y₂))) := by ring
  rw [e, abs_mul, abs_of_pos ha]
  suffices key : |t * κ * (y₁ - y₂) + (φ (p - y₁) - φ (p - y₂))| ≤ (X * κ + C) * |y₁ - y₂| by
    calc _ ≤ 2 / σ ^ 2 * ((X * κ + C) * |y₁ - y₂|) := mul_le_mul_of_nonneg_left key ha.le
      _ = _ := by ring
  have h1 := H.lip (p - y₁) (p - y₂)
  have e2 : p - y₁ - (p - y₂) = -(y₁ - y₂) := by ring
  rw [e2, abs_neg] at h1
  have h2 : |t * κ * (y₁ - y₂)| ≤ X * κ * |y₁ - y₂| := by
    rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_pos H.hκ]
    have := abs_nonneg (y₁ - y₂)
    have := H.hκ
    have : t * κ ≤ X * κ := by nlinarith
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  calc |t * κ * (y₁ - y₂) + (φ (p - y₁) - φ (p - y₂))|
      ≤ |t * κ * (y₁ - y₂)| + |φ (p - y₁) - φ (p - y₂)| := abs_add_le _ _
    _ ≤ X * κ * |y₁ - y₂| + C * |y₁ - y₂| := add_le_add h2 h1
    _ = (X * κ + C) * |y₁ - y₂| := by ring

lemma F_bound (H : Hyp κ p σ θ0 C φ) (β : ℝ) {t X : ℝ} (ht0 : 0 ≤ t) (htX : t ≤ X) (y : ℝ) :
    |F κ p σ φ β t y| ≤ 2 / σ ^ 2 * (|β| + (X * κ + C) * (p + |y|)) := by
  have ha : 0 < 2 / σ ^ 2 := by have := H.hσ; positivity
  unfold F
  rw [abs_mul, abs_of_pos ha]
  apply mul_le_mul_of_nonneg_left _ ha.le
  have h0 := H.lip (p - y) 0
  rw [H.zero, sub_zero, sub_zero] at h0
  have hpy : |p - y| ≤ p + |y| := by
    calc |p - y| ≤ |p| + |y| := abs_sub _ _
      _ = p + |y| := by rw [abs_of_pos H.hp]
  have h2 : |t * κ * (p - y)| ≤ X * κ * (p + |y|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_pos H.hκ]
    have := abs_nonneg (p - y)
    have := H.hκ
    have hX : 0 ≤ X := ht0.trans htX
    have : t * κ ≤ X * κ := by nlinarith
    calc t * κ * |p - y| ≤ X * κ * |p - y| := by nlinarith
      _ ≤ X * κ * (p + |y|) := mul_le_mul_of_nonneg_left hpy (by positivity)
  have h3 : C * |p - y| ≤ C * (p + |y|) := mul_le_mul_of_nonneg_left hpy H.hC
  calc |β - t * κ * (p - y) + φ (p - y)| ≤ |β - t * κ * (p - y)| + |φ (p - y)| := abs_add_le _ _
    _ ≤ |β| + |t * κ * (p - y)| + |φ (p - y)| := by
        have := abs_sub β (t * κ * (p - y)); linarith
    _ ≤ |β| + (X * κ + C) * (p + |y|) := by nlinarith

/-- clamp -/
def clamp (B y : ℝ) : ℝ := max (-B) (min B y)

lemma clamp_lip (B y₁ y₂ : ℝ) : |clamp B y₁ - clamp B y₂| ≤ |y₁ - y₂| := by
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> rw [abs_le] <;> constructor <;>
    (rcases abs_cases (y₁ - y₂) with ⟨h, _⟩ | ⟨h, _⟩) <;> linarith

lemma clamp_abs_le (B y : ℝ) (hB : 0 ≤ B) : |clamp B y| ≤ |y| := by
  have := clamp_lip B y 0
  unfold clamp at this ⊢
  simp only [max_def, min_def] at this ⊢
  split_ifs at this ⊢ <;> rw [abs_le] <;> constructor <;>
    (rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩) <;> linarith

lemma clamp_abs_le' (B y : ℝ) (hB : 0 ≤ B) : |clamp B y| ≤ B := by
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma clamp_eq (B y : ℝ) (h : |y| ≤ B) : clamp B y = y := by
  unfold clamp
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

lemma deriv_Ici_of_Icc {α : ℝ → ℝ} {d a b t : ℝ} (h : HasDerivWithinAt α d (Icc a b) t)
    (ht : t ∈ Ico a b) : HasDerivWithinAt α d (Ici t) t :=
  h.mono_of_mem_nhdsWithin (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl))

lemma gronwallBound_nonneg' {K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    0 ≤ gronwallBound 0 K ε x := by
  have := gronwallBound_mono (δ := 0) le_rfl hε hK hx
  rwa [gronwallBound_x0] at this

lemma exists_local (H : Hyp κ p σ θ0 C φ) (β X : ℝ) (hX : 0 ≤ X) :
    ∃ α : ℝ → ℝ, α 0 = 0 ∧
      ∀ t ∈ Icc 0 X, HasDerivWithinAt α (F κ p σ φ β t (α t)) (Icc 0 X) t := by
  have ha : 0 < 2 / σ ^ 2 := by have := H.hσ; positivity
  have hκ := H.hκ
  have hC := H.hC
  have hp := H.hp
  set K : ℝ := 2 / σ ^ 2 * (X * κ + C) with hK
  set A : ℝ := 2 / σ ^ 2 * (|β| + (X * κ + C) * p) with hA
  have hK0 : 0 ≤ K := by positivity
  have hA0 : 0 ≤ A := by positivity
  set B : ℝ := gronwallBound 0 K A X with hB
  have hB0 : 0 ≤ B := gronwallBound_nonneg' hK0 hA0 hX
  set G : ℝ → ℝ → ℝ := fun t y => F κ p σ φ β t (clamp B y) with hG
  set Lv : ℝ := 2 / σ ^ 2 * (|β| + (X * κ + C) * (p + B)) with hLv
  have hLv0 : 0 ≤ Lv := by positivity
  have hPL : IsPicardLindelof G (tmin := 0) (tmax := X) ⟨0, le_rfl, hX⟩ (0 : ℝ)
      (Lv * X).toNNReal 0 Lv.toNNReal K.toNNReal := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro y₁ _ y₂ _
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK0]
      calc |G t y₁ - G t y₂| ≤ K * |clamp B y₁ - clamp B y₂| :=
            F_lip H β ht.1 ht.2 _ _
        _ ≤ K * |y₁ - y₂| := mul_le_mul_of_nonneg_left (clamp_lip _ _ _) hK0
    · intro y _
      apply Continuous.continuousOn
      simp only [hG, F]
      fun_prop
    · intro t ht y _
      rw [Real.norm_eq_abs, Real.coe_toNNReal _ hLv0]
      calc |G t y| ≤ 2 / σ ^ 2 * (|β| + (X * κ + C) * (p + |clamp B y|)) :=
            F_bound H β ht.1 ht.2 _
        _ ≤ Lv := by
          have := clamp_abs_le' B y hB0
          have : 0 ≤ X * κ + C := by positivity
          apply mul_le_mul_of_nonneg_left _ ha.le
          nlinarith
    · simp only [NNReal.coe_zero, sub_zero, Real.coe_toNNReal _ hLv0]
      rw [Real.coe_toNNReal _ (by positivity)]
      simp [hX]
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hcont : ContinuousOn α (Icc 0 X) := fun t ht => (hα t ht).continuousWithinAt
  have hbound : ∀ t ∈ Icc 0 X, ‖α t‖ ≤ gronwallBound 0 K A (t - 0) := by
    apply norm_le_gronwallBound_of_norm_deriv_right_le (f' := fun t => G t (α t)) hcont
    · intro t ht
      exact deriv_Ici_of_Icc (hα t (Ico_subset_Icc_self ht)) ht
    · simp [hα0]
    · intro t ht
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      calc |G t (α t)| ≤ 2 / σ ^ 2 * (|β| + (X * κ + C) * (p + |clamp B (α t)|)) :=
            F_bound H β ht.1 ht.2.le _
        _ ≤ 2 / σ ^ 2 * (|β| + (X * κ + C) * (p + |α t|)) := by
          have := clamp_abs_le B (α t) hB0
          have : 0 ≤ X * κ + C := by positivity
          apply mul_le_mul_of_nonneg_left _ ha.le
          nlinarith
        _ = K * |α t| + A := by rw [hK, hA]; ring
  refine ⟨α, hα0, fun t ht => ?_⟩
  have hb : |α t| ≤ B := by
    have := hbound t ht
    rw [sub_zero, Real.norm_eq_abs] at this
    exact this.trans (gronwallBound_mono (δ := 0) le_rfl hA0 hK0 ht.2)
  have := hα t ht
  simp only [hG, clamp_eq B (α t) hb] at this
  exact this

end

end VolBellSol

namespace VolBellSol

section

variable {κ p σ θ0 C : ℝ} {φ : ℝ → ℝ}

lemma gron (H : Hyp κ p σ θ0 C φ) {β₁ β₂ X : ℝ} (hX : 0 ≤ X) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 X))
    (hf' : ∀ t ∈ Ico 0 X, HasDerivWithinAt f (F κ p σ φ β₁ t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc 0 X))
    (hg' : ∀ t ∈ Ico 0 X, HasDerivWithinAt g (F κ p σ φ β₂ t (g t)) (Ici t) t)
    (h0 : f 0 = g 0) :
    ∀ t ∈ Icc 0 X, dist (f t) (g t) ≤
      gronwallBound 0 (2 / σ ^ 2 * (X * κ + C)) (2 / σ ^ 2 * |β₁ - β₂|) t := by
  have ha : 0 < 2 / σ ^ 2 := by have := H.hσ; positivity
  have hK0 : 0 ≤ 2 / σ ^ 2 * (X * κ + C) := by have := H.hκ; have := H.hC; positivity
  intro t ht
  have := dist_le_of_approx_trajectories_ODE_of_mem (v := fun t => F κ p σ φ β₂ t)
    (s := fun _ => univ) (K := (2 / σ ^ 2 * (X * κ + C)).toNNReal)
    (εf := 2 / σ ^ 2 * |β₁ - β₂|) (εg := 0) (δ := 0)
    (f' := fun t => F κ p σ φ β₁ t (f t)) (g' := fun t => F κ p σ φ β₂ t (g t))
    ?_ hf hf' ?_ (fun _ _ => trivial) hg hg' ?_ (fun _ _ => trivial) (by simp [h0]) t ht
  · rwa [Real.coe_toNNReal _ hK0, add_zero, sub_zero] at this
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro y₁ _ y₂ _
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK0]
    exact F_lip H β₂ ht.1 ht.2.le _ _
  · intro t _
    rw [Real.dist_eq]
    unfold F
    have : 2 / σ ^ 2 * (β₁ - t * κ * (p - f t) + φ (p - f t)) -
        2 / σ ^ 2 * (β₂ - t * κ * (p - f t) + φ (p - f t)) = 2 / σ ^ 2 * (β₁ - β₂) := by ring
    rw [this, abs_mul, abs_of_pos ha]
  · intro t _
    simp

lemma exists_sol (H : Hyp κ p σ θ0 C φ) (β : ℝ) : ∃ v v' : ℝ → ℝ, Sol κ p σ φ β v v' := by
  have ha : 0 < 2 / σ ^ 2 := by have := H.hσ; positivity
  choose α hα0 hα using fun n : ℕ => exists_local H β n (Nat.cast_nonneg n)
  have agree : ∀ m n : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ m → t ≤ n → α m t = α n t := by
    intro m n t h0 hm hn
    have hX : (0 : ℝ) ≤ min (m : ℝ) n := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have key := gron H (β₁ := β) (β₂ := β) hX (f := α m) (g := α n)
      (fun s hs => ((hα m s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩).continuousWithinAt).mono
        (Icc_subset_Icc le_rfl (min_le_left _ _)))
      (fun s hs => deriv_Ici_of_Icc (hα m s ⟨hs.1, hs.2.le.trans (min_le_left _ _)⟩)
        ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩)
      (fun s hs => ((hα n s ⟨hs.1, hs.2.trans (min_le_right _ _)⟩).continuousWithinAt).mono
        (Icc_subset_Icc le_rfl (min_le_right _ _)))
      (fun s hs => deriv_Ici_of_Icc (hα n s ⟨hs.1, hs.2.le.trans (min_le_right _ _)⟩)
        ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩)
      (by rw [hα0, hα0]) t ⟨h0, le_min hm hn⟩
    rw [sub_self, abs_zero, mul_zero, gronwallBound_ε0_δ0] at key
    exact dist_le_zero.1 key
  set v : ℝ → ℝ := fun x => α (⌈x⌉₊ + 1) x with hv
  have hder : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt v (F κ p σ φ β x (v x)) (Ici 0) x := by
    intro x hx
    set N := ⌈x⌉₊ + 1 with hN
    have hxN : x < (N : ℝ) := by
      rw [hN]; push_cast
      exact lt_of_le_of_lt (Nat.le_ceil x) (by linarith)
    have h1 := hα N x ⟨hx, hxN.le⟩
    have hmem : Icc (0 : ℝ) N ∈ 𝓝[Ici 0] x := by
      rw [← Ici_inter_Iic]
      exact inter_mem_nhdsWithin _ (Iic_mem_nhds hxN)
    have h2 := h1.mono_of_mem_nhdsWithin hmem
    apply h2.congr_of_eventuallyEq
    · filter_upwards [hmem] with y hy
      simp only [hv]
      apply agree
      · exact hy.1
      · push_cast
        linarith [Nat.le_ceil y]
      · exact hy.2
    · rfl
  have hcont : ContinuousOn v (Ici 0) := fun x hx => (hder x hx).continuousWithinAt
  refine ⟨v, fun x => F κ p σ φ β x (v x), ?_, hder, ?_, ?_⟩
  · have hφ := H.cont
    unfold F
    fun_prop
  · intro x _
    have hσ := H.hσ.ne'
    unfold F
    field_simp
    ring
  · simp only [hv, Nat.ceil_zero, zero_add]
    exact hα0 1

lemma sol_deriv_eq (H : Hyp κ p σ θ0 C φ) {β : ℝ} {v v' : ℝ → ℝ} (h : Sol κ p σ φ β v v')
    {x : ℝ} (hx : 0 ≤ x) : v' x = F κ p σ φ β x (v x) := by
  have hσ := H.hσ
  have e := h.2.2.1 x hx
  unfold F
  rw [e]
  field_simp
  ring

lemma sol_gron (H : Hyp κ p σ θ0 C φ) {β₁ β₂ : ℝ} {v₁ v₁' v₂ v₂' : ℝ → ℝ}
    (h₁ : Sol κ p σ φ β₁ v₁ v₁') (h₂ : Sol κ p σ φ β₂ v₂ v₂') {x : ℝ} (hx : 0 ≤ x) :
    dist (v₁ x) (v₂ x) ≤
      gronwallBound 0 (2 / σ ^ 2 * (x * κ + C)) (2 / σ ^ 2 * |β₁ - β₂|) x := by
  apply gron H hx
  · exact fun t ht => (h₁.2.1 t ht.1).continuousWithinAt.mono (fun s hs => hs.1)
  · intro t ht
    rw [← sol_deriv_eq H h₁ ht.1]
    exact (h₁.2.1 t ht.1).mono (Ici_subset_Ici.2 ht.1)
  · exact fun t ht => (h₂.2.1 t ht.1).continuousWithinAt.mono (fun s hs => hs.1)
  · intro t ht
    rw [← sol_deriv_eq H h₂ ht.1]
    exact (h₂.2.1 t ht.1).mono (Ici_subset_Ici.2 ht.1)
  · rw [h₁.2.2.2, h₂.2.2.2]
  · exact ⟨hx, le_rfl⟩

lemma sol_cont (H : Hyp κ p σ θ0 C φ) (S S' : ℝ → ℝ → ℝ)
    (hS : ∀ β, Sol κ p σ φ β (S β) (S' β)) {x : ℝ} (hx : 0 ≤ x) :
    Continuous (fun β => S β x) := by
  have ha : 0 < 2 / σ ^ 2 := by have := H.hσ; positivity
  set K := 2 / σ ^ 2 * (x * κ + C)
  have hg := gronwallBound_continuous_ε 0 K x
  rw [Metric.continuous_iff] at hg ⊢
  intro b ε hε
  obtain ⟨ρ, hρ, hρ'⟩ := hg 0 ε hε
  refine ⟨ρ / (2 / σ ^ 2), div_pos hρ ha, fun a hab => ?_⟩
  have h1 := sol_gron H (hS a) (hS b) hx
  have h2 := hρ' (2 / σ ^ 2 * |a - b|) (by
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos ha, abs_abs]
    rw [Real.dist_eq] at hab
    rwa [lt_div_iff₀ ha, mul_comm] at hab)
  rw [gronwallBound_ε0_δ0, Real.dist_eq, sub_zero] at h2
  exact lt_of_le_of_lt h1 (lt_of_le_of_lt (le_abs_self _) h2)

end

end VolBellSol

namespace VolBellSol

section

variable {κ p σ θ0 C : ℝ} {φ : ℝ → ℝ} {β : ℝ} {v v' : ℝ → ℝ}

lemma sol_eqn (h : Sol κ p σ φ β v v') {x : ℝ} (hx : 0 ≤ x) :
    σ ^ 2 / 2 * v' x = β - x * κ * (p - v x) + φ (p - v x) := by
  have := h.2.2.1 x hx
  linarith

lemma sol_hasDerivAt (h : Sol κ p σ φ β v v') {x : ℝ} (hx : 0 < x) : HasDerivAt v (v' x) x :=
  (h.2.1 x hx.le).hasDerivAt (Ici_mem_nhds hx)

lemma sol_right (h : Sol κ p σ φ β v v') {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt v (v' x) (Ici x) x :=
  (h.2.1 x hx).mono (Ici_subset_Ici.2 hx)

lemma sol_contOn (h : Sol κ p σ φ β v v') {D : Set ℝ} (hD : D ⊆ Ici 0) : ContinuousOn v D :=
  fun x hx => ((h.2.1 x (hD hx)).continuousWithinAt).mono hD

lemma interior_sub {D : Set ℝ} (hD : D ⊆ Ici 0) {x : ℝ} (hx : x ∈ interior D) : 0 < x := by
  have := interior_mono hD hx
  rwa [interior_Ici] at this

lemma sol_antitoneOn (h : Sol κ p σ φ β v v') {D : Set ℝ} (hc : Convex ℝ D) (hD : D ⊆ Ici 0)
    (hn : ∀ x ∈ interior D, v' x ≤ 0) : AntitoneOn v D :=
  antitoneOn_of_hasDerivWithinAt_nonpos hc (sol_contOn h hD)
    (fun x hx => (sol_hasDerivAt h (interior_sub hD hx)).hasDerivWithinAt) hn

lemma sol_monotoneOn (h : Sol κ p σ φ β v v') {D : Set ℝ} (hc : Convex ℝ D) (hD : D ⊆ Ici 0)
    (hn : ∀ x ∈ interior D, 0 ≤ v' x) : MonotoneOn v D :=
  monotoneOn_of_hasDerivWithinAt_nonneg hc (sol_contOn h hD)
    (fun x hx => (sol_hasDerivAt h (interior_sub hD hx)).hasDerivWithinAt) hn

lemma sol_le_lin (h : Sol κ p σ φ β v v') {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hd : ∀ x ∈ Ico a b, v' x ≤ c) : v b ≤ v a + c * (b - a) := by
  have := image_le_of_deriv_right_le_deriv_boundary (f := v) (f' := v') (a := a) (b := b)
    (sol_contOn h (fun x hx => ha.trans hx.1)) (fun x hx => sol_right h (ha.trans hx.1))
    (B := fun x => v a + c * (x - a)) (B' := fun _ => c) (by simp) (by fun_prop)
    (fun x _ => by
      have := (((hasDerivAt_id x).sub_const a).const_mul c).const_add (v a)
      simpa using this.hasDerivWithinAt) hd (x := b) ⟨hab, le_rfl⟩
  simpa using this

lemma sol_ge_lin (h : Sol κ p σ φ β v v') {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hd : ∀ x ∈ Ico a b, c ≤ v' x) : v a + c * (b - a) ≤ v b := by
  have := image_le_of_deriv_right_le_deriv_boundary (f := fun x => v a + c * (x - a))
    (f' := fun _ => c) (a := a) (b := b) (by fun_prop)
    (fun x _ => by
      have := (((hasDerivAt_id x).sub_const a).const_mul c).const_add (v a)
      simpa using this.hasDerivWithinAt)
    (B := v) (B' := v') (by simp) (sol_contOn h (fun x hx => ha.trans hx.1))
    (fun x hx => sol_right h (ha.trans hx.1)) hd (x := b) ⟨hab, le_rfl⟩
  simpa using this

/-- Trap: once `v ≥ p`, it stays `≥ p` (needs `β > 0`). -/
lemma trap_above (H : Hyp κ p σ θ0 C φ) (hβ : 0 < β) (h : Sol κ p σ φ β v v') {xa : ℝ}
    (hxa : 0 ≤ xa) (hv : p ≤ v xa) : ∀ x, xa ≤ x → p ≤ v x := by
  intro x hx
  have hσ := H.hσ
  have := image_le_of_deriv_right_lt_deriv_boundary' (f := fun y => -v y)
    (f' := fun y => -v' y) (a := xa) (b := x)
    ((sol_contOn h (fun y hy => hxa.trans hy.1)).neg)
    (fun y hy => (sol_right h (hxa.trans hy.1)).neg)
    (B := fun _ => -p) (B' := fun _ => 0) (by show -v xa ≤ -p; linarith) continuousOn_const
    (fun y _ => hasDerivWithinAt_const _ _ _)
    (fun y hy hyB => by
      have hvy : v y = p := by change -v y = -p at hyB; linarith
      have e := sol_eqn h (hxa.trans hy.1)
      rw [hvy, sub_self, mul_zero, sub_zero, H.zero, add_zero] at e
      have : 0 < v' y := by
        have : 0 < σ ^ 2 / 2 := by positivity
        nlinarith
      show -v' y < 0
      linarith) (x := x) ⟨hx, le_rfl⟩
  change -v x ≤ -p at this
  linarith

/-- Key structural lemma: once `v' < 0` at a level below `p`, `v'` stays negative. -/
lemma neg_persist (H : Hyp κ p σ θ0 C φ) (h : Sol κ p σ φ β v v') {x0 : ℝ} (hx0 : 0 ≤ x0)
    (hvp : v x0 < p) (hd : v' x0 < 0) : ∀ x, x0 ≤ x → v' x < 0 := by
  by_contra hcon
  push Not at hcon
  have hκ := H.hκ
  have hC := H.hC
  set S : Set ℝ := Ici x0 ∩ v' ⁻¹' Ici 0 with hSdef
  have hSc : IsClosed S :=
    (h.1.mono (Ici_subset_Ici.2 hx0)).preimage_isClosed_of_isClosed isClosed_Ici isClosed_Ici
  have hSne : S.Nonempty := by
    obtain ⟨x, hx, hx'⟩ := hcon
    exact ⟨x, hx, hx'⟩
  have hSbdd : BddBelow S := ⟨x0, fun y hy => hy.1⟩
  set x1 := sInf S with hx1def
  have hx1S : x1 ∈ S := hSc.csInf_mem hSne hSbdd
  have hx01 : x0 ≤ x1 := hx1S.1
  have hd1 : 0 ≤ v' x1 := hx1S.2
  have hbefore : ∀ y, x0 ≤ y → y < x1 → v' y < 0 := by
    intro y hy1 hy2
    by_contra hy
    push Not at hy
    have : x1 ≤ y := csInf_le hSbdd ⟨hy1, hy⟩
    linarith
  have hlt : x0 < x1 := by
    rcases eq_or_lt_of_le hx01 with he | he
    · rw [← he] at hd1; linarith
    · exact he
  have hx1pos : 0 ≤ x1 := hx0.trans hx01
  have hanti : AntitoneOn v (Icc x0 x1) := by
    apply sol_antitoneOn h (convex_Icc _ _) (fun y hy => hx0.trans hy.1)
    intro y hy
    rw [interior_Icc] at hy
    exact (hbefore y hy.1.le hy.2).le
  have hv1 : v x1 < p := lt_of_le_of_lt (hanti ⟨le_rfl, hx01⟩ ⟨hx01, le_rfl⟩ hx01) hvp
  set w1 := p - v x1 with hw1
  have hw1pos : 0 < w1 := by rw [hw1]; linarith
  set ε := κ * w1 / (2 * (C + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hcont := h.1 x1 hx1pos
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, hδ'⟩ := hcont ε hεpos
  set x := max x0 (x1 - δ / 2) with hxdef
  have hx0x : x0 ≤ x := le_max_left _ _
  have hxx1 : x < x1 := max_lt hlt (by linarith)
  have hxpos : 0 ≤ x := hx0.trans hx0x
  have hgrad : ∀ y ∈ Ico x x1, -ε ≤ v' y := by
    intro y hy
    have hy0 : 0 ≤ y := hxpos.trans hy.1
    have hdist : dist y x1 < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · have : x1 - δ / 2 ≤ x := le_max_right _ _
        linarith [hy.1]
      · linarith [hy.2]
    have := hδ' (show y ∈ Ici (0 : ℝ) from hy0) hdist
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  have hlin := sol_ge_lin h hxpos hxx1.le hgrad
  set d := v x - v x1 with hd_def
  have hd0 : 0 ≤ d := by
    have := hanti ⟨hx0x, hxx1.le⟩ ⟨hx01, le_rfl⟩ hxx1.le
    rw [hd_def]; linarith
  have hdle : d ≤ ε * (x1 - x) := by rw [hd_def]; linarith
  have e1 := sol_eqn h hx1pos
  have e0 := sol_eqn h hxpos
  have hvx : v' x < 0 := hbefore x hx0x hxx1
  have hσ2 : 0 < σ ^ 2 / 2 := by have := H.hσ; positivity
  have hlhs1 : 0 ≤ σ ^ 2 / 2 * v' x1 := mul_nonneg hσ2.le hd1
  have hlhs0 : σ ^ 2 / 2 * v' x < 0 := mul_neg_of_pos_of_neg hσ2 hvx
  have hlip := H.lip (p - v x1) (p - v x)
  have e3 : p - v x1 - (p - v x) = d := by rw [hd_def]; ring
  rw [e3, abs_of_nonneg hd0] at hlip
  have hlip' : φ (p - v x1) - φ (p - v x) ≤ C * d := (le_abs_self _).trans hlip
  have hxκd : 0 ≤ x * κ * d := by positivity
  have hpvx : p - v x = w1 - d := by rw [hw1, hd_def]; ring
  have hCε : C * ε ≤ κ * w1 / 2 := by
    rw [hε]
    have : C / (C + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    calc C * (κ * w1 / (2 * (C + 1))) = (κ * w1 / 2) * (C / (C + 1)) := by
          field_simp
      _ ≤ (κ * w1 / 2) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = κ * w1 / 2 := mul_one _
  have hCd : C * d ≤ κ * w1 / 2 * (x1 - x) := by
    calc C * d ≤ C * (ε * (x1 - x)) := mul_le_mul_of_nonneg_left hdle hC
      _ = (C * ε) * (x1 - x) := by ring
      _ ≤ κ * w1 / 2 * (x1 - x) := mul_le_mul_of_nonneg_right hCε (by linarith)
  -- difference of the two equations
  have key : 0 < -(x1 - x) * κ * w1 + C * d := by
    have : 0 < (β - x1 * κ * (p - v x1) + φ (p - v x1)) -
        (β - x * κ * (p - v x) + φ (p - v x)) := by linarith
    rw [hpvx, ← hw1] at this
    nlinarith
  have : 0 < (x1 - x) * (κ * w1) := by
    have := mul_pos (sub_pos.2 hxx1) (mul_pos hκ hw1pos)
    exact this
  nlinarith

/-- If `v` stays below a level `q < p` from `x0` on, then it eventually becomes negative. -/
lemma eventually_neg (H : Hyp κ p σ θ0 C φ) (h : Sol κ p σ φ β v v') {x0 q : ℝ} (hx0 : 0 ≤ x0)
    (hq : q < p) (hle : ∀ x, x0 ≤ x → v x ≤ q) : ∃ x, x0 ≤ x ∧ v x < 0 := by
  by_contra hcon
  push Not at hcon
  have hκ := H.hκ
  have hC := H.hC
  have hp := H.hp
  have hσ2 : 0 < σ ^ 2 / 2 := by have := H.hσ; positivity
  set X3 := max x0 ((|β| + C * p + 1) / (κ * (p - q))) with hX3
  have hX3a : x0 ≤ X3 := le_max_left _ _
  have hX3b : (|β| + C * p + 1) / (κ * (p - q)) ≤ X3 := le_max_right _ _
  have hX30 : 0 ≤ X3 := hx0.trans hX3a
  have hgrad : ∀ y ∈ Ico X3 (X3 + σ ^ 2 / 2 * (|q| + 1)), v' y ≤ -1 / (σ ^ 2 / 2) := by
    intro y hy
    have hy0 : 0 ≤ y := hX30.trans hy.1
    have hxy : x0 ≤ y := hX3a.trans hy.1
    have e := sol_eqn h hy0
    have hv0 := hcon y hxy
    have hvq := hle y hxy
    have hφ : φ (p - v y) ≤ C * p := by
      have := H.lip (p - v y) 0
      rw [H.zero, sub_zero, sub_zero, abs_of_nonneg (show (0:ℝ) ≤ p - v y by linarith)] at this
      have h2 := (le_abs_self (φ (p - v y))).trans this
      nlinarith
    have hyκ : |β| + C * p + 1 ≤ y * κ * (p - q) := by
      have := hX3b.trans hy.1
      rw [div_le_iff₀ (by have : 0 < p - q := by linarith
                          positivity)] at this
      linarith
    have : y * κ * (p - q) ≤ y * κ * (p - v y) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hb := le_abs_self β
    have : σ ^ 2 / 2 * v' y ≤ -1 := by linarith
    rw [le_div_iff₀ hσ2]
    linarith
  have := sol_le_lin h hX30 (by have := abs_nonneg q; nlinarith) hgrad
  have hv3 := hle X3 hX3a
  have hfin := hcon (X3 + σ ^ 2 / 2 * (|q| + 1)) (by have := abs_nonneg q; nlinarith)
  have e : -1 / (σ ^ 2 / 2) * (X3 + σ ^ 2 / 2 * (|q| + 1) - X3) = -(|q| + 1) := by
    have := H.hσ.ne'
    field_simp
    ring
  rw [e] at this
  have := le_abs_self q
  linarith

/-- `U1 ∩ U2 = ∅` on `β > 0`. -/
lemma disjoint (H : Hyp κ p σ θ0 C φ) (hβ : 0 < β) (h : Sol κ p σ φ β v v') {xa xb : ℝ}
    (hxa : 0 ≤ xa) (ha : v xa < 0) (hxb : 0 ≤ xb) (hb : p < v xb) : False := by
  have hp := H.hp
  rcases le_or_gt xb xa with hab | hab
  · have := trap_above H hβ h hxb hb.le xa hab
    linarith
  · -- MVT on [0, xa]
    have hxa0 : 0 < xa := by
      rcases eq_or_lt_of_le hxa with he | he
      · rw [← he, h.2.2.2] at ha; linarith
      · exact he
    obtain ⟨x0, hx0, hx0'⟩ := exists_hasDerivAt_eq_slope v v' hxa0
      (sol_contOn h (fun y hy => hy.1)) (fun y hy => sol_hasDerivAt h hy.1)
    rw [h.2.2.2, sub_zero, sub_zero] at hx0'
    have hd : v' x0 < 0 := by rw [hx0']; exact div_neg_of_neg_of_pos ha hxa0
    have hvx0 : v x0 < p := by
      by_contra hc
      push Not at hc
      have := trap_above H hβ h hx0.1.le hc xa hx0.2.le
      linarith
    have hneg := neg_persist H h hx0.1.le hvx0 hd
    have hanti : AntitoneOn v (Ici x0) := by
      apply sol_antitoneOn h (convex_Ici _) (fun y hy => hx0.1.le.trans hy)
      intro y hy
      rw [interior_Ici] at hy
      exact (hneg y hy.le).le
    have : v xb ≤ v x0 := hanti (le_refl x0) (show x0 ≤ xb by linarith [hx0.2]) (by linarith [hx0.2])
    linarith

end

end VolBellSol

namespace VolBellSol

section

variable {κ p σ θ0 C : ℝ} {φ : ℝ → ℝ} {β : ℝ} {v v' : ℝ → ℝ}

/-- For `β = 0` the solution becomes negative. -/
lemma zero_goes_neg (H : Hyp κ p σ θ0 C φ) (h : Sol κ p σ φ 0 v v') :
    ∃ x, 0 ≤ x ∧ v x < 0 := by
  have hκ := H.hκ
  have hC := H.hC
  have hp := H.hp
  have hσ2 : 0 < σ ^ 2 / 2 := by have := H.hσ; positivity
  set a := C / (σ ^ 2 / 2) + 1 with ha
  have hbelow : ∀ x, 0 ≤ x → v x < p := by
    intro x hx
    have := image_le_of_deriv_right_lt_deriv_boundary'
      (f := fun y => -(p - v y) * Real.exp (a * y))
      (f' := fun y => (v' y - a * (p - v y)) * Real.exp (a * y)) (a := 0) (b := x)
      (by
        have := sol_contOn h (D := Icc 0 x) (fun y hy => hy.1)
        fun_prop)
      (fun y hy => by
        have hexp : HasDerivAt (fun y => Real.exp (a * y)) (Real.exp (a * y) * a) y := by
          simpa using ((hasDerivAt_id y).const_mul a).exp
        exact (((sol_right h hy.1).const_sub p).neg.mul hexp.hasDerivWithinAt).congr_deriv
          (by simp only [Pi.neg_apply]; ring))
      (B := fun _ => -p / 2) (B' := fun _ => 0)
      (by show -(p - v 0) * Real.exp (a * 0) ≤ -p / 2
          rw [h.2.2.2]; simp; linarith)
      continuousOn_const (fun y _ => hasDerivWithinAt_const _ _ _)
      (fun y hy hyB => by
        change -(p - v y) * Real.exp (a * y) = -p / 2 at hyB
        show (v' y - a * (p - v y)) * Real.exp (a * y) < 0
        have he := Real.exp_pos (a * y)
        have hw : 0 < p - v y := by
          by_contra hc
          push Not at hc
          have : -(p - v y) * Real.exp (a * y) ≥ 0 := by
            apply mul_nonneg (by linarith) he.le
          linarith
        have e := sol_eqn h hy.1
        have hφ : φ (p - v y) ≤ C * (p - v y) := by
          have := H.lip (p - v y) 0
          rw [H.zero, sub_zero, sub_zero, abs_of_pos hw] at this
          exact (le_abs_self _).trans this
        have hyκ : 0 ≤ y * κ * (p - v y) := by have := hy.1; positivity
        have h1 : σ ^ 2 / 2 * v' y ≤ C * (p - v y) := by linarith
        have h2 : v' y ≤ C / (σ ^ 2 / 2) * (p - v y) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hσ2]
          linarith
        have : v' y - a * (p - v y) < 0 := by
          rw [ha]
          nlinarith
        exact mul_neg_of_neg_of_pos this he) (x := x) ⟨hx, le_rfl⟩
    change -(p - v x) * Real.exp (a * x) ≤ -p / 2 at this
    have he := Real.exp_pos (a * x)
    by_contra hc
    push Not at hc
    have : -(p - v x) * Real.exp (a * x) ≥ 0 := mul_nonneg (by linarith) he.le
    linarith
  set X2 := (C + 1) / κ with hX2
  have hX20 : 0 ≤ X2 := by positivity
  have hw2 : 0 < p - v X2 := by have := hbelow X2 hX20; linarith
  have hd2 : v' X2 < 0 := by
    have e := sol_eqn h hX20
    have hφ : φ (p - v X2) ≤ C * (p - v X2) := by
      have := H.lip (p - v X2) 0
      rw [H.zero, sub_zero, sub_zero, abs_of_pos hw2] at this
      exact (le_abs_self _).trans this
    have hX2κ : X2 * κ = C + 1 := by rw [hX2]; field_simp
    have : σ ^ 2 / 2 * v' X2 < 0 := by
      rw [e, hX2κ]
      nlinarith
    by_contra hc
    push Not at hc
    have := mul_nonneg hσ2.le hc
    linarith
  have hneg := neg_persist H h hX20 (by linarith) hd2
  have hanti : AntitoneOn v (Ici X2) := by
    apply sol_antitoneOn h (convex_Ici _) (fun y hy => hX20.trans hy)
    intro y hy
    rw [interior_Ici] at hy
    exact (hneg y hy.le).le
  obtain ⟨x, hx, hx'⟩ := eventually_neg H h hX20 (q := v X2) (by linarith)
    (fun x hx => hanti (le_refl X2) hx hx)
  exact ⟨x, hX20.trans hx, hx'⟩

/-- For `β` large the solution exceeds `p`. -/
lemma big_goes_above (H : Hyp κ p σ θ0 C φ) (h : Sol κ p σ φ β v v')
    (hβ : β = (κ - θ0) * p + σ ^ 2 / 2 * p + 1) : ∃ x, 0 ≤ x ∧ p < v x := by
  by_contra hcon
  push Not at hcon
  have hκ := H.hκ
  have hp := H.hp
  have hθ := H.hθ0
  have hσ2 : 0 < σ ^ 2 / 2 := by have := H.hσ; positivity
  have hnn : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ v x := by
    intro x hx
    have := image_le_of_deriv_right_lt_deriv_boundary' (f := fun y => -v y)
      (f' := fun y => -v' y) (a := 0) (b := 1)
      ((sol_contOn h (fun y hy => hy.1)).neg)
      (fun y hy => (sol_right h hy.1).neg)
      (B := fun _ => 0) (B' := fun _ => 0) (by show -v 0 ≤ 0; rw [h.2.2.2]; simp)
      continuousOn_const (fun y _ => hasDerivWithinAt_const _ _ _)
      (fun y hy hyB => by
        change -v y = 0 at hyB
        show -v' y < 0
        have hvy : v y = 0 := by linarith
        have e := sol_eqn h hy.1
        rw [hvy, sub_zero] at e
        have hφ := H.ge p
        have : y * κ * p ≤ κ * p := by
          calc y * κ * p = y * (κ * p) := by ring
            _ ≤ 1 * (κ * p) := mul_le_mul_of_nonneg_right hy.2.le (mul_pos hκ hp).le
            _ = κ * p := one_mul _
        have : 0 < σ ^ 2 / 2 * v' y := by rw [e, hβ]; nlinarith
        have : 0 < v' y := by
          by_contra hc
          push Not at hc
          nlinarith
        linarith) hx
    change -v x ≤ 0 at this
    linarith
  have hgrad : ∀ y ∈ Ico (0 : ℝ) 1, p + 1 / (σ ^ 2 / 2) ≤ v' y := by
    intro y hy
    have e := sol_eqn h hy.1
    have h0 := hnn y ⟨hy.1, hy.2.le⟩
    have h1 := hcon y hy.1
    have hφ := H.ge (p - v y)
    have : y * κ * (p - v y) ≤ κ * p := by
      have : y * (p - v y) ≤ 1 * p := by
        apply mul_le_mul hy.2.le (by linarith) (by linarith) (by norm_num)
      nlinarith
    have : θ0 * p ≤ θ0 * (p - v y) := by nlinarith
    have : σ ^ 2 / 2 * p + 1 ≤ σ ^ 2 / 2 * v' y := by rw [e, hβ]; linarith
    rw [add_div' _ _ _ hσ2.ne', div_le_iff₀ hσ2]
    linarith
  have := sol_ge_lin h le_rfl zero_le_one hgrad
  rw [h.2.2.2] at this
  have h1 := hcon 1 zero_le_one
  have : 0 < 1 / (σ ^ 2 / 2) := by positivity
  linarith

/-- The properties of a solution trapped in `[0, p]`. -/
lemma bellman_props (H : Hyp κ p σ θ0 C φ) (hβ : 0 < β) (h : Sol κ p σ φ β v v')
    (hbd : ∀ x, 0 ≤ x → 0 ≤ v x ∧ v x ≤ p) :
    StrictMonoOn v (Ici 0) ∧ Tendsto v atTop (𝓝 p) := by
  have hκ := H.hκ
  have hp := H.hp
  have hσ2 : 0 < σ ^ 2 / 2 := by have := H.hσ; positivity
  have hder : ∀ x, 0 ≤ x → 0 ≤ v' x := by
    intro x0 hx0
    by_contra hc
    push Not at hc
    have hvx0 : v x0 < p := by
      rcases lt_or_eq_of_le (hbd x0 hx0).2 with hl | he
      · exact hl
      · exfalso
        have hx0pos : 0 < x0 := by
          rcases eq_or_lt_of_le hx0 with h0 | h0
          · rw [← h0, h.2.2.2] at he; linarith
          · exact h0
        have hmax : IsLocalMax v x0 := by
          filter_upwards [Ici_mem_nhds hx0pos] with y hy
          rw [he]; exact (hbd y hy).2
        have := hmax.hasDerivAt_eq_zero (sol_hasDerivAt h hx0pos)
        linarith
    have hneg := neg_persist H h hx0 hvx0 hc
    have hanti : AntitoneOn v (Ici x0) := by
      apply sol_antitoneOn h (convex_Ici _) (fun y hy => hx0.trans hy)
      intro y hy
      rw [interior_Ici] at hy
      exact (hneg y hy.le).le
    obtain ⟨x, hx, hx'⟩ := eventually_neg H h hx0 hvx0
      (fun x hx => hanti (le_refl x0) hx hx)
    have := (hbd x (hx0.trans hx)).1
    linarith
  have hmono : MonotoneOn v (Ici 0) := by
    apply sol_monotoneOn h (convex_Ici _) (fun y hy => hy)
    intro y hy
    rw [interior_Ici] at hy
    exact hder y hy.le
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    rcases lt_or_eq_of_le (hmono ha hb hab.le) with hl | he
    · exact hl
    · exfalso
      have hconst : ∀ y ∈ Icc a b, v y = v a := by
        intro y hy
        have h1 := hmono ha (show (0:ℝ) ≤ y from le_trans ha hy.1) hy.1
        have h2 := hmono (show (0:ℝ) ≤ y from le_trans ha hy.1) hb hy.2
        linarith
      have hzero : ∀ y ∈ Ioo a b, v' y = 0 := by
        intro y hy
        have hy0 : 0 < y := lt_of_le_of_lt ha hy.1
        have h1 := sol_hasDerivAt h hy0
        have h2 : HasDerivAt v 0 y := by
          apply (hasDerivAt_const y (v a)).congr_of_eventuallyEq
          filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
          exact hconst z ⟨hz.1.le, hz.2.le⟩
        exact h1.unique h2
      set y1 := a + (b - a) / 3
      set y2 := a + 2 * (b - a) / 3
      have hy1 : y1 ∈ Ioo a b := ⟨by simp only [y1]; linarith, by simp only [y1]; linarith⟩
      have hy2 : y2 ∈ Ioo a b := ⟨by simp only [y2]; linarith, by simp only [y2]; linarith⟩
      have ha0 : (0:ℝ) ≤ a := ha
      have e1 := sol_eqn h (show 0 ≤ y1 from ha0.trans hy1.1.le)
      have e2 := sol_eqn h (show 0 ≤ y2 from ha0.trans hy2.1.le)
      rw [hzero y1 hy1, hconst y1 ⟨hy1.1.le, hy1.2.le⟩] at e1
      rw [hzero y2 hy2, hconst y2 ⟨hy2.1.le, hy2.2.le⟩] at e2
      have hw : (y2 - y1) * κ * (p - v a) = 0 := by linarith
      have hy12 : 0 < y2 - y1 := by simp only [y1, y2]; linarith
      have hw0 : p - v a = 0 := by
        rcases mul_eq_zero.1 hw with h' | h'
        · rcases mul_eq_zero.1 h' with h'' | h''
          · linarith
          · linarith
        · exact h'
      rw [hw0, mul_zero, H.zero] at e1
      linarith
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have : ∃ x0, 0 ≤ x0 ∧ p - ε < v x0 := by
      by_contra hc
      push Not at hc
      obtain ⟨x, hx, hx'⟩ := eventually_neg H h le_rfl (q := p - ε) (by linarith)
        (fun x hx => hc x hx)
      have := (hbd x hx).1
      linarith
    obtain ⟨x0, hx0, hx0'⟩ := this
    refine ⟨x0, fun x hx => ?_⟩
    have h1 := hmono hx0 (hx0.trans hx) hx
    have h2 := (hbd x (hx0.trans hx)).2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

theorem main_abstract (H : Hyp κ p σ θ0 C φ) :
    ∃ β, 0 < β ∧ ∃ v v' : ℝ → ℝ, Sol κ p σ φ β v v' ∧
      StrictMonoOn v (Ici 0) ∧ Tendsto v atTop (𝓝 p) := by
  choose S S' hS using fun β => exists_sol H β
  have hκ := H.hκ
  have hp := H.hp
  have hθ := H.hθ0
  set U1 : Set ℝ := {β | ∃ x, 0 ≤ x ∧ S β x < 0} with hU1
  set U2 : Set ℝ := {β | ∃ x, 0 ≤ x ∧ p < S β x} with hU2
  have hU1o : IsOpen U1 := by
    rw [isOpen_iff_forall_mem_open]
    rintro β ⟨x, hx, hx'⟩
    refine ⟨(fun b => S b x) ⁻¹' Iio 0, fun b hb => ⟨x, hx, hb⟩,
      (sol_cont H S S' hS hx).isOpen_preimage _ isOpen_Iio, hx'⟩
  have hU2o : IsOpen U2 := by
    rw [isOpen_iff_forall_mem_open]
    rintro β ⟨x, hx, hx'⟩
    refine ⟨(fun b => S b x) ⁻¹' Ioi p, fun b hb => ⟨x, hx, hb⟩,
      (sol_cont H S S' hS hx).isOpen_preimage _ isOpen_Ioi, hx'⟩
  have h0 : (0 : ℝ) ∈ U1 := zero_goes_neg H (hS 0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU1o 0 h0
  have hne1 : (Ioi (0 : ℝ) ∩ U1).Nonempty := by
    refine ⟨r / 2, by show (0:ℝ) < r / 2; positivity, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  set βb := (κ - θ0) * p + σ ^ 2 / 2 * p + 1 with hβb
  have hβbpos : 0 < βb := by
    have : 0 ≤ σ ^ 2 / 2 * p := by positivity
    have : 0 < (κ - θ0) * p := mul_pos (by linarith) hp
    linarith
  have hne2 : (Ioi (0 : ℝ) ∩ U2).Nonempty :=
    ⟨βb, hβbpos, big_goes_above H (hS βb) rfl⟩
  have : ∃ β ∈ Ioi (0 : ℝ), β ∉ U1 ∪ U2 := by
    by_contra hc
    push Not at hc
    obtain ⟨β, hβ, ⟨x1, hx1, hx1'⟩, ⟨x2, hx2, hx2'⟩⟩ :=
      isPreconnected_Ioi U1 U2 hU1o hU2o (fun b hb => hc b hb) hne1 hne2
    exact disjoint H hβ (hS β) hx1 hx1' hx2 hx2'
  obtain ⟨β, hβ, hβU⟩ := this
  have hbd : ∀ x, 0 ≤ x → 0 ≤ S β x ∧ S β x ≤ p := by
    intro x hx
    constructor
    · by_contra hc
      push Not at hc
      exact hβU (Or.inl ⟨x, hx, hc⟩)
    · by_contra hc
      push Not at hc
      exact hβU (Or.inr ⟨x, hx, hc⟩)
  exact ⟨β, hβ, S β, S' β, hS β, bellman_props H hβ (hS β) hbd⟩

end

end VolBellSol

open VolunteerEngage.Bellman in
theorem solution (M : Model) (hM : M.Standing) :
    ∃ β : ℝ, 0 < β ∧ ∃ v v' : ℝ → ℝ, IsBellmanSol M β v v' := by
  have H : VolBellSol.Hyp M.κ M.p M.σ M.θ0 (VolBellSol.CL M) (phi M) :=
    { hκ := hM.2.2.2.2.2.2.2.1
      hp := hM.2.2.2.2.2.2.1
      hσ := hM.2.2.2.2.2.2.2.2
      hθ0 := hM.2.1
      hC := VolBellSol.CL_nonneg M
      lip := VolBellSol.phi_lip M hM
      zero := VolBellSol.phi_zero M hM
      ge := VolBellSol.phi_ge M hM
      cont := VolBellSol.phi_continuous M hM }
  obtain ⟨β, hβ, v, v', hs, hm, ht⟩ := VolBellSol.main_abstract H
  exact ⟨β, hβ, v, v', hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hm, ht⟩
