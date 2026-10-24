-- Prove2me | solution 1 for VolunteerEngage.Bellman.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:37:20.762994+00:00
-- url     : https://prove2.me/submissions/55bb2855-f316-4e61-b29c-fbe65844a17f

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

namespace VolBellSol

section

variable {κ p σ θ0 C : ℝ} {φ : ℝ → ℝ} {β : ℝ} {v v' : ℝ → ℝ}

lemma sol_unique (H : Hyp κ p σ θ0 C φ) {v₁ v₁' v₂ v₂' : ℝ → ℝ}
    (h₁ : Sol κ p σ φ β v₁ v₁') (h₂ : Sol κ p σ φ β v₂ v₂') {x : ℝ} (hx : 0 ≤ x) :
    v₁ x = v₂ x := by
  have := sol_gron H h₁ h₂ hx
  rw [sub_self, abs_zero, mul_zero, gronwallBound_ε0_δ0] at this
  exact dist_le_zero.1 this

lemma sol_deriv_unique (H : Hyp κ p σ θ0 C φ) {v₁ v₁' v₂ v₂' : ℝ → ℝ}
    (h₁ : Sol κ p σ φ β v₁ v₁') (h₂ : Sol κ p σ φ β v₂ v₂') {x : ℝ} (hx : 0 ≤ x) :
    v₁' x = v₂' x := by
  rw [sol_deriv_eq H h₁ hx, sol_deriv_eq H h₂ hx, sol_unique H h₁ h₂ hx]

lemma deriv_ge_of_ge_p (H : Hyp κ p σ θ0 C φ) (h : Sol κ p σ φ β v v') {x : ℝ} (hx : 0 ≤ x)
    (hv : p ≤ v x) : β ≤ σ ^ 2 / 2 * v' x := by
  have e := sol_eqn h hx
  have h1 := H.ge (p - v x)
  have hθ := H.hθ0
  have hκ := H.hκ
  have : 0 ≤ θ0 * (p - v x) := mul_nonneg_of_nonpos_of_nonpos hθ.le (by linarith)
  have hxκ : 0 ≤ x * κ := by positivity
  have : x * κ * (p - v x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hxκ (by linarith)
  linarith

lemma deriv_pos_of_ge_p (H : Hyp κ p σ θ0 C φ) (hβ : 0 < β) (h : Sol κ p σ φ β v v') {x : ℝ}
    (hx : 0 ≤ x) (hv : p ≤ v x) : 0 < v' x := by
  have := deriv_ge_of_ge_p H h hx hv
  have hσ2 : 0 < σ ^ 2 / 2 := by have := H.hσ; positivity
  by_contra hc
  push Not at hc
  nlinarith

lemma lt_p_of_deriv_neg (H : Hyp κ p σ θ0 C φ) (hβ : 0 < β) (h : Sol κ p σ φ β v v') {x : ℝ}
    (hx : 0 ≤ x) (hd : v' x < 0) : v x < p := by
  by_contra hc
  push Not at hc
  have := deriv_pos_of_ge_p H hβ h hx hc
  linarith

/-- No interval of constancy when `β ≠ 0`. -/
lemma const_false (H : Hyp κ p σ θ0 C φ) (hβ : β ≠ 0) (h : Sol κ p σ φ β v v') {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hconst : ∀ y ∈ Icc a b, v y = v a) : False := by
  have hκ := H.hκ
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
  have e1 := sol_eqn h (show 0 ≤ y1 from ha.trans hy1.1.le)
  have e2 := sol_eqn h (show 0 ≤ y2 from ha.trans hy2.1.le)
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
  exact hβ (by linarith)

lemma strictMono_of_deriv_nonneg (H : Hyp κ p σ θ0 C φ) (hβ : β ≠ 0) (h : Sol κ p σ φ β v v')
    (hnn : ∀ x, 0 < x → 0 ≤ v' x) : StrictMonoOn v (Ici 0) := by
  have hmono : MonotoneOn v (Ici 0) := by
    apply sol_monotoneOn h (convex_Ici _) (fun y hy => hy)
    intro y hy
    rw [interior_Ici] at hy
    exact hnn y hy
  intro a ha b hb hab
  rcases lt_or_eq_of_le (hmono ha hb hab.le) with hl | he
  · exact hl
  · exfalso
    apply const_false H hβ h ha hab
    intro y hy
    have h1 := hmono ha (show (0:ℝ) ≤ y from le_trans ha hy.1) hy.1
    have h2 := hmono (show (0:ℝ) ≤ y from le_trans ha hy.1) hb hy.2
    linarith

/-- Once `v' < 0`, `v → -∞`. -/
lemma atBot_of_neg_deriv (H : Hyp κ p σ θ0 C φ) (hβ : 0 < β) (h : Sol κ p σ φ β v v') {x0 : ℝ}
    (hx0 : 0 ≤ x0) (hd : v' x0 < 0) : Tendsto v atTop atBot := by
  have hκ := H.hκ
  have hC := H.hC
  have hσ2 : 0 < σ ^ 2 / 2 := by have := H.hσ; positivity
  have hvp := lt_p_of_deriv_neg H hβ h hx0 hd
  have hneg := neg_persist H h hx0 hvp hd
  have hanti : AntitoneOn v (Ici x0) := by
    apply sol_antitoneOn h (convex_Ici _) (fun y hy => hx0.trans hy)
    intro y hy
    rw [interior_Ici] at hy
    exact (hneg y hy.le).le
  set m := p - v x0 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  set X := max x0 ((β + 1 + C * m) / (κ * m)) with hX
  have hXa : x0 ≤ X := le_max_left _ _
  have hXb : (β + 1 + C * m) / (κ * m) ≤ X := le_max_right _ _
  have hX0 : 0 ≤ X := hx0.trans hXa
  have hgrad : ∀ y ∈ Ici X, v' y ≤ -1 / (σ ^ 2 / 2) := by
    intro y hy
    have hy0 : 0 ≤ y := hX0.trans hy
    have hxy : x0 ≤ y := hXa.trans hy
    have hw : m ≤ p - v y := by
      have := hanti (le_refl x0) hxy hxy
      rw [hm]; linarith
    have hwpos : 0 < p - v y := lt_of_lt_of_le hm0 hw
    have hφ : φ (p - v y) ≤ C * (p - v y) := by
      have := H.lip (p - v y) 0
      rw [H.zero, sub_zero, sub_zero, abs_of_pos hwpos] at this
      exact (le_abs_self _).trans this
    have hyκ : β + 1 + C * m ≤ y * κ * m := by
      have := hXb.trans hy
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have hpos : 0 < y * κ - C := by
      have : 0 < (y * κ - C) * m := by nlinarith
      exact pos_of_mul_pos_left this hm0.le
    have h3 : (y * κ - C) * m ≤ (y * κ - C) * (p - v y) :=
      mul_le_mul_of_nonneg_left hw hpos.le
    have e := sol_eqn h hy0
    have : σ ^ 2 / 2 * v' y ≤ -1 := by nlinarith
    rw [le_div_iff₀ hσ2]
    linarith
  rw [tendsto_atTop_atBot]
  intro b
  refine ⟨X + σ ^ 2 / 2 * (|b| + |v X|), fun x hx => ?_⟩
  have hXx : X ≤ x := by
    have : 0 ≤ σ ^ 2 / 2 * (|b| + |v X|) := by positivity
    linarith
  have := sol_le_lin h hX0 hXx (fun y hy => hgrad y hy.1)
  have e : -1 / (σ ^ 2 / 2) * (x - X) ≤ -(|b| + |v X|) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hσ2]
    nlinarith
  have := le_abs_self b
  have := neg_abs_le b
  have := le_abs_self (v X)
  linarith

/-- Comparison: `v_β` is strictly increasing in `β` for `x > 0`. -/
lemma mono_beta (H : Hyp κ p σ θ0 C φ) {β₁ β₂ : ℝ} (hb : β₁ < β₂) {v₁ v₁' v₂ v₂' : ℝ → ℝ}
    (h₁ : Sol κ p σ φ β₁ v₁ v₁') (h₂ : Sol κ p σ φ β₂ v₂ v₂') {x : ℝ} (hx : 0 < x) :
    v₁ x < v₂ x := by
  have hκ := H.hκ
  have hC := H.hC
  have ha : 0 < 2 / σ ^ 2 := by have := H.hσ; positivity
  set K := 2 / σ ^ 2 * (x * κ + C) with hK
  have hK0 : 0 ≤ K := by positivity
  set δ := 2 / σ ^ 2 * (β₂ - β₁) / (2 * (1 + K * x)) with hδ
  have hδ0 : 0 < δ := by
    have : 0 < 2 / σ ^ 2 * (β₂ - β₁) := mul_pos ha (by linarith)
    positivity
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := v₁) (f' := v₁') (a := 0) (b := x)
    (sol_contOn h₁ (fun y hy => hy.1)) (fun y hy => sol_right h₁ hy.1)
    (B := fun y => v₂ y - δ * y) (B' := fun y => v₂' y - δ)
    (by simp [h₁.2.2.2, h₂.2.2.2])
    ((sol_contOn h₂ (fun y hy => hy.1)).sub (continuousOn_const.mul continuousOn_id))
    (fun y hy => ((sol_right h₂ hy.1).sub
        (((hasDerivAt_id y).const_mul δ).hasDerivWithinAt)).congr_deriv (by simp))
    (fun y hy hyB => by
      change v₁ y = v₂ y - δ * y at hyB
      show v₁' y < v₂' y - δ
      rw [sol_deriv_eq H h₁ hy.1, sol_deriv_eq H h₂ hy.1]
      have hl := F_lip H β₁ hy.1 hy.2.le (v₂ y) (v₁ y)
      have hdiff : v₂ y - v₁ y = δ * y := by linarith
      rw [hdiff, abs_of_nonneg (mul_nonneg hδ0.le hy.1 : (0:ℝ) ≤ δ * y)] at hl
      have e : F κ p σ φ β₂ y (v₂ y) = F κ p σ φ β₁ y (v₂ y) + 2 / σ ^ 2 * (β₂ - β₁) := by
        unfold F; ring
      rw [e]
      have h4 : K * (δ * y) ≤ K * (δ * x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy.2.le hδ0.le) hK0
      have h5 : δ * (1 + K * x) = 2 / σ ^ 2 * (β₂ - β₁) / 2 := by
        rw [hδ]; field_simp
      have h6 : 0 < 2 / σ ^ 2 * (β₂ - β₁) := mul_pos ha (by linarith)
      have := (le_abs_self (F κ p σ φ β₁ y (v₂ y) - F κ p σ φ β₁ y (v₁ y))).trans hl
      have := neg_abs_le (F κ p σ φ β₁ y (v₂ y) - F κ p σ φ β₁ y (v₁ y))
      have := hl
      nlinarith [abs_nonneg (F κ p σ φ β₁ y (v₂ y) - F κ p σ φ β₁ y (v₁ y)),
        neg_abs_le (F κ p σ φ β₁ y (v₂ y) - F κ p σ φ β₁ y (v₁ y))])
    (x := x) ⟨hx.le, le_rfl⟩
  change v₁ x ≤ v₂ x - δ * x at key
  have : 0 < δ * x := mul_pos hδ0 hx
  linarith

/-- Lemma 10 (←): a negative slope yields the increase-then-decrease structure. -/
lemma dec_structure (H : Hyp κ p σ θ0 C φ) (hβ : 0 < β) (h : Sol κ p σ φ β v v') {x0 : ℝ}
    (hx0 : 0 ≤ x0) (hd : v' x0 < 0) :
    ∃ xβ : ℝ, MonotoneOn v (Ioo 0 xβ) ∧ AntitoneOn v (Ioi xβ) := by
  set T : Set ℝ := {x | 0 ≤ x ∧ v' x < 0} with hTdef
  have hT : ∀ x ∈ T, ∀ y, x ≤ y → v' y < 0 := by
    intro x hx y hy
    exact neg_persist H h hx.1 (lt_p_of_deriv_neg H hβ h hx.1 hx.2) hx.2 y hy
  have hbdd : BddBelow T := ⟨0, fun x hx => hx.1⟩
  have hne : T.Nonempty := ⟨x0, hx0, hd⟩
  set xβ := sInf T with hxβ
  have hxβ0 : 0 ≤ xβ := le_csInf hne (fun x hx => hx.1)
  refine ⟨xβ, ?_, ?_⟩
  · apply sol_monotoneOn h (convex_Ioo _ _) (fun y hy => hy.1.le)
    intro y hy
    rw [interior_Ioo] at hy
    by_contra hc
    push Not at hc
    have : xβ ≤ y := csInf_le hbdd ⟨hy.1.le, hc⟩
    linarith [hy.2]
  · apply sol_antitoneOn h (convex_Ioi _) (fun y hy => (hxβ0.trans (le_of_lt hy)))
    intro y hy
    rw [isOpen_Ioi.interior_eq] at hy
    obtain ⟨t, ht, hty⟩ := exists_lt_of_csInf_lt hne hy
    exact (hT t ht y hty.le).le

/-- Lemma 10 (→). -/
lemma not_dec_of_nonneg (H : Hyp κ p σ θ0 C φ) (hβ : β ≠ 0) (h : Sol κ p σ φ β v v') {xβ : ℝ}
    (hanti : AntitoneOn v (Ioi xβ)) (hnn : ∀ x, 0 < x → 0 ≤ v' x) : False := by
  have hmono : MonotoneOn v (Ici 0) := by
    apply sol_monotoneOn h (convex_Ici _) (fun y hy => hy)
    intro y hy
    rw [interior_Ici] at hy
    exact hnn y hy
  set m := max xβ 0 + 1 with hm
  have hm0 : 0 ≤ m := by have := le_max_right xβ 0; linarith
  have hmx : xβ < m := by have := le_max_left xβ 0; linarith
  apply const_false H hβ h (a := m) (b := m + 1) hm0 (by linarith)
  intro y hy
  have h1 := hmono (show (0:ℝ) ≤ m from hm0) (show (0:ℝ) ≤ y by linarith [hy.1]) hy.1
  have h2 := hanti (show xβ < m from hmx) (show xβ < y by linarith [hy.1]) hy.1
  linarith

/-- Lemma 14 (←): reaching `p` forces increase and unboundedness. -/
lemma above_p_props (H : Hyp κ p σ θ0 C φ) (hβ : 0 < β) (h : Sol κ p σ φ β v v') {xb : ℝ}
    (hxb : 0 ≤ xb) (hv : p ≤ v xb) :
    StrictMonoOn v (Ici 0) ∧ ¬ BddAbove (v '' Ici 0) := by
  have hσ2 : 0 < σ ^ 2 / 2 := by have := H.hσ; positivity
  have htrap := trap_above H hβ h hxb hv
  refine ⟨strictMono_of_deriv_nonneg H hβ.ne' h (fun x hx => ?_), ?_⟩
  · by_contra hc
    push Not at hc
    have := atBot_of_neg_deriv H hβ h hx.le hc
    obtain ⟨i, hi⟩ := tendsto_atTop_atBot.1 this (p - 1)
    have h1 := hi (max i xb) (le_max_left _ _)
    have h2 := htrap (max i xb) (le_max_right _ _)
    linarith
  · rintro ⟨Mb, hMb⟩
    have hgrad : ∀ y ∈ Ico xb (xb + (|Mb| + 1) * (σ ^ 2 / 2) / β), β / (σ ^ 2 / 2) ≤ v' y := by
      intro y hy
      have := deriv_ge_of_ge_p H h (hxb.trans hy.1) (htrap y hy.1)
      rw [div_le_iff₀ hσ2]
      linarith
    have hT : 0 ≤ (|Mb| + 1) * (σ ^ 2 / 2) / β := by positivity
    have := sol_ge_lin h hxb (by linarith) hgrad
    have e : β / (σ ^ 2 / 2) * (xb + (|Mb| + 1) * (σ ^ 2 / 2) / β - xb) = |Mb| + 1 := by
      have := H.hσ.ne'
      have := hβ.ne'
      field_simp
      ring
    rw [e] at this
    have h3 := hMb (mem_image_of_mem v (show xb + (|Mb| + 1) * (σ ^ 2 / 2) / β ∈ Ici (0:ℝ) by
      show (0:ℝ) ≤ _; linarith))
    have := le_abs_self Mb
    have := H.hp
    linarith

/-- Lemma 13 (D ≠ ∅), abstract core: at `β̲ = -φ(y*)` the solution becomes negative. -/
lemma low_goes_neg (H : Hyp κ p σ θ0 C φ) {ys : ℝ} (hys0 : 0 < ys) (hysp : ys ≤ p)
    (hmin : ∀ y ≤ p, φ ys ≤ φ y) (hneg : φ ys < 0) (h : Sol κ p σ φ (-φ ys) v v') :
    ∃ x, 0 ≤ x ∧ v x < 0 := by
  have hβ : 0 < -φ ys := by linarith
  have hκ := H.hκ
  have hC := H.hC
  have hp := H.hp
  have hσ2 : 0 < σ ^ 2 / 2 := by have := H.hσ; positivity
  by_contra hcon
  push Not at hcon
  have hnd : ∀ x0, 0 ≤ x0 → ¬ v' x0 < 0 := by
    intro x0 hx0 hd
    have := atBot_of_neg_deriv H hβ h hx0 hd
    obtain ⟨i, hi⟩ := tendsto_atTop_atBot.1 this (-1)
    have h1 := hcon (max i 0) (le_max_right _ _)
    have h2 := hi (max i 0) (le_max_left _ _)
    linarith
  have hA : ∀ x, 0 < x → p - v x = ys → False := by
    intro x hx he
    apply hnd x hx.le
    have e := sol_eqn h hx.le
    rw [he] at e
    have : σ ^ 2 / 2 * v' x < 0 := by
      rw [e]; have := mul_pos (mul_pos hx hκ) hys0; linarith
    by_contra hc
    push Not at hc
    have := mul_nonneg hσ2.le hc
    linarith
  have hcw : ContinuousOn (fun x => p - v x) (Ici 0) :=
    continuousOn_const.sub (sol_contOn h (subset_refl _))
  have hivt : ∀ x, 0 < x → ∀ c, c ∈ uIcc (p - v x) (p - v 1) → ∃ z, 0 < z ∧ p - v z = c := by
    intro x hx c hc
    have hsub : uIcc x 1 ⊆ Ici 0 := by
      intro z hz
      have := (mem_uIcc.1 hz)
      show (0:ℝ) ≤ z
      rcases this with h' | h' <;> linarith [h'.1]
    obtain ⟨z, hz, hz'⟩ := intermediate_value_uIcc (hcw.mono hsub) hc
    refine ⟨z, ?_, hz'⟩
    rcases mem_uIcc.1 hz with h' | h'
    · linarith [h'.1]
    · linarith [h'.1]
  rcases lt_trichotomy (p - v 1) ys with h1 | h1 | h1
  · have hall : ∀ x, 0 < x → p - v x < ys := by
      intro x hx
      by_contra hc
      push Not at hc
      obtain ⟨z, hz, hz'⟩ := hivt x hx ys (mem_uIcc.2 (Or.inr ⟨h1.le, hc⟩))
      exact hA z hz hz'
    have hyseq : ys = p := by
      by_contra hne
      have hlt : ys < p := lt_of_le_of_ne hysp hne
      have hc0 := (h.2.1 0 (self_mem_Ici)).continuousWithinAt
      rw [Metric.continuousWithinAt_iff] at hc0
      obtain ⟨δ, hδ, hδ'⟩ := hc0 (p - ys) (by linarith)
      have h2 := hδ' (show δ / 2 ∈ Ici (0:ℝ) by show (0:ℝ) ≤ δ / 2; positivity)
        (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
      rw [Real.dist_eq, h.2.2.2, sub_zero] at h2
      have h3 := hall (δ / 2) (by positivity)
      have := le_abs_self (v (δ / 2))
      linarith
    have hc1 := (h.2.1 0 (self_mem_Ici)).continuousWithinAt
    rw [Metric.continuousWithinAt_iff] at hc1
    obtain ⟨δ1, hδ1, hδ1'⟩ := hc1 p hp
    set x1 := δ1 / 2 with hx1
    have hx1pos : 0 < x1 := by positivity
    have hsmall : ∀ x ∈ Icc (0:ℝ) x1, v x < p := by
      intro x hx
      have := hδ1' (show x ∈ Ici (0:ℝ) from hx.1)
        (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]; linarith [hx.2])
      rw [Real.dist_eq, h.2.2.2, sub_zero] at this
      exact lt_of_le_of_lt (le_abs_self _) this
    set a := C / (σ ^ 2 / 2) with ha
    have hanti := strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc (0:ℝ) x1)
      (f := fun x => v x * Real.exp (-(a * x)))
      (f' := fun x => (v' x - a * v x) * Real.exp (-(a * x)))
      (by
        have := sol_contOn h (D := Icc 0 x1) (fun y hy => hy.1)
        fun_prop)
      (fun x hx => by
        rw [interior_Icc] at hx
        have hexp : HasDerivAt (fun y => Real.exp (-(a * y))) (Real.exp (-(a * x)) * (-a)) x := by
          simpa using ((hasDerivAt_id x).const_mul a).neg.exp
        exact ((sol_hasDerivAt h hx.1).mul hexp).hasDerivWithinAt.congr_deriv (by ring))
      (fun x hx => by
        rw [interior_Icc] at hx
        have he := Real.exp_pos (-(a * x))
        apply mul_neg_of_neg_of_pos _ he
        have e := sol_eqn h hx.1.le
        have hw : 0 < p - v x := by have := hsmall x ⟨hx.1.le, hx.2.le⟩; linarith
        have hvx := hcon x hx.1.le
        have hl := H.lip (p - v x) p
        have e2 : p - v x - p = -v x := by ring
        rw [e2, abs_neg, abs_of_nonneg hvx] at hl
        have hl' := (le_abs_self _).trans hl
        rw [hyseq] at e
        have : 0 < x * κ * (p - v x) := by
          have := mul_pos hx.1 hκ
          exact mul_pos this (by linarith)
        have h5 : σ ^ 2 / 2 * v' x < C * v x := by linarith
        have h6 : σ ^ 2 / 2 * (a * v x) = C * v x := by
          have := H.hσ.ne'
          rw [ha]; field_simp
        nlinarith)
    have := hanti (show (0:ℝ) ∈ Icc (0:ℝ) x1 from ⟨le_rfl, hx1pos.le⟩)
      (show x1 ∈ Icc (0:ℝ) x1 from ⟨hx1pos.le, le_rfl⟩) hx1pos
    simp only [h.2.2.2, zero_mul, mul_zero, neg_zero, Real.exp_zero] at this
    have h1' := hcon x1 hx1pos.le
    have := Real.exp_pos (-(a * x1))
    nlinarith
  · exact hA 1 one_pos h1
  · have hall : ∀ x, 0 < x → ys < p - v x := by
      intro x hx
      by_contra hc
      push Not at hc
      obtain ⟨z, hz, hz'⟩ := hivt x hx ys (mem_uIcc.2 (Or.inl ⟨hc, h1.le⟩))
      exact hA z hz hz'
    set X := (C * p + 1) / (κ * ys) with hX
    have hX0 : 0 < X := by positivity
    apply hnd X hX0.le
    have e := sol_eqn h hX0.le
    have hw := hall X hX0
    have hvX := hcon X hX0.le
    have hl := H.lip (p - v X) ys
    have hab : |p - v X - ys| ≤ p := by
      rw [abs_of_pos (by linarith)]; linarith
    have hl' : φ (p - v X) - φ ys ≤ C * p :=
      (le_abs_self _).trans (hl.trans (mul_le_mul_of_nonneg_left hab hC))
    have hXκ : X * κ * ys = C * p + 1 := by rw [hX]; field_simp
    have h7 : X * κ * ys ≤ X * κ * (p - v X) :=
      mul_le_mul_of_nonneg_left hw.le (by positivity)
    have : σ ^ 2 / 2 * v' X < 0 := by linarith
    by_contra hc
    push Not at hc
    have := mul_nonneg hσ2.le hc
    linarith

end

end VolBellSol

namespace VolBellSol

section

variable {κ p σ θ0 C : ℝ} {φ : ℝ → ℝ}

lemma sol_cont' (H : Hyp κ p σ θ0 C φ) {β : ℝ} {v v' : ℝ → ℝ} (h : Sol κ p σ φ β v v')
    {x : ℝ} (hx : 0 ≤ x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ β' : ℝ, |β' - β| < δ → ∀ w w' : ℝ → ℝ, Sol κ p σ φ β' w w' →
      |w x - v x| < ε := by
  have ha : 0 < 2 / σ ^ 2 := by have := H.hσ; positivity
  set K := 2 / σ ^ 2 * (x * κ + C)
  have hg := gronwallBound_continuous_ε 0 K x
  rw [Metric.continuous_iff] at hg
  obtain ⟨ρ, hρ, hρ'⟩ := hg 0 ε hε
  refine ⟨ρ / (2 / σ ^ 2), div_pos hρ ha, fun β' hβ' w w' hw => ?_⟩
  have h1 := sol_gron H hw h hx
  have h2 := hρ' (2 / σ ^ 2 * |β' - β|) (by
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos ha, abs_abs]
    rwa [lt_div_iff₀ ha, mul_comm] at hβ')
  rw [gronwallBound_ε0_δ0, Real.dist_eq, sub_zero] at h2
  rw [← Real.dist_eq]
  exact lt_of_le_of_lt h1 (lt_of_le_of_lt (le_abs_self _) h2)

end

open VolunteerEngage.Bellman

variable (M : Model)

lemma theta_zero : M.θ 0 = M.θ0 := by simp [Model.θ]

lemma c_ge_c1 (hM : M.Standing) : ∀ l, 1 ≤ l → l ≤ M.L → M.c 1 ≤ M.c l := by
  intro l h1 h2
  induction l with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; exact le_rfl
    · have := ih hk (by omega)
      have := hM.2.2.2.2.1 k (by rw [Finset.mem_Ico]; omega)
      linarith

lemma telescope (hM : M.Standing) (x : ℝ) : ∀ n, n ≤ M.L →
    ∑ l ∈ Finset.Icc 1 n, (min (M.θ l) (max (M.θ (l - 1)) x) - M.θ (l - 1)) =
      min (M.θ n) (max M.θ0 x) - M.θ0 := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [theta_zero]
  | succ k ih =>
    intro hk
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
    simp only [Nat.add_sub_cancel]
    have h1 := theta0_le M hM k (by omega)
    have h2 := theta_pred_le M hM (k + 1) (by rw [Finset.mem_Icc]; omega)
    simp only [Nat.add_sub_cancel] at h2
    simp only [min_def, max_def]
    split_ifs <;> linarith

lemma cost_ge (hM : M.Standing) {x : ℝ} (hx : x ∈ Icc M.θ0 (M.θ M.L)) :
    M.c 1 * (x - M.θ0) ≤ cost M x := by
  have ht := telescope M hM x M.L le_rfl
  rw [max_eq_right hx.1, min_eq_right hx.2] at ht
  unfold cost
  rw [← ht, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hc := c_ge_c1 M hM l (Finset.mem_Icc.1 hl).1 (Finset.mem_Icc.1 hl).2
  have := theta_pred_le M hM l hl
  have : 0 ≤ min (M.θ l) (max (M.θ (l - 1)) x) - M.θ (l - 1) := by
    have : M.θ (l - 1) ≤ min (M.θ l) (max (M.θ (l - 1)) x) := le_min this (le_max_left _ _)
    linarith
  exact mul_le_mul_of_nonneg_right hc this

lemma phi_neg_witness (hM : M.Standing) : phi M (min (M.c 1) M.p) < 0 := by
  have hc1 := hM.2.2.2.1
  have hp := hM.2.2.2.2.2.2.1
  have hθ := hM.2.1
  set y0 := min (M.c 1) M.p with hy0
  have hy0pos : 0 < y0 := lt_min hc1 hp
  have hy0c : y0 ≤ M.c 1 := min_le_left _ _
  have : phi M y0 ≤ y0 * M.θ0 := by
    apply phi_le M hM
    intro x hx
    have := cost_ge M hM hx
    have h1 : (y0 - M.c 1) * (x - M.θ0) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hx.1])
    nlinarith
  have : y0 * M.θ0 < 0 := mul_neg_of_pos_of_neg hy0pos hθ
  linarith

lemma phi_ge_Iic (hM : M.Standing) {y : ℝ} (hy : y ≤ M.p) : M.θ0 * M.p ≤ phi M y := by
  have := phi_ge M hM y
  have hθ := hM.2.1
  nlinarith

lemma exists_min (hM : M.Standing) : ∃ ys, 0 < ys ∧ ys ≤ M.p ∧ (∀ y ≤ M.p, phi M ys ≤ phi M y) ∧
    phi M ys < 0 ∧ betaLow M = -phi M ys := by
  have hp := hM.2.2.2.2.2.2.1
  have hθ := hM.2.1
  obtain ⟨ys, hys, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hp.le)
    (phi_continuous M hM).continuousOn
  have hneg : phi M ys < 0 := lt_of_le_of_lt (hmin ⟨(lt_min hM.2.2.2.1 hp).le, min_le_right _ _⟩)
    (phi_neg_witness M hM)
  have hall : ∀ y ≤ M.p, phi M ys ≤ phi M y := by
    intro y hy
    rcases le_or_gt 0 y with h0 | h0
    · exact hmin ⟨h0, hy⟩
    · have := phi_ge M hM y
      have : 0 < M.θ0 * y := mul_pos_of_neg_of_neg hθ h0
      linarith
  have hys0 : 0 < ys := by
    rcases eq_or_lt_of_le hys.1 with he | he
    · rw [← he, phi_zero M hM] at hneg; linarith
    · exact he
  refine ⟨ys, hys0, hys.2, hall, hneg, ?_⟩
  unfold betaLow
  have : IsLeast (phi M '' Iic M.p) (phi M ys) :=
    ⟨mem_image_of_mem _ (show ys ∈ Iic M.p from hys.2), by
      rintro _ ⟨y, hy, rfl⟩; exact hall y hy⟩
  rw [this.csInf_eq]

lemma betaLow_pos' (hM : M.Standing) : 0 < betaLow M := by
  obtain ⟨ys, _, _, _, hneg, he⟩ := exists_min M hM
  rw [he]; linarith

lemma betaLow_le (hM : M.Standing) : betaLow M ≤ -(M.θ0 * M.p) := by
  obtain ⟨ys, _, hys, _, _, he⟩ := exists_min M hM
  rw [he]
  have := phi_ge_Iic M hM hys
  linarith

lemma hypM (hM : M.Standing) : Hyp M.κ M.p M.σ M.θ0 (CL M) (phi M) :=
  { hκ := hM.2.2.2.2.2.2.2.1
    hp := hM.2.2.2.2.2.2.1
    hσ := hM.2.2.2.2.2.2.2.2
    hθ0 := hM.2.1
    hC := CL_nonneg M
    lip := phi_lip M hM
    zero := phi_zero M hM
    ge := phi_ge M hM
    cont := phi_continuous M hM }

/-- β ∈ D iff the solution goes negative (for β > β̲). -/
lemma D_iff_neg_slope (hM : M.Standing) {β : ℝ} (hβ : betaLow M < β) {v v' : ℝ → ℝ}
    (hv : IsIVPSol M β v v') : β ∈ Dset M ↔ ∃ x₀ : ℝ, 0 < x₀ ∧ v' x₀ < 0 := by
  have H := hypM M hM
  have hβ0 : 0 < β := (betaLow_pos' M hM).trans hβ
  have hv' : Sol M.κ M.p M.σ (phi M) β v v' := hv
  constructor
  · rintro ⟨_, u, u', hu, xβ, _, hanti⟩
    have hu' : Sol M.κ M.p M.σ (phi M) β u u' := hu
    by_contra hc
    push Not at hc
    apply not_dec_of_nonneg H hβ0.ne' hv' (xβ := max xβ 0) _ hc
    intro a ha b hb hab
    have ha0 : 0 ≤ a := (le_max_right _ _).trans (le_of_lt ha)
    have hb0 : 0 ≤ b := (le_max_right _ _).trans (le_of_lt hb)
    rw [← sol_unique H hu' hv' ha0, ← sol_unique H hu' hv' hb0]
    exact hanti (show xβ < a from lt_of_le_of_lt (le_max_left _ _) ha)
      (show xβ < b from lt_of_le_of_lt (le_max_left _ _) hb) hab
  · rintro ⟨x0, hx0, hd⟩
    obtain ⟨xβ, h1, h2⟩ := dec_structure H hβ0 hv' hx0.le hd
    exact ⟨hβ, v, v', hv, xβ, h1, h2⟩

lemma neg_slope_iff_neg_value (hM : M.Standing) {β : ℝ} (hβ : betaLow M < β) {v v' : ℝ → ℝ}
    (hv : IsIVPSol M β v v') : (∃ x₀ : ℝ, 0 < x₀ ∧ v' x₀ < 0) ↔ ∃ x : ℝ, 0 < x ∧ v x < 0 := by
  have H := hypM M hM
  have hβ0 : 0 < β := (betaLow_pos' M hM).trans hβ
  have hv' : Sol M.κ M.p M.σ (phi M) β v v' := hv
  constructor
  · rintro ⟨x0, hx0, hd⟩
    have := atBot_of_neg_deriv H hβ0 hv' hx0.le hd
    obtain ⟨i, hi⟩ := tendsto_atTop_atBot.1 this (-1)
    exact ⟨max i 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      lt_of_le_of_lt (hi _ (le_max_left _ _)) (by norm_num)⟩
  · rintro ⟨x, hx, hvx⟩
    obtain ⟨x0, hx0, hx0'⟩ := exists_hasDerivAt_eq_slope v v' hx
      (sol_contOn hv' (fun y hy => hy.1)) (fun y hy => sol_hasDerivAt hv' hy.1)
    rw [hv'.2.2.2, sub_zero, sub_zero] at hx0'
    exact ⟨x0, hx0.1, by rw [hx0']; exact div_neg_of_neg_of_pos hvx hx⟩

lemma I_D_disjoint (hM : M.Standing) {β : ℝ} (hI : β ∈ Iset M) (hD : β ∈ Dset M) : False := by
  obtain ⟨hβ, u, u', hu, hmono⟩ := hI
  obtain ⟨x, hx, hux⟩ := (neg_slope_iff_neg_value M hM hβ hu).1 ((D_iff_neg_slope M hM hβ hu).1 hD)
  have := hmono ((self_mem_Ici : (0:ℝ) ∈ Ici 0)) (show x ∈ Ici (0:ℝ) from hx.le) hx
  rw [show u 0 = 0 from hu.2.2.2] at this
  linarith

lemma I_of_not_D (hM : M.Standing) {β : ℝ} (hβ : betaLow M < β) {v v' : ℝ → ℝ}
    (hv : IsIVPSol M β v v') (hD : β ∉ Dset M) : StrictMonoOn v (Ici 0) := by
  have H := hypM M hM
  have hβ0 : 0 < β := (betaLow_pos' M hM).trans hβ
  apply strictMono_of_deriv_nonneg H hβ0.ne' hv
  intro x hx
  by_contra hc
  push Not at hc
  exact hD ((D_iff_neg_slope M hM hβ hv).2 ⟨x, hx, hc⟩)

lemma D_down (hM : M.Standing) {β₁ β₂ : ℝ} (h1 : betaLow M < β₁) (h12 : β₁ < β₂)
    (hD : β₂ ∈ Dset M) : β₁ ∈ Dset M := by
  have H := hypM M hM
  obtain ⟨v₂, v₂', hv₂⟩ := exists_sol H β₂
  obtain ⟨v₁, v₁', hv₁⟩ := exists_sol H β₁
  have h2 : betaLow M < β₂ := h1.trans h12
  obtain ⟨x, hx, hvx⟩ := (neg_slope_iff_neg_value M hM h2 hv₂).1
    ((D_iff_neg_slope M hM h2 hv₂).1 hD)
  have := mono_beta H h12 hv₁ hv₂ hx
  exact (D_iff_neg_slope M hM h1 hv₁).2
    ((neg_slope_iff_neg_value M hM h1 hv₁).2 ⟨x, hx, by linarith⟩)

lemma I_nonempty (hM : M.Standing) : (Iset M).Nonempty := by
  have H := hypM M hM
  have hκ := H.hκ
  have hp := H.hp
  have hθ := H.hθ0
  set βb := (M.κ - M.θ0) * M.p + M.σ ^ 2 / 2 * M.p + 1 with hβb
  obtain ⟨v, v', hv⟩ := exists_sol H βb
  have hlow : betaLow M < βb := by
    have := betaLow_le M hM
    have : 0 ≤ M.σ ^ 2 / 2 * M.p := by positivity
    have : 0 < M.κ * M.p := mul_pos hκ hp
    rw [hβb]; nlinarith
  have hβ0 : 0 < βb := (betaLow_pos' M hM).trans hlow
  obtain ⟨x, hx, hpx⟩ := big_goes_above H hv rfl
  exact ⟨βb, hlow, v, v', hv, (above_p_props H hβ0 hv hx hpx.le).1⟩

lemma D_nonempty (hM : M.Standing) : (Dset M).Nonempty := by
  have H := hypM M hM
  obtain ⟨ys, hys0, hysp, hmin, hneg, hlow⟩ := exists_min M hM
  obtain ⟨v, v', hv⟩ := exists_sol H (-phi M ys)
  obtain ⟨x1, hx1, hvx1⟩ := low_goes_neg H hys0 hysp hmin hneg hv
  obtain ⟨δ, hδ, hδ'⟩ := sol_cont' H hv hx1 (ε := -v x1) (by linarith)
  set β := -phi M ys + δ / 2 with hβ
  have hβlow : betaLow M < β := by rw [hlow, hβ]; linarith
  obtain ⟨w, w', hw⟩ := exists_sol H β
  have h1 := hδ' β (by rw [hβ]; rw [show -phi M ys + δ / 2 - -phi M ys = δ / 2 by ring,
    abs_of_pos (by positivity)]; linarith) w w' hw
  have hwx : w x1 < 0 := by
    have := le_abs_self (w x1 - v x1)
    linarith
  have hx1pos : 0 < x1 := by
    rcases eq_or_lt_of_le hx1 with he | he
    · rw [← he, hw.2.2.2] at hwx; linarith
    · exact he
  exact ⟨β, (D_iff_neg_slope M hM hβlow hw).2
    ((neg_slope_iff_neg_value M hM hβlow hw).2 ⟨x1, hx1pos, hwx⟩)⟩

lemma I_bddBelow (hM : M.Standing) : BddBelow (Iset M) := ⟨betaLow M, fun _ hb => hb.1.le⟩

lemma betaLow_lt_betaStar (hM : M.Standing) : betaLow M < betaStar M := by
  obtain ⟨β₀, hβ₀⟩ := D_nonempty M hM
  have : β₀ ≤ betaStar M := by
    apply le_csInf (I_nonempty M hM)
    intro β hβ
    by_contra hc
    push Not at hc
    exact I_D_disjoint M hM hβ (D_down M hM hβ.1 hc hβ₀)
  exact lt_of_lt_of_le hβ₀.1 this

lemma betaStar_not_D (hM : M.Standing) : betaStar M ∉ Dset M := by
  have H := hypM M hM
  intro hD
  have hlow := betaLow_lt_betaStar M hM
  obtain ⟨v, v', hv⟩ := exists_sol H (betaStar M)
  obtain ⟨x1, hx1, hvx1⟩ := (neg_slope_iff_neg_value M hM hlow hv).1
    ((D_iff_neg_slope M hM hlow hv).1 hD)
  obtain ⟨δ, hδ, hδ'⟩ := sol_cont' H hv hx1.le (ε := -v x1) (by linarith)
  obtain ⟨β, hβI, hβlt⟩ := exists_lt_of_csInf_lt (I_nonempty M hM)
    (show betaStar M < betaStar M + δ by linarith)
  have hβge : betaStar M ≤ β := csInf_le (I_bddBelow M hM) hβI
  obtain ⟨_, u, u', hu, hmono⟩ := hβI
  have h1 := hδ' β (by rw [abs_of_nonneg (by linarith)]; linarith) u u' hu
  have h2 := hmono ((self_mem_Ici : (0:ℝ) ∈ Ici 0)) (show x1 ∈ Ici (0:ℝ) from hx1.le) hx1
  rw [show u 0 = 0 from hu.2.2.2] at h2
  have := le_abs_self (u x1 - v x1)
  linarith

lemma betaStar_bounds (hM : M.Standing) {v v' : ℝ → ℝ} (hv : IsIVPSol M (betaStar M) v v') :
    StrictMonoOn v (Ici 0) ∧ ∀ x, 0 ≤ x → 0 ≤ v x ∧ v x ≤ M.p := by
  have H := hypM M hM
  have hlow := betaLow_lt_betaStar M hM
  have hmono := I_of_not_D M hM hlow hv (betaStar_not_D M hM)
  refine ⟨hmono, fun x hx => ⟨?_, ?_⟩⟩
  · rcases eq_or_lt_of_le hx with he | he
    · rw [← he, show v 0 = 0 from hv.2.2.2]
    · have := hmono ((self_mem_Ici : (0:ℝ) ∈ Ici 0)) (show x ∈ Ici (0:ℝ) from hx) he
      rw [show v 0 = 0 from hv.2.2.2] at this
      exact this.le
  · by_contra hc
    push Not at hc
    obtain ⟨δ, hδ, hδ'⟩ := sol_cont' H hv hx (ε := v x - M.p) (by linarith)
    set β := max (betaStar M - δ / 2) ((betaLow M + betaStar M) / 2) with hβ
    have hβlt : β < betaStar M := max_lt (by linarith) (by linarith)
    have hβlow : betaLow M < β := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    obtain ⟨w, w', hw⟩ := exists_sol H β
    have h1 := hδ' β (by
      rw [abs_of_neg (by linarith)]
      have := le_max_left (betaStar M - δ / 2) ((betaLow M + betaStar M) / 2)
      linarith) w w' hw
    have hwx : M.p < w x := by
      have := neg_abs_le (w x - v x)
      linarith
    have hβ0 : 0 < β := (betaLow_pos' M hM).trans hβlow
    have hI : β ∈ Iset M := ⟨hβlow, w, w', hw, (above_p_props H hβ0 hw hx hwx.le).1⟩
    have := csInf_le (I_bddBelow M hM) hI
    exact absurd this (not_le.2 hβlt)

lemma betaStar_bellman (hM : M.Standing) {v v' : ℝ → ℝ} (hv : IsIVPSol M (betaStar M) v v') :
    IsBellmanSol M (betaStar M) v v' := by
  have H := hypM M hM
  have hlow := betaLow_lt_betaStar M hM
  have hβ0 : 0 < betaStar M := (betaLow_pos' M hM).trans hlow
  obtain ⟨hmono, hbd⟩ := betaStar_bounds M hM hv
  have := bellman_props H hβ0 hv hbd
  exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hmono, this.2⟩

end VolBellSol

open VolunteerEngage.Bellman in
theorem solution (M : Model) (hM : M.Standing) : betaLow M < betaStar M := by
  exact VolBellSol.betaLow_lt_betaStar M hM
