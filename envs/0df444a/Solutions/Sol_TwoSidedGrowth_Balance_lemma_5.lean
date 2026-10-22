-- Prove2me | solution 1 for TwoSidedGrowth.Balance.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:02:05.352263+00:00
-- url     : https://prove2.me/submissions/68650be9-7df4-4321-886c-eef8498d67a1

import Mathlib
import Definitions.Def_TwoSidedGrowth_Balance_Setting

open Filter Topology

namespace TSGHelp
open TwoSidedGrowth.Balance

/-- balance at a value `k` of the right-hand side -/
def IsBal (M : Model) (k γ : ℝ) : Prop :=
  (γ ∈ Set.Ioo 0 1 ∧ deriv (h M) γ = k) ∨
  (γ = 0 ∧ ∀ η ∈ Set.Ioo (0:ℝ) 1, deriv (h M) η ≤ k) ∨
  (γ = 1 ∧ ∀ η ∈ Set.Ioo (0:ℝ) 1, k ≤ deriv (h M) η)

theorem isBalance_iff (M : Model) (x γ : ℝ) : IsBalance M x γ ↔ IsBal M (kappa M x) γ :=
  Iff.rfl

theorem hd_anti {M : Model} (hM : M.Standing) : StrictAntiOn (deriv (h M)) (Set.Ioo 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1) hM.h'_differentiableOn.continuousOn
  intro x hx
  rw [interior_Ioo] at hx
  exact hM.assumption_2 x hx

theorem bal_mem {M : Model} {k γ : ℝ} (hb : IsBal M k γ) : γ ∈ Set.Icc (0:ℝ) 1 := by
  rcases hb with ⟨hγ, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact ⟨hγ.1.le, hγ.2.le⟩
  · exact ⟨le_refl _, zero_le_one⟩
  · exact ⟨zero_le_one, le_refl _⟩

theorem bal_lt {M : Model} (hM : M.Standing) {k γ η : ℝ} (hb : IsBal M k γ)
    (hη : η ∈ Set.Ioo (0:ℝ) 1) (hlt : η < γ) : k ≤ deriv (h M) η := by
  rcases hb with ⟨hγ, hk⟩ | ⟨rfl, _⟩ | ⟨rfl, h1⟩
  · rw [← hk]; exact (hd_anti hM hη hγ hlt).le
  · exact absurd hlt (not_lt.2 hη.1.le)
  · exact h1 η hη

theorem bal_gt {M : Model} (hM : M.Standing) {k γ η : ℝ} (hb : IsBal M k γ)
    (hη : η ∈ Set.Ioo (0:ℝ) 1) (hlt : γ < η) : deriv (h M) η ≤ k := by
  rcases hb with ⟨hγ, hk⟩ | ⟨rfl, h0⟩ | ⟨rfl, _⟩
  · rw [← hk]; exact (hd_anti hM hγ hη hlt).le
  · exact h0 η hη
  · exact absurd hlt (not_lt.2 hη.2.le)

theorem bal_lt_strict {M : Model} (hM : M.Standing) {k γ η : ℝ} (hb : IsBal M k γ)
    (hη : η ∈ Set.Ioo (0:ℝ) 1) (hlt : η < γ) : k < deriv (h M) η := by
  have hγ1 := (bal_mem hb).2
  have h1 : (η + γ) / 2 ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hη.1], by linarith⟩
  calc k ≤ deriv (h M) ((η + γ) / 2) := bal_lt hM hb h1 (by linarith)
    _ < deriv (h M) η := hd_anti hM hη h1 (by linarith)

theorem bal_gt_strict {M : Model} (hM : M.Standing) {k γ η : ℝ} (hb : IsBal M k γ)
    (hη : η ∈ Set.Ioo (0:ℝ) 1) (hlt : γ < η) : deriv (h M) η < k := by
  have hγ0 := (bal_mem hb).1
  have h1 : (η + γ) / 2 ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith [hη.2]⟩
  calc deriv (h M) η < deriv (h M) ((η + γ) / 2) := hd_anti hM h1 hη (by linarith)
    _ ≤ k := bal_gt hM hb h1 (by linarith)

/-- ordering: a larger balance comes from a smaller value. -/
theorem bal_order {M : Model} (hM : M.Standing) {k1 k2 γ1 γ2 : ℝ} (h1 : IsBal M k1 γ1)
    (h2 : IsBal M k2 γ2) (hlt : γ1 < γ2) : k2 < k1 := by
  have m1 := bal_mem h1
  have m2 := bal_mem h2
  have hη : (γ1 + γ2) / 2 ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [m1.1], by linarith [m2.2]⟩
  calc k2 < deriv (h M) ((γ1 + γ2) / 2) := bal_lt_strict hM h2 hη (by linarith)
    _ < k1 := bal_gt_strict hM h1 hη (by linarith)

theorem bal_unique {M : Model} (hM : M.Standing) {k γ1 γ2 : ℝ} (h1 : IsBal M k γ1)
    (h2 : IsBal M k γ2) : γ1 = γ2 := by
  rcases lt_trichotomy γ1 γ2 with h | h | h
  · exact absurd (bal_order hM h1 h2 h) (lt_irrefl _)
  · exact h
  · exact absurd (bal_order hM h2 h1 h) (lt_irrefl _)

theorem bal_anti {M : Model} (hM : M.Standing) {k1 k2 γ1 γ2 : ℝ} (h1 : IsBal M k1 γ1)
    (h2 : IsBal M k2 γ2) (hk : k1 ≤ k2) : γ2 ≤ γ1 := by
  by_contra hc
  push Not at hc
  exact absurd (bal_order hM h1 h2 hc) (not_lt.2 hk)

theorem bal_santi {M : Model} (hM : M.Standing) {k1 k2 γ1 γ2 : ℝ} (h1 : IsBal M k1 γ1)
    (h2 : IsBal M k2 γ2) (hi : γ1 ∈ Set.Ioo (0:ℝ) 1) (hk : k1 < k2) : γ2 < γ1 := by
  rcases (bal_anti hM h1 h2 hk.le).lt_or_eq with h | h
  · exact h
  · exfalso
    subst h
    have e1 : deriv (h M) γ2 = k1 := by
      rcases h1 with ⟨_, e⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact e
      · exact absurd hi.1 (lt_irrefl _)
      · exact absurd hi.2 (lt_irrefl _)
    have e2 : deriv (h M) γ2 = k2 := by
      rcases h2 with ⟨_, e⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact e
      · exact absurd hi.1 (lt_irrefl _)
      · exact absurd hi.2 (lt_irrefl _)
    linarith

theorem bal_exists {M : Model} (hM : M.Standing) (k : ℝ) : ∃ γ, IsBal M k γ := by
  by_cases h0 : ∀ η ∈ Set.Ioo (0:ℝ) 1, deriv (h M) η ≤ k
  · exact ⟨0, Or.inr (Or.inl ⟨rfl, h0⟩)⟩
  by_cases h1 : ∀ η ∈ Set.Ioo (0:ℝ) 1, k ≤ deriv (h M) η
  · exact ⟨1, Or.inr (Or.inr ⟨rfl, h1⟩)⟩
  push Not at h0 h1
  obtain ⟨a, ha, hka⟩ := h0
  obtain ⟨b, hb, hkb⟩ := h1
  have hab : a ≤ b := by
    by_contra hc
    push Not at hc
    have := hd_anti hM hb ha hc
    linarith
  have hsub : Set.Icc a b ⊆ Set.Ioo (0:ℝ) 1 := fun t ht => ⟨lt_of_lt_of_le ha.1 ht.1,
    lt_of_le_of_lt ht.2 hb.2⟩
  have hc : ContinuousOn (deriv (h M)) (Set.Icc a b) :=
    hM.h'_differentiableOn.continuousOn.mono hsub
  obtain ⟨c, hc, hck⟩ := intermediate_value_Icc' hab hc ⟨hkb.le, hka.le⟩
  exact ⟨c, Or.inl ⟨hsub hc, hck⟩⟩

/-! ## the function G -/

theorem out_cont {M : Model} (hM : M.Standing) {x : ℝ} :
    ContinuousOn (fun γ => G M γ x) (Set.Icc 0 1) := by
  unfold G out
  have := hM.h_continuousOn
  fun_prop

theorem G_hasDeriv {M : Model} (hM : M.Standing) {x γ : ℝ} (hγ : γ ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun γ => G M γ x)
      ((M.v - M.c) * (x ^ M.α * deriv (h M) γ) - (M.bs0 - M.bd0) * x) γ := by
  have hd : HasDerivAt (h M) (deriv (h M) γ) γ :=
    ((hM.h_differentiableOn γ hγ).differentiableAt (Ioo_mem_nhds hγ.1 hγ.2)).hasDerivAt
  unfold G out
  have h2 : HasDerivAt (fun γ : ℝ => (M.ρ + M.bs0 * γ + M.bd0 * (1 - γ)) * x)
      ((M.bs0 - M.bd0) * x) γ := by
    have := ((hasDerivAt_id' γ).const_mul ((M.bs0 - M.bd0) * x)).const_add ((M.ρ + M.bd0) * x)
    have e : (fun γ : ℝ => (M.ρ + M.bs0 * γ + M.bd0 * (1 - γ)) * x) =
        fun y => (M.ρ + M.bd0) * x + (M.bs0 - M.bd0) * x * y := by funext y; ring
    rw [e]; exact this.congr_deriv (by ring)
  exact ((hd.const_mul (x ^ M.α)).const_mul (M.v - M.c)).sub h2

theorem G_deriv_eq {M : Model} (hM : M.Standing) {x γ : ℝ} (hx : 0 < x) :
    (M.v - M.c) * (x ^ M.α * deriv (h M) γ) - (M.bs0 - M.bd0) * x =
      (M.v - M.c) * x ^ M.α * (deriv (h M) γ - kappa M x) := by
  have hvc : M.v - M.c ≠ 0 := (sub_pos.2 hM.c_lt_v).ne'
  have hxa : x ^ M.α * x ^ (1 - M.α) = x := by
    rw [← Real.rpow_add hx]; simp
  have hk : (M.v - M.c) * x ^ M.α * kappa M x = (M.bs0 - M.bd0) * x := by
    unfold kappa; field_simp
    linear_combination (M.bs0 - M.bd0) * hxa
  linear_combination hk

theorem G_strict_max {M : Model} (hM : M.Standing) {x γ η : ℝ} (hx : 0 < x)
    (hb : IsBal M (kappa M x) γ) (hη : η ∈ Set.Icc (0:ℝ) 1) (hne : η ≠ γ) :
    G M η x < G M γ x := by
  have mγ := bal_mem hb
  have hpos : 0 < (M.v - M.c) * x ^ M.α :=
    mul_pos (sub_pos.2 hM.c_lt_v) (Real.rpow_pos_of_pos hx _)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hmono : StrictMonoOn (fun γ => G M γ x) (Set.Icc η γ) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc η γ)
        (out_cont hM |>.mono (Set.Icc_subset_Icc hη.1 mγ.2))
      intro t ht
      rw [interior_Icc] at ht
      have ht01 : t ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_of_le_of_lt hη.1 ht.1, lt_of_lt_of_le ht.2 mγ.2⟩
      rw [(G_hasDeriv hM ht01).deriv, G_deriv_eq hM hx]
      exact mul_pos hpos (sub_pos.2 (bal_lt_strict hM hb ht01 ht.2))
    exact hmono ⟨le_refl _, hlt.le⟩ ⟨hlt.le, le_refl _⟩ hlt
  · have hanti : StrictAntiOn (fun γ => G M γ x) (Set.Icc γ η) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc γ η)
        (out_cont hM |>.mono (Set.Icc_subset_Icc mγ.1 hη.2))
      intro t ht
      rw [interior_Icc] at ht
      have ht01 : t ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_of_le_of_lt mγ.1 ht.1, lt_of_lt_of_le ht.2 hη.2⟩
      rw [(G_hasDeriv hM ht01).deriv, G_deriv_eq hM hx]
      exact mul_neg_of_pos_of_neg hpos (sub_neg.2 (bal_gt_strict hM hb ht01 ht.1))
    exact hanti ⟨le_refl _, hlt.le⟩ ⟨hlt.le, le_refl _⟩ hlt

theorem eq33 (M : Model) (hM : M.Standing) :
    (∀ x : ℝ, 0 < x → ∃! γ : ℝ, IsBalance M x γ) ∧
    (∀ x : ℝ, 0 < x → ∀ γ ∈ Set.Icc (0:ℝ) 1,
      ((∀ η ∈ Set.Icc (0:ℝ) 1, G M η x ≤ G M γ x) ↔ IsBalance M x γ)) := by
  refine ⟨fun x _ => ?_, fun x hx γ hγ => ?_⟩
  · obtain ⟨γ, hγ⟩ := bal_exists hM (kappa M x)
    exact ⟨γ, hγ, fun γ' h' => bal_unique hM h' hγ⟩
  · constructor
    · intro hmax
      obtain ⟨γ', hγ'⟩ := bal_exists hM (kappa M x)
      by_cases he : γ = γ'
      · rw [he]; exact hγ'
      · have := G_strict_max hM hx hγ' hγ he
        linarith [hmax γ' (bal_mem hγ')]
    · intro hb η hη
      by_cases he : η = γ
      · rw [he]
      · exact (G_strict_max hM hx hb hη he).le

end TSGHelp


open Filter Topology

namespace TSGHelp
open TwoSidedGrowth.Balance

theorem lemma6 (M : Model) (hM : M.Standing) (x : ℝ) (hx : 0 < x) :
    StrictConcaveOn ℝ (Set.Icc (0:ℝ) 1) (fun γ => G M γ x) := by
  have hpos : 0 < (M.v - M.c) * x ^ M.α :=
    mul_pos (sub_pos.2 hM.c_lt_v) (Real.rpow_pos_of_pos hx _)
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc 0 1) (out_cont hM)
  rw [interior_Icc]
  intro a ha b hb hab
  rw [(G_hasDeriv hM ha).deriv, (G_hasDeriv hM hb).deriv, G_deriv_eq hM hx, G_deriv_eq hM hx]
  apply mul_lt_mul_of_pos_left _ hpos
  linarith [hd_anti hM ha hb hab]

theorem path_cont (M : Model) (hM : M.Standing) (T : ℝ) (x γ : ℝ → ℝ)
    (hpath : ∀ t ∈ Set.Icc 0 T, 0 < x t ∧ γ t ∈ Set.Icc 0 1)
    (hγc : ContinuousOn γ (Set.Icc 0 T)) (hxc : ContinuousOn x (Set.Icc 0 T)) :
    ContinuousOn (fun t => out M (γ t) (x t)) (Set.Icc 0 T) ∧
    ContinuousOn (fun t => Real.exp (-(M.ρ * t)) * G M (γ t) (x t)) (Set.Icc 0 T) := by
  have houtc : ContinuousOn (fun t => out M (γ t) (x t)) (Set.Icc 0 T) := by
    unfold out
    apply ContinuousOn.mul
    · exact hxc.rpow_const (fun t ht => Or.inl (hpath t ht).1.ne')
    · exact hM.h_continuousOn.comp hγc (fun t ht => (hpath t ht).2)
  refine ⟨houtc, ?_⟩
  have he : Continuous fun t : ℝ => Real.exp (-(M.ρ * t)) := by fun_prop
  apply he.continuousOn.mul
  show ContinuousOn (fun t => (M.v - M.c) * out M (γ t) (x t) -
    (M.ρ + M.bs0 * γ t + M.bd0 * (1 - γ t)) * x t) _
  exact (continuousOn_const.mul houtc).sub
    (((continuousOn_const.add (continuousOn_const.mul hγc)).add
      (continuousOn_const.mul (continuousOn_const.sub hγc))).mul hxc)

theorem lemma5 (M : Model) (hM : M.Standing) (T : ℝ) (x γ pm : ℝ → ℝ)
    (hadm : Admissible M T x γ pm) :
    profit M T x γ pm =
      (∫ t in (0:ℝ)..T, Real.exp (-(M.ρ * t)) * G M (γ t) (x t))
        - Real.exp (-(M.ρ * T)) * x T + x 0 := by
  obtain ⟨hT, hpath, hγc, hpmc, x', hx'c, hder⟩ := hadm
  have hxc : ContinuousOn x (Set.Icc 0 T) := fun t ht => (hder t ht).1.continuousWithinAt
  obtain ⟨houtc, hGc⟩ := path_cont M hM T x γ hpath hγc hxc
  have he : Continuous fun t : ℝ => Real.exp (-(M.ρ * t)) := by fun_prop
  have hPc : ContinuousOn (fun t => Real.exp (-(M.ρ * t)) * pm t * out M (γ t) (x t))
      (Set.Icc 0 T) := (he.continuousOn.mul hpmc).mul houtc
  have hi1 : IntervalIntegrable (fun t => Real.exp (-(M.ρ * t)) * G M (γ t) (x t))
      MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le hT]; exact hGc
  have hi2 : IntervalIntegrable (fun t => Real.exp (-(M.ρ * t)) * pm t * out M (γ t) (x t))
      MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le hT]; exact hPc
  have key : (∫ t in (0:ℝ)..T, (Real.exp (-(M.ρ * t)) * G M (γ t) (x t) -
      Real.exp (-(M.ρ * t)) * pm t * out M (γ t) (x t))) =
      Real.exp (-(M.ρ * T)) * x T - Real.exp (-(M.ρ * 0)) * x 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT (he.continuousOn.mul hxc)
    · intro t ht
      have hxd : HasDerivAt x (x' t) t :=
        (hder t (Set.Ioo_subset_Icc_self ht)).1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      have hed : HasDerivAt (fun t : ℝ => Real.exp (-(M.ρ * t)))
          (Real.exp (-(M.ρ * t)) * (-(M.ρ * 1))) t :=
        ((hasDerivAt_id' t).const_mul M.ρ).neg.exp
      have := hed.mul hxd
      apply this.congr_deriv
      rw [(hder t (Set.Ioo_subset_Icc_self ht)).2]
      unfold G
      ring
    · exact hi1.sub hi2
  rw [intervalIntegral.integral_sub hi1 hi2] at key
  unfold profit
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul] at key
  linarith

end TSGHelp

open TwoSidedGrowth.Balance in
theorem solution (M : Model) (hM : M.Standing) (T : ℝ) (x γ pm : ℝ → ℝ)
    (hadm : Admissible M T x γ pm) :
    profit M T x γ pm =
      (∫ t in (0:ℝ)..T, Real.exp (-(M.ρ * t)) * G M (γ t) (x t))
        - Real.exp (-(M.ρ * T)) * x T + x 0 :=
  TSGHelp.lemma5 M hM T x γ pm hadm
