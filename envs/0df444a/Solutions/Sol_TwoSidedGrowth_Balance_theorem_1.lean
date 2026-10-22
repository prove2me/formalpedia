-- Prove2me | solution 1 for TwoSidedGrowth.Balance.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:06:26.025977+00:00
-- url     : https://prove2.me/submissions/ede8a3b7-7023-4dda-81ef-0cf02273b141

import Mathlib
import Definitions.Def_TwoSidedGrowth_Balance_Setting
import Theorems.Thm_TwoSidedGrowth_Balance_eq_33
import Theorems.Thm_TwoSidedGrowth_Balance_lemma_5

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


open Filter Topology

namespace TSGHelp
open TwoSidedGrowth.Balance

theorem bal_interior_eq {M : Model} {k γ : ℝ} (hb : IsBal M k γ) (hi : γ ∈ Set.Ioo (0:ℝ) 1) :
    deriv (h M) γ = k := by
  rcases hb with ⟨_, e⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact e
  · exact absurd hi.1 (lt_irrefl _)
  · exact absurd hi.2 (lt_irrefl _)

theorem bal_near {M : Model} (hM : M.Standing) {k0 γ0 : ℝ} (h0 : γ0 ∈ Set.Ioo (0:ℝ) 1)
    (hk0 : deriv (h M) γ0 = k0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ k γ, |k - k0| < δ → IsBal M k γ → |γ - γ0| < ε := by
  obtain ⟨h01, h02⟩ := h0
  set e := min (ε / 2) (min (γ0 / 2) ((1 - γ0) / 2)) with he
  have he0 : 0 < e := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have he1 : e ≤ ε / 2 := min_le_left _ _
  have he2 : e ≤ γ0 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have he3 : e ≤ (1 - γ0) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have ha : γ0 - e ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hb : γ0 + e ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hHa : k0 < deriv (h M) (γ0 - e) := by
    rw [← hk0]; exact hd_anti hM ha ⟨h01, h02⟩ (by linarith)
  have hHb : deriv (h M) (γ0 + e) < k0 := by
    rw [← hk0]; exact hd_anti hM ⟨h01, h02⟩ hb (by linarith)
  refine ⟨min (deriv (h M) (γ0 - e) - k0) (k0 - deriv (h M) (γ0 + e)),
    lt_min (by linarith) (by linarith), ?_⟩
  intro k γ hk hbal
  have hk1 := lt_of_lt_of_le hk (min_le_left _ _)
  have hk2 := lt_of_lt_of_le hk (min_le_right _ _)
  rw [abs_lt] at hk1 hk2 ⊢
  have hγa : γ0 - e ≤ γ := by
    by_contra hc
    push Not at hc
    have := bal_gt hM hbal ha hc
    linarith
  have hγb : γ ≤ γ0 + e := by
    by_contra hc
    push Not at hc
    have := bal_lt hM hbal hb hc
    linarith
  constructor <;> linarith

theorem bal_big {M : Model} (hM : M.Standing) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∀ k γ, K < k → IsBal M k γ → γ < ε := by
  set e := min (ε / 2) (1 / 2)
  have he0 : 0 < e := lt_min (by linarith) (by norm_num)
  have he1 : e < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have he2 : e < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨deriv (h M) e, fun k γ hk hb => ?_⟩
  by_contra hc
  push Not at hc
  have := bal_lt hM hb ⟨he0, he2⟩ (lt_of_lt_of_le he1 hc)
  linarith

theorem bal_small {M : Model} (hM : M.Standing) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∀ k γ, k < K → IsBal M k γ → 1 - ε < γ := by
  set e := max (1 - ε / 2) (1 / 2)
  have he0 : 0 < e := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have he1 : 1 - ε < e := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have he2 : e < 1 := max_lt (by linarith) (by norm_num)
  refine ⟨deriv (h M) e, fun k γ hk hb => ?_⟩
  by_contra hc
  push Not at hc
  have := bal_gt hM hb ⟨he0, he2⟩ (lt_of_le_of_lt hc he1)
  linarith

section
variable {M : Model} (hM : M.Standing) (γs : ℝ → ℝ)
  (hγs : ∀ x : ℝ, 0 < x → IsBal M (kappa M x) (γs x))
include hM hγs

theorem tend_mid {l : Filter ℝ} (hpos : ∀ᶠ x in l, 0 < x) {γo : ℝ}
    (hγo : γo ∈ Set.Ioo (0:ℝ) 1) (hH : deriv (h M) γo = 0) (hk : Tendsto (kappa M) l (𝓝 0)) :
    Tendsto γs l (𝓝 γo) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := bal_near hM hγo hH hε
  have := (Metric.tendsto_nhds.1 hk) δ hδ
  filter_upwards [this, hpos] with x hx hx0
  rw [Real.dist_eq] at hx ⊢
  exact H _ _ hx (hγs x hx0)

theorem tend_zero {l : Filter ℝ} (hpos : ∀ᶠ x in l, 0 < x) (hk : Tendsto (kappa M) l atTop) :
    Tendsto γs l (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [hpos] with x hx
    exact lt_of_lt_of_le ha (bal_mem (hγs x hx)).1
  · intro a ha
    obtain ⟨K, HK⟩ := bal_big hM ha
    filter_upwards [hk.eventually_gt_atTop K, hpos] with x hx hx0
    exact HK _ _ hx (hγs x hx0)

theorem tend_one {l : Filter ℝ} (hpos : ∀ᶠ x in l, 0 < x) (hk : Tendsto (kappa M) l atBot) :
    Tendsto γs l (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨K, HK⟩ := bal_small hM (sub_pos.2 ha)
    filter_upwards [hk.eventually_lt_atBot K, hpos] with x hx hx0
    have := HK _ _ hx (hγs x hx0)
    linarith
  · intro a ha
    filter_upwards [hpos] with x hx
    exact lt_of_le_of_lt (bal_mem (hγs x hx)).2 ha

theorem mono_of_kanti (hk : StrictAntiOn (kappa M) (Set.Ioi 0)) :
    MonotoneOn γs (Set.Ioi 0) ∧ StrictMonoOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} := by
  constructor
  · intro a ha b hb hab
    rcases hab.lt_or_eq with hlt | rfl
    · exact bal_anti hM (hγs b hb) (hγs a ha) (hk ha hb hlt).le
    · exact le_refl _
  · intro a ha b hb hab
    exact bal_santi hM (hγs b hb.1) (hγs a ha.1) hb.2 (hk ha.1 hb.1 hab)

theorem anti_of_kmono (hk : StrictMonoOn (kappa M) (Set.Ioi 0)) :
    AntitoneOn γs (Set.Ioi 0) ∧ StrictAntiOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} := by
  constructor
  · intro a ha b hb hab
    rcases hab.lt_or_eq with hlt | rfl
    · exact bal_anti hM (hγs a ha) (hγs b hb) (hk ha hb hlt).le
    · exact le_refl _
  · intro a ha b hb hab
    exact bal_santi hM (hγs a ha.1) (hγs b hb.1) ha.2 (hk ha.1 hb.1 hab)

end

theorem kappa_eq (M : Model) :
    kappa M = fun x => (M.bs0 - M.bd0) / (M.v - M.c) * x ^ (1 - M.α) := by
  funext x; unfold kappa; ring

theorem kappa_smono {M : Model} {C : ℝ} (hC : (M.bs0 - M.bd0) / (M.v - M.c) = C)
    (hp : 0 < 1 - M.α) (hCs : 0 < C) : StrictMonoOn (kappa M) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [kappa_eq, hC]
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (le_of_lt ha) hab hp) hCs

theorem kappa_santi {M : Model} {C : ℝ} (hC : (M.bs0 - M.bd0) / (M.v - M.c) = C)
    (hp : 0 < 1 - M.α) (hCs : C < 0) : StrictAntiOn (kappa M) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [kappa_eq, hC]
  exact mul_lt_mul_of_neg_left (Real.rpow_lt_rpow (le_of_lt ha) hab hp) hCs

theorem kappa_santi' {M : Model} {C : ℝ} (hC : (M.bs0 - M.bd0) / (M.v - M.c) = C)
    (hp : 1 - M.α < 0) (hCs : 0 < C) : StrictAntiOn (kappa M) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [kappa_eq, hC]
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg ha hab hp) hCs

theorem kappa_smono' {M : Model} {C : ℝ} (hC : (M.bs0 - M.bd0) / (M.v - M.c) = C)
    (hp : 1 - M.α < 0) (hCs : C < 0) : StrictMonoOn (kappa M) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [kappa_eq, hC]
  exact mul_lt_mul_of_neg_left (Real.rpow_lt_rpow_of_neg ha hab hp) hCs

theorem rpow_tend0 {p : ℝ} (hp : 0 < p) : Tendsto (fun x : ℝ => x ^ p) (𝓝[>] 0) (𝓝 0) := by
  have h1 : ContinuousAt (fun x : ℝ => x ^ p) 0 := Real.continuousAt_rpow_const 0 p (Or.inr hp.le)
  have h2 := h1.tendsto
  rw [Real.zero_rpow hp.ne'] at h2
  exact h2.mono_left nhdsWithin_le_nhds

theorem rpow_tendTop {p : ℝ} (hp : p < 0) : Tendsto (fun x : ℝ => x ^ p) atTop (𝓝 0) := by
  have := tendsto_rpow_neg_atTop (neg_pos.2 hp)
  rwa [neg_neg] at this

theorem kappa_tend {M : Model} {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => x ^ (1 - M.α)) l (𝓝 0)) :
    Tendsto (kappa M) l (𝓝 0) := by
  rw [kappa_eq]
  have := (tendsto_const_nhds (x := (M.bs0 - M.bd0) / (M.v - M.c))).mul hl
  rwa [mul_zero] at this

theorem kappa_top {M : Model} {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => x ^ (1 - M.α)) l atTop)
    (hC : 0 < (M.bs0 - M.bd0) / (M.v - M.c)) : Tendsto (kappa M) l atTop := by
  rw [kappa_eq]; exact hl.const_mul_atTop hC

theorem kappa_bot {M : Model} {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => x ^ (1 - M.α)) l atTop)
    (hC : (M.bs0 - M.bd0) / (M.v - M.c) < 0) : Tendsto (kappa M) l atBot := by
  rw [kappa_eq]; exact hl.const_mul_atTop_of_neg hC

theorem part4 (M : Model) (hM : M.Standing) : ∀ γs : ℝ → ℝ, (∀ x : ℝ, 0 < x → IsBalance M x (γs x)) →
      ∀ γo ∈ Set.Ioo (0:ℝ) 1, deriv (h M) γo = 0 →
      (M.α < 1 → M.bd0 < M.bs0 →
        AntitoneOn γs (Set.Ioi 0) ∧ StrictAntiOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} ∧
        Tendsto γs (𝓝[>] 0) (𝓝 γo) ∧ Tendsto γs atTop (𝓝 0)) ∧
      (M.α < 1 → M.bs0 < M.bd0 →
        MonotoneOn γs (Set.Ioi 0) ∧ StrictMonoOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} ∧
        Tendsto γs (𝓝[>] 0) (𝓝 γo) ∧ Tendsto γs atTop (𝓝 1)) ∧
      (1 < M.α → M.bd0 < M.bs0 →
        MonotoneOn γs (Set.Ioi 0) ∧ StrictMonoOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} ∧
        Tendsto γs (𝓝[>] 0) (𝓝 0) ∧ Tendsto γs atTop (𝓝 γo)) ∧
      (1 < M.α → M.bs0 < M.bd0 →
        AntitoneOn γs (Set.Ioi 0) ∧ StrictAntiOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} ∧
        Tendsto γs (𝓝[>] 0) (𝓝 1) ∧ Tendsto γs atTop (𝓝 γo)) := by
  intro γs hγs γo hγo hH
  have hγs' : ∀ x : ℝ, 0 < x → IsBal M (kappa M x) (γs x) := hγs
  have hp0 : ∀ᶠ x in 𝓝[>] (0:ℝ), 0 < x := eventually_mem_nhdsWithin
  have hpT : ∀ᶠ x in atTop, (0:ℝ) < x := eventually_gt_atTop 0
  have hvc : 0 < M.v - M.c := sub_pos.2 hM.c_lt_v
  refine ⟨fun hα hb => ?_, fun hα hb => ?_, fun hα hb => ?_, fun hα hb => ?_⟩
  · have hp : 0 < 1 - M.α := by linarith
    have hC : 0 < (M.bs0 - M.bd0) / (M.v - M.c) := div_pos (by linarith) hvc
    obtain ⟨h1, h2⟩ := anti_of_kmono hM γs hγs' (kappa_smono rfl hp hC)
    exact ⟨h1, h2, tend_mid hM γs hγs' hp0 hγo hH (kappa_tend (rpow_tend0 hp)),
      tend_zero hM γs hγs' hpT (kappa_top (tendsto_rpow_atTop hp) hC)⟩
  · have hp : 0 < 1 - M.α := by linarith
    have hC : (M.bs0 - M.bd0) / (M.v - M.c) < 0 := div_neg_of_neg_of_pos (by linarith) hvc
    obtain ⟨h1, h2⟩ := mono_of_kanti hM γs hγs' (kappa_santi rfl hp hC)
    exact ⟨h1, h2, tend_mid hM γs hγs' hp0 hγo hH (kappa_tend (rpow_tend0 hp)),
      tend_one hM γs hγs' hpT (kappa_bot (tendsto_rpow_atTop hp) hC)⟩
  · have hp : 1 - M.α < 0 := by linarith
    have hC : 0 < (M.bs0 - M.bd0) / (M.v - M.c) := div_pos (by linarith) hvc
    obtain ⟨h1, h2⟩ := mono_of_kanti hM γs hγs' (kappa_santi' rfl hp hC)
    exact ⟨h1, h2, tend_zero hM γs hγs' hp0 (kappa_top (tendsto_rpow_neg_nhdsGT_zero hp) hC),
      tend_mid hM γs hγs' hpT hγo hH (kappa_tend (rpow_tendTop hp))⟩
  · have hp : 1 - M.α < 0 := by linarith
    have hC : (M.bs0 - M.bd0) / (M.v - M.c) < 0 := div_neg_of_neg_of_pos (by linarith) hvc
    obtain ⟨h1, h2⟩ := anti_of_kmono hM γs hγs' (kappa_smono' rfl hp hC)
    exact ⟨h1, h2, tend_one hM γs hγs' hp0 (kappa_bot (tendsto_rpow_neg_nhdsGT_zero hp) hC),
      tend_mid hM γs hγs' hpT hγo hH (kappa_tend (rpow_tendTop hp))⟩

theorem eq34 (M : Model) (hM : M.Standing) (γs : ℝ → ℝ)
    (hγs : ∀ x : ℝ, 0 < x → IsBalance M x (γs x)) (x : ℝ) (hx : 0 < x)
    (hint : γs x ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt γs
      ((M.bs0 - M.bd0) * (1 - M.α) /
        ((M.v - M.c) * deriv (deriv (h M)) (γs x) * x ^ M.α)) x ∧
    SignType.sign ((M.bs0 - M.bd0) * (1 - M.α) /
        ((M.v - M.c) * deriv (deriv (h M)) (γs x) * x ^ M.α)) =
      SignType.sign ((M.α - 1) * (M.bs0 - M.bd0)) := by
  have hγs' : ∀ x : ℝ, 0 < x → IsBal M (kappa M x) (γs x) := hγs
  choose Φ hΦ using fun k => bal_exists hM k
  have hΦ0 : Φ (kappa M x) = γs x := bal_unique hM (hΦ _) (hγs' x hx)
  have hH0 : deriv (h M) (γs x) = kappa M x := bal_interior_eq (hγs' x hx) hint
  have hcont : ContinuousAt Φ (kappa M x) := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := bal_near hM hint hH0 hε
    refine ⟨δ, hδ, fun {k} hk => ?_⟩
    rw [hΦ0, Real.dist_eq]
    rw [Real.dist_eq] at hk
    exact H k (Φ k) hk (hΦ k)
  have hev : ∀ᶠ k in 𝓝 (kappa M x), deriv (h M) (Φ k) = k := by
    have : ∀ᶠ k in 𝓝 (kappa M x), Φ k ∈ Set.Ioo (0:ℝ) 1 :=
      hcont.eventually (by rw [hΦ0]; exact Ioo_mem_nhds hint.1 hint.2)
    filter_upwards [this] with k hk
    exact bal_interior_eq (hΦ k) hk
  have hd2 : HasDerivAt (deriv (h M)) (deriv (deriv (h M)) (γs x)) (Φ (kappa M x)) := by
    rw [hΦ0]
    exact ((hM.h'_differentiableOn _ hint).differentiableAt
      (Ioo_mem_nhds hint.1 hint.2)).hasDerivAt
  have hneg : deriv (deriv (h M)) (γs x) < 0 := hM.assumption_2 _ hint
  have hΦd := HasDerivAt.of_local_left_inverse hcont hd2 hneg.ne hev
  have hκ : HasDerivAt (kappa M)
      ((M.bs0 - M.bd0) * ((1 - M.α) * x ^ (1 - M.α - 1)) / (M.v - M.c)) x := by
    have := ((Real.hasDerivAt_rpow_const (p := 1 - M.α) (Or.inl hx.ne')).const_mul
      (M.bs0 - M.bd0)).div_const (M.v - M.c)
    exact this
  have hcomp := hΦd.comp x hκ
  have heq : γs =ᶠ[𝓝 x] Φ ∘ kappa M := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (bal_unique hM (hΦ (kappa M y)) (hγs' y hy)).symm
  have hvc : 0 < M.v - M.c := sub_pos.2 hM.c_lt_v
  have hxa0 : 0 < x ^ M.α := Real.rpow_pos_of_pos hx M.α
  refine ⟨?_, ?_⟩
  · apply (hcomp.congr_of_eventuallyEq heq).congr_deriv
    have hxa : x ^ (1 - M.α - 1) = (x ^ M.α)⁻¹ := by
      rw [show 1 - M.α - 1 = -M.α by ring, Real.rpow_neg hx.le]
    rw [hxa]
    field_simp
  · have hb : (M.v - M.c) * deriv (deriv (h M)) (γs x) * x ^ M.α < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hvc hneg) hxa0
    rcases lt_trichotomy ((M.α - 1) * (M.bs0 - M.bd0)) 0 with hr | hr | hr
    · rw [sign_neg hr, sign_neg (div_neg_of_pos_of_neg (by linarith) hb)]
    · have : (M.bs0 - M.bd0) * (1 - M.α) = 0 := by linarith
      rw [hr, this, zero_div]
    · rw [sign_pos hr, sign_pos (div_pos_of_neg_of_neg (by linarith) hb)]

end TSGHelp

open TwoSidedGrowth.Balance in
theorem solution (M : Model) (hM : M.Standing) :
    (∀ x : ℝ, 0 < x → ∃! γ : ℝ, IsBalance M x γ) ∧
    (∀ x : ℝ, 0 < x → ∀ γ ∈ Set.Icc (0:ℝ) 1,
      ((∀ η ∈ Set.Icc (0:ℝ) 1, G M η x ≤ G M γ x) ↔ IsBalance M x γ)) ∧
    (∀ (T : ℝ) (x γ pm γb pmb : ℝ → ℝ), Admissible M T x γ pm → Admissible M T x γb pmb →
      (∀ t ∈ Set.Icc 0 T, IsBalance M (x t) (γb t)) →
      profit M T x γ pm ≤ profit M T x γb pmb) ∧
    (∀ γs : ℝ → ℝ, (∀ x : ℝ, 0 < x → IsBalance M x (γs x)) →
      ∀ γo ∈ Set.Ioo (0:ℝ) 1, deriv (h M) γo = 0 →
      (M.α < 1 → M.bd0 < M.bs0 →
        AntitoneOn γs (Set.Ioi 0) ∧ StrictAntiOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} ∧
        Tendsto γs (𝓝[>] 0) (𝓝 γo) ∧ Tendsto γs atTop (𝓝 0)) ∧
      (M.α < 1 → M.bs0 < M.bd0 →
        MonotoneOn γs (Set.Ioi 0) ∧ StrictMonoOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} ∧
        Tendsto γs (𝓝[>] 0) (𝓝 γo) ∧ Tendsto γs atTop (𝓝 1)) ∧
      (1 < M.α → M.bd0 < M.bs0 →
        MonotoneOn γs (Set.Ioi 0) ∧ StrictMonoOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} ∧
        Tendsto γs (𝓝[>] 0) (𝓝 0) ∧ Tendsto γs atTop (𝓝 γo)) ∧
      (1 < M.α → M.bs0 < M.bd0 →
        AntitoneOn γs (Set.Ioi 0) ∧ StrictAntiOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} ∧
        Tendsto γs (𝓝[>] 0) (𝓝 1) ∧ Tendsto γs atTop (𝓝 γo))) := by
  obtain ⟨p1, p2⟩ := TwoSidedGrowth.Balance.eq_33 M hM
  refine ⟨p1, p2, ?_, TSGHelp.part4 M hM⟩
  intro T x γ pm γb pmb h1 h2 hb
  rw [TwoSidedGrowth.Balance.lemma_5 M hM T x γ pm h1,
    TwoSidedGrowth.Balance.lemma_5 M hM T x γb pmb h2]
  have hT := h1.1
  obtain ⟨_, hpath, hγc, _, x', _, hder⟩ := h1
  obtain ⟨_, hpathb, hγbc, _, _⟩ := h2
  have hxc : ContinuousOn x (Set.Icc 0 T) := fun t ht => (hder t ht).1.continuousWithinAt
  have c1 := (TSGHelp.path_cont M hM T x γ hpath hγc hxc).2
  have c2 := (TSGHelp.path_cont M hM T x γb hpathb hγbc hxc).2
  have hmono : (∫ t in (0:ℝ)..T, Real.exp (-(M.ρ * t)) * G M (γ t) (x t)) ≤
      ∫ t in (0:ℝ)..T, Real.exp (-(M.ρ * t)) * G M (γb t) (x t) := by
    apply intervalIntegral.integral_mono_on hT
    · apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le hT]; exact c1
    · apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le hT]; exact c2
    · intro t ht
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact ((p2 (x t) (hpath t ht).1 (γb t) (hpathb t ht).2).2 (hb t ht)) (γ t) (hpath t ht).2
  linarith
