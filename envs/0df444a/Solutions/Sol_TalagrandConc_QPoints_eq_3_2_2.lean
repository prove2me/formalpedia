-- Prove2me | solution 1 for TalagrandConc.QPoints.eq_3_2_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:18:03.059316+00:00
-- url     : https://prove2.me/submissions/c24c981f-c220-4192-8c52-b27e2da257b5

import Mathlib
import Definitions.Def_TalagrandConc_QPoints_aConst



namespace TalagrandConc.QPoints

open Set

/-- The function `ψ(x) = x + q α x^{-1/α}`. -/
noncomputable def psiQ (q : ℕ) (α : ℝ) (x : ℝ) : ℝ := x + (q : ℝ) * α * x ^ (-(1 / α))

lemma psiQ_hasDerivAt (q : ℕ) (α : ℝ) (hα : 1 < α) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (psiQ q α) (1 - (q : ℝ) * x ^ (-(1 / α) - 1)) x := by
  have hα0 : α ≠ 0 := by positivity
  have h1 := Real.hasDerivAt_rpow_const (x := x) (p := -(1 / α)) (Or.inl hx.ne')
  have h2 := (hasDerivAt_id x).add (h1.const_mul ((q : ℝ) * α))
  refine h2.congr_deriv ?_
  field_simp
  ring

lemma psiQ_continuousOn (q : ℕ) (α : ℝ) (hα : 1 < α) {s : Set ℝ} (hs : ∀ x ∈ s, 0 < x) :
    ContinuousOn (psiQ q α) s :=
  fun x hx => (psiQ_hasDerivAt q α hα (hs x hx)).continuousAt.continuousWithinAt

/-- The turning point `x₀ = q^{α/(α+1)}`. -/
noncomputable def x0Q (q : ℕ) (α : ℝ) : ℝ := (q : ℝ) ^ (α / (α + 1))

lemma x0Q_pow (q : ℕ) (α : ℝ) (hα : 1 < α) (hq : 2 ≤ q) :
    x0Q q α ^ (1 + 1 / α) = q := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  unfold x0Q
  rw [← Real.rpow_mul hq0]
  have : α / (α + 1) * (1 + 1 / α) = 1 := by
    field_simp
  rw [this, Real.rpow_one]

lemma one_lt_x0Q (q : ℕ) (α : ℝ) (hα : 1 < α) (hq : 2 ≤ q) : 1 < x0Q q α := by
  unfold x0Q
  apply Real.one_lt_rpow
  · exact_mod_cast (by omega : 1 < q)
  · positivity

/-- Sign of the derivative. -/
lemma deriv_sign (q : ℕ) (α : ℝ) (hα : 1 < α) (hq : 2 ≤ q) {x : ℝ} (hx : 0 < x) :
    (1 - (q : ℝ) * x ^ (-(1 / α) - 1) < 0 ↔ x < x0Q q α) ∧
    (0 < 1 - (q : ℝ) * x ^ (-(1 / α) - 1) ↔ x0Q q α < x) := by
  have hβ : (0 : ℝ) < 1 + 1 / α := by positivity
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have e1 : x ^ (-(1 / α) - 1) = (x ^ (1 + 1 / α))⁻¹ := by
    rw [← Real.rpow_neg hx.le]
    congr 1
    ring
  have hxp : 0 < x ^ (1 + 1 / α) := Real.rpow_pos_of_pos hx _
  have hx0pos : 0 < x0Q q α := by
    have := one_lt_x0Q q α hα hq; linarith
  have key : x < x0Q q α ↔ x ^ (1 + 1 / α) < q := by
    rw [← x0Q_pow q α hα hq]
    exact (Real.rpow_lt_rpow_iff hx.le hx0pos.le hβ).symm
  have key2 : x0Q q α < x ↔ (q : ℝ) < x ^ (1 + 1 / α) := by
    rw [← x0Q_pow q α hα hq]
    exact (Real.rpow_lt_rpow_iff hx0pos.le hx.le hβ).symm
  rw [e1, key, key2]
  constructor
  · rw [sub_neg, ← div_eq_mul_inv, lt_div_iff₀ hxp, one_mul]
  · rw [sub_pos, ← div_eq_mul_inv, div_lt_iff₀ hxp, one_mul]

lemma psiQ_strictAntiOn (q : ℕ) (α : ℝ) (hα : 1 < α) (hq : 2 ≤ q) :
    StrictAntiOn (psiQ q α) (Icc 1 (x0Q q α)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact psiQ_continuousOn q α hα fun x hx => by linarith [hx.1]
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [(psiQ_hasDerivAt q α hα hx0).deriv]
    exact (deriv_sign q α hα hq hx0).1.2 hx.2

lemma psiQ_strictMonoOn (q : ℕ) (α : ℝ) (hα : 1 < α) (hq : 2 ≤ q) :
    StrictMonoOn (psiQ q α) (Ici (x0Q q α)) := by
  have h1 := one_lt_x0Q q α hα hq
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · exact psiQ_continuousOn q α hα fun x hx => by
      simp only [mem_Ici] at hx; linarith
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := by simp only [mem_Ioi] at hx; linarith
    rw [(psiQ_hasDerivAt q α hα hx0).deriv]
    exact (deriv_sign q α hα hq hx0).2.2 hx

lemma psiQ_one (q : ℕ) (α : ℝ) : psiQ q α 1 = 1 + (q : ℝ) * α := by
  simp [psiQ]

lemma self_le_psiQ (q : ℕ) (α : ℝ) (hα : 1 < α) {x : ℝ} (hx : 0 < x) : x ≤ psiQ q α x := by
  unfold psiQ
  have : 0 ≤ (q : ℝ) * α * x ^ (-(1 / α)) := by
    have := Real.rpow_nonneg hx.le (-(1 / α))
    positivity
  linarith

theorem eq_3_2_2_core (q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) :
    1 < aConst q α ∧
      aConst q α + (q : ℝ) * α * aConst q α ^ (-(1 / α)) = 1 + (q : ℝ) * α ∧
      ∀ x : ℝ, 1 < x → x + (q : ℝ) * α * x ^ (-(1 / α)) = 1 + (q : ℝ) * α →
        x = aConst q α := by
  set c : ℝ := 1 + (q : ℝ) * α with hc
  set x₀ := x0Q q α with hx₀
  have h1 := one_lt_x0Q q α hα hq
  have hanti := psiQ_strictAntiOn q α hα hq
  have hmono := psiQ_strictMonoOn q α hα hq
  have hψ1 : psiQ q α 1 = c := psiQ_one q α
  have hψx₀ : psiQ q α x₀ < c := by
    rw [← hψ1]
    exact hanti ⟨le_rfl, h1.le⟩ ⟨h1.le, le_rfl⟩ h1
  -- a root in `(x₀, ∞)`
  set M := max x₀ c with hM
  have hx₀M : x₀ ≤ M := le_max_left _ _
  have hψM : c ≤ psiQ q α M :=
    le_trans (le_max_right _ _) (self_le_psiQ q α hα (by linarith [le_max_left x₀ c]))
  obtain ⟨r, hrI, hr⟩ := intermediate_value_Icc hx₀M
    (psiQ_continuousOn q α hα fun x hx => by linarith [hx.1]) ⟨hψx₀.le, hψM⟩
  have hrx₀ : x₀ < r := by
    rcases eq_or_lt_of_le hrI.1 with h | h
    · rw [← h] at hr; linarith
    · exact h
  have hr1 : 1 < r := by linarith
  -- the set `S`
  set S : Set ℝ := {x : ℝ | 1 < x ∧ x + (q : ℝ) * α * x ^ (-(1 / α)) ≤ 1 + (q : ℝ) * α} with hS
  have hrS : r ∈ S := ⟨hr1, by change psiQ q α r ≤ c; rw [hr]⟩
  have hSle : ∀ x ∈ S, x ≤ r := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    change psiQ q α x ≤ c at hx2
    by_contra hcon
    push Not at hcon
    have : psiQ q α r < psiQ q α x := hmono (mem_Ici.2 hrx₀.le) (mem_Ici.2 (by linarith)) hcon
    linarith
  have haeq : aConst q α = r := by
    unfold aConst
    exact le_antisymm (csSup_le ⟨r, hrS⟩ hSle) (le_csSup ⟨r, hSle⟩ hrS)
  refine ⟨by rw [haeq]; exact hr1, by rw [haeq]; exact hr, ?_⟩
  intro x hx1 hx2
  rw [haeq]
  change psiQ q α x = c at hx2
  rcases lt_or_ge x x₀ with hlt | hge
  · exfalso
    have : psiQ q α x < psiQ q α 1 := hanti ⟨le_rfl, h1.le⟩ ⟨hx1.le, hlt.le⟩ hx1
    linarith
  · exact hmono.injOn (mem_Ici.2 hge) (mem_Ici.2 hrx₀.le) (by rw [hx2, hr])

end TalagrandConc.QPoints

open TalagrandConc.QPoints


theorem solution (q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) :
    1 < aConst q α ∧
      aConst q α + (q : ℝ) * α * aConst q α ^ (-(1 / α)) = 1 + (q : ℝ) * α ∧
      ∀ x : ℝ, 1 < x → x + (q : ℝ) * α * x ^ (-(1 / α)) = 1 + (q : ℝ) * α →
        x = aConst q α := by
  exact eq_3_2_2_core q hq α hα
