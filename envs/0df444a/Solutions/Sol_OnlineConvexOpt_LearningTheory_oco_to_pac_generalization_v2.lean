-- Prove2me | solution 1 for OnlineConvexOpt.LearningTheory.oco_to_pac_generalization_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:53:36.932737+00:00
-- url     : https://prove2.me/submissions/120b75a5-c6ff-4f86-9394-f254190dc18f

import Mathlib
import Definitions.Def_OnlineConvexOpt_LearningTheory_GeneralizationError
import Definitions.Def_OnlineConvexOpt_LearningTheory_AgnosticReduction
import Definitions.Def_OnlineConvexOpt_FirstOrder_Algorithm
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

set_option autoImplicit false

open MeasureTheory

/-- A convex function on `ℝ` with values in `[0,1]` is constant. -/
theorem f5ac0adb_bdd_convex_le (g : ℝ → ℝ) (hb : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hc : ConvexOn ℝ Set.univ g) (a b : ℝ) : g b ≤ g a := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hn1 : (1 : ℝ) ≤ n := by
    have : (0:ℝ) < 1 / ε := by positivity
    have h0 : (0:ℝ) < n := lt_trans this hn
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at h0
    · exact_mod_cast h
  have hnpos : (0:ℝ) < n := by linarith
  set x : ℝ := a + n * (b - a)
  have hcomb : (1 - 1 / (n:ℝ)) • a + (1 / (n:ℝ)) • x = b := by
    simp only [smul_eq_mul, x]; field_simp; ring
  have hle1 : 1 / (n:ℝ) ≤ 1 := by rw [div_le_one hnpos]; exact hn1
  have h1 : g ((1 - 1 / (n:ℝ)) • a + (1 / (n:ℝ)) • x) ≤
      (1 - 1 / (n:ℝ)) • g a + (1 / (n:ℝ)) • g x :=
    hc.2 (Set.mem_univ a) (Set.mem_univ x) (by linarith) (by positivity) (by ring)
  rw [hcomb] at h1
  simp only [smul_eq_mul] at h1
  have hxle := (hb x).2
  have hale := (hb a).1
  have hinv : 1 / (n:ℝ) < ε := by
    rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ hε] at hn; linarith
  have hp : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
  have k1 : 1 / (n:ℝ) * g x ≤ 1 / (n:ℝ) := by
    have := mul_le_mul_of_nonneg_left hxle hp; linarith
  have k2 : 0 ≤ 1 / (n:ℝ) * g a := mul_nonneg hp hale
  have k3 : (1 - 1 / (n:ℝ)) * g a = g a - 1 / (n:ℝ) * g a := by ring
  linarith

open MeasureTheory OnlineConvexOpt.LearningTheory in
theorem solution
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (H : Set E) (hHconv : Convex ℝ H) (pred : E → X → ℝ) (ℓ : ℝ → Y → ℝ)
    (hℓbdd : ∀ yhat y, 0 ≤ ℓ yhat y ∧ ℓ yhat y ≤ 1)
    (hℓconv : ∀ y, ConvexOn ℝ Set.univ (fun yhat => ℓ yhat y))
    (hpredaff : ∀ (x : X) (h₁ h₂ : E) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
      pred (a • h₁ + b • h₂) x = a * pred h₁ x + b * pred h₂ x)
    (hpred : Measurable (Function.uncurry pred))
    (hℓmeas : Measurable (Function.uncurry ℓ))
    (A : (ℕ → E → ℝ) → ℕ → E)
    (hAnonant : OnlineConvexOpt.FirstOrder.IsOnlineAlgorithm H A)
    (RegretBoundA : ℕ → ℝ)
    (hA : ∀ (T : ℕ) (f : ℕ → E → ℝ), 1 ≤ T →
      (∀ t, ConvexOn ℝ H (f t)) → (∀ t, ∀ x ∈ H, 0 ≤ f t x ∧ f t x ≤ 1) →
      OnlineConvexOpt.FirstOrder.RegretT H f (A f) T ≤ RegretBoundA T)
    (T : ℕ) (hT : 1 ≤ T)
    (samp : ℕ → Ω → X × Y) (h : ℕ → Ω → E) (hbar : Ω → E)
    (hrun : IsAgnosticReductionRun Prob D pred ℓ A T samp h hbar)
    (hhmeas : ∀ t, Measurable (h t)) (hhbar : Measurable hbar)
    (hstar : E) (hstar_mem : hstar ∈ H)
    (hstar_min : ∀ y ∈ H, GeneralizationError D pred ℓ hstar ≤ GeneralizationError D pred ℓ y)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ) ≤
      (Prob {ω | GeneralizationError D pred ℓ (hbar ω) ≤
        GeneralizationError D pred ℓ hstar + RegretBoundA T / T +
          Real.sqrt (8 * Real.log (2 / δ) / T)}).toReal := by
  have hconst : ∀ y, GeneralizationError D pred ℓ y = GeneralizationError D pred ℓ hstar := by
    intro y
    unfold GeneralizationError
    congr 1
    funext p
    exact le_antisymm
      (f5ac0adb_bdd_convex_le (fun yhat => ℓ yhat p.2) (fun yhat => hℓbdd yhat p.2) (hℓconv p.2) _ _)
      (f5ac0adb_bdd_convex_le (fun yhat => ℓ yhat p.2) (fun yhat => hℓbdd yhat p.2) (hℓconv p.2) _ _)
  have hR : 0 ≤ RegretBoundA T := by
    have := hA T (fun _ _ => 0) hT (fun _ => convexOn_const 0 hHconv)
      (fun _ _ _ => ⟨le_refl _, zero_le_one⟩)
    refine le_trans (le_of_eq ?_) this
    unfold OnlineConvexOpt.FirstOrder.RegretT
    rw [(Set.Nonempty.image_const ⟨hstar, hstar_mem⟩ _)]
    simp
  have hset : {ω | GeneralizationError D pred ℓ (hbar ω) ≤
        GeneralizationError D pred ℓ hstar + RegretBoundA T / T +
          Real.sqrt (8 * Real.log (2 / δ) / T)} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [hconst (hbar ω)]
    have : 0 ≤ RegretBoundA T / T := div_nonneg hR (Nat.cast_nonneg _)
    have := Real.sqrt_nonneg (8 * Real.log (2 / δ) / T)
    linarith
  rw [hset, measure_univ]
  simp
  linarith
