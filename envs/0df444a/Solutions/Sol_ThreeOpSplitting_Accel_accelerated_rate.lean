-- Prove2me | solution 1 for ThreeOpSplitting.Accel.accelerated_rate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:45:10.908217+00:00
-- url     : https://prove2.me/submissions/2b014c9d-8e22-4c0e-909c-de820bc72787

import Theorems.Thm_ThreeOpSplitting_Accel_prop_3_1_part1
import Theorems.Thm_ThreeOpSplitting_Accel_prop_3_1_part2
import Theorems.Thm_ThreeOpSplitting_Accel_stepsize_limit_part1
import Theorems.Thm_ThreeOpSplitting_Accel_stepsize_limit_part2
import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Accel_Algorithm3
import Definitions.Def_ThreeOpSplitting_Accel_Stepsizes

open InnerProductSpace Filter Topology


namespace ThreeOpSplitting.Accel

/-- Generic Lyapunov argument giving an `O(1/(k+1)²)` bound. -/
lemma lyap_rate (X V c : ℕ → ℝ) (hX : ∀ k, 0 ≤ X k) (hV : ∀ k, 0 ≤ V k)
    (hc : ∀ k : ℕ, 1 ≤ k → 0 < c k)
    (hdec : ∀ k : ℕ, 1 ≤ k → c (k + 1) * X (k + 1) + V (k + 1) ≤ c k * X k + V k)
    (M : ℝ) (hM : ∀ k : ℕ, 1 ≤ k → ((k : ℝ) + 1) ^ 2 / c k ≤ M) :
    ∃ K : ℝ, ∀ k : ℕ, X k ≤ K / ((k : ℝ) + 1) ^ 2 := by
  set Φ := fun k => c k * X k + V k with hΦ
  have hmono : ∀ k : ℕ, 1 ≤ k → Φ k ≤ Φ 1 := by
    intro k hk
    induction k with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; exact le_rfl
      · exact (hdec j h).trans (ih h)
  have hΦ1 : 0 ≤ Φ 1 := by
    simp only [hΦ]; nlinarith [hc 1 le_rfl, hX 1, hV 1]
  refine ⟨max (Φ 1 * M) (X 0), fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp
  · have hck := hc k h
    have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
    have h1 : c k * X k ≤ Φ 1 := by
      have := hmono k h; simp only [hΦ] at this ⊢; linarith [hV k]
    have h2 : X k ≤ Φ 1 / c k := by rw [le_div_iff₀ hck]; linarith
    have h3 : 1 / c k ≤ M / ((k : ℝ) + 1) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have := hM k h
      rw [div_le_iff₀ hck] at this
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hck]; linarith
    calc X k ≤ Φ 1 / c k := h2
      _ = Φ 1 * (1 / c k) := by ring
      _ ≤ Φ 1 * (M / ((k : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left h3 hΦ1
      _ = Φ 1 * M / ((k : ℝ) + 1) ^ 2 := by ring
      _ ≤ max (Φ 1 * M) (X 0) / ((k : ℝ) + 1) ^ 2 :=
        div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)

/-! Stepsize facts for rule (3.6). -/

noncomputable def nextStep1 (μB μC η g : ℝ) : ℝ :=
  (-2 * g ^ 2 * μC * η + Real.sqrt ((2 * g ^ 2 * μC * η) ^ 2 + 4 * (1 + 2 * g * μB) * g ^ 2))
    / (2 * (1 + 2 * g * μB))

lemma steps1_succ' (μB μC η γ0 : ℝ) (k : ℕ) :
    stepsPart1 μB μC η γ0 (k + 1) = nextStep1 μB μC η (stepsPart1 μB μC η γ0 k) := rfl

lemma step1_facts' (μB μC η g : ℝ) (ha : 0 < μC * η) (hb : 0 ≤ μB) (hg : 0 < g) :
    0 < nextStep1 μB μC η g ∧
      (1 + 2 * g * μB) * nextStep1 μB μC η g ^ 2 + 2 * g ^ 2 * (μC * η) * nextStep1 μB μC η g
        = g ^ 2 := by
  have hc : 0 < 1 + 2 * g * μB := by positivity
  have hΔ0 : 0 ≤ (2 * g ^ 2 * μC * η) ^ 2 + 4 * (1 + 2 * g * μB) * g ^ 2 := by positivity
  have hsq := Real.sq_sqrt hΔ0
  have hdef : 2 * (1 + 2 * g * μB) * nextStep1 μB μC η g = -2 * g ^ 2 * μC * η +
      Real.sqrt ((2 * g ^ 2 * μC * η) ^ 2 + 4 * (1 + 2 * g * μB) * g ^ 2) := by
    rw [nextStep1, mul_div_cancel₀ _ (by positivity)]
  have hgt : 2 * g ^ 2 * μC * η <
      Real.sqrt ((2 * g ^ 2 * μC * η) ^ 2 + 4 * (1 + 2 * g * μB) * g ^ 2) := by
    rw [Real.lt_sqrt (by nlinarith [sq_nonneg g])]
    have : 0 < 4 * (1 + 2 * g * μB) * g ^ 2 := by positivity
    linarith
  set x := nextStep1 μB μC η g
  set s := Real.sqrt ((2 * g ^ 2 * μC * η) ^ 2 + 4 * (1 + 2 * g * μB) * g ^ 2)
  refine ⟨?_, ?_⟩
  · have : 0 < 2 * (1 + 2 * g * μB) * x := by rw [hdef]; linarith
    have h2 : 0 < 2 * (1 + 2 * g * μB) := by positivity
    exact pos_of_mul_pos_right this h2.le
  · have hs : s = 2 * (1 + 2 * g * μB) * x + 2 * g ^ 2 * μC * η := by linarith
    rw [hs] at hsq
    have h5 : (1 + 2 * g * μB) * ((1 + 2 * g * μB) * x ^ 2 + 2 * g ^ 2 * (μC * η) * x - g ^ 2)
        = 0 := by linear_combination hsq / 4
    rcases mul_eq_zero.1 h5 with h | h
    · linarith
    · linarith

/-! Stepsize facts for rule (3.7). -/

lemma steps2_succ' (μB LC γ0 : ℝ) (k : ℕ) :
    stepsPart2 μB LC γ0 (k + 1) = stepsPart2 μB LC γ0 k /
      Real.sqrt (1 + 2 * stepsPart2 μB LC γ0 k * (μB - stepsPart2 μB LC γ0 k * LC ^ 2 / 2)) := rfl

lemma steps2_bounds' (μB LC γ0 : ℝ) (hμB : 0 < μB) (hLC : 0 < LC) (hγ0 : 0 < γ0)
    (hγ0' : γ0 < 2 * μB / LC ^ 2) (k : ℕ) :
    0 < stepsPart2 μB LC γ0 k ∧ stepsPart2 μB LC γ0 k ≤ γ0 := by
  induction k with
  | zero => exact ⟨hγ0, le_rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    set g := stepsPart2 μB LC γ0 k
    have hgL : g * LC ^ 2 < 2 * μB := by
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < LC ^ 2)).1 (lt_of_le_of_lt h2 hγ0')
      linarith
    have hD : 1 < 1 + 2 * g * (μB - g * LC ^ 2 / 2) := by nlinarith
    have hs : 1 < Real.sqrt (1 + 2 * g * (μB - g * LC ^ 2 / 2)) := by
      rw [Real.lt_sqrt zero_le_one, one_pow]; exact hD
    rw [steps2_succ']
    refine ⟨div_pos h1 (by linarith), ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith

/-- A convergent sequence of the form `(k+1) γ_k` gives bounded `((k+1) γ_k)^2 / d_k` when
`d_k → 1`. -/
lemma bdd_of_tendsto (s : ℕ → ℝ) (l : ℝ) (hs : Tendsto s atTop (𝓝 l)) :
    ∃ M, ∀ k, s k ≤ M := by
  obtain ⟨M, hM⟩ := hs.bddAbove_range
  exact ⟨M, fun k => hM ⟨k, rfl⟩⟩

theorem accelerated_rate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (JA JB : ℝ → H → H) (μB : ℝ) (xA0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hμB : 0 ≤ μB) (hBs : IsStronglyMonotoneOp μB B)
    (hJA : IsResolventFamily A JA) (hJB : IsResolventFamily B JB) :
    (∀ (C : H → H) (β μC η γ0 : ℝ),
      0 < β → IsCocoercive β C → 0 < μC → IsStronglyMonotoneFun μC C →
      0 < η → η < 1 → 0 < γ0 → γ0 < 2 * β * (1 - η) →
      ∀ xs ∈ zer (opSum A B C), ∃ K : ℝ, ∀ k : ℕ,
        ‖(accelIter JA JB C (stepsPart1 μB μC η γ0) xA0 k).xB - xs‖ ^ 2
          ≤ K / ((k : ℝ) + 1) ^ 2) ∧
    (∀ (C : H → H) (LC γ0 : ℝ),
      IsMonotoneFun C → 0 < LC → IsLipschitzOp LC C →
      0 < μB → 0 < γ0 → γ0 < 2 * μB / LC ^ 2 →
      ∀ xs ∈ zer (opSum A B C), ∃ K : ℝ, ∀ k : ℕ,
        ‖(accelIter JA JB C (stepsPart2 μB LC γ0) xA0 k).xB - xs‖ ^ 2
          ≤ K / ((k : ℝ) + 1) ^ 2) := by
  constructor
  · intro C β μC η γ0 hβ hC hμC hCs hη0 hη1 hγ0 hγ0' xs hxs
    obtain ⟨uAs, huA, uBs, huB, h0⟩ := hxs
    have hsum : uAs + uBs + C xs = 0 := h0.symm
    have ha : 0 < μC * η := mul_pos hμC hη0
    set γ := stepsPart1 μB μC η γ0 with hγdef
    have hpos : ∀ k, 0 < γ k := by
      intro k
      induction k with
      | zero => exact hγ0
      | succ k ih => rw [hγdef, steps1_succ']; exact (step1_facts' μB μC η _ ha hμB ih).1
    have hrel : ∀ k, (1 + 2 * γ k * μB) * γ (k + 1) ^ 2 + 2 * γ k ^ 2 * (μC * η) * γ (k + 1)
        = γ k ^ 2 := by
      intro k
      rw [hγdef, steps1_succ']; exact (step1_facts' μB μC η _ ha hμB (hpos k)).2
    have hdecr : ∀ k, γ (k + 1) ≤ γ k := by
      intro k
      by_contra hlt
      push Not at hlt
      have h1 := hpos k
      have h2 := hpos (k + 1)
      have := hrel k
      have e1 : γ k ^ 2 < γ (k + 1) ^ 2 := by nlinarith
      have e2 : 0 ≤ 2 * γ k * μB * γ (k + 1) ^ 2 := by positivity
      have e3 : 0 < 2 * γ k ^ 2 * (μC * η) * γ (k + 1) := by positivity
      nlinarith
    have hle0 : ∀ k, γ k ≤ γ0 := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih => exact (hdecr k).trans ih
    have hγc : ∀ j, 0 < γ j ∧ γ j < 2 * (1 - η) * β := by
      intro j
      refine ⟨hpos j, ?_⟩
      have := hle0 j
      have e : 2 * β * (1 - η) = 2 * (1 - η) * β := by ring
      linarith
    -- positivity of 1 - 2 a γ_{k+1}
    have hq : ∀ j, (1 - 2 * (μC * η) * γ (j + 1)) * γ j ^ 2 =
        (1 + 2 * γ j * μB) * γ (j + 1) ^ 2 := by
      intro j; have := hrel j; linarith
    have hqpos : ∀ k : ℕ, 1 ≤ k → 0 < 1 - 2 * (μC * η) * γ k := by
      intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h1 := hpos j
      have h2 := hpos (j + 1)
      have hr := hq j
      have hr' : 0 < (1 + 2 * γ j * μB) * γ (j + 1) ^ 2 := by positivity
      rw [← hr] at hr'
      exact pos_of_mul_pos_left hr' (sq_nonneg _)
    set c : ℕ → ℝ := fun k => (1 - 2 * (μC * η) * γ k) / γ k ^ 2 with hcdef
    set X : ℕ → ℝ := fun k => ‖(accelIter JA JB C γ xA0 k).xB - xs‖ ^ 2 with hXdef
    set V : ℕ → ℝ := fun k => ‖(accelIter JA JB C γ xA0 k).uB - uBs‖ ^ 2 with hVdef
    -- boundedness
    have hlim := stepsize_limit_part1 μB μC η γ0 hμB hμC hη0 hη1 hγ0
    have hγ0lim : Tendsto γ atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1
          tendsto_natCast_atTop_atTop)
      have := hlim.mul h1
      rw [mul_zero] at this
      refine this.congr (fun k => ?_)
      have : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      try rfl
    have hslim : Tendsto (fun k : ℕ => (((k : ℝ) + 1) * γ k) ^ 2 / (1 - 2 * (μC * η) * γ k))
        atTop (𝓝 ((1 / (μC * η + μB)) ^ 2 / (1 - 2 * (μC * η) * 0))) :=
      (hlim.pow 2).div (tendsto_const_nhds.sub (hγ0lim.const_mul _)) (by simp)
    obtain ⟨M, hM⟩ := bdd_of_tendsto _ _ hslim
    have hmain := lyap_rate X V c (fun k => sq_nonneg _) (fun k => sq_nonneg _)
      (fun k hk => div_pos (hqpos k hk) (pow_pos (hpos k) 2)) ?_ M ?_
    · exact hmain
    · intro k hk
      have hp := prop_3_1_part1 A B C JA JB μB μC β η γ xA0 xs uAs uBs hA hB hμB hBs hβ hC hμC
        hCs hη0 hη1 hγc hJA hJB huA huB hsum k hk
      have hnn : 0 ≤ (1 - γ k / (2 * (1 - η) * β)) *
          ‖(accelIter JA JB C γ xA0 k).xA - (accelIter JA JB C γ xA0 k).xB‖ ^ 2 := by
        apply mul_nonneg _ (sq_nonneg _)
        have h1 := (hγc k).2
        have h2 : 0 < 2 * (1 - η) * β := by
          have : 0 < 1 - η := by linarith
          positivity
        rw [sub_nonneg, div_le_one h2]; exact h1.le
      have hgk := hpos k
      have hck1 : c (k + 1) = (1 + 2 * γ k * μB) / γ k ^ 2 := by
        simp only [hcdef]
        have := hq k
        have h2 := hpos (k + 1)
        rw [div_eq_div_iff (by positivity) (by positivity)]
        linarith
      rw [hck1]
      simp only [hcdef, hXdef, hVdef]
      have hg2 : 0 < γ k ^ 2 := by positivity
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_add' _ _ _ hg2.ne',
        div_add' _ _ _ hg2.ne', div_le_div_iff_of_pos_right hg2]
      have e : 2 * γ k * μC * η = 2 * (μC * η) * γ k := by ring
      rw [e] at hp
      linarith
    · intro k hk
      have hqk := hqpos k hk
      have hgk := hpos k
      have := hM k
      simp only [hcdef]
      rw [div_div_eq_mul_div]
      calc ((k : ℝ) + 1) ^ 2 * γ k ^ 2 / (1 - 2 * (μC * η) * γ k)
          = (((k : ℝ) + 1) * γ k) ^ 2 / (1 - 2 * (μC * η) * γ k) := by ring
        _ ≤ M := this
  · intro C LC γ0 hCm hLC hCL hμBp hγ0 hγ0' xs hxs
    obtain ⟨uAs, huA, uBs, huB, h0⟩ := hxs
    have hsum : uAs + uBs + C xs = 0 := h0.symm
    set γ := stepsPart2 μB LC γ0 with hγdef
    have hb := steps2_bounds' μB LC γ0 hμBp hLC hγ0 hγ0'
    have hpos : ∀ k, 0 < γ k := fun k => (hb k).1
    have hD : ∀ k, 0 < 1 + 2 * γ k * (μB - γ k * LC ^ 2 / 2) := by
      intro k
      have hgL : γ k * LC ^ 2 < 2 * μB := by
        have := (lt_div_iff₀ (by positivity : (0:ℝ) < LC ^ 2)).1
          (lt_of_le_of_lt (hb k).2 hγ0')
        linarith
      nlinarith [hpos k]
    have hsq : ∀ k, γ (k + 1) ^ 2 = γ k ^ 2 / (1 + 2 * γ k * (μB - γ k * LC ^ 2 / 2)) := by
      intro k
      rw [hγdef, steps2_succ', ← hγdef, div_pow, Real.sq_sqrt (hD k).le]
    set c : ℕ → ℝ := fun k => 1 / γ k ^ 2 + LC ^ 2 with hcdef
    set X : ℕ → ℝ := fun k => ‖(accelIter JA JB C γ xA0 k).xB - xs‖ ^ 2 with hXdef
    set V : ℕ → ℝ := fun k => ‖(accelIter JA JB C γ xA0 k).uB - uBs‖ ^ 2 with hVdef
    have hlim := stepsize_limit_part2 μB LC γ0 hμBp hLC hγ0 hγ0'
    obtain ⟨M, hM⟩ := bdd_of_tendsto _ _ (hlim.pow 2)
    have hmain := lyap_rate X V c (fun k => sq_nonneg _) (fun k => sq_nonneg _)
      (fun k _ => by simp only [hcdef]; have := hpos k; positivity) ?_ M ?_
    · exact hmain
    · intro k hk
      have hp := prop_3_1_part2 A B C JA JB μB LC γ xA0 xs uAs uBs hA hB hμBp hBs hCm hLC.le hCL
        hpos hJA hJB huA huB hsum k hk
      have hgk := hpos k
      have hg2 : 0 < γ k ^ 2 := by positivity
      have hck1 : c (k + 1) = (1 + 2 * γ k * (μB - γ k * LC ^ 2 / 2)) / γ k ^ 2 + LC ^ 2 := by
        simp only [hcdef]
        rw [hsq k, one_div_div]
      rw [hck1]
      simp only [hcdef, hXdef, hVdef]
      have e1 : ((1 + 2 * γ k * (μB - γ k * LC ^ 2 / 2)) / γ k ^ 2 + LC ^ 2) =
          ((1 + 2 * γ k * (μB - γ k * LC ^ 2 / 2)) + γ k ^ 2 * LC ^ 2) / γ k ^ 2 := by
        field_simp
      have e2 : (1 / γ k ^ 2 + LC ^ 2) = (1 + γ k ^ 2 * LC ^ 2) / γ k ^ 2 := by
        field_simp
      rw [e1, e2, div_mul_eq_mul_div, div_mul_eq_mul_div, div_add' _ _ _ hg2.ne',
        div_add' _ _ _ hg2.ne', div_le_div_iff_of_pos_right hg2]
      linarith
    · intro k hk
      have hgk := hpos k
      have := hM k
      simp only [hcdef]
      have hc1 : 1 / γ k ^ 2 ≤ 1 / γ k ^ 2 + LC ^ 2 := by nlinarith [sq_nonneg LC]
      calc ((k : ℝ) + 1) ^ 2 / (1 / γ k ^ 2 + LC ^ 2)
          ≤ ((k : ℝ) + 1) ^ 2 / (1 / γ k ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hc1
        _ = (((k : ℝ) + 1) * γ k) ^ 2 := by field_simp
        _ ≤ M := this

end ThreeOpSplitting.Accel

open ThreeOpSplitting.Accel

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (JA JB : ℝ → H → H) (μB : ℝ) (xA0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hμB : 0 ≤ μB) (hBs : IsStronglyMonotoneOp μB B)
    (hJA : IsResolventFamily A JA) (hJB : IsResolventFamily B JB) :
    (∀ (C : H → H) (β μC η γ0 : ℝ),
      0 < β → IsCocoercive β C → 0 < μC → IsStronglyMonotoneFun μC C →
      0 < η → η < 1 → 0 < γ0 → γ0 < 2 * β * (1 - η) →
      ∀ xs ∈ zer (opSum A B C), ∃ K : ℝ, ∀ k : ℕ,
        ‖(accelIter JA JB C (stepsPart1 μB μC η γ0) xA0 k).xB - xs‖ ^ 2
          ≤ K / ((k : ℝ) + 1) ^ 2) ∧
    (∀ (C : H → H) (LC γ0 : ℝ),
      IsMonotoneFun C → 0 < LC → IsLipschitzOp LC C →
      0 < μB → 0 < γ0 → γ0 < 2 * μB / LC ^ 2 →
      ∀ xs ∈ zer (opSum A B C), ∃ K : ℝ, ∀ k : ℕ,
        ‖(accelIter JA JB C (stepsPart2 μB LC γ0) xA0 k).xB - xs‖ ^ 2
          ≤ K / ((k : ℝ) + 1) ^ 2) := by
  exact accelerated_rate A B JA JB μB xA0 hA hB hμB hBs hJA hJB
