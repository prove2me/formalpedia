-- Prove2me | solution 1 for PeriodicMAB.Upper.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T00:32:18.77956+00:00
-- url     : https://prove2.me/submissions/9496a5d1-2592-44ed-99be-3159eda2b2e5

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral
import Definitions.Def_PeriodicMAB_Upper_Policy

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
open PeriodicMAB.Upper

/-- `x ↦ (A + log x) log x` is concave on `[1, ∞)` when `A ≥ 2`. -/
lemma pmab16_concave (A : ℝ) (hA : 2 ≤ A) :
    ConcaveOn ℝ (Set.Ici 1) (fun x => (A + Real.log x) * Real.log x) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici 1)
    (f' := fun x => (A + 2 * Real.log x) * x⁻¹)
    (f'' := fun x => 2 * x⁻¹ * x⁻¹ + (A + 2 * Real.log x) * (-(x ^ 2)⁻¹))
  · apply ContinuousOn.mul
    · exact continuousOn_const.add (Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_Ici] at hx; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith))
    · exact Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_Ici] at hx; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith)
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : x ≠ 0 := by simp only [Set.mem_Ioi] at hx; linarith
    have h1 : HasDerivAt (fun x => (A + Real.log x) * Real.log x) _ x :=
      ((Real.hasDerivAt_log hx0).const_add A).mul (Real.hasDerivAt_log hx0)
    exact h1.hasDerivWithinAt.congr_deriv (by ring)
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : x ≠ 0 := by simp only [Set.mem_Ioi] at hx; linarith
    have h1 := (((Real.hasDerivAt_log hx0).const_mul 2).const_add A).mul (hasDerivAt_inv hx0)
    apply HasDerivAt.hasDerivWithinAt
    exact h1
  · intro x hx
    rw [interior_Ici] at hx
    simp only [Set.mem_Ioi] at hx
    have hx0 : 0 < x := by linarith
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx.le
    have : 2 * x⁻¹ * x⁻¹ + (A + 2 * Real.log x) * (-(x ^ 2)⁻¹) = (2 - A - 2 * Real.log x) / x ^ 2 := by
      field_simp; ring
    rw [this]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    linarith

lemma pmab16_jensen {ι : Type*} (I : Finset ι) (C : ι → ℝ) (A T : ℝ) (hA : 2 ≤ A)
    (hC : ∀ i ∈ I, 1 ≤ C i) (hsum : ∑ i ∈ I, C i ≤ T) (hI : 0 < I.card) :
    ∑ i ∈ I, (A + Real.log (C i)) * Real.log (C i) ≤
      (I.card : ℝ) * ((A + Real.log (T / I.card)) * Real.log (T / I.card)) := by
  set m : ℝ := (I.card : ℝ) with hm
  have hm0 : 0 < m := by rw [hm]; exact_mod_cast hI
  have hJ := (pmab16_concave A hA).le_map_sum (t := I) (w := fun _ => 1 / m) (p := C)
    (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul, ← hm]; field_simp)
    (fun i hi => hC i hi)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  set f := fun x : ℝ => (A + Real.log x) * Real.log x with hf
  have hmean1 : 1 ≤ 1 / m * ∑ i ∈ I, C i := by
    have : m ≤ ∑ i ∈ I, C i := by
      calc m = ∑ _i ∈ I, (1 : ℝ) := by rw [hm]; simp
        _ ≤ ∑ i ∈ I, C i := Finset.sum_le_sum hC
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hm0]; linarith
  have hmono : f (1 / m * ∑ i ∈ I, C i) ≤ f (T / m) := by
    have h2 : 1 / m * ∑ i ∈ I, C i ≤ T / m := by
      rw [one_div, ← div_eq_inv_mul]; exact div_le_div_of_nonneg_right hsum hm0.le
    have hl1 : 0 ≤ Real.log (1 / m * ∑ i ∈ I, C i) := Real.log_nonneg hmean1
    have hl2 := Real.log_le_log (by linarith) h2
    simp only [hf]
    apply mul_le_mul (by linarith) hl2 hl1 (by linarith)
  have : 1 / m * ∑ i ∈ I, f (C i) ≤ f (T / m) := le_trans hJ hmono
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm0] at this
  simp only [hf] at this
  linarith

lemma pmab16_harmonic : ∀ m : ℕ, ∑ j ∈ Ico 2 (m + 1), (1 / (j : ℝ)) ≤ Real.log m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp
    rw [Finset.sum_Ico_succ_top (by omega), Nat.cast_add, Nat.cast_one]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hpos
    have key : 1 / ((m : ℝ) + 1) ≤ Real.log (m + 1) - Real.log m := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.add_one_le_exp (-(1 / ((m : ℝ) + 1)))
      have h2 : Real.exp (1 / ((m : ℝ) + 1)) ≤ (m + 1) / m := by
        have h4 : (m : ℝ) / (m + 1) ≤ Real.exp (-(1 / ((m : ℝ) + 1))) := by
          have : -(1 / ((m : ℝ) + 1)) + 1 = m / (m + 1) := by field_simp; ring
          linarith
        have h5 : Real.exp (1 / ((m : ℝ) + 1)) = 1 / Real.exp (-(1 / ((m : ℝ) + 1))) := by
          rw [Real.exp_neg]; field_simp
        rw [h5]
        calc 1 / Real.exp (-(1 / ((m : ℝ) + 1))) ≤ 1 / ((m : ℝ) / (m + 1)) :=
              one_div_le_one_div_of_le (by positivity) h4
          _ = (m + 1) / m := by rw [one_div_div]
      rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
      exact h2
    linarith

section Struct
variable {K : ℕ} [NeZero K] (σ δ : ℝ) (T n : ℕ) (Phat : Fin K → ℕ) (Y : Fin K → ℕ → ℝ)

lemma pmab16_runHist_length : ∀ m, (runHist σ δ T n Phat Y m).length = m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => simp [runHist, ih]

lemma pmab16_runHist_get : ∀ m j, 1 ≤ j → j ≤ m →
    (runHist σ δ T n Phat Y m)[j - 1]? = some (decisionAt σ δ T n Phat Y j) := by
  intro m
  induction m with
  | zero => intro j h1 h2; omega
  | succ m ih =>
    intro j h1 h2
    rw [runHist]
    rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · rw [List.getElem?_append_left (by rw [pmab16_runHist_length]; omega)]
      exact ih j h1 (by omega)
    · have hj' : j = m + 1 := by omega
      subst hj'
      rw [List.getElem?_append_right (by rw [pmab16_runHist_length]; omega)]
      simp [pmab16_runHist_length, decisionAt]

lemma pmab16_armAt (t j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ t - 1) :
    armAt (runHist σ δ T n Phat Y (t - 1)) j = some (policy σ δ T n Phat Y j) := by
  unfold armAt
  rw [pmab16_runHist_get σ δ T n Phat Y (t - 1) j hj1 hj]
  rfl

lemma pmab16_tagAt (t j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ t - 1) :
    tagAt (runHist σ δ T n Phat Y (t - 1)) j = some (decisionAt σ δ T n Phat Y j).2 := by
  unfold tagAt
  rw [pmab16_runHist_get σ δ T n Phat Y (t - 1) j hj1 hj]
  rfl

/-- `Ψ^(s)(t)` in terms of the global records. -/
lemma pmab16_psiSet (s t : ℕ) :
    psiSet (runHist σ δ T n Phat Y (t - 1)) n s t =
      (Icc (n * K + 1) (t - 1)).filter (fun j => (decisionAt σ δ T n Phat Y j).2 = (s, true)) := by
  unfold psiSet
  apply Finset.filter_congr
  intro j hj
  rw [Finset.mem_Icc] at hj
  rw [pmab16_tagAt σ δ T n Phat Y t j (by omega) hj.2]
  simp

/-- counts in terms of the global records. -/
lemma pmab16_count (k : Fin K) (t : ℕ) (X : Finset ℕ) (hX : X ⊆ Icc 1 (t - 1)) :
    count Phat (runHist σ δ T n Phat Y (t - 1)) k t X =
      (X.filter (fun j => policy σ δ T n Phat Y j = k ∧ j % Phat k = t % Phat k)).card := by
  unfold count
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_Icc.mp (hX hj)
  rw [pmab16_armAt σ δ T n Phat Y t j hj'.1 hj'.2]
  simp [Nat.ModEq]

lemma pmab16_stageOne (j : ℕ) (hj : j ≤ n * K) :
    policy σ δ T n Phat Y j = stageOneArm n j := by
  unfold policy decisionAt decision
  rw [if_pos hj]

end Struct

lemma pmab16_term (σ δ D c u : ℝ) (hσ : 0 ≤ σ) (hδ : 0 < δ) (hD : δ ≤ D) (hc : 1 ≤ c)
    (hcu : c ≤ u) :
    c / u * Real.sqrt (4 * σ ^ 2 / c * Real.log (D * c / δ)) ≤
      2 * σ * Real.sqrt (Real.log (D * u / δ) / u) := by
  have hc0 : 0 < c := by linarith
  have hu0 : 0 < u := by linarith
  have hD0 : 0 < D := by linarith
  have hDc : 1 ≤ D * c / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  have hl0 : 0 ≤ Real.log (D * c / δ) := Real.log_nonneg hDc
  have hl1 : Real.log (D * c / δ) ≤ Real.log (D * u / δ) :=
    Real.log_le_log (by positivity) (by gcongr)
  have lhs : c / u * Real.sqrt (4 * σ ^ 2 / c * Real.log (D * c / δ)) =
      Real.sqrt (4 * σ ^ 2 * (c * Real.log (D * c / δ) / u ^ 2)) := by
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ c / u), ← Real.sqrt_mul (by positivity)]
    congr 1; field_simp
  have rhs : 2 * σ * Real.sqrt (Real.log (D * u / δ) / u) =
      Real.sqrt (4 * σ ^ 2 * (u * Real.log (D * u / δ) / u ^ 2)) := by
    rw [Real.sqrt_mul (by positivity), show (4 : ℝ) * σ ^ 2 = (2 * σ) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    congr 2; field_simp
  rw [lhs, rhs]
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul hcu hl1 hl0 hu0.le

/-- Every phase of every arm is sampled at least twice in stage one. -/
lemma pmab16_stage_two {K : ℕ} [NeZero K] (σ δ : ℝ) (T n : ℕ) (Phat : Fin K → ℕ)
    (Y : Fin K → ℕ → ℝ) (P : Fin K → ℕ) (k : Fin K) (p : ℕ) (hp : p < P k)
    (hn : 2 * P k ≤ n) :
    2 ≤ ((psiBar n K).filter (fun j => policy σ δ T n Phat Y j = k ∧ j % P k = p)).card := by
  set q := P k with hq
  have hq0 : 0 < q := by omega
  set base := n * (k : ℕ) + 1 with hbase
  set x := base + q - 1 - p with hx
  set m := x / q with hm
  have h1 : q * m ≤ x := Nat.mul_div_le x q
  have h2 : x < q * m + q := by
    have := Nat.lt_div_mul_add (a := x) hq0
    rw [← hm] at this
    linarith [mul_comm q m]
  set y := q * m with hy
  have hk : (k : ℕ) < K := k.2
  have hnk : n * (k : ℕ) + n ≤ n * K := by
    have : n * ((k : ℕ) + 1) ≤ n * K := Nat.mul_le_mul_left n hk
    linarith [mul_add n (k : ℕ) 1]
  have hmem : ∀ j, base ≤ j → j ≤ n * (k : ℕ) + n → j % q = p →
      j ∈ (psiBar n K).filter (fun j => policy σ δ T n Phat Y j = k ∧ j % P k = p) := by
    intro j hj1 hj2 hjp
    rw [Finset.mem_filter, psiBar, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_, hjp⟩
    rw [pmab16_stageOne σ δ T n Phat Y j (by omega), stageOneArm]
    have hdiv : (j - 1) / n = k := by
      apply Nat.div_eq_of_lt_le
      · rw [mul_comm]; omega
      · rw [add_mul, one_mul, mul_comm]; omega
    rw [dif_pos (by rw [hdiv]; exact hk)]
    ext; exact hdiv
  have hj1p : (p + y) % q = p := by
    rw [hy, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hp
  have hj2p : (p + y + q) % q = p := by
    rw [Nat.add_mod_right]; exact hj1p
  have hA := hmem (p + y) (by omega) (by omega) hj1p
  have hB := hmem (p + y + q) (by omega) (by omega) hj2p
  have : ({p + y, p + y + q} : Finset ℕ) ⊆
      (psiBar n K).filter (fun j => policy σ δ T n Phat Y j = k ∧ j % P k = p) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact hA
    · exact hB
  have hc := Finset.card_le_card this
  rw [Finset.card_pair (by omega)] at hc
  exact hc

set_option maxHeartbeats 2000000 in
theorem solution (σ : ℝ≥0) (hσ : 0 < σ) {K : ℕ} [NeZero K] (Tper : Fin K → ℕ) (T n g : ℕ)
    (δ : ℝ) (hTper : ∀ k, 0 < Tper k) (hA3 : Assumption3 T n g Tper) (hnK : n * K ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) (Y : Fin K → ℕ → ℝ) :
    ∀ s ∈ Icc 1 (Nat.log 2 T),
      ∑ t ∈ psiAt σ δ T n Tper Y s T, wAt σ δ T n Tper Y s (policy σ δ T n Tper Y t) t ≤
        4 * σ * Real.sqrt ((psiAt σ δ T n Tper Y s T).card * effArms Tper *
          Real.log (8 * T / δ) * Real.log (T / effArms Tper)) := by
  intro s _
  have hσR : (0 : ℝ) ≤ σ := σ.2
  set pol := policy (σ : ℝ) δ T n Tper Y with hpol
  set dec := decisionAt (σ : ℝ) δ T n Tper Y with hdec
  set Ψ := psiAt (σ : ℝ) δ T n Tper Y s T with hΨdef
  have hΨ : Ψ = (Icc (n * K + 1) (T - 1)).filter (fun j => (dec j).2 = (s, true)) :=
    pmab16_psiSet (σ : ℝ) δ T n Tper Y s T
  set Ψt := fun t => (Icc (n * K + 1) (t - 1)).filter (fun j => (dec j).2 = (s, true)) with hΨt
  set Sset := fun t => (Ψt t ∪ psiBar n K).filter
    (fun j => pol j = pol t ∧ j % Tper (pol t) = t % Tper (pol t)) with hSset
  set cu := fun t => ((Sset t).card : ℝ) with hcu
  set d : ℝ := (effArms Tper : ℝ) with hd
  -- basic facts
  have hKpos : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have h2T : ∀ k, 2 * Tper k ≤ n := by
    intro k
    obtain ⟨_, hg2, _, hTk⟩ := hA3
    have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
    have h1 := hTk k
    have : (Tper k : ℝ) * (2 * g) < n := by
      rwa [lt_div_iff₀ (by positivity)] at h1
    have : (2 * Tper k : ℝ) < n := by nlinarith [(by positivity : (0:ℝ) ≤ Tper k)]
    exact_mod_cast this.le
  have hd1 : (1 : ℝ) ≤ d := by
    rw [hd, effArms]; push_cast
    calc (1 : ℝ) ≤ Tper 0 := by exact_mod_cast hTper 0
      _ ≤ ∑ k, (Tper k : ℝ) :=
        Finset.single_le_sum (f := fun k => (Tper k : ℝ)) (fun k _ => by positivity) (mem_univ _)
  have hδD : δ ≤ 8 * d := by linarith
  have hΨmem : ∀ t ∈ Ψ, n * K + 1 ≤ t ∧ t ≤ T - 1 ∧ (dec t).2 = (s, true) := by
    intro t ht
    rw [hΨ, Finset.mem_filter, Finset.mem_Icc] at ht
    exact ⟨ht.1.1, ht.1.2, ht.2⟩
  have hstage : ∀ t, 2 ≤ ((psiBar n K).filter
      (fun j => pol j = pol t ∧ j % Tper (pol t) = t % Tper (pol t))).card := fun t =>
    pmab16_stage_two (σ : ℝ) δ T n Tper Y Tper (pol t) (t % Tper (pol t))
      (Nat.mod_lt _ (hTper _)) (h2T _)
  have hcu2 : ∀ t, 2 ≤ (Sset t).card := by
    intro t
    refine le_trans (hstage t) (Finset.card_le_card ?_)
    exact Finset.filter_subset_filter _ Finset.subset_union_right
  -- Step 1: width bound
  have hW : ∀ t ∈ Ψ, wAt (σ : ℝ) δ T n Tper Y s (pol t) t ≤
      4 * σ * Real.sqrt (Real.log (8 * d * cu t / δ) / cu t) := by
    intro t ht
    obtain ⟨ht1, ht2, _⟩ := hΨmem t ht
    unfold wAt wHat
    simp only []
    rw [pmab16_psiSet (σ : ℝ) δ T n Tper Y s t]
    have hsub1 : psiBar n K ⊆ Icc 1 (t - 1) := by
      intro j hj; rw [psiBar, Finset.mem_Icc] at hj; rw [Finset.mem_Icc]; omega
    have hsub2 : Ψt t ⊆ Icc 1 (t - 1) := by
      intro j hj; rw [hΨt, Finset.mem_filter, Finset.mem_Icc] at hj; rw [Finset.mem_Icc]; omega
    rw [pmab16_count (σ : ℝ) δ T n Tper Y (pol t) t _ hsub1,
      pmab16_count (σ : ℝ) δ T n Tper Y (pol t) t _ hsub2,
      pmab16_count (σ : ℝ) δ T n Tper Y (pol t) t _ (Finset.union_subset hsub2 hsub1)]
    have hdhat : (∑ k', (Tper k' : ℝ)) = d := by rw [hd, effArms]; push_cast; rfl
    rw [hdhat]
    set cb := (((psiBar n K).filter
      (fun j => pol j = pol t ∧ j % Tper (pol t) = t % Tper (pol t))).card : ℝ) with hcb
    set cs := (((Ψt t).filter
      (fun j => pol j = pol t ∧ j % Tper (pol t) = t % Tper (pol t))).card : ℝ) with hcs
    have hcuE : cu t = (((Ψt t ∪ psiBar n K).filter
      (fun j => pol j = pol t ∧ j % Tper (pol t) = t % Tper (pol t))).card : ℝ) := rfl
    rw [← hcuE]
    have hcb1 : 1 ≤ cb := by
      rw [hcb]; have := hstage t; exact_mod_cast (by omega : 1 ≤ _)
    have hcbu : cb ≤ cu t := by
      rw [hcb, hcuE]; exact_mod_cast Finset.card_le_card
        (Finset.filter_subset_filter _ Finset.subset_union_right)
    have hcsu : cs ≤ cu t := by
      rw [hcs, hcuE]; exact_mod_cast Finset.card_le_card
        (Finset.filter_subset_filter _ Finset.subset_union_left)
    have e1 := pmab16_term σ δ (8 * d) cb (cu t) hσR hδ hδD hcb1 hcbu
    have e2 : cs / cu t * Real.sqrt (4 * (σ : ℝ) ^ 2 / cs * Real.log (8 * d * cs / δ)) ≤
        2 * σ * Real.sqrt (Real.log (8 * d * cu t / δ) / cu t) := by
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ cs by positivity) with h0 | hpos
      · rw [← h0]; simp; positivity
      · have hcs1 : 1 ≤ cs := by
          rw [hcs] at hpos ⊢
          have : 0 < ((Ψt t).filter
            (fun j => pol j = pol t ∧ j % Tper (pol t) = t % Tper (pol t))).card := by
            exact_mod_cast hpos
          exact_mod_cast this
        exact pmab16_term σ δ (8 * d) cs (cu t) hσR hδ hδD hcs1 hcsu
    linarith
  -- Step 2/3 setup: fibers by (arm, phase)
  set G := fun t => Real.log (8 * d * cu t / δ) / cu t with hG
  have hcu_pos : ∀ t, (2 : ℝ) ≤ cu t := fun t => by
    rw [hcu]; beta_reduce; exact_mod_cast hcu2 t
  have hG0 : ∀ t, 0 ≤ G t := by
    intro t
    have h2 := hcu_pos t
    apply div_nonneg _ (by linarith)
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]; nlinarith
  set I : Finset (Σ _ : Fin K, ℕ) := (univ : Finset (Fin K)).sigma (fun k => range (Tper k)) with hI
  set key : ℕ → (Σ _ : Fin K, ℕ) := fun j => ⟨pol j, j % Tper (pol j)⟩ with hkey
  have hkeyI : ∀ j, key j ∈ I := by
    intro j
    rw [hI, Finset.mem_sigma]
    exact ⟨mem_univ _, Finset.mem_range.mpr (Nat.mod_lt _ (hTper _))⟩
  set U := psiBar n K ∪ Ψ with hU
  set C := fun q : (Σ _ : Fin K, ℕ) => ((U.filter (fun j => key j = q)).card : ℝ) with hC
  have hkey_eq : ∀ j (q : Σ _ : Fin K, ℕ), key j = q ↔ pol j = q.1 ∧ j % Tper q.1 = q.2 := by
    intro j q
    obtain ⟨k, p⟩ := q
    simp only [hkey, Sigma.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      subst h1
      exact ⟨rfl, eq_of_heq h2⟩
    · rintro ⟨h1, h2⟩
      subst h1
      exact ⟨rfl, heq_of_eq h2⟩
  have hIcard : (I.card : ℝ) = d := by
    rw [hI, Finset.card_sigma, hd, effArms]
    simp
  have hC2 : ∀ q ∈ I, (2 : ℝ) ≤ C q := by
    intro q hq
    rw [hI, Finset.mem_sigma, Finset.mem_range] at hq
    have := pmab16_stage_two (σ : ℝ) δ T n Tper Y Tper q.1 q.2 hq.2 (h2T _)
    have hsub : (psiBar n K).filter (fun j => pol j = q.1 ∧ j % Tper q.1 = q.2) ⊆
        U.filter (fun j => key j = q) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨Finset.mem_union_left _ hj.1, (hkey_eq j q).mpr hj.2⟩
    have := le_trans this (Finset.card_le_card hsub)
    rw [hC]; beta_reduce; exact_mod_cast this
  have hUsub : U ⊆ Icc 1 T := by
    intro j hj
    rw [hU, Finset.mem_union] at hj
    rw [Finset.mem_Icc]
    rcases hj with hj | hj
    · rw [psiBar, Finset.mem_Icc] at hj; omega
    · have := hΨmem j hj; omega
  have hCsum : ∑ q ∈ I, C q ≤ T := by
    have h := Finset.card_eq_sum_card_fiberwise (s := U) (t := I) (f := key)
      (fun j _ => hkeyI j)
    have h2 := Finset.card_le_card hUsub
    rw [Nat.card_Icc] at h2
    rw [hC]
    beta_reduce
    have : ∑ q ∈ I, (U.filter (fun j => key j = q)).card ≤ T := by omega
    exact_mod_cast this
  -- fiber bound
  have hfiber : ∀ q ∈ I, ∑ t ∈ Ψ.filter (fun t => key t = q), G t ≤
      Real.log (8 * d * C q / δ) * Real.log (C q) := by
    intro q hq
    set F := Ψ.filter (fun t => key t = q) with hF
    have hFmem : ∀ t ∈ F, t ∈ Ψ ∧ pol t = q.1 ∧ t % Tper q.1 = q.2 := by
      intro t ht
      rw [hF, Finset.mem_filter] at ht
      exact ⟨ht.1, (hkey_eq t q).mp ht.2⟩
    -- the counts along the fiber stay below C q
    have hSsub : ∀ t ∈ F, Sset t ⊆ U.filter (fun j => key j = q) := by
      intro t ht j hj
      obtain ⟨htΨ, hpt, hpm⟩ := hFmem t ht
      obtain ⟨ht1, ht2, _⟩ := hΨmem t htΨ
      rw [hSset, Finset.mem_filter] at hj
      obtain ⟨hj1, hj2, hj3⟩ := hj
      rw [Finset.mem_filter]
      refine ⟨?_, (hkey_eq j q).mpr ⟨by rw [hj2, hpt], by rw [← hpt, hj3, hpt, hpm]⟩⟩
      rw [Finset.mem_union] at hj1
      rw [hU, Finset.mem_union]
      rcases hj1 with hj1 | hj1
      · right
        rw [hΨt, Finset.mem_filter, Finset.mem_Icc] at hj1
        rw [hΨ, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hj1.1.1, by omega⟩, hj1.2⟩
      · left; exact hj1
    have hcuC : ∀ t ∈ F, cu t ≤ C q := by
      intro t ht
      rw [hcu, hC]; beta_reduce; exact_mod_cast Finset.card_le_card (hSsub t ht)
    -- strictly increasing counts
    have hmono : ∀ t ∈ F, ∀ t' ∈ F, t < t' → (Sset t).card < (Sset t').card := by
      intro t ht t' ht' hlt
      obtain ⟨htΨ, hpt, hpm⟩ := hFmem t ht
      obtain ⟨htΨ', hpt', hpm'⟩ := hFmem t' ht'
      obtain ⟨ht1, ht2, htag⟩ := hΨmem t htΨ
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨t, ?_, ?_⟩
        · rw [hSset, Finset.mem_filter]
          refine ⟨Finset.mem_union_left _ ?_, by rw [hpt, hpt'], by rw [hpt', hpm, ← hpm']⟩
          rw [hΨt, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨ht1, by omega⟩, htag⟩
        · rw [hSset, Finset.mem_filter, Finset.mem_union]
          rintro ⟨h | h, -⟩
          · rw [hΨt, Finset.mem_filter, Finset.mem_Icc] at h; omega
          · rw [psiBar, Finset.mem_Icc] at h; omega
      · intro j hj
        rw [hSset, Finset.mem_filter, Finset.mem_union] at hj ⊢
        obtain ⟨hj1, hj2, hj3⟩ := hj
        refine ⟨?_, by rw [hj2, hpt, hpt'], by rw [hpt', ← hpt, hj3, hpt, hpm, hpm']⟩
        rcases hj1 with hj1 | hj1
        · left
          rw [hΨt, Finset.mem_filter, Finset.mem_Icc] at hj1 ⊢
          exact ⟨⟨hj1.1.1, by omega⟩, hj1.2⟩
        · right; exact hj1
    have hinj : Set.InjOn (fun t => (Sset t).card) (F : Set ℕ) := by
      intro t ht t' ht' heq
      simp only at heq
      rcases lt_trichotomy t t' with h | h | h
      · exact absurd heq (ne_of_lt (hmono t ht t' ht' h))
      · exact h
      · exact absurd heq (ne_of_gt (hmono t' ht' t ht h))
    -- harmonic bound
    have hCnat : ∃ c : ℕ, C q = c := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := hCnat
    have hharm : ∑ t ∈ F, 1 / cu t ≤ Real.log (C q) := by
      have himg : F.image (fun t => (Sset t).card) ⊆ Ico 2 (c + 1) := by
        intro j hj
        rw [Finset.mem_image] at hj
        obtain ⟨t, ht, rfl⟩ := hj
        rw [Finset.mem_Ico]
        refine ⟨hcu2 t, ?_⟩
        have := hcuC t ht
        rw [hcu, hc] at this
        beta_reduce at this
        have : (Sset t).card ≤ c := by exact_mod_cast this
        omega
      calc ∑ t ∈ F, 1 / cu t = ∑ j ∈ F.image (fun t => (Sset t).card), 1 / (j : ℝ) := by
            rw [Finset.sum_image hinj]
        _ ≤ ∑ j ∈ Ico 2 (c + 1), 1 / (j : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun j _ _ => by positivity)
        _ ≤ Real.log c := pmab16_harmonic c
        _ = Real.log (C q) := by rw [hc]
    have hLq0 : 0 ≤ Real.log (8 * d * C q / δ) := by
      apply Real.log_nonneg
      have := hC2 q hq
      rw [le_div_iff₀ hδ]; nlinarith
    calc ∑ t ∈ F, G t ≤ ∑ t ∈ F, Real.log (8 * d * C q / δ) * (1 / cu t) := by
          apply Finset.sum_le_sum
          intro t ht
          rw [hG]
          simp only
          rw [mul_one_div]
          apply div_le_div_of_nonneg_right _ (by linarith [hcu_pos t])
          apply Real.log_le_log
          · have := hcu_pos t; positivity
          · have := hcuC t ht
            gcongr
      _ = Real.log (8 * d * C q / δ) * ∑ t ∈ F, 1 / cu t := by rw [Finset.mul_sum]
      _ ≤ Real.log (8 * d * C q / δ) * Real.log (C q) :=
          mul_le_mul_of_nonneg_left hharm hLq0
  -- Step 3: sum of G
  set A := Real.log (8 * d / δ) with hA
  have hA2 : 2 ≤ A := by
    have he2 : Real.exp 2 < 8 := by
      have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      have h1 := Real.exp_one_lt_d9
      have h0 := Real.exp_pos 1
      nlinarith
    rw [hA, Real.le_log_iff_exp_le (by positivity)]
    have : (8 : ℝ) ≤ 8 * d / δ := by
      rw [le_div_iff₀ hδ]; nlinarith
    linarith
  have hlogsplit : ∀ x : ℝ, 0 < x → Real.log (8 * d * x / δ) = A + Real.log x := by
    intro x hx
    rw [hA, ← Real.log_mul (by positivity) hx.ne']
    congr 1; field_simp
  have hGsum : ∑ t ∈ Ψ, G t ≤ d * (Real.log (8 * T / δ) * Real.log (T / d)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := key) (t := I) (fun t _ => hkeyI t)]
    calc ∑ q ∈ I, ∑ t ∈ Ψ.filter (fun t => key t = q), G t
        ≤ ∑ q ∈ I, (A + Real.log (C q)) * Real.log (C q) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [← hlogsplit (C q) (by linarith [hC2 q hq])]
          exact hfiber q hq
      _ ≤ (I.card : ℝ) * ((A + Real.log (T / I.card)) * Real.log (T / I.card)) :=
          pmab16_jensen I C A T hA2 (fun q hq => by linarith [hC2 q hq]) hCsum
            (by rw [Finset.card_pos]; exact ⟨key 0, hkeyI 0⟩)
      _ = d * (Real.log (8 * T / δ) * Real.log (T / d)) := by
          rw [hIcard]
          have hTd : 0 < (T : ℝ) / d := by
            have : (0 : ℝ) < T := by
              have h := hCsum
              have : (2 : ℝ) * I.card ≤ ∑ q ∈ I, C q := by
                calc (2 : ℝ) * I.card = ∑ _q ∈ I, (2 : ℝ) := by simp [mul_comm]
                  _ ≤ ∑ q ∈ I, C q := Finset.sum_le_sum hC2
              rw [hIcard] at this; linarith
            positivity
          rw [← hlogsplit _ hTd]
          congr 3; field_simp
  -- Step 2: Cauchy-Schwarz
  have hCS : ∑ t ∈ Ψ, Real.sqrt (G t) ≤ Real.sqrt (Ψ.card * ∑ t ∈ Ψ, G t) := by
    apply Real.le_sqrt_of_sq_le
    have := Finset.sum_mul_sq_le_sq_mul_sq Ψ (fun _ => (1 : ℝ)) (fun t => Real.sqrt (G t))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at this
    calc (∑ t ∈ Ψ, Real.sqrt (G t)) ^ 2 ≤ Ψ.card * ∑ t ∈ Ψ, Real.sqrt (G t) ^ 2 := this
      _ = Ψ.card * ∑ t ∈ Ψ, G t := by
        congr 1; exact Finset.sum_congr rfl (fun t _ => Real.sq_sqrt (hG0 t))
  calc ∑ t ∈ Ψ, wAt (σ : ℝ) δ T n Tper Y s (pol t) t
      ≤ ∑ t ∈ Ψ, 4 * σ * Real.sqrt (G t) := Finset.sum_le_sum hW
    _ = 4 * σ * ∑ t ∈ Ψ, Real.sqrt (G t) := by rw [Finset.mul_sum]
    _ ≤ 4 * σ * Real.sqrt (Ψ.card * ∑ t ∈ Ψ, G t) := mul_le_mul_of_nonneg_left hCS (by positivity)
    _ ≤ 4 * σ * Real.sqrt (Ψ.card * (d * (Real.log (8 * T / δ) * Real.log (T / d)))) := by
        gcongr
    _ = _ := by rw [hd]; ring_nf
