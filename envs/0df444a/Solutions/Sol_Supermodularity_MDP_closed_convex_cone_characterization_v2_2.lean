-- Prove2me | solution 2 for Supermodularity.MDP.closed_convex_cone_characterization_v2
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T20:52:47.108089+00:00
-- url     : https://prove2.me/submissions/c44d8ede-ae0d-48a5-a037-d0250d2bced4

import Mathlib

open MeasureTheory

lemma key_card (N : ℕ) (hN : 0 < N) (a : ℝ) (c : ℕ)
    (hc0 : c = ((Finset.range (2*N*N)).filter (fun j : ℕ => -(N:ℝ) + ((j:ℝ)+1)/N ≤ a)).card) :
    -(N:ℝ) + (c:ℝ)/N ≤ max a (-N) ∧ min a N - 1/N ≤ -(N:ℝ) + (c:ℝ)/N := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  set K := ⌊(N:ℝ)*(a+N)⌋ with hK
  have hmem : ∀ j : ℕ, (-(N:ℝ) + ((j:ℝ)+1)/N ≤ a) ↔ ((j:ℤ)+1 ≤ K) := by
    intro j
    rw [hK, Int.le_floor]
    push_cast
    constructor
    · intro h
      have := mul_le_mul_of_nonneg_left h hNr.le
      field_simp at this ⊢
      nlinarith
    · intro h
      have : ((j:ℝ)+1) / N ≤ a + N := by rw [div_le_iff₀ hNr]; linarith
      linarith
  have hc : c = min (2*N*N) K.toNat := by
    have : (Finset.range (2*N*N)).filter (fun j : ℕ => -(N:ℝ) + ((j:ℝ)+1)/N ≤ a)
        = Finset.range (min (2*N*N) K.toNat) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, hmem]
      omega
    rw [hc0, this, Finset.card_range]
  have hK1 : (K:ℝ) ≤ N*(a+N) := Int.floor_le _
  have hK2 : (N:ℝ)*(a+N) < K + 1 := Int.lt_floor_add_one _
  constructor
  · rcases Nat.eq_zero_or_pos c with h0 | hpos
    · rw [h0]; simp
    · have : (c:ℝ) ≤ K := by
        have : c ≤ K.toNat := hc ▸ min_le_right _ _
        have h2 : (c:ℤ) ≤ K := by omega
        exact_mod_cast h2
      rw [le_max_iff]; left
      have : (c:ℝ)/N ≤ a + N := by rw [div_le_iff₀ hNr]; nlinarith
      linarith
  · by_cases hm : 2*N*N ≤ K.toNat
    · have : c = 2*N*N := by rw [hc]; exact min_eq_left hm
      rw [this]; push_cast
      have : (2*(N:ℝ)*N)/N = 2*N := by field_simp
      rw [this]
      have : 0 < 1/(N:ℝ) := by positivity
      have := min_le_right a (N:ℝ)
      linarith
    · have : c = K.toNat := by rw [hc]; omega
      have h3 : (K:ℝ) ≤ c := by
        have : K ≤ (c:ℤ) := by omega
        exact_mod_cast this
      have : a - 1/N ≤ -(N:ℝ) + (c:ℝ)/N := by
        have : (N*(a+N) - 1)/N ≤ (c:ℝ)/N := by
          apply div_le_div_of_nonneg_right _ hNr.le; linarith
        have e : (N*(a+N) - 1)/(N:ℝ) = a + N - 1/N := by field_simp
        linarith
      have := min_le_left a (N:ℝ)
      linarith


theorem solution {m n : ℕ} (T : Set (Fin m → ℝ))
    (μ : (Fin m → ℝ) → Measure (Fin n → ℝ))
    (hμprob : ∀ t : T, IsProbabilityMeasure (μ (t : Fin m → ℝ)))
    (V : Set (T → ℝ))
    (hVclosed : IsClosed V)
    (hVadd : ∀ ⦃f g : T → ℝ⦄, f ∈ V → g ∈ V → f + g ∈ V)
    (hVsmul : ∀ ⦃f : T → ℝ⦄, f ∈ V → ∀ ⦃c : ℝ⦄, 0 ≤ c → c • f ∈ V)
    (hVconst : ∀ c : ℝ, (fun _ : T => c) ∈ V) :
    (∀ ⦃S : Set (Fin n → ℝ)⦄, MeasurableSet S → IsUpperSet S →
        (fun t : T => (μ (t : Fin m → ℝ) S).toReal) ∈ V) ↔
      (∀ ⦃h : (Fin n → ℝ) → ℝ⦄, Measurable h → Monotone h →
        (∀ t : T, Integrable h (μ (t : Fin m → ℝ))) →
        (fun t : T => ∫ w, h w ∂ (μ (t : Fin m → ℝ))) ∈ V) := by
  constructor
  · intro hS h hmeas hmono hint
    -- level sets
    let S : ℕ → ℕ → Set (Fin n → ℝ) := fun N j => {w | -(N:ℝ) + ((j:ℝ)+1)/N ≤ h w}
    have hSm : ∀ N j, MeasurableSet (S N j) := fun N j => measurableSet_le measurable_const hmeas
    have hSu : ∀ N j, IsUpperSet (S N j) := fun N j a b hab ha =>
      le_trans ha (hmono hab)
    let g : ℕ → (Fin n → ℝ) → ℝ := fun N w =>
      -(N:ℝ) + (1/(N:ℝ)) * ∑ j ∈ Finset.range (2*N*N), (S N j).indicator (fun _ => (1:ℝ)) w
    have hgcard : ∀ N w, g N w = -(N:ℝ) + (((Finset.range (2*N*N)).filter
        (fun j : ℕ => -(N:ℝ) + ((j:ℝ)+1)/N ≤ h w)).card : ℝ) / N := by
      intro N w
      simp only [g, Set.indicator_apply, Finset.sum_boole, S, Set.mem_setOf_eq]
      ring
    have hsum : ∀ (s : Finset ℕ) (f : ℕ → T → ℝ), (∀ j ∈ s, f j ∈ V) →
        (fun t => ∑ j ∈ s, f j t) ∈ V := by
      intro s f hf
      induction s using Finset.induction_on with
      | empty => simpa using hVconst 0
      | insert a s ha ih =>
        have := hVadd (hf a (Finset.mem_insert_self _ _))
          (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
        convert this using 1
        funext t
        simp [Finset.sum_insert ha]
    have hgV : ∀ N, (fun t : T => ∫ w, g N w ∂ (μ (t : Fin m → ℝ))) ∈ V := by
      intro N
      have e : (fun t : T => ∫ w, g N w ∂ (μ (t : Fin m → ℝ))) =
          (fun _ : T => -(N:ℝ)) + (1/(N:ℝ)) • (fun t : T =>
            ∑ j ∈ Finset.range (2*N*N), (μ (t : Fin m → ℝ) (S N j)).toReal) := by
        funext t
        haveI := hμprob t
        simp only [g, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [integral_add (integrable_const _), integral_const_mul,
          integral_finset_sum]
        · simp only [integral_const, smul_eq_mul]
          simp only [probReal_univ, one_mul]
          congr 2
          exact Finset.sum_congr rfl fun j _ => by
            rw [integral_indicator_const _ (hSm N j), measureReal_def, smul_eq_mul, mul_one]
        · intro j _
          exact (integrable_const (1:ℝ)).indicator (hSm N j)
        · exact ((integrable_finset_sum _ fun j _ =>
            (integrable_const (1:ℝ)).indicator (hSm N j))).const_mul _
      rw [e]
      exact hVadd (hVconst _) (hVsmul (hsum _ _ fun j _ => hS (hSm N j) (hSu N j))
        (by positivity))
    refine hVclosed.mem_of_tendsto (b := Filter.atTop) (f := fun k : ℕ =>
      (fun t : T => ∫ w, g (k+1) w ∂ (μ (t : Fin m → ℝ)))) ?_
      (Filter.Eventually.of_forall fun k => hgV (k+1))
    rw [tendsto_pi_nhds]
    intro t
    have hb : ∀ k w, |g (k+1) w| ≤ |h w| + 1 ∧ (|h w| ≤ (k+1:ℕ) → h w - 1/((k+1:ℕ):ℝ) ≤ g (k+1) w ∧ g (k+1) w ≤ h w) := by
      intro k w
      obtain ⟨h1, h2⟩ := key_card (k+1) (Nat.succ_pos k) (h w) _ rfl
      rw [hgcard]
      have hN1 : (1:ℝ) ≤ ((k+1:ℕ):ℝ) := by norm_cast; omega
      have hinv : 1/((k+1:ℕ):ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hN1
      have hinv0 : 0 ≤ 1/((k+1:ℕ):ℝ) := by positivity
      refine ⟨?_, fun hk => ?_⟩
      · rw [abs_le]
        constructor
        · rcases le_total (h w) ((k+1:ℕ):ℝ) with hh | hh
          · rw [min_eq_left hh] at h2; linarith [neg_abs_le (h w)]
          · rw [min_eq_right hh] at h2; linarith [abs_nonneg (h w)]
        · rcases le_total (h w) (-((k+1:ℕ):ℝ)) with hh | hh
          · rw [max_eq_right hh] at h1; linarith [abs_nonneg (h w)]
          · rw [max_eq_left hh] at h1; linarith [le_abs_self (h w)]
      · have := abs_le.mp hk
        rw [max_eq_left (by linarith)] at h1
        rw [min_eq_left (by linarith)] at h2
        exact ⟨h2, h1⟩
    haveI := hμprob t
    apply tendsto_integral_of_dominated_convergence (fun w => |h w| + 1)
    · intro k
      exact (Measurable.aestronglyMeasurable (by
        simp only [g]
        exact measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun j _ =>
          measurable_const.indicator (hSm _ j)))))
    · exact (hint t).abs.add (integrable_const _)
    · intro k
      exact Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]; exact (hb k w).1
    · refine Filter.Eventually.of_forall fun w => ?_
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨K, hK⟩ := exists_nat_gt (max |h w| (1/ε))
      refine ⟨K, fun k hk => ?_⟩
      have hk' : (K:ℝ) ≤ k := by exact_mod_cast hk
      have hkk : |h w| ≤ ((k+1:ℕ):ℝ) := by
        push_cast; linarith [le_max_left |h w| (1/ε)]
      obtain ⟨l1, l2⟩ := (hb k w).2 hkk
      rw [Real.dist_eq, abs_lt]
      have : 1/((k+1:ℕ):ℝ) < ε := by
        rw [div_lt_iff₀ (by positivity)]
        have : 1/ε < ((k+1:ℕ):ℝ) := by push_cast; linarith [le_max_right |h w| (1/ε)]
        rw [div_lt_iff₀ hε] at this
        linarith
      constructor <;> linarith
  · intro hH S hSm hSu
    have := hH (h := S.indicator (fun _ => (1:ℝ)))
      (measurable_const.indicator hSm)
      (by
        intro a b hab
        by_cases ha : a ∈ S
        · simp [Set.indicator_of_mem ha, Set.indicator_of_mem (hSu hab ha)]
        · rw [Set.indicator_of_notMem ha]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (fun t => by haveI := hμprob t; exact (integrable_const _).indicator hSm)
    convert this using 2 with t
    rw [integral_indicator_const _ hSm, measureReal_def, smul_eq_mul, mul_one]
