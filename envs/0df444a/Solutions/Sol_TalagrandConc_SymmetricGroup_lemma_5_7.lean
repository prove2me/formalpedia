-- Prove2me | solution 1 for TalagrandConc.SymmetricGroup.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:05:15.931095+00:00
-- url     : https://prove2.me/submissions/92d51165-bbf5-4d5e-9277-213e5387e569

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic



namespace TalagrandConc.SymmetricGroup

open scoped ENNReal Classical
open Equiv

/-! ### Basic geometry of `U`, `V` -/

lemma U_finite {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) : (U A σ).Finite := by
  apply (Set.finite_range (fun b : Fin N → Bool => fun i => if b i then (1 : ℝ) else 0)).subset
  intro s hs
  refine ⟨fun i => decide (s i = 1), ?_⟩
  funext i
  rcases hs.1 i with h | h <;> simp [h]

lemma V_compact {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) : IsCompact (V A σ) :=
  (U_finite A σ).isCompact_convexHull ℝ

lemma V_convex {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) : Convex ℝ (V A σ) :=
  convex_convexHull ℝ _

lemma U_subset_box {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) :
    U A σ ⊆ Set.Icc (0 : Fin N → ℝ) 1 := by
  intro s hs
  refine ⟨fun ℓ => ?_, fun ℓ => ?_⟩ <;> rcases hs.1 ℓ with h | h <;> simp [h]

lemma V_subset_box {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) :
    V A σ ⊆ Set.Icc (0 : Fin N → ℝ) 1 :=
  convexHull_min (U_subset_box A σ) (convex_Icc _ _)

lemma V_coord {N : ℕ} {A : Set (Perm (Fin N))} {σ : Perm (Fin N)} {s : Fin N → ℝ}
    (hs : s ∈ V A σ) (ℓ : Fin N) : 0 ≤ s ℓ ∧ s ℓ ≤ 1 :=
  ⟨(V_subset_box A σ hs).1 ℓ, (V_subset_box A σ hs).2 ℓ⟩

/-- Infimum of `ofReal ∘ F` over a compact set: `⊤` if empty, attained otherwise. -/
lemma iInf_ofReal_cases {N : ℕ} (S : Set (Fin N → ℝ)) (hS : IsCompact S)
    (F : (Fin N → ℝ) → ℝ) (hF : Continuous F) :
    (S = ∅ ∧ (⨅ x ∈ S, ENNReal.ofReal (F x)) = ⊤) ∨
      (∃ s ∈ S, (⨅ x ∈ S, ENNReal.ofReal (F x)) = ENNReal.ofReal (F s) ∧ ∀ x ∈ S, F s ≤ F x) := by
  rcases S.eq_empty_or_nonempty with h | h
  · left; refine ⟨h, ?_⟩; simp [h]
  · right
    obtain ⟨s, hs, hmin⟩ := hS.exists_isMinOn h hF.continuousOn
    refine ⟨s, hs, le_antisymm (iInf₂_le s hs) ?_, fun x hx => hmin hx⟩
    exact le_iInf₂ fun x hx => ENNReal.ofReal_le_ofReal (hmin hx)

lemma sum_split {N : ℕ} (i j : Fin N) (hij : i ≠ j) (h : Fin N → ℝ) :
    ∑ ℓ, h ℓ = h i + h j + ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j), h ℓ := by
  have e : Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j) = (Finset.univ.erase i).erase j := by
    ext ℓ; simp [and_comm]
  rw [e, ← Finset.add_sum_erase _ h (Finset.mem_univ i),
    ← Finset.add_sum_erase _ h (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩), add_assoc]

lemma cont_fp {N : ℕ} (i : Fin N) :
    Continuous (fun s : Fin N → ℝ => s i ^ 2 + ∑ ℓ, s ℓ ^ 2) :=
  ((continuous_apply i).pow 2).add (continuous_finsetSum _ fun ℓ _ => (continuous_apply ℓ).pow 2)

lemma cont_g {N : ℕ} (i j : Fin N) :
    Continuous (fun s : Fin N → ℝ =>
      ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j), s ℓ ^ 2) :=
  continuous_finsetSum _ fun ℓ _ => (continuous_apply ℓ).pow 2

lemma T_compact {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) (m : Fin N) :
    IsCompact {s ∈ V A σ | s m = 0} :=
  (V_compact A σ).inter_right (isClosed_eq (continuous_apply m) continuous_const)

/-- Pointwise convexity bound used for every coordinate. -/
lemma coord_bound (a c u v : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1) :
    (a * u + c * v) ^ 2 ≤ a * u ^ 2 + c * v ^ 2 := by
  have : a * u ^ 2 + c * v ^ 2 - (a * u + c * v) ^ 2 = a * c * (u - v) ^ 2 := by
    have hc' : c = 1 - a := by linarith
    subst hc'; ring
  nlinarith [mul_nonneg (mul_nonneg ha hc) (sq_nonneg (u - v))]

lemma coord_bound_j (a c u v : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1)
    (hu : 0 ≤ u) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (a * u + c * v) ^ 2 ≤ 2 * a * u ^ 2 + 2 * c ^ 2 := by
  have h1 : (a * u + c * v) ^ 2 ≤ (a * u + c) ^ 2 := by
    have : a * u + c * v ≤ a * u + c := by nlinarith
    have h0 : 0 ≤ a * u + c * v := by positivity
    nlinarith
  have h2 : 2 * (a * c) * u ≤ a * u ^ 2 + a * c ^ 2 := by
    nlinarith [mul_nonneg ha (sq_nonneg (u - c))]
  have h3 : a ^ 2 ≤ a := by nlinarith
  have h4 : a * c ^ 2 ≤ c ^ 2 := by nlinarith [sq_nonneg c]
  nlinarith

/-- The real inequality behind Lemma 5.3. -/
lemma real_ineq_53 {N : ℕ} (i j : Fin N) (hij : i ≠ j) (s s' : Fin N → ℝ) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hs : ∀ ℓ, 0 ≤ s ℓ ∧ s ℓ ≤ 1) (hs' : ∀ ℓ, 0 ≤ s' ℓ ∧ s' ℓ ≤ 1) (hsi : s i = 0) :
    (lam • s + (1 - lam) • s') i ^ 2 + ∑ ℓ, (lam • s + (1 - lam) • s') ℓ ^ 2
      ≤ 4 * (1 - lam) ^ 2
        + (1 - lam) * ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j), s' ℓ ^ 2
        + lam * (s j ^ 2 + ∑ ℓ, s ℓ ^ 2) := by
  set c := 1 - lam with hc
  have hc0 : 0 ≤ c := by linarith
  have hac : lam + c = 1 := by linarith
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_split i j hij (fun ℓ => (lam * s ℓ + c * s' ℓ) ^ 2),
    sum_split i j hij (fun ℓ => s ℓ ^ 2)]
  simp only [hsi]
  have hi : (lam * 0 + c * s' i) ^ 2 ≤ c ^ 2 := by
    have := hs' i
    have h1 : s' i ^ 2 ≤ 1 := by nlinarith
    rw [mul_zero, zero_add, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg c)]
  have hj := coord_bound_j lam c (s j) (s' j) hlam0 hc0 hac (hs j).1 (hs' j).1 (hs' j).2
  have hrest : ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j), (lam * s ℓ + c * s' ℓ) ^ 2
      ≤ ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j), (lam * s ℓ ^ 2 + c * s' ℓ ^ 2) := by
    apply Finset.sum_le_sum
    intro ℓ _
    exact coord_bound lam c _ _ hlam0 hc0 hac
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hrest
  nlinarith

/-- Lemma 5.3. -/
theorem lemma_5_3_core {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i j : Fin (N + 1))
    (hij : i ≠ j) (σ : Perm (Fin (N + 1))) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fp A σ i ≤ ENNReal.ofReal (4 * (1 - lam) ^ 2) + ENNReal.ofReal (1 - lam) * g A σ i j
      + ENNReal.ofReal lam * fpm A σ j i := by
  have hc0 : 0 ≤ 1 - lam := by linarith
  rcases iInf_ofReal_cases (V A σ) (V_compact A σ) _ (cont_g i j) with ⟨hV, hg⟩ | ⟨s', hs', hg, hmin'⟩
  · -- V empty: g = ⊤ and fpm = ⊤
    have hfpm : (⨅ s ∈ {s ∈ V A σ | s i = 0}, ENNReal.ofReal (s j ^ 2 + ∑ ℓ, s ℓ ^ 2)) = ⊤ := by
      have : {s ∈ V A σ | s i = 0} = ∅ := by rw [hV]; simp
      simp [this]
    unfold g fpm
    rw [hg, hfpm]
    rcases eq_or_lt_of_le hlam1 with h1 | h1
    · rw [h1]; simp
    · rw [ENNReal.mul_top (by simpa [ENNReal.ofReal_eq_zero] using h1)]; simp
  · rcases iInf_ofReal_cases {s ∈ V A σ | s i = 0} (T_compact A σ i) _ (cont_fp j)
      with ⟨hT, hfpm⟩ | ⟨s, hs, hfpm, hmin⟩
    · unfold g fpm
      rw [hg, hfpm]
      rcases eq_or_lt_of_le hlam0 with h0 | h0
      · subst h0
        simp only [sub_zero, ENNReal.ofReal_one, one_mul, ENNReal.ofReal_zero, zero_mul, add_zero]
        refine (iInf₂_le s' hs').trans ?_
        rw [← ENNReal.ofReal_add (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [sum_split i j hij (fun ℓ => s' ℓ ^ 2)]
        have h1 := V_coord hs' i
        have h2 := V_coord hs' j
        nlinarith
      · rw [ENNReal.mul_top (by simpa [ENNReal.ofReal_eq_zero] using h0)]; simp
    · unfold g fpm
      rw [hg, hfpm]
      have hs'' : lam • s + (1 - lam) • s' ∈ V A σ :=
        V_convex A σ hs.1 hs' hlam0 hc0 (by ring)
      refine (iInf₂_le _ hs'').trans ?_
      rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul hlam0,
        ← ENNReal.ofReal_add (by positivity)
          (mul_nonneg hc0 (Finset.sum_nonneg fun _ _ => sq_nonneg _)),
        ← ENNReal.ofReal_add (by positivity)
          (mul_nonneg hlam0 (by positivity))]
      apply ENNReal.ofReal_le_ofReal
      exact real_ineq_53 i j hij s s' lam hlam0 hlam1 (fun ℓ => V_coord hs.1 ℓ)
        (fun ℓ => V_coord hs' ℓ) hs.2

/-- Lemma 5.7. -/
theorem lemma_5_7_core {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (σ : Perm (Fin (N + 1)))
    (j : Fin (N + 1)) (hj : j ≠ σ (Fin.last N)) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fp A σ (Fin.last N) ≤ ENNReal.ofReal (4 * (1 - lam) ^ 2)
      + ENNReal.ofReal (1 - lam) * g A σ (Fin.last N) (σ⁻¹ j)
      + ENNReal.ofReal lam * fpm A σ (σ⁻¹ j) (Fin.last N) := by
  apply lemma_5_3_core A (Fin.last N) (σ⁻¹ j) _ σ lam hlam0 hlam1
  intro h
  apply hj
  rw [h]; simp

end TalagrandConc.SymmetricGroup

open TalagrandConc.SymmetricGroup
open Equiv

theorem solution {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (σ : Perm (Fin (N + 1)))
    (j : Fin (N + 1)) (hj : j ≠ σ (Fin.last N)) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fp A σ (Fin.last N) ≤ ENNReal.ofReal (4 * (1 - lam) ^ 2)
      + ENNReal.ofReal (1 - lam) * g A σ (Fin.last N) (σ⁻¹ j)
      + ENNReal.ofReal lam * fpm A σ (σ⁻¹ j) (Fin.last N) := by
  exact lemma_5_7_core A σ j hj lam hlam0 hlam1
