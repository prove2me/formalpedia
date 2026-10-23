-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.psd_polar_and_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:22:34.344427+00:00
-- url     : https://prove2.me/submissions/c6998325-8ab0-466d-9508-279378f668db

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

lemma X7PP_pairing_eq {n : ℕ} (f : Coeff n) (y : Part n → ℝ) :
    pairing f y = ∑ l ∈ f.support, f l * y l := by
  unfold pairing Finsupp.sum; rfl

lemma X7PP_pairing_cont {n : ℕ} (f : Coeff n) : Continuous (fun y : Part n → ℝ => pairing f y) := by
  simp_rw [X7PP_pairing_eq]
  exact continuous_finsetSum _ (fun l _ => continuous_const.mul (continuous_apply l))

lemma X7PP_closedCone {n : ℕ} (f : Coeff n) (S : Set (Part n → ℝ))
    (hS : ∀ y ∈ S, 0 ≤ pairing f y) : ∀ y ∈ closedCone S, 0 ≤ pairing f y := by
  have hsub : finiteCone S ⊆ {y | 0 ≤ pairing f y} := by
    rintro y ⟨N, c, u, hcu, rfl⟩
    simp only [Set.mem_setOf_eq, X7PP_pairing_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_nonneg
    intro i _
    have h := hS (u i) (hcu i).2
    rw [X7PP_pairing_eq] at h
    have : ∑ l ∈ f.support, f l * (c i * u i l) = c i * ∑ l ∈ f.support, f l * u i l := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l _ => by ring)
    rw [this]
    exact mul_nonneg (hcu i).1 h
  have hcl : IsClosed {y : Part n → ℝ | 0 ≤ pairing f y} :=
    isClosed_le continuous_const (X7PP_pairing_cont f)
  intro y hy
  exact (closure_minimal hsub hcl) hy

lemma X7PP_mem_closedCone {V : Type*} [AddCommMonoid V] [Module ℝ V] [TopologicalSpace V]
    (S : Set V) (y : V) (hy : y ∈ S) : y ∈ closedCone S := by
  apply subset_closure
  refine ⟨1, fun _ => 1, fun _ => y, fun _ => ⟨zero_le_one, hy⟩, ?_⟩
  simp


lemma X7PP_g_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (fun m : ℕ => ∑ _i : Fin (m+1), (1 / ((m:ℝ)+1)) ^ k) atTop
      (nhds (if k = 1 then 1 else 0)) := by
  have e : ∀ m : ℕ, ∑ _i : Fin (m+1), (1 / ((m:ℝ)+1)) ^ k = (1 / ((m:ℝ)+1)) ^ (k-1) := by
    intro m
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hpos : (0:ℝ) < (m:ℝ) + 1 := by positivity
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k-1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    push_cast
    field_simp
  simp_rw [e]
  by_cases h1 : k = 1
  · subst h1; simp
  · rw [if_neg h1]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow (k-1)
    rw [zero_pow (by omega)] at this
    exact this

lemma X7PP_list_tendsto (L : List ℕ) (hL : ∀ k ∈ L, 0 < k) :
    Tendsto (fun m : ℕ => (L.map (fun k => ∑ _i : Fin (m+1), (1 / ((m:ℝ)+1)) ^ k)).prod) atTop
      (nhds (if ∀ k ∈ L, k = 1 then 1 else 0)) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : 0 < a := hL a (by simp)
    have ih' := ih (fun k hk => hL k (by simp [hk]))
    have := (X7PP_g_tendsto a ha).mul ih'
    simp only [List.map_cons, List.prod_cons]
    convert this using 2
    by_cases h1 : a = 1
    · simp [h1]
    · simp [h1]

end QAlgorithms.Papers.Independent.Information100.P19

end

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    psdCone n = spectralPolar (psdMom n) ∧
    Tendsto (fun m : ℕ => @spectralMoments n (m+1) (fun _ => 1 / ((m:ℝ)+1)))
      atTop (nhds (fun l : Part n => if ∀ k ∈ l.val, k = 1 then 1 else 0)) ∧
    (2 ≤ n → ¬ ∃ d : ℕ, 0 < d ∧ ∃ x : Fin d → ℝ,
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧
      spectralMoments x = (fun l : Part n => if ∀ k ∈ l.val, k=1 then 1 else 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · ext f
    constructor
    · intro hf y hy
      exact X7PP_closedCone f _ (by rintro y ⟨d, hd, x, hx, rfl⟩; exact hf d hd x hx) y hy
    · intro hf d hd x hx
      exact hf _ (X7PP_mem_closedCone _ _ ⟨d, hd, x, hx, rfl⟩)
  · rw [tendsto_pi_nhds]
    intro l
    exact X7PP_list_tendsto l.val l.2.2.1
  · rintro h2 ⟨d, hd, x, hx0, hx1, hx⟩
    let L : List ℕ := 2 :: List.replicate (n-2) 1
    have hLs : L.sum = n := by simp [L]; omega
    have hL : L.Pairwise (· ≥ ·) ∧ (∀ k ∈ L, 0 < k) ∧ L.sum = n := by
      refine ⟨?_, ?_, hLs⟩
      · simp only [L, List.pairwise_cons, List.mem_replicate]
        refine ⟨fun b hb => by omega, ?_⟩
        exact List.pairwise_replicate.2 (Or.inr le_rfl)
      · intro k hk
        simp only [L, List.mem_cons, List.mem_replicate] at hk
        omega
    have := congrFun hx ⟨L, hL⟩
    have hnot : ¬ ∀ k ∈ L, k = 1 := fun h => by have := h 2 (by simp [L]); omega
    simp only [hnot, if_false, spectralMoments, L, List.map_cons, List.prod_cons,
      List.map_replicate, List.prod_replicate, pow_one, hx1, one_pow, mul_one] at this
    have h0 : ∀ i, x i ^ 2 = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).1 this i
        (Finset.mem_univ _)
      exact this
    have : ∑ i, x i = 0 := Finset.sum_eq_zero (fun i _ => pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (h0 i))
    rw [hx1] at this; norm_num at this

end
