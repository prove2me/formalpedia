-- Prove2me | solution 1 for WaitJudge.Convex.prob_violation_eq_sum_integral
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:29:09.669119+00:00
-- url     : https://prove2.me/submissions/61bcc16f-5b44-4eee-aeb6-43feb43dc8c0

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting
import Theorems.Thm_WaitJudge_Convex_sstar_le_dim
import Theorems.Thm_WaitJudge_Convex_prob_Sk_eq_choose_mul
import Theorems.Thm_WaitJudge_Convex_prob_A_eq_integral

open MeasureTheory ScenarioApproach.Generalization WaitJudge.Convex

theorem solution {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]
    (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ)
    (hX : Convex ℝ X) (hXδ : ∀ δ, Convex ℝ (Xδ δ))
    (htb : ∀ j, ConvexOn ℝ Set.univ (tb j))
    (hA1 : Assumption1 c X Xδ tb) (hA2 : Assumption2 c X Xδ tb P)
    (hmeas : MeasurabilityPins c X Xδ tb)
    (N : ℕ) (hN : d < N) (ε : ℕ → ℝ) (hε : ∀ k ≤ d, 0 ≤ ε k ∧ ε k ≤ 1) :
    (Measure.pi fun _ : Fin N => P) {ω | ε (sstar c X Xδ tb ω) < violation P Xδ (xstar c X Xδ tb ω)} =
      ENNReal.ofReal (∑ k ∈ Finset.range (d + 1),
        (N.choose k : ℝ) * ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(Fk P c X Xδ tb k)) := by
  classical
  -- measurability of the violation of the solution
  have hviol : Measurable (fun x : E d => violation P Xδ x) := by
    have hs : MeasurableSet {q : E d × Δ | q.1 ∉ Xδ q.2} := hmeas.1.compl
    have := measurable_measure_prodMk_left (ν := P) hs
    exact this.ennreal_toReal
  have hV : Measurable (fun ω : Fin N → Δ => violation P Xδ (xstar c X Xδ tb ω)) :=
    hviol.comp (hmeas.2 N)
  -- measurability of the support indicator
  have hsupp : ∀ i : Fin N, MeasurableSet {ω : Fin N → Δ | i ∈ supportSet c X Xδ tb ω} := by
    intro i
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hF : ∀ ω : Fin (n + 1) → Δ, feasibleOn X Xδ ω (Finset.univ.erase i) =
        feasibleOn X Xδ (fun j => ω (i.succAbove j)) Finset.univ := by
      intro ω
      ext x
      simp only [feasibleOn, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_erase,
        Finset.mem_univ, and_true, true_implies]
      constructor
      · rintro ⟨hx, h⟩; exact ⟨hx, fun j => h _ (Fin.succAbove_ne i j)⟩
      · rintro ⟨hx, h⟩; refine ⟨hx, fun j hj => ?_⟩
        obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        exact h j'
    have hm1 : Measurable (fun ω : Fin (n + 1) → Δ =>
        sol c tb (feasibleOn X Xδ ω (Finset.univ.erase i))) := by
      simp_rw [hF]
      exact (hmeas.2 n).comp (measurable_pi_lambda _ (fun j => measurable_pi_apply _))
    have : {ω : Fin (n + 1) → Δ | i ∈ supportSet c X Xδ tb ω} =
        {ω | sol c tb (feasibleOn X Xδ ω (Finset.univ.erase i)) = xstar c X Xδ tb ω}ᶜ := by
      ext ω; simp [supportSet, IsSupport, xstar]
    rw [this]
    exact (measurableSet_eq_fun hm1 (hmeas.2 (n + 1))).compl
  have hsstar : Measurable (fun ω : Fin N → Δ => sstar c X Xδ tb ω) := by
    have : (fun ω : Fin N → Δ => sstar c X Xδ tb ω) =
        fun ω => ∑ i : Fin N, Set.indicator {ω | i ∈ supportSet c X Xδ tb ω} (fun _ => 1) ω := by
      funext ω
      simp only [sstar, Finset.card_eq_sum_ones, supportSet, Finset.sum_filter, Set.indicator,
        Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [this]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hsupp i))
  -- (13): split according to the number of support constraints
  have hle := sstar_le_dim c X Xδ tb hX hXδ htb hA1 N
  have hsplit : {ω : Fin N → Δ | ε (sstar c X Xδ tb ω) < violation P Xδ (xstar c X Xδ tb ω)} =
      ⋃ k ∈ Finset.range (d + 1),
        {ω | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ sstar c X Xδ tb ω = k} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · intro h; exact ⟨_, Nat.lt_succ_of_le (hle ω), h, rfl⟩
    · rintro ⟨k, _, h, rfl⟩; exact h
  rw [hsplit, measure_biUnion_finset]
  · rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro k hk
      have hkN : k ≤ N := by simp at hk; omega
      rw [prob_Sk_eq_choose_mul P c X Xδ tb hmeas ε N k hkN,
        prob_A_eq_integral P c X Xδ tb hA1 hA2 hmeas ε N k hkN,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    · intro k _
      apply mul_nonneg (by positivity)
      apply setIntegral_nonneg measurableSet_Ioc
      intro v hv
      exact pow_nonneg (by linarith [hv.2]) _
  · intro k _ l _ hkl
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro ω ⟨_, h1⟩ ⟨_, h2⟩
    exact hkl (h1.symm.trans h2)
  · intro k _
    exact (measurableSet_lt measurable_const hV).inter (measurableSet_eq_fun hsstar measurable_const)
