-- Prove2me | solution 1 for WaitJudge.Convex.moment_conditions
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:30:26.82384+00:00
-- url     : https://prove2.me/submissions/0a4fc694-bdf4-4dbc-adff-758a97765603

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
    (hmeas : MeasurabilityPins c X Xδ tb) :
    ∀ m : ℕ, ∑ k ∈ Finset.range (min m d + 1),
      (m.choose k : ℝ) * ∫ v in Set.Icc 0 1, (1 - v) ^ (m - k) ∂(Fk P c X Xδ tb k) = 1 := by
  classical
  intro m
  -- measurability of the violation of the solution
  have hviol : Measurable (fun x : E d => violation P Xδ x) := by
    have hs : MeasurableSet {q : E d × Δ | q.1 ∉ Xδ q.2} := hmeas.1.compl
    have := measurable_measure_prodMk_left (ν := P) hs
    exact this.ennreal_toReal
  have hV : Measurable (fun ω : Fin m → Δ => violation P Xδ (xstar c X Xδ tb ω)) :=
    hviol.comp (hmeas.2 m)
  -- measurability of the support indicator
  have hsupp : ∀ i : Fin m, MeasurableSet {ω : Fin m → Δ | i ∈ supportSet c X Xδ tb ω} := by
    intro i
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := i.isLt; omega⟩
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
  have hsstar : Measurable (fun ω : Fin m → Δ => sstar c X Xδ tb ω) := by
    have : (fun ω : Fin m → Δ => sstar c X Xδ tb ω) =
        fun ω => ∑ i : Fin m, Set.indicator {ω | i ∈ supportSet c X Xδ tb ω} (fun _ => 1) ω := by
      funext ω
      simp only [sstar, Finset.card_eq_sum_ones, supportSet, Finset.sum_filter, Set.indicator,
        Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [this]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hsupp i))
  have hviol01 : ∀ x : E d, violation P Xδ x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  -- F_k is concentrated on [0,1]
  have hconc : ∀ (k : ℕ) (S : Set ℝ), MeasurableSet S → Set.Icc (0 : ℝ) 1 ⊆ S →
      (Fk P c X Xδ tb k).restrict S = Fk P c X Xδ tb k := by
    intro k S hS hsub
    apply Measure.restrict_eq_self_of_ae_mem
    have hVk : Measurable (fun ω : Fin k → Δ => violation P Xδ (xstar c X Xδ tb ω)) :=
      hviol.comp (hmeas.2 k)
    unfold Fk
    exact (ae_map_iff hVk.aemeasurable hS).2
      (Filter.Eventually.of_forall (fun ω => hsub (hviol01 _)))
  have hle : ∀ ω : Fin m → Δ, sstar c X Xδ tb ω ≤ min m d := by
    intro ω
    refine le_min ?_ (sstar_le_dim c X Xδ tb hX hXδ htb hA1 m ω)
    show (supportSet c X Xδ tb ω).card ≤ m
    simpa using Finset.card_le_univ (supportSet c X Xδ tb ω)
  let ε : ℕ → ℝ := fun _ => -1
  have hsplit : (Set.univ : Set (Fin m → Δ)) =
      ⋃ k ∈ Finset.range (min m d + 1),
        {ω | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ sstar c X Xδ tb ω = k} := by
    ext ω
    simp only [Set.mem_univ, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop,
      true_iff]
    exact ⟨_, Nat.lt_succ_of_le (hle ω), by linarith [(hviol01 (xstar c X Xδ tb ω)).1], rfl⟩
  have hint : ∀ k, ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (m - k) ∂(Fk P c X Xδ tb k) =
      ∫ v in Set.Icc 0 1, (1 - v) ^ (m - k) ∂(Fk P c X Xδ tb k) := by
    intro k
    rw [hconc k _ measurableSet_Ioc (fun v hv => ⟨by simp only [ε]; linarith [hv.1], hv.2⟩),
      hconc k _ measurableSet_Icc subset_rfl]
  have hnonneg : ∀ k ∈ Finset.range (min m d + 1),
      0 ≤ (m.choose k : ℝ) * ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (m - k) ∂(Fk P c X Xδ tb k) := by
    intro k _
    apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Ioc
    intro v hv
    exact pow_nonneg (by linarith [hv.2]) _
  have hmain : (1 : ENNReal) = ENNReal.ofReal (∑ k ∈ Finset.range (min m d + 1),
      (m.choose k : ℝ) * ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (m - k) ∂(Fk P c X Xδ tb k)) := by
    rw [← measure_univ (μ := Measure.pi fun _ : Fin m => P), hsplit, measure_biUnion_finset]
    · rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k ≤ m := by simp at hk; omega
      rw [prob_Sk_eq_choose_mul P c X Xδ tb hmeas ε m k hkm,
        prob_A_eq_integral P c X Xδ tb hA1 hA2 hmeas ε m k hkm,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    · intro k _ l _ hkl
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      rintro ω ⟨_, h1⟩ ⟨_, h2⟩
      exact hkl (h1.symm.trans h2)
    · intro k _
      exact (measurableSet_lt measurable_const hV).inter
        (measurableSet_eq_fun hsstar measurable_const)
  have h2 := congrArg ENNReal.toReal hmain
  rw [ENNReal.toReal_one, ENNReal.toReal_ofReal (Finset.sum_nonneg hnonneg)] at h2
  simp_rw [hint] at h2
  exact h2.symm
