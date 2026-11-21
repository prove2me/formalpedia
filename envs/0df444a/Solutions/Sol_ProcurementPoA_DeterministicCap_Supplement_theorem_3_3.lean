-- Prove2me | solution 1 for ProcurementPoA.DeterministicCap.Supplement.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:11:41.60048+00:00
-- url     : https://prove2.me/submissions/409dcf59-f6cf-4b44-b4d9-cd8f0851dd19

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction
import Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_lemma_3_1

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T33

/-- index of the first lowest bid -/
noncomputable def firstLow {n : ℕ} (b : Suppliers n → ℝ) : Suppliers n :=
  (Finset.univ.filter (fun i => ∀ j, b i ≤ b j)).min' (by
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ b Finset.univ_nonempty
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => hi j (Finset.mem_univ _)⟩⟩)

lemma firstLow_mem {n : ℕ} (b : Suppliers n → ℝ) : ∀ j, b (firstLow b) ≤ b j := by
  have := Finset.min'_mem (Finset.univ.filter (fun i => ∀ j, b i ≤ b j)) (by
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ b Finset.univ_nonempty
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => hi j (Finset.mem_univ _)⟩⟩)
  exact (Finset.mem_filter.1 this).2

lemma firstLow_eq_iff {n : ℕ} (b : Suppliers n → ℝ) (i : Suppliers n) :
    firstLow b = i ↔ (∀ j, b i ≤ b j) ∧ ∀ k : Suppliers n, k < i → ∃ j, b j < b k := by
  constructor
  · intro h
    refine ⟨fun j => h ▸ firstLow_mem b j, fun k hk => ?_⟩
    by_contra hcon
    push_neg at hcon
    have hmem : k ∈ Finset.univ.filter (fun i => ∀ j, b i ≤ b j) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩
    have := Finset.min'_le _ k hmem
    have h2 : firstLow b ≤ k := this
    rw [h] at h2
    exact absurd hk (not_lt.2 h2)
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact Finset.min'_le _ i (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩)
    · by_contra hlt
      push_neg at hlt
      obtain ⟨j, hj⟩ := h2 _ hlt
      exact absurd (firstLow_mem b j) (not_le.2 hj)

lemma measurable_firstLow {n : ℕ} : Measurable (firstLow : (Suppliers n → ℝ) → Suppliers n) := by
  apply measurable_to_countable'
  intro i
  have : firstLow ⁻¹' {i} =
      {b : Suppliers n → ℝ | (∀ j, b i ≤ b j) ∧ ∀ k : Suppliers n, k < i → ∃ j, b j < b k} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact firstLow_eq_iff b i
  rw [this]
  have h1 : MeasurableSet {b : Suppliers n → ℝ | ∀ j, b i ≤ b j} := by
    have : {b : Suppliers n → ℝ | ∀ j, b i ≤ b j} = ⋂ j, {b | b i ≤ b j} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
  have h2 : MeasurableSet {b : Suppliers n → ℝ | ∀ k : Suppliers n, k < i → ∃ j, b j < b k} := by
    have : {b : Suppliers n → ℝ | ∀ k : Suppliers n, k < i → ∃ j, b j < b k} =
        ⋂ k, ⋂ (_ : k < i), ⋃ j, {b | b j < b k} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun j => measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply k)
  exact h1.inter h2

noncomputable def tie (n : ℕ) : TieRule n where
  select := Kernel.deterministic firstLow measurable_firstLow
  markov := inferInstance
  lowest_only b := by
    simp only [Kernel.deterministic_apply]
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.2 (firstLow_mem b)

lemma sum_select {n : ℕ} (τ : TieRule n) (b : Suppliers n → ℝ) : ∑ i, τ.select b {i} = 1 := by
  rw [sum_measure_singleton]; simp

lemma ae_cost_mem {n : ℕ} (D : IndependentTypes n) (σ : MixedProfile n) :
    ∀ᵐ x ∂(playLaw D σ), ∀ i, (x i).1 ∈ D.types i := by
  rw [ae_all_iff]
  intro i
  have hq := (measurePreserving_eval (fun i => D.law i ⊗ₘ σ.bid i) i).quasiMeasurePreserving
  have h1 : ∀ᵐ y ∂(D.law i ⊗ₘ σ.bid i), y.1 ∈ D.types i := by
    have h2 : ∀ᵐ y ∂(D.law i ⊗ₘ σ.bid i).fst, y ∈ D.types i := by
      rw [Measure.fst_compProd]
      exact mem_ae_iff.2 (D.concentrated i)
    exact ae_of_ae_map measurable_fst.aemeasurable h2
  exact hq.ae h1

lemma ae_type_mem {n : ℕ} (D : IndependentTypes n) :
    ∀ᵐ c ∂(typeLaw D), ∀ i, c i ∈ D.types i := by
  rw [ae_all_iff]
  intro i
  have hq := (measurePreserving_eval D.law i).quasiMeasurePreserving
  exact hq.ae (mem_ae_iff.2 (D.concentrated i))

lemma ratio_le {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    {L U : ℝ} (hL : 0 < L) (hcost : InCostInterval D L U) :
    standardSocialCost D τ σ / optimalSocialCost D ≤ ENNReal.ofReal (U / L) := by
  haveI : IsProbabilityMeasure (playLaw D σ) := by unfold playLaw; infer_instance
  haveI : IsProbabilityMeasure (typeLaw D) := by unfold typeLaw; infer_instance
  have hSC : standardSocialCost D τ σ ≤ ENNReal.ofReal U := by
    unfold standardSocialCost
    calc ∫⁻ x, winnerCost τ x ∂(playLaw D σ) ≤ ∫⁻ _x, ENNReal.ofReal U ∂(playLaw D σ) := by
          apply lintegral_mono_ae
          filter_upwards [ae_cost_mem D σ] with x hx
          unfold winnerCost
          calc ∑ i, ENNReal.ofReal (x i).1 * τ.select (fun j => (x j).2) {i}
              ≤ ∑ i, ENNReal.ofReal U * τ.select (fun j => (x j).2) {i} := by
                apply Finset.sum_le_sum
                intro i _
                exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hcost i (hx i)).2) le_rfl
            _ = ENNReal.ofReal U := by rw [← Finset.mul_sum, sum_select, mul_one]
      _ = ENNReal.ofReal U := by simp
  have hOPT : ENNReal.ofReal L ≤ optimalSocialCost D := by
    unfold optimalSocialCost
    calc ENNReal.ofReal L = ∫⁻ _c, ENNReal.ofReal L ∂(typeLaw D) := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_type_mem D] with c hc
        apply ENNReal.ofReal_le_ofReal
        unfold lowest
        exact Finset.le_inf' _ _ (fun i _ => (hcost i (hc i)).1)
  calc standardSocialCost D τ σ / optimalSocialCost D ≤ ENNReal.ofReal U / ENNReal.ofReal L :=
        ENNReal.div_le_div hSC hOPT
    _ = ENNReal.ofReal (U / L) := (ENNReal.ofReal_div_of_pos hL).symm

noncomputable def costs (L U : ℝ) (n : ℕ) : Suppliers n → ℝ := fun i => if i = 0 then L else U

lemma costs_sum (L U : ℝ) (n : ℕ) : ∑ i, costs L U n i = L + n * U := by
  rw [Fin.sum_univ_succ]
  simp [costs]

lemma costs_lowest {L U : ℝ} (hLU : L ≤ U) (n : ℕ) : lowest (costs L U n) = L := by
  unfold lowest
  apply le_antisymm
  · exact Finset.inf'_le _ (Finset.mem_univ 0) |>.trans (by simp [costs])
  · exact Finset.le_inf' _ _ (fun i _ => by simp only [costs]; split_ifs <;> linarith)

lemma inCostInterval_costs {L U : ℝ} (hLU : L ≤ U) (n : ℕ) :
    InCostInterval (deterministicTypes (costs L U n)) L U := by
  intro i x hx
  simp only [deterministicTypes, Set.mem_singleton_iff] at hx
  subst hx
  simp only [costs, Set.mem_Icc]
  split_ifs <;> constructor <;> linarith

lemma instance_le {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) {L U : ℝ}
    (hcost : InCostInterval D L U) :
    standardInstancePoA D τ ≤ standardPoA L U := by
  unfold standardInstancePoA standardPoA
  apply sSup_le_sSup
  rintro q ⟨σ, hσ, rfl⟩
  exact ⟨n, D, τ, σ, hcost, hσ, rfl⟩

lemma part1 {L U : ℝ} (hL : 0 < L) (hLU : L < U) : standardPoA L U = ENNReal.ofReal (U / L) := by
  apply le_antisymm
  · apply sSup_le
    rintro q ⟨n, D, τ, σ, hcost, _, rfl⟩
    exact ratio_le D τ σ hL hcost
  · have hlow : ∀ k : ℕ, ENNReal.ofReal (U / L + (L - U) / L * (1 / ((k : ℝ) + 2))) ≤
        standardPoA L U := by
      intro k
      have h1 := lemma_3_1 (n := k + 1) (by omega) (costs L U (k + 1)) (tie (k + 1))
      have h2 := h1.2 (by rw [costs_lowest hLU.le]; exact hL)
      refine le_trans ?_ ((h2.trans (instance_le _ _ (inCostInterval_costs hLU.le _))))
      apply le_of_eq
      congr 1
      rw [costs_sum, costs_lowest hLU.le]
      push_cast
      field_simp
      ring
    have htend : Tendsto (fun k : ℕ => ENNReal.ofReal (U / L + (L - U) / L * (1 / ((k : ℝ) + 2))))
        atTop (𝓝 (ENNReal.ofReal (U / L))) := by
      apply (ENNReal.tendsto_ofReal)
      have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
        refine this.congr (fun k => ?_)
        simp only [Function.comp]
        push_cast; ring_nf
      simpa using (tendsto_const_nhds (x := U / L)).add (h0.const_mul ((L - U) / L))
    exact le_of_tendsto htend (Eventually.of_forall hlow)

end ProcurementPoA.DeterministicCap.Supplement.Dev.T33

namespace ProcurementPoA.DeterministicCap.Supplement

open Dev.T33 in
theorem chk_theorem_3_3 :
    (∀ L U : ℝ, 0 < L → L < U → standardPoA L U = ENNReal.ofReal (U / L)) ∧
    (∀ M : ℝ, ∃ (L U : ℝ) (n : ℕ) (D : IndependentTypes n)
      (τ : TieRule n) (σ : MixedProfile n),
      0 < L ∧ L < U ∧ InCostInterval D L U ∧ IsStandardBNE D τ σ ∧
      ENNReal.ofReal M < standardSocialCost D τ σ / optimalSocialCost D) := by
  refine ⟨fun L U hL hLU => part1 hL hLU, fun M => ?_⟩
  have hU : (1 : ℝ) < max M 1 + 1 := by linarith [le_max_right M 1]
  have h := part1 (L := 1) (U := max M 1 + 1) one_pos hU
  have hlt : ENNReal.ofReal M < standardPoA 1 (max M 1 + 1) := by
    rw [h, div_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [le_max_right M 1])).2
      (by linarith [le_max_left M 1])
  unfold standardPoA at hlt
  obtain ⟨q, ⟨n, D, τ, σ, hcost, hσ, rfl⟩, hq⟩ := lt_sSup_iff.1 hlt
  exact ⟨1, max M 1 + 1, n, D, τ, σ, one_pos, hU, hcost, hσ, hq⟩

end ProcurementPoA.DeterministicCap.Supplement
end

theorem solution : type_of% @ProcurementPoA.DeterministicCap.Supplement.chk_theorem_3_3 := @ProcurementPoA.DeterministicCap.Supplement.chk_theorem_3_3
