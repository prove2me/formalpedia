-- Prove2me | solution 1 for PeriodicMAB.Lower.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:49:10.751194+00:00
-- url     : https://prove2.me/submissions/acde80be-0e9c-4a5a-8814-f7aea94f4f72

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_PeriodicMAB_Lower_Model
import Theorems.Thm_PeriodicMAB_Lower_lemma_13
import Theorems.Thm_PeriodicMAB_Lower_fact_1_dense
import Theorems.Thm_PeriodicMAB_Lower_fact_2_continuity

open MeasureTheory ProbabilityTheory BanditAlgorithm PeriodicMAB.Lower

namespace PMABRelabelAux

/-- Relabel the arms of a history by a permutation. -/
def relabelHist {K : ℕ} (σ : Equiv.Perm (Fin K)) {n : ℕ} (h : BanditHistory K n) :
    BanditHistory K n :=
  fun i => (σ (h i).1, (h i).2)

lemma measurable_relabelHist {K : ℕ} (σ : Equiv.Perm (Fin K)) (n : ℕ) :
    Measurable (relabelHist σ (n := n)) := by
  apply measurable_pi_lambda
  intro i
  exact ((Measurable.of_discrete (f := (σ : Fin K → Fin K))).comp
    (measurable_fst.comp (measurable_pi_apply i))).prodMk
    (measurable_snd.comp (measurable_pi_apply i))

lemma relabelHist_symm {K : ℕ} (σ : Equiv.Perm (Fin K)) {n : ℕ} (h : BanditHistory K n) :
    relabelHist σ.symm (relabelHist σ h) = h := by
  funext i; simp [relabelHist]

/-- The policy that plays, in the `σ`-relabelled world, what `π` plays in the original one. -/
noncomputable def relabelPolicy {K : ℕ} (σ : Equiv.Perm (Fin K)) (π : BanditPolicy K) :
    BanditPolicy K where
  select := fun n => ((π.select n).comap (relabelHist σ.symm) (measurable_relabelHist _ n)).map σ
  markov n := Kernel.IsMarkovKernel.map _ (Measurable.of_discrete)

lemma map_compProd_eq {α β α' β' : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace α'] [MeasurableSpace β'] (P : Measure α) [IsProbabilityMeasure P]
    (κ : Kernel α β) [IsMarkovKernel κ] (κ' : Kernel α' β') [IsMarkovKernel κ']
    {f : α → α'} {g : β → β'} (hf : Measurable f) (hg : Measurable g)
    (hκ : ∀ a, κ' (f a) = (κ a).map g) :
    (P.map f).compProd κ' = (P.compProd κ).map (Prod.map f g) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (hf.prodMap hg) hs,
    Measure.compProd_apply ((hf.prodMap hg) hs),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  congr 1
  funext a
  rw [hκ a, Measure.map_apply hg (measurable_prodMk_left hs)]
  rfl

lemma step_relabel {K : ℕ} (σ : Equiv.Perm (Fin K)) (π : BanditPolicy K) (m : Fin K → ℝ)
    (n : ℕ) (h : BanditHistory K n) :
    banditStepKernel (gaussianBandit m) (relabelPolicy σ π) n (relabelHist σ h) =
      (banditStepKernel (gaussianBandit (fun a => m (σ a))) π n h).map
        (Prod.map σ id) := by
  ext s hs
  have hmeas : Measurable (Prod.map (σ : Fin K → Fin K) (id : ℝ → ℝ)) :=
    (Measurable.of_discrete).prodMap measurable_id
  rw [Measure.map_apply hmeas hs]
  simp only [banditStepKernel]
  rw [Kernel.compProd_apply hs, Kernel.compProd_apply (hmeas hs)]
  simp only [relabelPolicy]
  rw [Kernel.map_apply _ (Measurable.of_discrete), Kernel.comap_apply, relabelHist_symm,
    lintegral_map (Measurable.of_discrete) (Measurable.of_discrete)]
  congr 1

lemma periodicMeasure_relabel {K : ℕ} (σ : Equiv.Perm (Fin K)) (μ : Fin K → ℕ → ℝ)
    (π : BanditPolicy K) (n : ℕ) :
    periodicMeasure μ (relabelPolicy σ π) n =
      (periodicMeasure (fun k => μ (σ k)) π n).map (relabelHist σ) := by
  induction n with
  | zero =>
    simp only [periodicMeasure]
    rw [Measure.map_dirac' (measurable_relabelHist σ 0)]
    congr 1
    funext t; exact t.elim0
  | succ n ih =>
    simp only [periodicMeasure]
    rw [ih, map_compProd_eq _ _ _ (measurable_relabelHist σ n)
      ((Measurable.of_discrete (f := (σ : Fin K → Fin K))).prodMap measurable_id)
      (fun h => step_relabel σ π (fun a => μ a (n + 1)) n h),
      Measure.map_map measurable_banditHistorySnoc
        ((measurable_relabelHist σ n).prodMap
          ((Measurable.of_discrete (f := (σ : Fin K → Fin K))).prodMap measurable_id)),
      Measure.map_map (measurable_relabelHist σ (n + 1)) measurable_banditHistorySnoc]
    congr 1
    funext p
    funext i
    simp only [Function.comp, relabelHist]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Prod.map]
    · simp [relabelHist]

lemma periodicRegret_relabel {K : ℕ} [NeZero K] (σ : Equiv.Perm (Fin K))
    (μ : Fin K → ℕ → ℝ) (π : BanditPolicy K) (T : ℕ) :
    periodicRegret (fun k => μ (σ k)) π T = periodicRegret μ (relabelPolicy σ π) T := by
  unfold periodicRegret
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hsup : (Finset.univ.sup' Finset.univ_nonempty (fun k => μ (σ k) ((i : ℕ) + 1))) =
      Finset.univ.sup' Finset.univ_nonempty (fun k => μ k ((i : ℕ) + 1)) := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun k _ => Finset.le_sup' (fun k => μ k ((i : ℕ) + 1))
        (Finset.mem_univ (σ k)))
    · refine Finset.sup'_le _ _ (fun k _ => ?_)
      calc μ k ((i : ℕ) + 1) = μ (σ (σ.symm k)) ((i : ℕ) + 1) := by simp
        _ ≤ _ := Finset.le_sup' (fun k => μ (σ k) ((i : ℕ) + 1)) (Finset.mem_univ (σ.symm k))
  rw [hsup, periodicMeasure_relabel, integral_map (measurable_relabelHist σ T).aemeasurable]
  · rfl
  · exact (Measurable.aestronglyMeasurable
      ((Measurable.of_discrete (f := fun a : Fin K => μ a ((i : ℕ) + 1))).comp
        (measurable_fst.comp (measurable_pi_apply i))))

end PMABRelabelAux

open PMABRelabelAux in
theorem solution (K T : ℕ) [NeZero K] (Tper : Fin K → ℕ) (hK : 2 ≤ K)
    (hTper : ∀ k, 1 ≤ Tper k) (hA3 : Assumption3 K T Tper) (π : BanditPolicy K) :
    ∃ μ : Fin K → ℕ → ℝ, InE3 T Tper μ ∧
      Real.sqrt ((T : ℝ) * ((Finset.univ.sup Tper : ℕ) : ℝ)) / (32 * Real.exp 1) ≤
        periodicRegret μ π T := by
  obtain ⟨kstar, -, hkstar⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty Tper
  set σ : Equiv.Perm (Fin K) := Equiv.swap 0 kstar with hσ
  set Tper' : Fin K → ℕ := fun k => Tper (σ k) with hTper'
  have hT0 : Tper' 0 = Tper kstar := by simp [hTper', hσ]
  set π' := relabelPolicy σ π with hπ'
  obtain ⟨hA1, hA2, hA3k⟩ := hA3
  have hA3' : Assumption3 K T (Function.update (fun _ => 1) 0 (Tper' 0)) := by
    refine ⟨hA1, hA2, fun k => ?_⟩
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [Function.update_self, hT0]; exact hA3k kstar
    · simp only [Function.update_of_ne hk]
      have := hA3k 0
      have h1 : (1 : ℝ) ≤ Tper 0 := by exact_mod_cast hTper 0
      push_cast; linarith
  have hT1 : 1 ≤ Tper' 0 := hTper _
  obtain ⟨μ, hμE2, -, hμreg⟩ := lemma_13 K T (Tper' 0) hK hT1 hA3' π'
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  set B := Real.sqrt ((T : ℝ) * (Tper' 0 : ℝ)) / (16 * Real.exp 1) with hB
  have hBpos : 0 < B := by
    apply div_pos _ (by positivity)
    apply Real.sqrt_pos.mpr
    have : (1 : ℝ) ≤ Tper' 0 := by exact_mod_cast hT1
    positivity
  obtain ⟨δ, hδ, hcont⟩ := fact_2_continuity K T Tper' hK (fun k => hTper _) μ (Or.inl hμE2)
    (B / 2) (by linarith)
  obtain ⟨μ₂, hμ₂E3, -, hdist⟩ := fact_1_dense K T Tper' hK (fun k => hTper _) μ hμE2 δ hδ
  have hclose := hcont π' μ₂ (Or.inr hμ₂E3) hdist
  refine ⟨fun k => μ₂ (σ k), ?_, ?_⟩
  · obtain ⟨hper, hbd⟩ := hμ₂E3
    refine ⟨fun k => ?_, fun k t ht1 ht2 => hbd (σ k) t ht1 ht2⟩
    have := hper (σ k)
    simpa [hTper', hσ, Equiv.swap_apply_self] using this
  · rw [periodicRegret_relabel σ μ₂ π T, ← hπ', hkstar, ← hT0]
    have h2 : Real.sqrt ((T : ℝ) * (Tper' 0 : ℝ)) / (32 * Real.exp 1) = B / 2 := by
      rw [hB]; field_simp; ring
    rw [h2]
    have := abs_lt.mp hclose
    linarith [this.2]
