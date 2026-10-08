-- Prove2me | solution 1 for ScenarioApproach.Nonconvex.violation_tail_le_beta
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:32:16.806271+00:00
-- url     : https://prove2.me/submissions/e1fa85ca-d6bc-420d-817e-6f47d7889098

import Mathlib
import Definitions.Def_ScenarioApproach_Nonconvex_violation
import Definitions.Def_ScenarioApproach_Nonconvex_scenarioProgram
import Definitions.Def_ScenarioApproach_Nonconvex_supportSet
import Definitions.Def_ScenarioApproach_Nonconvex_epsBeta

set_option autoImplicit false

open MeasureTheory

namespace VTLB07f2

open ScenarioApproach.Nonconvex

lemma isSolutionOn_congr {Θ Δ : Type*} {N : ℕ} (f : Θ → ℝ) (Θδ : Δ → Set Θ)
    (ω ω' : Fin N → Δ) (J : Finset (Fin N)) (h : ∀ i ∈ J, ω i = ω' i) (θ : Θ) :
    IsSolutionOn f Θδ ω J θ ↔ IsSolutionOn f Θδ ω' J θ := by
  have hF : feasibleOn Θδ ω J = feasibleOn Θδ ω' J := by
    ext t; simp only [feasibleOn, Set.mem_ofPred_eq]
    constructor
    · intro ht i hi; rw [← h i hi]; exact ht i hi
    · intro ht i hi; rw [h i hi]; exact ht i hi
  simp only [IsSolutionOn, hF]

lemma violation_le_one {Θ Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ)
    [IsProbabilityMeasure P] (Θδ : Δ → Set Θ) (θ : Θ) : violation P Θδ θ ≤ 1 := by
  unfold violation
  have := prob_le_one (μ := P) (s := violationSet Θδ θ)
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)

lemma measurable_violation {Θ Δ : Type*} [MeasurableSpace Θ] [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P] (Θδ : Δ → Set Θ)
    (hmeas : MeasurableSet {p : Θ × Δ | p.1 ∈ Θδ p.2}) :
    Measurable (fun θ => violation P Θδ θ) := by
  have h := measurable_measure_prodMk_left (ν := P) hmeas.compl
  refine ENNReal.measurable_toReal.comp ?_
  convert h using 2
  rfl

lemma prob_good_le {Θ Δ : Type*} [MeasurableSpace Θ] [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P] (Θδ : Δ → Set Θ)
    (hmeas : MeasurableSet {p : Θ × Δ | p.1 ∈ Θδ p.2}) (θ : Θ) (e : ℝ)
    (he : e < violation P Θδ θ) : P {δ | θ ∈ Θδ δ} ≤ ENNReal.ofReal (1 - e) := by
  have hm : MeasurableSet {δ | θ ∈ Θδ δ} := measurable_prodMk_left hmeas
  have hc : violationSet Θδ θ = {δ | θ ∈ Θδ δ}ᶜ := by ext; simp [violationSet]
  have hsum : (P {δ | θ ∈ Θδ δ}).toReal + violation P Θδ θ = 1 := by
    unfold violation; rw [hc, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl hm, measure_univ, ENNReal.toReal_one]
  rw [← ENNReal.ofReal_toReal (measure_ne_top P {δ | θ ∈ Θδ δ})]
  exact ENNReal.ofReal_le_ofReal (by linarith)


lemma thetastar_eq {Θ Δ : Type*} {N : ℕ} (f : Θ → ℝ) (Θδ : Δ → Set Θ)
    (θstar : (Fin N → Δ) → Θ)
    (hθstar : ∀ ω, IsUniqueSolutionOn f Θδ ω Finset.univ (θstar ω))
    (alg : (Fin N → Δ) → Finset (Fin N))
    (halg : ∀ ω, IsSupportSet f Θδ ω (alg ω)) (J : Finset (Fin N))
    (ω ω0 : Fin N → Δ) (hJ : alg ω = J) (hJ0 : alg ω0 = J) (hag : ∀ i ∈ J, ω i = ω0 i) :
    θstar ω = θstar ω0 := by
  have uJ : ∀ w, alg w = J → IsUniqueSolutionOn f Θδ w J (θstar w) := by
    intro w hw
    obtain ⟨θ, h1, h2⟩ := halg w
    have : θ = θstar w := (hθstar w).2 θ h1.1
    rw [← this, ← hw]; exact h2
  have h1 := uJ ω hJ
  have h0 := uJ ω0 hJ0
  exact h0.2 _ ((isSolutionOn_congr f Θδ ω ω0 J hag _).1 h1.1)

lemma eventJ_bound {Θ Δ : Type*} [MeasurableSpace Θ] [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (f : Θ → ℝ) (Θδ : Δ → Set Θ) (N : ℕ)
    (hmeas : MeasurableSet {p : Θ × Δ | p.1 ∈ Θδ p.2})
    (θstar : (Fin N → Δ) → Θ)
    (hθstar : ∀ ω, IsUniqueSolutionOn f Θδ ω Finset.univ (θstar ω))
    (hθstar_meas : Measurable θstar)
    (alg : (Fin N → Δ) → Finset (Fin N))
    (halg : ∀ ω, IsSupportSet f Θδ ω (alg ω))
    (halg_meas : ∀ J : Finset (Fin N), MeasurableSet {ω | alg ω = J})
    (J : Finset (Fin N)) (c : ℝ) :
    Measure.pi (fun _ : Fin N => P) {ω | alg ω = J ∧ c < violation P Θδ (θstar ω)}
      ≤ ENNReal.ofReal (1 - c) ^ (N - J.card) := by
  classical
  set E := {ω : Fin N → Δ | alg ω = J ∧ c < violation P Θδ (θstar ω)} with hEdef
  have hE : MeasurableSet E :=
    (halg_meas J).inter (measurableSet_lt measurable_const
      ((measurable_violation P Θδ hmeas).comp hθstar_meas))
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin N => P) (fun i => i ∈ J)
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => Δ) (fun i => i ∈ J) with he
  rw [← (MeasurePreserving.symm e hp).measure_preimage_equiv E,
    Measure.prod_apply (e.symm.measurable hE)]
  have hsymm : ∀ (x : {i // i ∈ J} → Δ) (y : {i // i ∉ J} → Δ) (i : Fin N),
      e.symm (x, y) i = if h : i ∈ J then x ⟨i, h⟩ else y ⟨i, h⟩ := by
    intro x y i; rfl
  have hcard : Fintype.card {i : Fin N // i ∉ J} = N - J.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  refine (lintegral_mono (g := fun _ => ENNReal.ofReal (1 - c) ^ (N - J.card)) fun x => ?_).trans
    (by simp [lintegral_const, measure_univ])
  by_cases hne : (Prod.mk x ⁻¹' (e.symm ⁻¹' E)).Nonempty
  · obtain ⟨y0, hy0⟩ := hne
    have hy0' : alg (e.symm (x, y0)) = J ∧ c < violation P Θδ (θstar (e.symm (x, y0))) := hy0
    set θ0 := θstar (e.symm (x, y0)) with hθ0
    have key : Prod.mk x ⁻¹' (e.symm ⁻¹' E) ⊆ Set.pi Set.univ (fun _ => {δ | θ0 ∈ Θδ δ}) := by
      intro y hy
      have hy' : alg (e.symm (x, y)) = J ∧ c < violation P Θδ (θstar (e.symm (x, y))) := hy
      have heq : θstar (e.symm (x, y)) = θ0 :=
        thetastar_eq f Θδ θstar hθstar alg halg J _ _ hy'.1 hy0'.1
          (fun i hi => by rw [hsymm, hsymm, dif_pos hi, dif_pos hi])
      intro i _
      have hf := (hθstar (e.symm (x, y))).1.1 i.1 (Finset.mem_univ _)
      rw [heq, hsymm, dif_neg i.2] at hf
      exact hf
    calc Measure.pi (fun _ : {i // i ∉ J} => P) (Prod.mk x ⁻¹' (e.symm ⁻¹' E))
        ≤ Measure.pi (fun _ : {i // i ∉ J} => P) (Set.pi Set.univ (fun _ => {δ | θ0 ∈ Θδ δ})) :=
          measure_mono key
      _ = P {δ | θ0 ∈ Θδ δ} ^ (N - J.card) := by
          rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ, hcard]
      _ ≤ ENNReal.ofReal (1 - c) ^ (N - J.card) := by
          gcongr
          exact prob_good_le P Θδ hmeas θ0 c hy0'.2
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]; exact zero_le

end VTLB07f2

open ScenarioApproach.Nonconvex in
theorem solution {Θ Δ : Type*} [MeasurableSpace Θ] [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (f : Θ → ℝ) (Θδ : Δ → Set Θ) (N : ℕ)
    (hmeas : MeasurableSet {p : Θ × Δ | p.1 ∈ Θδ p.2})
    (θstar : (Fin N → Δ) → Θ)
    (hθstar : ∀ ω, IsUniqueSolutionOn f Θδ ω Finset.univ (θstar ω))
    (hθstar_meas : Measurable θstar)
    (alg : (Fin N → Δ) → Finset (Fin N))
    (halg : ∀ ω, IsSupportSet f Θδ ω (alg ω))
    (halg_meas : ∀ J : Finset (Fin N), MeasurableSet {ω | alg ω = J})
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P)
        {ω | epsBeta N β (alg ω).card < violation P Θδ (θstar ω)} ≤ ENNReal.ofReal β := by
  classical
  set g : ℕ → ℝ := fun k => if k = N then 0 else β / ((N : ℝ) * (N.choose k : ℝ)) with hg
  have hgnn : ∀ k, 0 ≤ g k := by
    intro k; simp only [hg]; split_ifs
    · exact le_rfl
    · positivity
  have hJ : ∀ J : Finset (Fin N),
      Measure.pi (fun _ : Fin N => P)
        {ω | alg ω = J ∧ epsBeta N β J.card < violation P Θδ (θstar ω)}
        ≤ ENNReal.ofReal (g J.card) := by
    intro J
    by_cases hk : J.card = N
    · have : {ω : Fin N → Δ | alg ω = J ∧ epsBeta N β J.card < violation P Θδ (θstar ω)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
        intro _
        rw [epsBeta, if_pos hk]
        exact VTLB07f2.violation_le_one P Θδ _
      rw [this, measure_empty]; exact zero_le
    · refine (VTLB07f2.eventJ_bound P f Θδ N hmeas θstar hθstar hθstar_meas alg halg halg_meas
        J _).trans (le_of_eq ?_)
      have hm : (N - J.card) ≠ 0 := by
        have := card_finset_fin_le J; omega
      have hx : 0 ≤ β / ((N : ℝ) * (N.choose J.card : ℝ)) := by positivity
      rw [epsBeta, if_neg hk, sub_sub_cancel, ← ENNReal.ofReal_pow (by positivity), one_div,
        Real.rpow_inv_natCast_pow hx hm]
      simp only [hg, if_neg hk]
  have hsub : {ω : Fin N → Δ | epsBeta N β (alg ω).card < violation P Θδ (θstar ω)} ⊆
      ⋃ J ∈ (Finset.univ : Finset (Finset (Fin N))),
        {ω | alg ω = J ∧ epsBeta N β J.card < violation P Θδ (θstar ω)} := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_univ, exists_true_left]
    exact ⟨alg ω, rfl, hω⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
    ((Finset.sum_le_sum fun J _ => hJ J).trans ?_))
  rw [← ENNReal.ofReal_sum_of_nonneg (fun J _ => hgnn _)]
  apply ENNReal.ofReal_le_ofReal
  have hsum : ∑ J : Finset (Fin N), g J.card = ∑ m ∈ Finset.range N, (N.choose m) • g m := by
    rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card, Finset.card_univ,
      Fintype.card_fin, Finset.sum_range_succ]
    simp [hg]
  rw [hsum]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simpa using hβ0
  have : ∀ m ∈ Finset.range N, (N.choose m) • g m = β / N := by
    intro m hm
    have hmN : m < N := Finset.mem_range.1 hm
    have hc : (0 : ℝ) < N.choose m := by exact_mod_cast Nat.choose_pos hmN.le
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [hg, if_neg hmN.ne, nsmul_eq_mul]
    field_simp
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mul_div_cancel₀ _ hN'.ne']
