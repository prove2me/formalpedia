-- Prove2me | solution 1 for ScenarioApproach.Generalization.violation_tail_eq_binomial_sum_of_fullySupported
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:52:28.137045+00:00
-- url     : https://prove2.me/submissions/03f09f2a-2661-447d-bf6e-c2378d160179
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint
import Definitions.Def_ScenarioExact_PartOne_Basic
import Theorems.Thm_ScenarioExact_PartOne_tail_eq_choose_mul_integral
import Theorems.Thm_ScenarioExact_PartOne_violationLaw_Iic_eq_pow
import Theorems.Thm_ScenarioExact_PartOne_choose_mul_integral_eq_binomial_sum

set_option autoImplicit false

open MeasureTheory ScenarioApproach.Generalization
open scoped ENNReal

namespace CFFA

theorem essential_index_set {d k : ℕ} {Δ : Type*} (c : EuclideanSpace ℝ (Fin d))
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ) (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ))
    (ω : Fin k → Δ) (θ : EuclideanSpace ℝ (Fin d)) (hθ : IsSolution c Θ Θδ ω θ) :
    ∃ J : Finset (Fin k), J.card ≤ d ∧
      ∀ θ' ∈ Θ, (∀ j ∈ J, θ' ∈ Θδ (ω j)) → inner ℝ c θ ≤ inner ℝ c θ' := by
  classical
  by_contra hcon
  push Not at hcon
  let F : Option (Fin k) → Set (EuclideanSpace ℝ (Fin d)) := fun o =>
    match o with
    | none => Θ ∩ {x | inner ℝ c x < inner ℝ c θ}
    | some i => Θδ (ω i)
  have hconv : ∀ o ∈ (Finset.univ : Finset (Option (Fin k))), Convex ℝ (F o) := by
    intro o _
    cases o with
    | none =>
      refine hΘ_convex.inter ?_
      have := convex_halfSpace_lt (innerₛₗ ℝ c).isLinear (inner ℝ c θ)
      simpa using this
    | some i => exact hΘδ_convex _
  have hinter : ∀ I ⊆ (Finset.univ : Finset (Option (Fin k))),
      I.card ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) + 1 → (⋂ o ∈ I, F o).Nonempty := by
    intro I _ hI
    rw [finrank_euclideanSpace_fin] at hI
    by_cases hn : none ∈ I
    · let J : Finset (Fin k) := Finset.univ.filter (fun j => some j ∈ I)
      have hJ : J.card ≤ d := by
        have h1 : J.map Function.Embedding.some ⊆ I.erase none := by
          intro o ho
          simp only [Finset.mem_map, J, Finset.mem_filter, Finset.mem_univ, true_and,
            Function.Embedding.some_apply] at ho
          obtain ⟨j, hj, rfl⟩ := ho
          exact Finset.mem_erase.2 ⟨by simp, hj⟩
        have h2 := Finset.card_le_card h1
        rw [Finset.card_map, Finset.card_erase_of_mem hn] at h2
        omega
      obtain ⟨θ', hΘ', hJ', hlt⟩ := hcon J hJ
      refine ⟨θ', Set.mem_iInter₂.2 fun o ho => ?_⟩
      cases o with
      | none => exact ⟨hΘ', hlt⟩
      | some i => exact hJ' i (by simp [J, ho])
    · refine ⟨θ, Set.mem_iInter₂.2 fun o ho => ?_⟩
      cases o with
      | none => exact absurd ho hn
      | some i => exact Set.mem_iInter.1 hθ.1.2 i
  obtain ⟨x, hx⟩ := Convex.helly_theorem' hconv hinter
  have hx' := Set.mem_iInter₂.1 hx
  have h0 : x ∈ Θ ∩ {x | inner ℝ c x < inner ℝ c θ} := hx' none (Finset.mem_univ _)
  have hfeas : x ∈ feasibleSet Θ Θδ ω :=
    ⟨h0.1, Set.mem_iInter.2 fun i => hx' (some i) (Finset.mem_univ _)⟩
  exact absurd (hθ.2 x hfeas) (not_le.2 h0.2)

theorem exists_drop {d k : ℕ} {Δ : Type*} (c : EuclideanSpace ℝ (Fin d))
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ) (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ))
    (hexu : ∀ (m : ℕ) (ω : Fin m → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    (hk : d ≤ k) (ω : Fin (k + 1) → Δ) (g : (Fin k → Δ) → EuclideanSpace ℝ (Fin d))
    (hg : ∀ ω, IsSolution c Θ Θδ ω (g ω)) :
    ∃ i : Fin (k + 1), ∀ j, g (Fin.removeNth i ω) ∈ Θδ (ω j) := by
  classical
  obtain ⟨θ, hθ, -⟩ := hexu (k + 1) ω
  obtain ⟨J, hJ, hess⟩ := essential_index_set c Θ Θδ hΘ_convex hΘδ_convex ω θ hθ
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := J) (t := (Finset.univ : Finset (Fin (k + 1)))) (by simp; omega)
  refine ⟨i, ?_⟩
  set ω' := Fin.removeNth i ω with hω'
  have hfeas : θ ∈ feasibleSet Θ Θδ ω' :=
    ⟨hθ.1.1, Set.mem_iInter.2 fun j => Set.mem_iInter.1 hθ.1.2 (i.succAbove j)⟩
  have h1 : inner ℝ c (g ω') ≤ inner ℝ c θ := (hg ω').2 θ hfeas
  have h2 : inner ℝ c θ ≤ inner ℝ c (g ω') := by
    refine hess _ (hg ω').1.1 fun j hj => ?_
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hji
    exact Set.mem_iInter.1 (hg ω').1.2 z
  have hsol : IsSolution c Θ Θδ ω' θ :=
    ⟨hfeas, fun x hx => le_trans h2 ((hg ω').2 x hx)⟩
  have heq : θ = g ω' := (hexu k ω').unique hsol (hg ω')
  intro j
  rw [← heq]
  exact Set.mem_iInter.1 hθ.1.2 j

theorem step {d k : ℕ} {Δ : Type*} [MeasurableSpace Δ] (c : EuclideanSpace ℝ (Fin d))
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ) (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ))
    (hexu : ∀ (m : ℕ) (ω : Fin m → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    (hk : d ≤ k) (g : (Fin k → Δ) → EuclideanSpace ℝ (Fin d))
    (hg : ∀ ω, IsSolution c Θ Θδ ω (g ω)) (hgm : Measurable g) :
    ∃ g' : (Fin (k + 1) → Δ) → EuclideanSpace ℝ (Fin d),
      (∀ ω, IsSolution c Θ Θδ ω (g' ω)) ∧ Measurable g' := by
  classical
  let idx : ℕ → Fin (k + 1) := fun n => ⟨min n k, Nat.lt_succ_of_le (min_le_right _ _)⟩
  let f : ℕ → (Fin (k + 1) → Δ) → EuclideanSpace ℝ (Fin d) :=
    fun n ω => g (Fin.removeNth (idx n) ω)
  let p : ℕ → (Fin (k + 1) → Δ) → Prop := fun n ω => ∀ j, f n ω ∈ Θδ (ω j)
  have hfm : ∀ n, Measurable (f n) := by
    intro n
    exact hgm.comp (measurable_pi_iff.2 fun j => measurable_pi_apply ((idx n).succAbove j))
  have hpm : ∀ n, MeasurableSet {ω | p n ω} := by
    intro n
    have : {ω | p n ω} = ⋂ j, (fun ω => (f n ω, ω j)) ⁻¹'
        {q : EuclideanSpace ℝ (Fin d) × Δ | q.1 ∈ Θδ q.2} := by
      ext ω; simp [p]
    rw [this]
    exact MeasurableSet.iInter fun j => ((hfm n).prodMk (measurable_pi_apply j)) hmeas
  have hex : ∀ ω, ∃ n, p n ω := by
    intro ω
    obtain ⟨i, hi⟩ := exists_drop c Θ Θδ hΘ_convex hΘδ_convex hexu hk ω g hg
    refine ⟨i.val, fun j => ?_⟩
    have : idx i.val = i := Fin.ext (Nat.min_eq_left (Nat.lt_succ_iff.1 i.2))
    simp only [f, this]
    exact hi j
  refine ⟨fun ω => f (Nat.find (hex ω)) ω, fun ω => ?_, Measurable.find hfm hpm hex⟩
  have hp := Nat.find_spec (hex ω)
  set n := Nat.find (hex ω)
  have hs := hg (Fin.removeNth (idx n) ω)
  refine ⟨⟨hs.1.1, Set.mem_iInter.2 hp⟩, fun x hx => hs.2 x ⟨hx.1, ?_⟩⟩
  exact Set.mem_iInter.2 fun j => Set.mem_iInter.1 hx.2 _

theorem base {d N k : ℕ} {Δ : Type*} [MeasurableSpace Δ] (c : EuclideanSpace ℝ (Fin d))
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (θstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθstar : ∀ ω, IsSolution c Θ Θδ ω (θstar ω)) (hθstar_meas : Measurable θstar)
    (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    ∃ g : (Fin k → Δ) → EuclideanSpace ℝ (Fin d),
      (∀ ω, IsSolution c Θ Θδ ω (g ω)) ∧ Measurable g := by
  let π : Fin N → Fin k := fun i => ⟨min i.val (k - 1), by omega⟩
  refine ⟨fun ω => θstar (fun i => ω (π i)), fun ω => ?_, ?_⟩
  · have hfe : ∀ x, x ∈ feasibleSet Θ Θδ (fun i => ω (π i)) ↔ x ∈ feasibleSet Θ Θδ ω := by
      intro x
      constructor
      · intro hx
        refine ⟨hx.1, Set.mem_iInter.2 fun j => ?_⟩
        have hj : π ⟨j.val, by omega⟩ = j := Fin.ext (by simp [π]; omega)
        have := Set.mem_iInter.1 hx.2 ⟨j.val, by omega⟩
        simpa [hj] using this
      · intro hx
        exact ⟨hx.1, Set.mem_iInter.2 fun i => Set.mem_iInter.1 hx.2 (π i)⟩
    have hs := hθstar (fun i => ω (π i))
    exact ⟨(hfe _).1 hs.1, fun x hx => hs.2 x ((hfe x).2 hx)⟩
  · exact hθstar_meas.comp (measurable_pi_iff.2 fun i => measurable_pi_apply (π i))

theorem exists_family {d N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ) (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ))
    (hexu : ∀ (m : ℕ) (ω : Fin m → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    (θstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθstar : ∀ ω, IsSolution c Θ Θδ ω (θstar ω)) (hθstar_meas : Measurable θstar)
    (hN : d ≤ N) :
    ∃ θs : (k : ℕ) → (Fin k → Δ) → EuclideanSpace ℝ (Fin d),
      (∀ k ω, IsSolution c Θ Θδ ω (θs k ω)) ∧ (∀ k, Measurable (θs k)) := by
  have key : ∀ k, ∃ g : (Fin k → Δ) → EuclideanSpace ℝ (Fin d),
      (∀ ω, IsSolution c Θ Θδ ω (g ω)) ∧ Measurable g := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun ω => Classical.choose (hexu 0 ω), fun ω => (Classical.choose_spec (hexu 0 ω)).1,
        measurable_const' fun x y => ?_⟩
      have : x = y := funext fun i => Fin.elim0 i
      rw [this]
    | succ k ih =>
      by_cases hk : N ≤ k
      · obtain ⟨g, hg, hgm⟩ := ih
        exact step c Θ Θδ hΘ_convex hΘδ_convex hexu hmeas (le_trans hN hk) g hg hgm
      · exact base c Θ Θδ θstar hθstar hθstar_meas (by omega) (by omega)
  choose θs h1 h2 using key
  exact ⟨θs, h1, h2⟩

theorem lintegral_dens_Icc {d : ℕ} (hd : 1 ≤ d) {b : ℝ} (hb0 : 0 ≤ b) :
    ∫⁻ x in Set.Icc 0 b, ENNReal.ofReal ((d : ℝ) * x ^ (d - 1)) = ENNReal.ofReal (b ^ d) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb0,
      intervalIntegral.integral_const_mul, integral_pow]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [zero_pow (by omega), sub_zero]
    field_simp
  · exact (continuous_const.mul (continuous_pow _)).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have := hx.1
    positivity

theorem violationLaw_univ_le {d : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ)
    [IsProbabilityMeasure P] (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (θs : (k : ℕ) → (Fin k → Δ) → EuclideanSpace ℝ (Fin d)) :
    ScenarioExact.PartOne.violationLaw P Θδ θs Set.univ ≤ 1 := by
  unfold ScenarioExact.PartOne.violationLaw
  by_cases hf : AEMeasurable (fun ω => violation P Θδ (θs d ω)) (Measure.pi fun _ : Fin d => P)
  · rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ, Set.preimage_univ, measure_univ]
  · rw [Measure.map_of_not_aemeasurable hf]
    simp

theorem choose_mul_lintegral {d N : ℕ} (F : Measure ℝ) (hF1 : F Set.univ ≤ 1)
    (hd : 1 ≤ d) (hN : d ≤ N)
    (hF : ∀ α ∈ Set.Icc (0 : ℝ) 1, F (Set.Iic α) = ENNReal.ofReal (α ^ d))
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hchild : (N.choose d : ℝ) * ∫ α in ε..1, (1 - α) ^ (N - d) * ((d : ℝ) * α ^ (d - 1)) =
      ∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) :
    (N.choose d : ℝ≥0∞) * ∫⁻ α in Set.Ioc ε 1, ENNReal.ofReal ((1 - α) ^ (N - d)) ∂F =
      ENNReal.ofReal
        (∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) := by
  have : IsFiniteMeasure F := ⟨lt_of_le_of_lt hF1 ENNReal.one_lt_top⟩
  set dens : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal ((d : ℝ) * x ^ (d - 1)) with hdens
  have hdm : Measurable dens := by
    have : Measurable fun x : ℝ => (d : ℝ) * x ^ (d - 1) := by fun_prop
    exact this.ennreal_ofReal
  have hFeq : F = (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity dens := by
    apply Measure.ext_of_Iic
    intro a
    rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    rcases lt_or_ge a 0 with ha | ha
    · have e1 : Set.Iic a ∩ Set.Icc (0 : ℝ) 1 = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h1 h2
        linarith
      rw [e1, Measure.restrict_empty, lintegral_zero_measure]
      refine le_antisymm ?_ (by simp)
      calc F (Set.Iic a) ≤ F (Set.Iic 0) := measure_mono (Set.Iic_subset_Iic.2 ha.le)
        _ = 0 := by
          rw [hF 0 ⟨le_rfl, zero_le_one⟩, zero_pow (by omega)]
          simp
    rcases le_or_gt a 1 with ha1 | ha1
    · have e1 : Set.Iic a ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 a := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2 ha1⟩
      rw [e1, lintegral_dens_Icc hd ha, hF a ⟨ha, ha1⟩]
    · have e1 : Set.Iic a ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 :=
        Set.inter_eq_right.2 fun x hx => le_trans hx.2 ha1.le
      rw [e1, lintegral_dens_Icc hd zero_le_one, one_pow]
      apply le_antisymm (le_trans (measure_mono (Set.subset_univ _)) (by simpa using hF1))
      calc ENNReal.ofReal 1 = F (Set.Iic 1) := by rw [hF 1 ⟨zero_le_one, le_rfl⟩, one_pow]
        _ ≤ F (Set.Iic a) := measure_mono (Set.Iic_subset_Iic.2 ha1.le)
  have hgm : Measurable fun α : ℝ => ENNReal.ofReal ((1 - α) ^ (N - d)) := by
    have : Measurable fun α : ℝ => (1 - α) ^ (N - d) := by fun_prop
    exact this.ennreal_ofReal
  rw [hFeq, MeasureTheory.restrict_withDensity measurableSet_Ioc,
    lintegral_withDensity_eq_lintegral_mul _ hdm hgm, Measure.restrict_restrict measurableSet_Ioc]
  have e2 : Set.Ioc ε 1 ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc ε 1 :=
    Set.inter_eq_left.2 fun x hx => ⟨le_trans hε0 hx.1.le, hx.2⟩
  rw [e2]
  have e3 : ∫⁻ a in Set.Ioc ε 1, (dens * fun α => ENNReal.ofReal ((1 - α) ^ (N - d))) a
      = ∫⁻ a in Set.Ioc ε 1, ENNReal.ofReal ((1 - a) ^ (N - d) * ((d : ℝ) * a ^ (d - 1))) := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro x hx
    have h1 : 0 ≤ 1 - x := by linarith [hx.2]
    simp only [Pi.mul_apply, hdens]
    rw [mul_comm, ← ENNReal.ofReal_mul (by positivity)]
  rw [e3, ← ofReal_integral_eq_lintegral_ofReal, ← intervalIntegral.integral_of_le hε1,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hchild]
  · have hc : Continuous fun a : ℝ => (1 - a) ^ (N - d) * ((d : ℝ) * a ^ (d - 1)) := by fun_prop
    exact (hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have h1 : 0 ≤ 1 - x := by linarith [hx.2]
    have h2 : 0 ≤ x := by linarith [hx.1]
    positivity

end CFFA

open CFFA in
theorem solution
    {d N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ) (hΘ_closed : IsClosed Θ)
    (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ)) (hΘδ_closed : ∀ δ, IsClosed (Θδ δ))
    (hexu : ∀ (m : ℕ) (ω : Fin m → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    (θstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθstar : ∀ ω, IsSolution c Θ Θδ ω (θstar ω)) (hθstar_meas : Measurable θstar)
    (hfs : FullySupported c Θ Θδ P)
    (hd : 1 ≤ d) (hN : d ≤ N) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P) {ω | ε < violation P Θδ (θstar ω)} =
      ENNReal.ofReal
        (∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) := by
  obtain ⟨θs, hθs, hθs_meas⟩ := CFFA.exists_family c Θ Θδ hΘ_convex hΘδ_convex hexu hmeas
    θstar hθstar hθstar_meas hN
  have hset : {ω : Fin N → Δ | ε < violation P Θδ (θstar ω)} =
      {ω | ε < violation P Θδ (θs N ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [(hexu N ω).unique (hθstar ω) (hθs N ω)]
  rw [hset, ScenarioExact.PartOne.tail_eq_choose_mul_integral P c Θ Θδ hΘ_convex hΘ_closed
    hΘδ_convex hΘδ_closed hexu hmeas θs hθs hθs_meas hfs hd hN ε hε0 hε1]
  exact CFFA.choose_mul_lintegral _ (CFFA.violationLaw_univ_le P Θδ θs) hd hN
    (ScenarioExact.PartOne.violationLaw_Iic_eq_pow P c Θ Θδ hΘ_convex hΘ_closed hΘδ_convex
      hΘδ_closed hexu hmeas θs hθs hθs_meas hfs hd) ε hε0 hε1
    (ScenarioExact.PartOne.choose_mul_integral_eq_binomial_sum hd hN ε hε0 hε1)
