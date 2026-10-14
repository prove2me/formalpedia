-- Prove2me | solution 1 for StochApproxDyn.SubgaussianNoise.deviation_tail_eq18
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:03:15.015973+00:00
-- url     : https://prove2.me/submissions/4ffb89f5-495b-4874-b6c8-d257da0e69f8

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro
import Definitions.Def_StochApproxDyn_SubgaussianNoise_Subgaussian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace


universe u

namespace StochApproxDyn.SubgaussianNoise

lemma d39_pull {Ω : Type*} {m m0 : MeasurableSpace Ω} (P : Measure[m0] Ω) (hm : m ≤ m0)
    [SigmaFinite (P.trim hm)] (X : Ω → ℝ≥0∞) (hX : Measurable X) (g : Ω → ℝ≥0∞)
    (hg : Measurable[m] g) :
    ∫⁻ ω, g ω * X ω ∂P = ∫⁻ ω, g ω * P⁻[X|m] ω ∂P := by
  have hY : Measurable P⁻[X|m] := (measurable_condLExp m P X).mono hm le_rfl
  have e : (P.withDensity X).trim hm = (P.withDensity P⁻[X|m]).trim hm := by
    refine @Measure.ext _ m _ _ fun s hs => ?_
    rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs, withDensity_apply _ (hm s hs),
      withDensity_apply _ (hm s hs), setLIntegral_condLExp hm P X hs]
  have h1 : ∫⁻ ω, g ω * X ω ∂P = ∫⁻ ω, g ω ∂((P.withDensity X).trim hm) := by
    rw [lintegral_trim hm hg, lintegral_withDensity_eq_lintegral_mul _ hX (hg.mono hm le_rfl)]
    simp [mul_comm]
  have h2 : ∫⁻ ω, g ω * P⁻[X|m] ω ∂P = ∫⁻ ω, g ω ∂((P.withDensity P⁻[X|m]).trim hm) := by
    rw [lintegral_trim hm hg, lintegral_withDensity_eq_lintegral_mul _ hY (hg.mono hm le_rfl)]
    simp [mul_comm]
  rw [h1, h2, e]

lemma d39_KL {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (Γ : ℝ) (hsg : IsSubgaussianWith P ℱ U Γ)
    (hUm : ∀ n : ℕ, StronglyMeasurable[ℱ (n + 1)] (U (n + 1)))
    (k : ℕ) (θ : EuclideanSpace ℝ (Fin d)) (g : Ω → ℝ≥0∞) (hg : Measurable[ℱ k] g) :
    ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp ⟪θ, U (k + 1) ω⟫_ℝ) ∂P
      ≤ ENNReal.ofReal (Real.exp (Γ / 2 * ‖θ‖ ^ 2)) * ∫⁻ ω, g ω ∂P := by
  obtain ⟨hint, hce⟩ := hsg k θ
  have hXm : Measurable (fun ω => ENNReal.ofReal (Real.exp ⟪θ, U (k + 1) ω⟫_ℝ)) := by
    have : StronglyMeasurable[m0] (U (k + 1)) := (hUm k).mono (ℱ.le _)
    have h2 := this.measurable
    fun_prop
  rw [d39_pull P (ℱ.le k) _ hXm g hg]
  have h3 := condLExp_ofReal (ℱ k) hint (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
  rw [mul_comm (ENNReal.ofReal _), ← lintegral_mul_const _ (hg.mono (ℱ.le k) le_rfl)]
  apply lintegral_mono_ae
  filter_upwards [h3, hce] with ω h3ω hceω
  rw [h3ω]
  gcongr


lemma d39_core {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (Γ : ℝ) (hΓ : 0 < Γ) (hsg : IsSubgaussianWith P ℱ U Γ)
    (hUm : ∀ n : ℕ, StronglyMeasurable[ℱ (n + 1)] (U (n + 1)))
    (e : EuclideanSpace ℝ (Fin d)) (he : ‖e‖ = 1) (α : ℝ) (hα : 0 < α) (c : ℕ → ℝ) (n M : ℕ) :
    P {ω | ∃ k ∈ Finset.Ioc n M, α ≤ ⟪e, ∑ i ∈ Finset.Ico n k, c i • U (i + 1) ω⟫_ℝ}
      ≤ ENNReal.ofReal (Real.exp (-α ^ 2 / (2 * Γ * ∑ i ∈ Finset.Ico n M, c i ^ 2))) := by
  obtain ⟨S, hSdef⟩ : ∃ S, S = ∑ i ∈ Finset.Ico n M, c i ^ 2 := ⟨_, rfl⟩
  rw [← hSdef]
  have hS0 : 0 ≤ S := hSdef ▸ Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hS0.eq_or_lt with hS | hSpos
  · rw [← hS]; simpa using prob_le_one
  have hnM : n < M := by
    by_contra h
    rw [Finset.Ico_eq_empty_of_le (not_lt.1 h)] at hSdef
    simp at hSdef; linarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = α / (Γ * S) := ⟨_, rfl⟩
  have hlampos : 0 < lam := hlam ▸ div_pos hα (mul_pos hΓ hSpos)
  obtain ⟨sv, hsv⟩ : ∃ sv : ℕ → Ω → ℝ,
      sv = fun k ω => ⟪e, ∑ i ∈ Finset.Ico n k, c i • U (i + 1) ω⟫_ℝ := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ → ℝ, q = fun k => ∑ i ∈ Finset.Ico n k, c i ^ 2 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ → Ω → ℝ≥0∞,
      Z = fun k ω => ENNReal.ofReal (Real.exp (lam * sv k ω - lam ^ 2 * Γ / 2 * q k)) :=
    ⟨_, rfl⟩
  obtain ⟨hit, hhit⟩ : ∃ hit : ℕ → Set Ω, hit = fun k => {ω | ∃ j ∈ Finset.Ioc n k, α ≤ sv j ω} :=
    ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : ℝ≥0∞, cc = ENNReal.ofReal (Real.exp (lam * α - lam ^ 2 * Γ / 2 * S)) :=
    ⟨_, rfl⟩
  -- measurability
  have hsm : ∀ k, Measurable[ℱ k] (sv k) := by
    intro k
    have h1 : StronglyMeasurable[ℱ k] (fun ω => ∑ i ∈ Finset.Ico n k, c i • U (i + 1) ω) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro i hi
      have : i + 1 ≤ k := (Finset.mem_Ico.1 hi).2
      exact ((hUm i).mono (ℱ.mono this)).const_smul (c i)
    rw [hsv]
    exact (stronglyMeasurable_const.inner h1).measurable
  have hhm : ∀ k, MeasurableSet[ℱ k] (hit k) := by
    intro k
    have : hit k = ⋃ j ∈ Finset.Ioc n k, {ω | α ≤ sv j ω} := by
      ext ω; simp [hhit]
    rw [this]
    refine Finset.measurableSet_biUnion _ fun j hj => ?_
    exact measurableSet_le measurable_const ((hsm j).mono (ℱ.mono (Finset.mem_Ioc.1 hj).2) le_rfl)
  have hZm : ∀ k, Measurable[ℱ k] (Z k) := by
    intro k
    rw [hZ]
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (((hsm k).const_mul lam).sub_const _))
  have claim : ∀ k, n ≤ k → k ≤ M →
      cc * P (hit k) + ∫⁻ ω, (hit k)ᶜ.indicator (Z k) ω ∂P ≤ 1 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro _
      have h1 : hit n = ∅ := by ext ω; simp [hhit]
      have h2 : ∀ ω, Z n ω = 1 := by intro ω; simp [hZ, hsv, hq]
      simp [h1, h2]
    | succ k hk ih =>
      intro hkM
      have ih := ih (by omega)
      obtain ⟨B, hB⟩ : ∃ B : Set Ω, B = {ω | α ≤ sv (k + 1) ω} := ⟨_, rfl⟩
      have hBm : MeasurableSet B := hB ▸ measurableSet_le measurable_const
        ((hsm (k + 1)).mono (ℱ.le _) le_rfl)
      have hhm0 : ∀ j, MeasurableSet (hit j) := fun j => (ℱ.le j) _ (hhm j)
      have hsplit : hit (k + 1) = hit k ∪ ((hit k)ᶜ ∩ B) := by
        ext ω
        simp only [hhit, hB, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
          Finset.mem_Ioc]
        constructor
        · rintro ⟨j, ⟨hj1, hj2⟩, hj⟩
          by_cases hjk : j ≤ k
          · exact Or.inl ⟨j, ⟨hj1, hjk⟩, hj⟩
          · by_cases h : ∃ j, (n < j ∧ j ≤ k) ∧ α ≤ sv j ω
            · exact Or.inl h
            · right; refine ⟨h, ?_⟩
              have : j = k + 1 := by omega
              exact this ▸ hj
        · rintro (⟨j, ⟨hj1, hj2⟩, hj⟩ | ⟨_, h⟩)
          · exact ⟨j, ⟨hj1, by omega⟩, hj⟩
          · exact ⟨k + 1, ⟨by omega, le_rfl⟩, h⟩
      have hPsplit : P (hit (k + 1)) = P (hit k) + P ((hit k)ᶜ ∩ B) := by
        rw [hsplit, measure_union _ ((hhm0 k).compl.inter hBm)]
        exact Set.disjoint_left.2 fun ω h1 h2 => h2.1 h1
      have hcompl : (hit (k + 1))ᶜ = (hit k)ᶜ ∩ Bᶜ := by
        rw [hsplit]; ext ω; simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff]; tauto
      -- the multiplicative relation
      obtain ⟨θ, hθ⟩ : ∃ θ : EuclideanSpace ℝ (Fin d), θ = (lam * c k) • e := ⟨_, rfl⟩
      have hθn : ‖θ‖ ^ 2 = (lam * c k) ^ 2 := by
        rw [hθ, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
      have hZrel : ∀ ω, Z (k + 1) ω = Z k ω * ENNReal.ofReal (Real.exp ⟪θ, U (k + 1) ω⟫_ℝ) *
          ENNReal.ofReal (Real.exp (-(Γ / 2 * ‖θ‖ ^ 2))) := by
        intro ω
        rw [hZ]
        simp only
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul
          (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le, ← Real.exp_add, ← Real.exp_add]
        congr 2
        rw [hθn, hθ, real_inner_smul_left, hsv, hq]
        simp only
        rw [Finset.sum_Ico_succ_top hk, Finset.sum_Ico_succ_top hk, inner_add_right,
          real_inner_smul_right]
        ring
      obtain ⟨g, hg⟩ : ∃ g : Ω → ℝ≥0∞, g = (hit k)ᶜ.indicator (Z k) := ⟨_, rfl⟩
      have hgm : Measurable[ℱ k] g := hg ▸ (hZm k).indicator (hhm k).compl
      have hKL := d39_KL P ℱ U Γ hsg hUm k θ g hgm
      have hstep : ∫⁻ ω, (hit k)ᶜ.indicator (Z (k + 1)) ω ∂P ≤ ∫⁻ ω, (hit k)ᶜ.indicator (Z k) ω ∂P := by
        have h1 : ∀ ω, (hit k)ᶜ.indicator (Z (k + 1)) ω =
            g ω * ENNReal.ofReal (Real.exp ⟪θ, U (k + 1) ω⟫_ℝ) *
              ENNReal.ofReal (Real.exp (-(Γ / 2 * ‖θ‖ ^ 2))) := by
          intro ω
          rw [hg]
          by_cases hω : ω ∈ (hit k)ᶜ
          · simp only [Set.indicator_of_mem hω, hZrel]
          · simp [Set.indicator_of_notMem hω]
        rw [lintegral_congr h1, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ← hg]
        calc _ ≤ ENNReal.ofReal (Real.exp (Γ / 2 * ‖θ‖ ^ 2)) * (∫⁻ ω, g ω ∂P) *
              ENNReal.ofReal (Real.exp (-(Γ / 2 * ‖θ‖ ^ 2))) := by gcongr
          _ = ∫⁻ ω, g ω ∂P := by
            rw [mul_comm _ (∫⁻ ω, g ω ∂P), mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
              ← Real.exp_add]
            simp
      have hsplit2 : ∀ ω, (hit k)ᶜ.indicator (Z (k + 1)) ω =
          ((hit k)ᶜ ∩ B).indicator (Z (k + 1)) ω + (hit (k + 1))ᶜ.indicator (Z (k + 1)) ω := by
        intro ω
        rw [hcompl]
        by_cases h1 : ω ∈ (hit k)ᶜ <;> by_cases h2 : ω ∈ B <;>
          simp [Set.indicator, h1, h2]
      have hZm0 : Measurable (Z (k + 1)) := (hZm (k + 1)).mono (ℱ.le _) le_rfl
      rw [lintegral_congr hsplit2,
        lintegral_add_left (hZm0.indicator ((hhm0 k).compl.inter hBm))] at hstep
      have hlow : cc * P ((hit k)ᶜ ∩ B) ≤ ∫⁻ ω, ((hit k)ᶜ ∩ B).indicator (Z (k + 1)) ω ∂P := by
        rw [← lintegral_indicator_const ((hhm0 k).compl.inter hBm)]
        apply lintegral_mono
        intro ω
        by_cases hω : ω ∈ (hit k)ᶜ ∩ B
        · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hcc, hZ]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.2
          have h1 : α ≤ sv (k + 1) ω := by
            have := hω.2; rw [hB] at this; exact this
          have h2 : q (k + 1) ≤ S := by
            rw [hq, hSdef]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hkM)
              fun i _ _ => sq_nonneg _
          have h3 : 0 ≤ lam ^ 2 * Γ / 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h2 h3]
        · simp [Set.indicator_of_notMem hω]
      rw [hPsplit, mul_add, add_assoc]
      calc cc * P (hit k) + (cc * P ((hit k)ᶜ ∩ B) + ∫⁻ ω, (hit (k + 1))ᶜ.indicator (Z (k + 1)) ω ∂P)
          ≤ cc * P (hit k) + ∫⁻ ω, (hit k)ᶜ.indicator (Z k) ω ∂P := by
            gcongr
            exact (add_le_add hlow le_rfl).trans hstep
        _ ≤ 1 := ih
  have hfin := claim M hnM.le le_rfl
  have hle : cc * P (hit M) ≤ 1 := le_trans le_self_add hfin
  have hev : {ω | ∃ k ∈ Finset.Ioc n M, α ≤ ⟪e, ∑ i ∈ Finset.Ico n k, c i • U (i + 1) ω⟫_ℝ}
      = hit M := by rw [hhit, hsv]
  rw [hev]
  obtain ⟨Tt, hTt⟩ : ∃ Tt : ℝ≥0∞, Tt = ENNReal.ofReal (Real.exp (-α ^ 2 / (2 * Γ * S))) :=
    ⟨_, rfl⟩
  rw [← hTt]
  have hcT : cc * Tt = 1 := by
    rw [hcc, hTt, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    have : lam * α - lam ^ 2 * Γ / 2 * S + -α ^ 2 / (2 * Γ * S) = 0 := by
      rw [hlam]; field_simp; ring
    rw [this]; simp
  calc P (hit M) = (cc * Tt) * P (hit M) := by rw [hcT, one_mul]
    _ = (cc * P (hit M)) * Tt := by ring
    _ ≤ 1 * Tt := by gcongr
    _ = Tt := one_mul _

lemma d39_tau_mono (γ : ℕ → ℝ) (hγ : MartingaleNoise.IsStepSequence γ) :
    Monotone (Interpolation.tau γ) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [Interpolation.tau, Finset.sum_range_succ]
  linarith [hγ.1 k]

lemma d39_tau_zero (γ : ℕ → ℝ) : Interpolation.tau γ 0 = 0 := by
  simp [Interpolation.tau]

lemma d39_spec (γ : ℕ → ℝ) (hγ : MartingaleNoise.IsStepSequence γ) (s : ℝ) (hs : 0 ≤ s) :
    Interpolation.tau γ (MartingaleNoise.stepIndex γ s) ≤ s ∧
      s < Interpolation.tau γ (MartingaleNoise.stepIndex γ s + 1) := by
  have htend : Tendsto (Interpolation.tau γ) atTop atTop := hγ.2.1
  obtain ⟨K, hK⟩ := (htend.eventually_gt_atTop s).exists
  have hbdd : BddAbove {k : ℕ | Interpolation.tau γ k ≤ s} := by
    refine ⟨K, fun k hk => ?_⟩
    by_contra h
    push Not at h
    have := d39_tau_mono γ hγ h.le
    simp only [Set.mem_setOf_eq] at hk
    linarith
  have hne : ({k : ℕ | Interpolation.tau γ k ≤ s}).Nonempty := ⟨0, by simp [d39_tau_zero, hs]⟩
  refine ⟨Nat.sSup_mem hne hbdd, ?_⟩
  by_contra h
  push Not at h
  have := le_csSup hbdd (show MartingaleNoise.stepIndex γ s + 1 ∈ {k : ℕ | Interpolation.tau γ k ≤ s} from h)
  unfold MartingaleNoise.stepIndex at this
  omega

lemma d39_eq (γ : ℕ → ℝ) (hγ : MartingaleNoise.IsStepSequence γ) (s : ℝ) (hs : 0 ≤ s) (i : ℕ)
    (h1 : Interpolation.tau γ i ≤ s) (h2 : s < Interpolation.tau γ (i + 1)) :
    MartingaleNoise.stepIndex γ s = i := by
  obtain ⟨a1, a2⟩ := d39_spec γ hγ s hs
  rcases lt_trichotomy (MartingaleNoise.stepIndex γ s) i with h | h | h
  · have := d39_tau_mono γ hγ (show MartingaleNoise.stepIndex γ s + 1 ≤ i by omega)
    linarith
  · exact h
  · have := d39_tau_mono γ hγ (show i + 1 ≤ MartingaleNoise.stepIndex γ s by omega)
    linarith

lemma d39_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (γ : ℕ → ℝ) (hγ : MartingaleNoise.IsStepSequence γ) (f : ℕ → E) (t u : ℝ) (ht : 0 ≤ t)
    (htu : t ≤ u) (N : ℕ) (hN : u ≤ Interpolation.tau γ N) :
    ∫ s in t..u, MartingaleNoise.noisePath γ f s =
      ∑ i ∈ Finset.range N, (max t (min (Interpolation.tau γ (i + 1)) u) -
        max t (min (Interpolation.tau γ i) u)) • f (i + 1) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun i => max t (min (Interpolation.tau γ i) u) := ⟨_, rfl⟩
  have hτm := d39_tau_mono γ hγ
  have ha0 : a 0 = t := by
    rw [ha]; simp only [d39_tau_zero]
    exact max_eq_left (min_le_left _ _ |>.trans ht)
  have haN : a N = u := by
    rw [ha]; simp only
    rw [min_eq_right hN, max_eq_right htu]
  have hmono : ∀ i, a i ≤ a (i + 1) := by
    intro i; rw [ha]
    exact max_le_max le_rfl (min_le_min (hτm (Nat.le_succ i)) le_rfl)
  have hEq : ∀ i, ∀ s ∈ Set.Ioo (a i) (a (i + 1)), MartingaleNoise.noisePath γ f s = f (i + 1) := by
    intro i s hs
    rw [ha] at hs
    obtain ⟨hs1, hs2⟩ := hs
    have hts : t < s := lt_of_le_of_lt (le_max_left _ _) hs1
    have hsu : s < u := lt_of_lt_of_le hs2 (max_le htu (min_le_right _ _))
    have h1 : Interpolation.tau γ i < s := by
      have := lt_of_le_of_lt (le_max_right _ _) hs1
      rcases min_lt_iff.1 this with h | h
      · exact h
      · linarith
    have h2 : s < Interpolation.tau γ (i + 1) := by
      rcases lt_max_iff.1 hs2 with h | h
      · linarith
      · exact (lt_min_iff.1 h).1
    unfold MartingaleNoise.noisePath
    rw [d39_eq γ hγ s (by linarith) i h1.le h2]
  have piece : ∀ i, ∫ s in a i..a (i + 1), MartingaleNoise.noisePath γ f s =
      (a (i + 1) - a i) • f (i + 1) := by
    intro i
    rw [intervalIntegral.integral_of_le (hmono i), integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo (hEq i), setIntegral_const]
    simp [Measure.real, Real.volume_Ioo, hmono i]
  have pint : ∀ i, IntervalIntegrable (MartingaleNoise.noisePath γ f) volume (a i) (a (i + 1)) := by
    intro i
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (hmono i)]
    exact (integrableOn_const (C := f (i + 1)) (by simp)).congr_fun
      (fun s hs => (hEq i s hs).symm) measurableSet_Ioo
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (n := N) (fun k _ => pint k)
  rw [ha0, haN] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [piece i, ha]


lemma d39_conv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : ℕ → ℝ) (hγ : MartingaleNoise.IsStepSequence γ) (f : ℕ → E) (t T u : ℝ) (ht : 0 ≤ t)
    (htu : t ≤ u) (hu : u ≤ t + T) :
    ∃ j ≤ MartingaleNoise.stepIndex γ (t + T) + 1,
      ‖∑ i ∈ Finset.range (MartingaleNoise.stepIndex γ (t + T) + 1),
          (max t (min (Interpolation.tau γ (i + 1)) u) - max t (min (Interpolation.tau γ i) u)) •
            f (i + 1)‖ ≤
      ‖∑ i ∈ Finset.range j, (max t (min (Interpolation.tau γ (i + 1)) (t + T)) -
          max t (min (Interpolation.tau γ i) (t + T))) • f (i + 1)‖ := by
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = Interpolation.tau γ := ⟨_, rfl⟩
  rw [← hτ]
  have hτm : Monotone τ := hτ ▸ d39_tau_mono γ hγ
  obtain ⟨N, hN⟩ : ∃ N, N = MartingaleNoise.stepIndex γ (t + T) + 1 := ⟨_, rfl⟩
  rw [← hN]
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun i => max t (min (τ (i + 1)) (t + T)) -
      max t (min (τ i) (t + T)) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, w = fun i => max t (min (τ (i + 1)) u) -
      max t (min (τ i) u) := ⟨_, rfl⟩
  have e1 : ∀ i, (max t (min (τ (i + 1)) (t + T)) - max t (min (τ i) (t + T))) = c i := by
    intro i; rw [hc]
  have e2 : ∀ i, (max t (min (τ (i + 1)) u) - max t (min (τ i) u)) = w i := by
    intro i; rw [hw]
  simp only [e1, e2]
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 = MartingaleNoise.stepIndex γ u := ⟨_, rfl⟩
  have hsp := d39_spec γ hγ u (by linarith)
  rw [← hj0, ← hτ] at hsp
  obtain ⟨hs1, hs2⟩ := hsp
  have hspT := d39_spec γ hγ (t + T) (by linarith)
  rw [← hτ] at hspT
  have hj0N : j0 + 1 ≤ N := by
    by_contra h
    have := hτm (show N ≤ j0 by omega)
    rw [hN] at this
    linarith [hspT.2]
  have hlt : ∀ i, i < j0 → w i = c i := by
    intro i hi
    have a1 : τ (i + 1) ≤ u := (hτm (show i + 1 ≤ j0 by omega)).trans hs1
    have a2 : τ i ≤ u := (hτm (Nat.le_succ i)).trans a1
    rw [hw, hc]; simp only
    rw [min_eq_left a1, min_eq_left a2, min_eq_left (a1.trans hu), min_eq_left (a2.trans hu)]
  have hgt : ∀ i, j0 < i → w i = 0 := by
    intro i hi
    have a1 : u < τ i := lt_of_lt_of_le hs2 (hτm (show j0 + 1 ≤ i by omega))
    have a2 : u < τ (i + 1) := lt_of_lt_of_le a1 (hτm (Nat.le_succ i))
    rw [hw]; simp only
    rw [min_eq_right a1.le, min_eq_right a2.le]; ring
  have hw0 : 0 ≤ w j0 := by
    rw [hw]; simp only
    linarith [max_le_max (le_refl t) (min_le_min (hτm (Nat.le_succ j0)) (le_refl u))]
  have hwc : w j0 ≤ c j0 := by
    rw [hw, hc]; simp only
    rw [min_eq_right hs2.le, min_eq_left hs1, min_eq_left (hs1.trans hu)]
    have : max t u ≤ max t (min (τ (j0 + 1)) (t + T)) :=
      max_le_max le_rfl (le_min hs2.le hu)
    linarith
  -- decomposition
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ i ∈ Finset.range j0, c i • f (i + 1) := ⟨_, rfl⟩
  have hv : ∑ i ∈ Finset.range N, w i • f (i + 1) = A + w j0 • f (j0 + 1) := by
    rw [← Finset.sum_range_add_sum_Ico _ hj0N, Finset.sum_range_succ, hA]
    rw [Finset.sum_eq_zero (s := Finset.Ico (j0 + 1) N)]
    · rw [add_zero]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by rw [hlt i (Finset.mem_range.1 hi)]
    · intro i hi
      rw [hgt i (by have := (Finset.mem_Ico.1 hi).1; omega), zero_smul]
  have hB : ∑ i ∈ Finset.range (j0 + 1), c i • f (i + 1) = A + c j0 • f (j0 + 1) := by
    rw [Finset.sum_range_succ, hA]
  rw [hv]
  rcases (hw0.trans hwc).eq_or_lt with hc0 | hcpos
  · refine ⟨j0, by omega, ?_⟩
    have : w j0 = 0 := le_antisymm (hc0 ▸ hwc) hw0
    rw [this, zero_smul, add_zero, hA]
  · obtain ⟨θ, hθ⟩ : ∃ θ, θ = w j0 / c j0 := ⟨_, rfl⟩
    have hθ0 : 0 ≤ θ := hθ ▸ div_nonneg hw0 hcpos.le
    have hθ1 : θ ≤ 1 := hθ ▸ (div_le_one hcpos).2 hwc
    have hrep : A + w j0 • f (j0 + 1) = (1 - θ) • A + θ • (A + c j0 • f (j0 + 1)) := by
      have : w j0 = θ * c j0 := by rw [hθ]; field_simp
      rw [this, smul_add, ← add_assoc, ← add_smul, mul_smul]
      congr 1; simp
    have hnorm : ‖A + w j0 • f (j0 + 1)‖ ≤ (1 - θ) * ‖A‖ + θ * ‖A + c j0 • f (j0 + 1)‖ := by
      rw [hrep]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hθ0]
    rcases le_total ‖A‖ ‖A + c j0 • f (j0 + 1)‖ with h | h
    · refine ⟨j0 + 1, by omega, ?_⟩
      rw [hB]; nlinarith
    · refine ⟨j0, by omega, ?_⟩
      rw [← hA]; nlinarith


lemma d39_clamp (t v x y : ℝ) (hxy : y ≤ x) :
    0 ≤ max t (min x v) - max t (min y v) ∧ max t (min x v) - max t (min y v) ≤ x - y := by
  constructor
  · linarith [max_le_max (le_refl t) (min_le_min hxy (le_refl v))]
  · simp only [max_def, min_def]; split_ifs <;> linarith

lemma d39_coord {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (α : ℝ) (hα : 0 < α) (h : α ≤ ‖v‖) :
    ∃ r : Fin d, α / Real.sqrt (d + 1) ≤ |v r| := by
  by_contra H
  push Not at H
  have hd : (0 : ℝ) < d + 1 := by positivity
  have h1 : ‖v‖ ^ 2 = ∑ r, ‖v r‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have h2 : ∑ r, ‖v r‖ ^ 2 ≤ ∑ _r : Fin d, (α / Real.sqrt (d + 1)) ^ 2 := by
    apply Finset.sum_le_sum
    intro r _
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (H r).le 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, div_pow, Real.sq_sqrt hd.le,
    nsmul_eq_mul] at h2
  have h3 : (d : ℝ) * (α ^ 2 / (d + 1)) < α ^ 2 := by
    rw [mul_div_assoc', div_lt_iff₀ hd]; nlinarith
  nlinarith [pow_le_pow_left₀ hα.le h 2]


theorem deviation_tail_eq18_core (d : ℕ) (Γ : ℝ) (hΓ : 0 < Γ) :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
      ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ m0) (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (γ : ℕ → ℝ) (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)),
        StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U → IsSubgaussianWith P ℱ U Γ →
        ∀ t : ℝ, 0 ≤ t → ∀ T : ℝ, 0 < T → ∀ α : ℝ, 0 < α →
          P {ω | ENNReal.ofReal α ≤ StochApproxDyn.MartingaleNoise.noiseDev γ (fun n => U n ω) t T}
            ≤ ENNReal.ofReal (C * Real.exp (-α ^ 2 /
                (C' * ∫ s in t..(t + T), StochApproxDyn.MartingaleNoise.stepPath γ s))) := by
  refine ⟨2 * d + 1, 2 * Γ * (d + 1), by positivity, by positivity, ?_⟩
  intro Ω m0 P _ ℱ F γ x U hRM hsg t ht T hT α hα
  have hγ : MartingaleNoise.IsStepSequence γ := hRM.2.1
  have hUm := hRM.2.2.2.1
  obtain ⟨N, hN⟩ : ∃ N, N = MartingaleNoise.stepIndex γ (t + T) + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun i => max t (min (Interpolation.tau γ (i + 1)) (t + T)) -
      max t (min (Interpolation.tau γ i) (t + T)) := ⟨_, rfl⟩
  have hspT := d39_spec γ hγ (t + T) (by linarith)
  have hτN : t + T ≤ Interpolation.tau γ N := by rw [hN]; exact hspT.2.le
  have hcb : ∀ i, 0 ≤ c i ∧ c i ≤ γ (i + 1) := by
    intro i
    have h1 := d39_clamp t (t + T) _ _ (d39_tau_mono γ hγ (Nat.le_succ i))
    have h2 : Interpolation.tau γ (i + 1) - Interpolation.tau γ i = γ (i + 1) := by
      simp [Interpolation.tau, Finset.sum_range_succ]
    rw [hc]; simp only
    rw [← h2]; exact h1
  -- the integral of the step path
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ s in t..(t + T), MartingaleNoise.stepPath γ s := ⟨_, rfl⟩
  rw [← hI]
  have hIsum : I = ∑ i ∈ Finset.range N, c i * γ (i + 1) := by
    rw [hI, show MartingaleNoise.stepPath γ = MartingaleNoise.noisePath γ γ from rfl,
      d39_int γ hγ γ t (t + T) ht (by linarith) N hτN, hc]
    rfl
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i ∈ Finset.Ico 0 N, c i ^ 2 := ⟨_, rfl⟩
  have hSI : S ≤ I := by
    rw [hS, hIsum, Finset.range_eq_Ico]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [sq]; exact mul_le_mul_of_nonneg_left (hcb i).2 (hcb i).1
  have hS0 : 0 ≤ S := hS ▸ Finset.sum_nonneg fun i _ => sq_nonneg _
  -- deterministic inclusion
  have hincl : ∀ ω, ENNReal.ofReal α ≤ MartingaleNoise.noiseDev γ (fun n => U n ω) t T →
      ∃ j ≤ N, α ≤ ‖∑ i ∈ Finset.range j, c i • U (i + 1) ω‖ := by
    intro ω hω
    by_contra H
    push Not at H
    have hle : MartingaleNoise.noiseDev γ (fun n => U n ω) t T ≤
        (Finset.range (N + 1)).sup fun j => ‖∑ i ∈ Finset.range j, c i • U (i + 1) ω‖ₑ := by
      unfold MartingaleNoise.noiseDev
      refine iSup₂_le fun h hh => ?_
      rw [d39_int γ hγ (fun n => U n ω) t (t + h) ht (by linarith [hh.1]) N
        (by linarith [hh.2])]
      obtain ⟨j, hj, hjb⟩ := d39_conv γ hγ (fun n => U n ω) t T (t + h) ht (by linarith [hh.1])
        (by linarith [hh.2])
      rw [← hN] at hj hjb
      have hjb' : ‖∑ i ∈ Finset.range N, (max t (min (Interpolation.tau γ (i + 1)) (t + h)) -
          max t (min (Interpolation.tau γ i) (t + h))) • U (i + 1) ω‖ ≤
          ‖∑ i ∈ Finset.range j, c i • U (i + 1) ω‖ := by rw [hc]; exact hjb
      refine le_trans ?_ (Finset.le_sup (f := fun j => ‖∑ i ∈ Finset.range j, c i • U (i + 1) ω‖ₑ)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal hjb'
    have hlt : ((Finset.range (N + 1)).sup fun j => ‖∑ i ∈ Finset.range j, c i • U (i + 1) ω‖ₑ)
        < ENNReal.ofReal α := by
      rw [Finset.sup_lt_iff (by simpa using hα)]
      intro j hj
      rw [← ofReal_norm_eq_enorm]
      exact (ENNReal.ofReal_lt_ofReal_iff hα).2 (H j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
    exact absurd (hω.trans hle) (not_le.2 hlt)
  rcases hS0.eq_or_lt with hS0' | hSpos
  · -- all coefficients vanish: the event is empty
    have hc0 : ∀ i ∈ Finset.range N, c i = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (c i))).1 (hS ▸ hS0'.symm)
      intro i hi
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (this i (by
        rw [← Finset.range_eq_Ico]; exact hi))
    have hempty : {ω | ENNReal.ofReal α ≤ MartingaleNoise.noiseDev γ (fun n => U n ω) t T} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hω
      obtain ⟨j, hj, hjb⟩ := hincl ω hω
      rw [Finset.sum_eq_zero (fun i hi => by
        rw [hc0 i (Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hj)), zero_smul])]
        at hjb
      simp at hjb; linarith
    rw [hempty, measure_empty]; simp
  · have hIpos : 0 < I := lt_of_lt_of_le hSpos hSI
    obtain ⟨α', hα'⟩ : ∃ α', α' = α / Real.sqrt (d + 1) := ⟨_, rfl⟩
    have hα'pos : 0 < α' := hα' ▸ div_pos hα (Real.sqrt_pos.2 (by positivity))
    have hα'sq : α' ^ 2 = α ^ 2 / (d + 1) := by
      rw [hα', div_pow, Real.sq_sqrt (by positivity)]
    obtain ⟨E, hE⟩ : ∃ E : Fin d × Bool → EuclideanSpace ℝ (Fin d),
        E = fun p => (if p.2 then (1 : ℝ) else -1) • EuclideanSpace.single p.1 (1 : ℝ) := ⟨_, rfl⟩
    have hEn : ∀ p, ‖E p‖ = 1 := by
      intro p; rw [hE]; simp only
      rw [norm_smul, EuclideanSpace.norm_single]
      split_ifs <;> simp
    have hsub : {ω | ENNReal.ofReal α ≤ MartingaleNoise.noiseDev γ (fun n => U n ω) t T} ⊆
        ⋃ p : Fin d × Bool, {ω | ∃ k ∈ Finset.Ioc 0 N,
          α' ≤ ⟪E p, ∑ i ∈ Finset.Ico 0 k, c i • U (i + 1) ω⟫_ℝ} := by
      intro ω hω
      obtain ⟨j, hj, hjb⟩ := hincl ω hω
      have hj0 : j ≠ 0 := by
        rintro rfl; simp at hjb; linarith
      obtain ⟨r, hr⟩ := d39_coord _ α hα hjb
      rw [← hα'] at hr
      refine Set.mem_iUnion.2 ⟨(r, decide (0 ≤ (∑ i ∈ Finset.range j, c i • U (i + 1) ω) r)), ?_⟩
      refine ⟨j, Finset.mem_Ioc.2 ⟨Nat.pos_of_ne_zero hj0, hj⟩, ?_⟩
      rw [← Finset.range_eq_Ico, hE]
      simp only [real_inner_smul_left, EuclideanSpace.inner_single_left]
      by_cases h0 : 0 ≤ (∑ i ∈ Finset.range j, c i • U (i + 1) ω) r
      · simp only [h0, decide_true, if_true]
        rw [abs_of_nonneg h0] at hr
        simpa using hr
      · simp only [h0, decide_false]
        rw [abs_of_neg (not_le.1 h0)] at hr
        simpa using hr
    have hbound : ∀ p, P {ω | ∃ k ∈ Finset.Ioc 0 N,
          α' ≤ ⟪E p, ∑ i ∈ Finset.Ico 0 k, c i • U (i + 1) ω⟫_ℝ} ≤
        ENNReal.ofReal (Real.exp (-α ^ 2 / (2 * Γ * (d + 1) * I))) := by
      intro p
      refine (d39_core P ℱ U Γ hΓ hsg hUm (E p) (hEn p) α' hα'pos c 0 N).trans ?_
      rw [← hS]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      rw [hα'sq, neg_div, neg_div, neg_le_neg_iff, div_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : 2 * Γ * S * (d + 1) ≤ 2 * Γ * I * (d + 1) := by gcongr
      linarith
    calc P {ω | ENNReal.ofReal α ≤ MartingaleNoise.noiseDev γ (fun n => U n ω) t T}
        ≤ P (⋃ p : Fin d × Bool, {ω | ∃ k ∈ Finset.Ioc 0 N,
          α' ≤ ⟪E p, ∑ i ∈ Finset.Ico 0 k, c i • U (i + 1) ω⟫_ℝ}) := measure_mono hsub
      _ ≤ ∑ p : Fin d × Bool, P {ω | ∃ k ∈ Finset.Ioc 0 N,
          α' ≤ ⟪E p, ∑ i ∈ Finset.Ico 0 k, c i • U (i + 1) ω⟫_ℝ} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _p : Fin d × Bool, ENNReal.ofReal (Real.exp (-α ^ 2 / (2 * Γ * (d + 1) * I))) :=
          Finset.sum_le_sum fun p _ => hbound p
      _ = ENNReal.ofReal ((2 * d : ℝ) * Real.exp (-α ^ 2 / (2 * Γ * (d + 1) * I))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            Fintype.card_bool, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show ((2 * d : ℝ)) = ((d * 2 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((2 * d + 1) * Real.exp (-α ^ 2 / (2 * Γ * (d + 1) * I))) := by
          apply ENNReal.ofReal_le_ofReal
          gcongr; linarith

end StochApproxDyn.SubgaussianNoise

open StochApproxDyn.SubgaussianNoise


theorem solution (d : ℕ) (Γ : ℝ) (hΓ : 0 < Γ) :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
      ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ m0) (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (γ : ℕ → ℝ) (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)),
        StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U → IsSubgaussianWith P ℱ U Γ →
        ∀ t : ℝ, 0 ≤ t → ∀ T : ℝ, 0 < T → ∀ α : ℝ, 0 < α →
          P {ω | ENNReal.ofReal α ≤ StochApproxDyn.MartingaleNoise.noiseDev γ (fun n => U n ω) t T}
            ≤ ENNReal.ofReal (C * Real.exp (-α ^ 2 /
                (C' * ∫ s in t..(t + T), StochApproxDyn.MartingaleNoise.stepPath γ s))) := by
  exact deviation_tail_eq18_core d Γ hΓ
