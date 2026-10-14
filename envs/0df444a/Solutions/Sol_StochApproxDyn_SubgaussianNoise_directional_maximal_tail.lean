-- Prove2me | solution 1 for StochApproxDyn.SubgaussianNoise.directional_maximal_tail
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:53:27.937759+00:00
-- url     : https://prove2.me/submissions/88a84a9a-ec44-4550-937b-da47da538a1c

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro
import Definitions.Def_StochApproxDyn_SubgaussianNoise_Subgaussian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace


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

theorem directional_maximal_tail_core {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U)
    (Γ : ℝ) (hΓ : 0 < Γ) (hsg : IsSubgaussianWith P ℱ U Γ)
    (e : EuclideanSpace ℝ (Fin d)) (he : ‖e‖ = 1) (α : ℝ) (hα : 0 < α)
    (n : ℕ) (T : ℝ) (hT : 0 < T) :
    P {ω | ∃ k ∈ Finset.Ioc n (StochApproxDyn.MartingaleNoise.stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T)),
        α ≤ ⟪e, ∑ i ∈ Finset.Ico n k, γ (i + 1) • U (i + 1) ω⟫_ℝ}
      ≤ ENNReal.ofReal (Real.exp (-α ^ 2 /
          (2 * Γ * ∑ i ∈ Finset.Ico n (StochApproxDyn.MartingaleNoise.stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T)), γ (i + 1) ^ 2))) :=
  d39_core P ℱ U Γ hΓ hsg hRM.2.2.2.1 e he α hα (fun i => γ (i + 1)) n _

end StochApproxDyn.SubgaussianNoise

open StochApproxDyn.SubgaussianNoise


theorem solution {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U)
    (Γ : ℝ) (hΓ : 0 < Γ) (hsg : IsSubgaussianWith P ℱ U Γ)
    (e : EuclideanSpace ℝ (Fin d)) (he : ‖e‖ = 1) (α : ℝ) (hα : 0 < α)
    (n : ℕ) (T : ℝ) (hT : 0 < T) :
    P {ω | ∃ k ∈ Finset.Ioc n (StochApproxDyn.MartingaleNoise.stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T)),
        α ≤ ⟪e, ∑ i ∈ Finset.Ico n k, γ (i + 1) • U (i + 1) ω⟫_ℝ}
      ≤ ENNReal.ofReal (Real.exp (-α ^ 2 /
          (2 * Γ * ∑ i ∈ Finset.Ico n (StochApproxDyn.MartingaleNoise.stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T)), γ (i + 1) ^ 2))) := by
  exact directional_maximal_tail_core P ℱ F γ x U hRM Γ hΓ hsg e he α hα n T hT
