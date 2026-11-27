-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.prop_33
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:16:12.172803+00:00
-- url     : https://prove2.me/submissions/8ace5795-1e65-4d5e-8cf7-b23c45c0e8b6

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical.P33Aux

/-- selector factor -/
def gsel {ℓ m : ℕ} (f : Fin ℓ → Fin m) (p : Fin ℓ × Fin m) (x : ℝ) : ℝ :=
  if p.2 = f p.1 then x / m else 1

lemma expand {ℓ m : ℕ} (z : Fin ℓ × Fin m → ℝ) :
    ∏ i, (∑ j, z (i, j)) / (m : ℝ) = ∑ f : Fin ℓ → Fin m, ∏ p, gsel f p (z p) := by
  simp only [Finset.sum_div]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl; intro f _
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl; intro i _
  simp only [gsel]
  rw [Finset.prod_ite_eq']
  simp

lemma gsel_int {ℓ m : ℕ} (lm : Measure ℝ) [IsProbabilityMeasure lm] (h1 : Integrable id lm)
    (f : Fin ℓ → Fin m) (p : Fin ℓ × Fin m) : Integrable (gsel f p) lm := by
  unfold gsel
  split_ifs
  · exact h1.div_const _
  · exact integrable_const _

lemma gsel2_int {ℓ m : ℕ} (lm : Measure ℝ) [IsProbabilityMeasure lm] (h1 : Integrable id lm)
    (h2 : Integrable (fun x => x ^ 2) lm)
    (f g : Fin ℓ → Fin m) (p : Fin ℓ × Fin m) : Integrable (fun x => gsel f p x * gsel g p x) lm := by
  unfold gsel
  split_ifs
  · have := h2.div_const ((m:ℝ) * m)
    refine this.congr (Filter.Eventually.of_forall (fun x => ?_)); simp only; ring
  · simpa using h1.div_const (m:ℝ)
  · simpa using h1.div_const (m:ℝ)
  · simp

theorem moments (ℓ m : ℕ) (hm : 0 < m) (lam : Fin ℓ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (lam i)] (h1 : ∀ i, Integrable id (lam i))
    (h2 : ∀ i, Integrable (fun x => x ^ 2) (lam i)) :
    let π := Measure.pi (fun p : Fin ℓ × Fin m => lam p.1)
    let F := fun z : Fin ℓ × Fin m → ℝ => ∏ i, (∑ j, z (i, j)) / (m : ℝ)
    Integrable F π ∧ ∫ z, F z ∂π = ∏ i, ∫ x, x ∂(lam i) ∧
    Integrable (fun z => F z ^ 2) π ∧
    ∫ z, F z ^ 2 ∂π = ∏ i, ((∫ x, x ^ 2 ∂(lam i)) / m + (1 - 1 / (m:ℝ)) * (∫ x, x ∂(lam i)) ^ 2) := by
  intro π F
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hF : F = fun z => ∑ f : Fin ℓ → Fin m, ∏ p, gsel f p (z p) := by
    funext z; exact expand z
  have hT : ∀ f : Fin ℓ → Fin m, Integrable (fun z : Fin ℓ × Fin m → ℝ => ∏ p, gsel f p (z p)) π :=
    fun f => Integrable.fintype_prod (fun p => gsel_int (lam p.1) (h1 p.1) f p)
  have hF2 : (fun z => F z ^ 2) = fun z => ∑ f : Fin ℓ → Fin m, ∑ g : Fin ℓ → Fin m,
      ∏ p, (gsel f p (z p) * gsel g p (z p)) := by
    funext z
    rw [show F z = ∑ f : Fin ℓ → Fin m, ∏ p, gsel f p (z p) from expand z, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro f _
    apply Finset.sum_congr rfl; intro g _
    rw [Finset.prod_mul_distrib]
  have hT2 : ∀ f g : Fin ℓ → Fin m, Integrable (fun z : Fin ℓ × Fin m → ℝ =>
      ∏ p, (gsel f p (z p) * gsel g p (z p))) π :=
    fun f g => Integrable.fintype_prod (f := fun p x => gsel f p x * gsel g p x)
      (fun p => gsel2_int (lam p.1) (h1 p.1) (h2 p.1) f g p)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hF]; exact integrable_finset_sum _ (fun f _ => hT f)
  · rw [hF, integral_finset_sum _ (fun f _ => hT f)]
    have : ∀ f : Fin ℓ → Fin m, ∫ z, ∏ p, gsel f p (z p) ∂π = ∏ i, (∫ x, x ∂(lam i)) / m := by
      intro f
      rw [integral_fintype_prod_eq_prod (f := fun p => gsel f p), Fintype.prod_prod_type]
      apply Finset.prod_congr rfl; intro i _
      simp only [gsel]
      have : ∀ j : Fin m, ∫ x, (if j = f i then x / m else 1) ∂(lam i) =
          if j = f i then (∫ x, x ∂(lam i)) / m else 1 := by
        intro j; split_ifs
        · exact integral_div _ _
        · simp
      simp only [this]
      rw [Finset.prod_ite_eq']; simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Finset.prod_div_distrib, Finset.prod_const]
    push_cast
    field_simp
  · rw [hF2]
    exact integrable_finset_sum _ (fun f _ => integrable_finset_sum _ (fun g _ => hT2 f g))
  · rw [hF2, integral_finset_sum _ (fun f _ => integrable_finset_sum _ (fun g _ => hT2 f g))]
    set p : Fin ℓ → ℝ := fun i => ∫ x, x ∂(lam i)
    set q : Fin ℓ → ℝ := fun i => ∫ x, x ^ 2 ∂(lam i)
    set c : Fin ℓ → Fin m → Fin m → ℝ := fun i a b =>
      if a = b then q i / ((m:ℝ) * m) else p i / m * (p i / m)
    have hpair : ∀ f g : Fin ℓ → Fin m,
        ∫ z, ∏ p, (gsel f p (z p) * gsel g p (z p)) ∂π = ∏ i, c i (f i) (g i) := by
      intro f g
      rw [integral_fintype_prod_eq_prod (f := fun p x => gsel f p x * gsel g p x),
        Fintype.prod_prod_type]
      apply Finset.prod_congr rfl; intro i _
      simp only [gsel, c]
      by_cases hfg : f i = g i
      · rw [if_pos hfg]
        have : ∀ j : Fin m, ∫ x, ((if j = f i then x / m else 1) * if j = g i then x / m else 1)
            ∂(lam i) = if j = f i then q i / ((m:ℝ) * m) else 1 := by
          intro j; rw [← hfg]; split_ifs
          · rw [← integral_div]; congr 1; funext x; ring
          · simp
        simp only [this]; rw [Finset.prod_ite_eq']; simp
      · rw [if_neg hfg]
        have : ∀ j : Fin m, ∫ x, ((if j = f i then x / m else 1) * if j = g i then x / m else 1)
            ∂(lam i) = (if j = f i then p i / m else 1) * (if j = g i then p i / m else 1) := by
          intro j
          by_cases h1' : j = f i
          · have h2' : ¬ j = g i := fun h => hfg (h1'.symm.trans h)
            simp only [if_pos h1', if_neg h2', mul_one]; rw [integral_div]
          · by_cases h2' : j = g i
            · simp only [if_neg h1', if_pos h2', one_mul]; rw [integral_div]
            · simp only [if_neg h1', if_neg h2', mul_one]; simp
        simp only [this]
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
        simp
    have hint : ∀ f : Fin ℓ → Fin m, ∫ z, ∑ g : Fin ℓ → Fin m,
        ∏ p, (gsel f p (z p) * gsel g p (z p)) ∂π =
        ∑ g : Fin ℓ → Fin m, ∫ z, ∏ p, (gsel f p (z p) * gsel g p (z p)) ∂π :=
      fun f => integral_finset_sum _ (fun g _ => hT2 f g)
    simp only [hint, hpair]
    -- reorganize the double sum
    have hsw : ∑ f : Fin ℓ → Fin m, ∑ g : Fin ℓ → Fin m, ∏ i, c i (f i) (g i) =
        ∏ i, ∑ a : Fin m, ∑ b : Fin m, c i a b := by
      have e1 : ∀ i, ∑ a : Fin m, ∑ b : Fin m, c i a b = ∑ ab : Fin m × Fin m, c i ab.1 ab.2 := by
        intro i; rw [Fintype.sum_prod_type]
      simp only [e1]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ, ← Fintype.sum_prod_type']
      exact (Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _
        (fun fg => rfl))
    rw [hsw]
    apply Finset.prod_congr rfl; intro i _
    have hrow : ∀ a : Fin m, ∑ b : Fin m, c i a b = q i / ((m:ℝ) * m) + (m - 1) * (p i / m * (p i / m)) := by
      intro a
      simp only [c]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_eq,
        Finset.filter_ne, if_pos (Finset.mem_univ a)]
      simp only [Finset.card_singleton, Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ, Fintype.card_fin, one_smul, nsmul_eq_mul]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring


lemma cheb {Ω' : Type*} [MeasurableSpace Ω'] (π : Measure Ω') [IsProbabilityMeasure π]
    (F : Ω' → ℝ) (hFm : Measurable F) (hF : Integrable F π)
    (hF2 : Integrable (fun z => F z ^ 2) π) (P ε : ℝ) (hP : 0 < P) (hε : 0 < ε)
    (hmean : ∫ z, F z ∂π = P) (hsec : ∫ z, F z ^ 2 ∂π ≤ (1 + ε ^ 2 / 8) * P ^ 2) :
    7 / 8 ≤ π.real {z | (1 - ε) * P ≤ F z ∧ F z ≤ (1 + ε) * P} := by
  have hmem : MemLp F 2 π := (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).2 hF2
  have hvar : variance F π ≤ ε ^ 2 / 8 * P ^ 2 := by
    rw [variance_eq_sub hmem]
    have : π[F ^ 2] = ∫ z, F z ^ 2 ∂π := rfl
    rw [this, hmean]; nlinarith
  have hc : 0 < ε * P := mul_pos hε hP
  have hcheb := meas_ge_le_variance_div_sq hmem hc
  rw [hmean] at hcheb
  set S := {z | ε * P ≤ |F z - P|}
  have hS : MeasurableSet S := measurableSet_le measurable_const ((hFm.sub measurable_const).abs)
  have hSreal : π.real S ≤ 1 / 8 := by
    have h1 : π.real S ≤ variance F π / (ε * P) ^ 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
      rwa [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at this
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsub : Sᶜ ⊆ {z | (1 - ε) * P ≤ F z ∧ F z ≤ (1 + ε) * P} := by
    intro z hz
    simp only [S, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hz
    rw [abs_lt] at hz
    constructor <;> nlinarith [hz.1, hz.2]
  calc (7:ℝ) / 8 ≤ 1 - π.real S := by linarith
    _ = π.real Sᶜ := by rw [measureReal_compl (μ := π) hS, probReal_univ]
    _ ≤ _ := measureReal_mono hsub


theorem prop33 {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℓ : ℕ) (W : Fin ℓ → Ω → ℝ) (hW : ∀ i, Measurable (W i))
    (hpos : ∀ i, ∀ᵐ ω ∂μ, 0 < W i ω)
    (hmoment : ∀ i, Integrable (fun ω => (W i ω)^2) μ)
    (hind : iIndepFun W μ) (B ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hB : ∀ i, (∫ ω, (W i ω)^2 ∂μ) / (∫ ω, W i ω ∂μ)^2 ≤ B)
    (X : Fin ℓ → Fin ⌈16*B*(ℓ : ℝ)/ε^2⌉₊ → Ξ → ℝ)
    (hX : iIndepFun (fun ij : Fin ℓ × Fin ⌈16*B*(ℓ : ℝ)/ε^2⌉₊ => X ij.1 ij.2) ν)
    (hlaw : ∀ i j, IdentDistrib (X i j) (W i) ν μ) :
  let m := ⌈16*B*(ℓ : ℝ)/ε^2⌉₊
  let estimate := fun ξ => ∏ i, ((∑ j, X i j ξ) / (m : ℝ))
  3/4 ≤ ν.real {ξ | (1-ε) * (∫ ω, ∏ i, W i ω ∂μ) ≤ estimate ξ ∧
    estimate ξ ≤ (1+ε) * (∫ ω, ∏ i, W i ω ∂μ)} := by
  intro m estimate
  obtain ⟨hε0, hε1⟩ := hε
  have hint : ∀ i, Integrable (W i) μ := fun i =>
    ((memLp_two_iff_integrable_sq (hW i).aestronglyMeasurable).2 (hmoment i)).integrable one_le_two
  have hP : ∫ ω, ∏ i, W i ω ∂μ = ∏ i, ∫ ω, W i ω ∂μ :=
    hind.integral_fun_prod_eq_prod_integral (fun i => (hW i).aestronglyMeasurable)
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · subst hℓ
    have : {ξ | (1-ε) * (∫ ω, ∏ i, W i ω ∂μ) ≤ estimate ξ ∧
        estimate ξ ≤ (1+ε) * (∫ ω, ∏ i, W i ω ∂μ)} = Set.univ := by
      ext ξ
      simp only [estimate, Finset.univ_eq_empty, Finset.prod_empty, integral_const, probReal_univ,
        smul_eq_mul, mul_one, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      constructor <;> linarith
    rw [this, probReal_univ]; norm_num
  have hp_pos : ∀ i, 0 < ∫ ω, W i ω ∂μ := by
    intro i
    have h0 : 0 ≤ᵐ[μ] W i := (hpos i).mono (fun ω h => h.le)
    by_contra hle
    push Not at hle
    have heq : ∫ ω, W i ω ∂μ = 0 := le_antisymm hle (integral_nonneg_of_ae h0)
    rw [integral_eq_zero_iff_of_nonneg_ae h0 (hint i)] at heq
    obtain ⟨ω, h1, h2⟩ := (heq.and (hpos i)).exists
    simp only [Pi.zero_apply] at h1
    linarith
  have hq : ∀ i, (∫ ω, W i ω ∂μ) ^ 2 ≤ ∫ ω, (W i ω) ^ 2 ∂μ := by
    intro i
    have hmem := (memLp_two_iff_integrable_sq (hW i).aestronglyMeasurable).2 (hmoment i)
    have := variance_nonneg (W i) μ
    rw [variance_eq_sub hmem] at this
    have e : μ[W i ^ 2] = ∫ ω, (W i ω) ^ 2 ∂μ := rfl
    rw [e] at this; linarith
  have hqB : ∀ i, ∫ ω, (W i ω) ^ 2 ∂μ ≤ B * (∫ ω, W i ω ∂μ) ^ 2 := by
    intro i
    have := hB i
    rwa [div_le_iff₀ (by have := hp_pos i; positivity)] at this
  have hB1 : 1 ≤ B := by
    set i0 : Fin ℓ := ⟨0, hℓ⟩
    have h1 := hq i0; have h2 := hqB i0
    have hp := hp_pos i0
    nlinarith [sq_pos_of_pos hp]
  have hmpos : 0 < m := Nat.ceil_pos.2 (by positivity)
  have hmr : (0:ℝ) < m := by exact_mod_cast hmpos
  -- the laws
  set lam : Fin ℓ → Measure ℝ := fun i => μ.map (W i)
  haveI : ∀ i, IsProbabilityMeasure (lam i) := fun i => Measure.isProbabilityMeasure_map (hW i).aemeasurable
  have hl1 : ∀ i, Integrable id (lam i) := fun i =>
    (integrable_map_measure aestronglyMeasurable_id (hW i).aemeasurable).2 (hint i)
  have hl2 : ∀ i, Integrable (fun x => x ^ 2) (lam i) := fun i =>
    (integrable_map_measure (continuous_pow 2).aestronglyMeasurable (hW i).aemeasurable).2 (hmoment i)
  have hm1 : ∀ i, ∫ x, x ∂(lam i) = ∫ ω, W i ω ∂μ := fun i =>
    integral_map (hW i).aemeasurable aestronglyMeasurable_id
  have hm2 : ∀ i, ∫ x, x ^ 2 ∂(lam i) = ∫ ω, (W i ω) ^ 2 ∂μ := fun i =>
    integral_map (hW i).aemeasurable (continuous_pow 2).aestronglyMeasurable
  set Z : Ξ → (Fin ℓ × Fin m → ℝ) := fun ξ p => X p.1 p.2 ξ
  have hXae : ∀ p : Fin ℓ × Fin m, AEMeasurable (X p.1 p.2) ν := fun p => (hlaw p.1 p.2).aemeasurable_fst
  have hZ : AEMeasurable Z ν := aemeasurable_pi_lambda _ hXae
  have hmap : ν.map Z = Measure.pi (fun p : Fin ℓ × Fin m => lam p.1) := by
    rw [hX.map_fun_eq_pi_map hXae]
    congr 1; funext p; exact (hlaw p.1 p.2).map_eq
  obtain ⟨hFi, hFmean, hF2i, hF2⟩ := moments ℓ m hmpos lam hl1 hl2
  set F : (Fin ℓ × Fin m → ℝ) → ℝ := fun z => ∏ i, (∑ j, z (i, j)) / (m : ℝ)
  have hFm : Measurable F := by
    apply Finset.measurable_prod; intro i _
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun j _ => measurable_pi_apply (i, j))
  set P := ∏ i, ∫ ω, W i ω ∂μ
  have hPpos : 0 < P := Finset.prod_pos (fun i _ => hp_pos i)
  have hmean : ∫ z, F z ∂(Measure.pi (fun p : Fin ℓ × Fin m => lam p.1)) = P := by
    rw [hFmean]; simp only [hm1, P]
  have hsec : ∫ z, F z ^ 2 ∂(Measure.pi (fun p : Fin ℓ × Fin m => lam p.1)) ≤ (1 + ε ^ 2 / 8) * P ^ 2 := by
    rw [hF2]
    simp only [hm1, hm2]
    have hfac : ∀ i, (∫ ω, (W i ω) ^ 2 ∂μ) / m + (1 - 1 / (m:ℝ)) * (∫ ω, W i ω ∂μ) ^ 2 ≤
        (∫ ω, W i ω ∂μ) ^ 2 * (1 + B / m) := by
      intro i
      have h1 := hqB i
      have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hmpos
      have : (∫ ω, (W i ω) ^ 2 ∂μ) / m ≤ B * (∫ ω, W i ω ∂μ) ^ 2 / m :=
        div_le_div_of_nonneg_right h1 hmr.le
      have h3 : (1 - 1 / (m:ℝ)) * (∫ ω, W i ω ∂μ) ^ 2 ≤ (∫ ω, W i ω ∂μ) ^ 2 := by
        have : 0 ≤ 1 / (m:ℝ) := by positivity
        nlinarith [sq_nonneg (∫ ω, W i ω ∂μ)]
      calc _ ≤ B * (∫ ω, W i ω ∂μ) ^ 2 / m + (∫ ω, W i ω ∂μ) ^ 2 := add_le_add this h3
        _ = _ := by field_simp; ring
    have hfac0 : ∀ i, 0 ≤ (∫ ω, (W i ω) ^ 2 ∂μ) / m + (1 - 1 / (m:ℝ)) * (∫ ω, W i ω ∂μ) ^ 2 := by
      intro i
      have : 0 ≤ ∫ ω, (W i ω) ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
      have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hmpos
      have : 0 ≤ 1 - 1 / (m:ℝ) := by rw [sub_nonneg, div_le_one hmr]; exact hm1'
      positivity
    calc ∏ i, ((∫ ω, (W i ω) ^ 2 ∂μ) / m + (1 - 1 / (m:ℝ)) * (∫ ω, W i ω ∂μ) ^ 2)
        ≤ ∏ i, ((∫ ω, W i ω ∂μ) ^ 2 * (1 + B / m)) :=
          Finset.prod_le_prod (fun i _ => hfac0 i) (fun i _ => hfac i)
      _ = P ^ 2 * (1 + B / m) ^ ℓ := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
      _ ≤ P ^ 2 * (1 + ε ^ 2 / 8) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          have hceil : 16 * B * (ℓ:ℝ) / ε ^ 2 ≤ m := Nat.le_ceil _
          have hlB : (ℓ:ℝ) * (B / m) ≤ ε ^ 2 / 16 := by
            rw [div_le_iff₀ (by positivity)] at hceil
            rw [mul_div_assoc', div_le_iff₀ hmr]; nlinarith
          calc (1 + B / m) ^ ℓ ≤ Real.exp (B / m) ^ ℓ :=
                pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (B / m)]) ℓ
            _ = Real.exp (ℓ * (B / m)) := by rw [← Real.exp_nat_mul]
            _ ≤ Real.exp (ε ^ 2 / 16) := Real.exp_le_exp.2 hlB
            _ ≤ 1 + ε ^ 2 / 8 := by
                have hx : |ε ^ 2 / 16| ≤ 1 := by
                  rw [abs_of_nonneg (by positivity)]; nlinarith
                have := Real.abs_exp_sub_one_le hx
                rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ε ^ 2 / 16)] at this
                have := (abs_le.1 this).2
                linarith
      _ = (1 + ε ^ 2 / 8) * P ^ 2 := by ring
  have hc := cheb (Measure.pi (fun p : Fin ℓ × Fin m => lam p.1)) F hFm hFi hF2i P ε hPpos hε0 hmean hsec
  rw [← hmap] at hc
  have hset : MeasurableSet {z | (1 - ε) * P ≤ F z ∧ F z ≤ (1 + ε) * P} :=
    (measurableSet_le measurable_const hFm).inter (measurableSet_le hFm measurable_const)
  rw [Measure.real, Measure.map_apply_of_aemeasurable hZ hset] at hc
  rw [hP]
  have : (3:ℝ) / 4 ≤ 7 / 8 := by norm_num
  exact this.trans hc

end TFIMPhaseDiagram.Classical.P33Aux

theorem solution {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℓ : ℕ) (W : Fin ℓ → Ω → ℝ) (hW : ∀ i, Measurable (W i))
    (hpos : ∀ i, ∀ᵐ ω ∂μ, 0 < W i ω)
    (hmoment : ∀ i, Integrable (fun ω => (W i ω)^2) μ)
    (hind : iIndepFun W μ) (B ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hB : ∀ i, (∫ ω, (W i ω)^2 ∂μ) / (∫ ω, W i ω ∂μ)^2 ≤ B)
    (X : Fin ℓ → Fin ⌈16*B*(ℓ : ℝ)/ε^2⌉₊ → Ξ → ℝ)
    (hX : iIndepFun (fun ij : Fin ℓ × Fin ⌈16*B*(ℓ : ℝ)/ε^2⌉₊ => X ij.1 ij.2) ν)
    (hlaw : ∀ i j, IdentDistrib (X i j) (W i) ν μ) :
  let m := ⌈16*B*(ℓ : ℝ)/ε^2⌉₊
  let estimate := fun ξ => ∏ i, ((∑ j, X i j ξ) / (m : ℝ))
  3/4 ≤ ν.real {ξ | (1-ε) * (∫ ω, ∏ i, W i ω ∂μ) ≤ estimate ξ ∧
    estimate ξ ≤ (1+ε) * (∫ ω, ∏ i, W i ω ∂μ)} :=
  TFIMPhaseDiagram.Classical.P33Aux.prop33 μ ν ℓ W hW hpos hmoment hind B ε hε hB X hX hlaw
