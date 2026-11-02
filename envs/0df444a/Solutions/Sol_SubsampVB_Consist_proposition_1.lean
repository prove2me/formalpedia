-- Prove2me | solution 1 for SubsampVB.Consist.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T20:48:55.967913+00:00
-- url     : https://prove2.me/submissions/80040fa2-3f28-4a12-9b97-7a74c903b01d

import Mathlib
import Definitions.Def_SubsampVB_Consist_Setting

open MeasureTheory Filter Finset ProbabilityTheory SubsampVB.Consist

universe u v

namespace SVBProp1Aux

/-- `2|Cov(X,Y)| ≤ l Var X + Var Y / l`, packaged as a bound on `Var(X+Y) - Var X`. -/
lemma var_add_bound {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) {l : ℝ} (hl : 0 < l) :
    |Var[fun ω => X ω + Y ω; μ] - Var[X; μ]| ≤ l * Var[X; μ] + (1 + 1 / l) * Var[Y; μ] := by
  have h1 := variance_fun_add hX hY
  have h2 := variance_fun_add (hX.const_mul l) hY
  have h3 := variance_fun_sub (hX.const_mul l) hY
  rw [variance_const_mul, covariance_const_mul_left] at h2 h3
  have n2 := variance_nonneg (fun ω => l * X ω + Y ω) μ
  have n3 := variance_nonneg (fun ω => l * X ω - Y ω) μ
  have nY := variance_nonneg Y μ
  set c := cov[X, Y; μ]
  set V := Var[X; μ]
  set W := Var[Y; μ]
  rw [show Var[fun ω => X ω + Y ω; μ] = V + 2 * c + W from h1]
  have hup : 2 * l * c ≤ l ^ 2 * V + W := by nlinarith
  have hlo : -(l ^ 2 * V + W) ≤ 2 * l * c := by nlinarith
  have e : l * V + W / l = (l ^ 2 * V + W) / l := by field_simp
  have hup' : 2 * c ≤ l * V + W / l := by
    rw [e, le_div_iff₀ hl]; nlinarith
  have hlo' : -(l * V + W / l) ≤ 2 * c := by
    rw [e, show -((l ^ 2 * V + W) / l) = (-(l ^ 2 * V + W)) / l by ring, div_le_iff₀ hl]
    nlinarith
  have e2 : (1 + 1 / l) * W = W + W / l := by ring
  rw [e2, abs_le]
  constructor <;> linarith

variable {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
  {Ω : Type v} [MeasurableSpace Ω]

/-- The linear (influence-function) part of the expansion: its variance is `∑ σᵢ² / Nᵢ`. -/
lemma linear_part (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Inputs Ξ) [∀ i, IsProbabilityMeasure (F i)]
    (g : Inputs Ξ → ∀ i, Ξ i → ℝ) (X : ∀ i : Fin m, ℕ → Ω → Ξ i)
    (hData : IIDData P F X) (hg : ∀ i, MemLp (g F i) 2 (F i)) (N : Fin m → ℕ)
    (hN : ∀ i, N i ≠ 0) :
    ∃ L : Ω → ℝ, MemLp L 2 P ∧ Var[L; P] = ∑ i, sigma2 F g i / (N i : ℝ) ∧
      (fun ω => ∑ i : Fin m, ((N i : ℝ)⁻¹ * ∑ j : Fin (N i), g F i (X i j ω) -
        ∫ z, g F i z ∂(F i))) =ᵐ[P] L := by
  set h : ∀ i, Ξ i → ℝ := fun i => (hg i).1.mk (g F i) with hh_def
  have hhm : ∀ i, Measurable (h i) := fun i => (hg i).1.stronglyMeasurable_mk.measurable
  have hheq : ∀ i, g F i =ᵐ[F i] h i := fun i => (hg i).1.ae_eq_mk
  set μ : Fin m → ℝ := fun i => ∫ z, g F i z ∂(F i) with hμ_def
  set Z : (Σ _ : Fin m, ℕ) → Ω → ℝ :=
    fun p ω => (N p.1 : ℝ)⁻¹ * (h p.1 (X p.1 p.2 ω) - μ p.1) with hZ_def
  set s : Finset (Σ _ : Fin m, ℕ) := univ.sigma (fun i => range (N i)) with hs_def
  have hX : ∀ i j, MeasurePreserving (X i j) P (F i) :=
    fun i j => ⟨(hData.1 i j).1, (hData.1 i j).2⟩
  have hhX : ∀ i j, MemLp (fun ω => h i (X i j ω)) 2 P :=
    fun i j => ((hg i).ae_eq (hheq i)).comp_measurePreserving (hX i j)
  have hZ : ∀ p, MemLp (Z p) 2 P := fun p =>
    ((hhX p.1 p.2).sub (memLp_const (μ p.1))).const_mul _
  refine ⟨∑ p ∈ s, Z p, memLp_finsetSum' _ (fun p _ => hZ p), ?_, ?_⟩
  · rw [IndepFun.variance_sum (fun p _ => hZ p)]
    · have hv : ∀ p : (Σ _ : Fin m, ℕ), Var[Z p; P] =
          ((N p.1 : ℝ)⁻¹) ^ 2 * sigma2 F g p.1 := by
        intro p
        simp only [hZ_def]
        rw [variance_const_mul, variance_sub_const (hhX p.1 p.2).1,
          (hX p.1 p.2).variance_fun_comp (hhm p.1).aemeasurable, sigma2,
          variance_congr (hheq p.1)]
      simp_rw [hv]
      rw [hs_def, Finset.sum_sigma]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      dsimp only
      rw [Finset.sum_const, card_range, nsmul_eq_mul]
      have : (N i : ℝ) ≠ 0 := by exact_mod_cast hN i
      field_simp
    · intro p _ q _ hpq
      have hind := hData.2.indepFun hpq
      exact hind.comp (((hhm p.1).sub_const (μ p.1)).const_mul _)
        (((hhm q.1).sub_const (μ q.1)).const_mul _)
  · have hall : ∀ᵐ ω ∂P, ∀ p : (Σ _ : Fin m, ℕ),
        g F p.1 (X p.1 p.2 ω) = h p.1 (X p.1 p.2 ω) := by
      rw [ae_all_iff]
      intro p
      have hmap : g F p.1 =ᵐ[P.map (X p.1 p.2)] h p.1 := by
        rw [(hX p.1 p.2).map_eq]; exact hheq p.1
      exact ae_eq_comp (hX p.1 p.2).measurable.aemeasurable hmap
    filter_upwards [hall] with ω hω
    simp only [Finset.sum_apply]
    rw [hs_def, Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hNi : (N i : ℝ) ≠ 0 := by exact_mod_cast hN i
    rw [Fin.sum_univ_eq_sum_range (fun j => g F i (X i j ω)) (N i)]
    simp only [hZ_def]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
    have : ∀ j ∈ range (N i), g F i (X i j ω) = h i (X i j ω) := fun j _ => hω ⟨i, j⟩
    rw [Finset.sum_congr rfl this]
    simp only [hμ_def]
    field_simp

end SVBProp1Aux

open SVBProp1Aux in
theorem solution
    {m : ℕ} [NeZero m] {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Inputs Ξ) [∀ i, IsProbabilityMeasure (F i)]
    (S : ∀ i, Set (Ξ i)) (ψ : Inputs Ξ → ℝ)
    (g : Inputs Ξ → ∀ i, Ξ i → ℝ)
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : ℕ → Fin m → ℕ)
    (hS : ∀ i, MeasurableSet (S i) ∧ F i (S i)ᶜ = 0)
    (hData : IIDData P F X) (hA1 : A1 n) (hA2 : A2 F S ψ g)
    (hA3 : A3 P F ψ g X n) :
    Tendsto (fun k => nbar (n k) *
      (sigmaI ψ P X (n k) - ∑ i : Fin m, sigma2 F g i / (n k i : ℝ)))
      atTop (nhds 0) := by
  obtain ⟨hσ, hRemEv, hRemLim⟩ := hA3
  obtain ⟨hntend, C, hC, hbal⟩ := hA1
  have hg2 : ∀ i, MemLp (g F i) 2 (F i) := fun i =>
    (hσ i).2.mono_exponent (by norm_num)
  have hpos : ∀ᶠ k in atTop, ∀ i, (n k i) ≠ 0 := by
    rw [eventually_all]
    intro i
    filter_upwards [(hntend i).eventually_gt_atTop 0] with k hk
    exact_mod_cast hk.ne'
  set K : ℝ := C * ∑ i : Fin m, sigma2 F g i with hK
  have hK0 : 0 ≤ K := mul_nonneg hC.le (Finset.sum_nonneg (fun i _ => variance_nonneg _ _))
  -- bound on n̄ * ∑ σᵢ²/nᵢ
  have hnS : ∀ᶠ k in atTop, 0 ≤ nbar (n k) ∧
      nbar (n k) * (∑ i : Fin m, sigma2 F g i / (n k i : ℝ)) ≤ K := by
    filter_upwards [hbal, hpos] with k hk hk0
    have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
    have hnb0 : 0 ≤ nbar (n k) := by
      unfold nbar; positivity
    refine ⟨hnb0, ?_⟩
    have hnb : ∀ i, nbar (n k) ≤ C * n k i := by
      intro i
      unfold nbar
      rw [div_le_iff₀ hm]
      calc (∑ j : Fin m, (n k j : ℝ)) ≤ ∑ _j : Fin m, C * n k i :=
            Finset.sum_le_sum (fun j _ => hk j i)
        _ = C * n k i * m := by
          rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    rw [hK, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hni : (0 : ℝ) < n k i := by exact_mod_cast Nat.pos_of_ne_zero (hk0 i)
    have hs := variance_nonneg (g F i) (F i)
    rw [mul_div_assoc', div_le_iff₀ hni]
    unfold sigma2
    nlinarith [hnb i]
  rw [Metric.tendsto_nhds]
  intro η hη
  set l : ℝ := η / (2 * (K + 1)) with hl
  have hl0 : 0 < l := by positivity
  have hlK : l * K < η / 2 := by
    rw [hl, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hlim2 := hRemLim.const_mul (1 + 1 / l)
  rw [mul_zero] at hlim2
  have hev2 := hlim2.eventually (gt_mem_nhds (show (0 : ℝ) < η / 2 by positivity))
  filter_upwards [hRemEv, hpos, hnS, hev2] with k hk hk0 hkS hk2
  obtain ⟨hRem2, hψ2⟩ := hk
  obtain ⟨L, hL2, hLvar, hLae⟩ := linear_part P F g X hData hg2 (n k) hk0
  set R : Ω → ℝ := fun ω => dataRemainder F ψ g (dataSample X (n k) ω) with hR
  have hdecomp : (fun ω => ψ (Fhat (dataSample X (n k) ω))) =ᵐ[P]
      fun ω => ψ F + (L ω + R ω) := by
    filter_upwards [hLae] with ω hω
    rw [← hω]
    simp only [hR, dataRemainder, dataSample]
    ring
  have hσI : sigmaI ψ P X (n k) = Var[fun ω => L ω + R ω; P] := by
    unfold sigmaI
    rw [variance_congr hdecomp]
    exact variance_const_add (X := fun ω => L ω + R ω) (hL2.1.add hRem2.1) (ψ F)
  have hb := var_add_bound hL2 hRem2 hl0
  have hVR : Var[R; P] ≤ ∫ ω, (dataRemainder F ψ g (dataSample X (n k) ω)) ^ 2 ∂P :=
    variance_le_expectation_sq hRem2.1
  rw [← hσI, hLvar] at hb
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hkS.1]
  set S := ∑ i : Fin m, sigma2 F g i / (n k i : ℝ)
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => div_nonneg (variance_nonneg _ _)
    (Nat.cast_nonneg _))
  have hc : 0 ≤ 1 + 1 / l := by positivity
  calc nbar (n k) * |sigmaI ψ P X (n k) - S|
      ≤ nbar (n k) * (l * S + (1 + 1 / l) * Var[R; P]) :=
        mul_le_mul_of_nonneg_left hb hkS.1
    _ ≤ l * (nbar (n k) * S) + (1 + 1 / l) * (nbar (n k) *
          ∫ ω, (dataRemainder F ψ g (dataSample X (n k) ω)) ^ 2 ∂P) := by
        have := mul_le_mul_of_nonneg_left hVR hkS.1
        nlinarith
    _ < η / 2 + η / 2 := by
        have := mul_le_mul_of_nonneg_left hkS.2 hl0.le
        linarith
    _ = η := by ring
