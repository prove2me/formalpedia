-- Prove2me | solution 1 for SubsetShrink.Events.prob_H
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T21:12:34.100616+00:00
-- url     : https://prove2.me/submissions/78e09110-44ae-47a1-9525-cea6ff11a9ae

/-
  DS10 target: SubsetShrink.Events.prob_H
  theorem_id bf5e6157-89eb-4507-8496-725ea3526021
  (Open milestone of mission 97e863d6-ac4e-4114-a6d3-d16a481f46a2
  "Four Gaussian Noise Events ...").

  𝓗 = {‖Xᵀϵ‖_∞ ≤ σ√(2 log 2p) + σ√(2 log(1/δ₀))} is measurable and has
  probability ≥ 1 − δ₀ under the product noise law N(0,σ²)^{⊗n}.

  Method.  Each coordinate `(Xᵀϵ)_j = ∑_i X_ij ϵ_i` is a sum of independent
  weighted standard Gaussians; through Mathlib's sub-Gaussian MGF API
  (`HasSubgaussianMGF.sum_of_iIndepFun`) it is sub-Gaussian with parameter
  `∑_i X_ij² · σ² = σ²`, using `UnitCols`.  The Chernoff bound
  `HasSubgaussianMGF.measure_ge_le` gives the two one-sided Gaussian tails
  `P(±(Xᵀϵ)_j ≥ t) ≤ exp(−t²/(2σ²))`, and a union bound over the `p`
  coordinates gives

      P(𝓗ᶜ) ≤ 2p · exp(−t²/(2σ²)) = δ₀ · exp(−ab) ≤ δ₀ ,

  where `a = √(2 log 2p)`, `b = √(2 log(1/δ₀))`.  No platform theorem is
  imported: the whole argument is self-contained.
-/
import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory
open SubsetShrink.Events
open scoped NNReal

/-- `σ²` packaged as an `ℝ≥0`.  Using this wrapper (instead of a literal
`⟨σ ^ 2, sq_nonneg σ⟩`) keeps the subtype transparent for instance search. -/
private def sigNN (σ : ℝ) : ℝ≥0 := ⟨σ ^ 2, sq_nonneg σ⟩

/-- `noiseLaw` is by definition the product Gaussian law. -/
private lemma noiseLaw_eq {n : ℕ} (σ : ℝ) :
    noiseLaw n σ = Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ)) := rfl

/-- `id : ℝ → ℝ` is sub-Gaussian with parameter `σ²` under `N(0,σ²)`. -/
private lemma gaussianReal_id_subG (σ : ℝ) :
    HasSubgaussianMGF (id : ℝ → ℝ) (sigNN σ) (gaussianReal 0 (sigNN σ)) := by
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
  rw [mgf_id_gaussianReal]
  simp

/-- The `i`-th coordinate `ε ↦ ε i` is sub-Gaussian with parameter `σ²` under the
product noise law (its law is `N(0,σ²)`). -/
private lemma eval_pi_subG {n : ℕ} (σ : ℝ) (i : Fin n) :
    HasSubgaussianMGF (fun ε : Fin n → ℝ => ε i) (sigNN σ)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))) := by
  rw [← HasSubgaussianMGF.id_map_iff (X := fun ε : Fin n → ℝ => ε i)
    (measurable_pi_apply i).aemeasurable]
  rw [(measurePreserving_eval (μ := fun _ : Fin n => gaussianReal 0 (sigNN σ)) i).map_eq]
  exact gaussianReal_id_subG σ

/-- The linear combination `ε ↦ ∑ i, X i j * ε i` is sub-Gaussian with parameter
`σ² = ∑_i X_ij² · σ²`, because the columns of `X` have unit norm. -/
private lemma linear_subG {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (σ : ℝ) (j : Fin p) :
    HasSubgaussianMGF (fun ε : Fin n → ℝ => ∑ i, X i j * ε i) (sigNN σ)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))) := by
  have hindep : iIndepFun (fun i (ε : Fin n → ℝ) => X i j * ε i)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))) :=
    iIndepFun_pi (X := fun i (x : ℝ) => X i j * x) (fun i => by fun_prop)
  have hsum : HasSubgaussianMGF (fun ε : Fin n → ℝ => ∑ i, X i j * ε i)
      (∑ i : Fin n, sigNN (X i j) * sigNN σ)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))) := by
    refine HasSubgaussianMGF.sum_of_iIndepFun hindep (c := fun i => sigNN (X i j) * sigNN σ)
      (s := Finset.univ) (fun i _ => ?_)
    simpa [sigNN] using (eval_pi_subG σ i).const_mul (X i j)
  have hconst : (∑ i : Fin n, sigNN (X i j) * sigNN σ) = sigNN σ := by
    have hsplit : (∑ i : Fin n, sigNN (X i j) * sigNN σ) =
        (∑ i : Fin n, sigNN (X i j)) * sigNN σ := (Finset.sum_mul _ _ _).symm
    rw [hsplit]
    have hXj : (∑ i : Fin n, sigNN (X i j)) = 1 := by
      apply NNReal.coe_inj.mp
      rw [NNReal.coe_sum, NNReal.coe_one]
      simp only [sigNN]
      exact hX j
    rw [hXj, one_mul]
  rw [hconst] at hsum
  exact hsum

/-- Numeric threshold: `2p · exp(−t²/(2σ²)) ≤ δ₀` for
`t = σ√(2 log 2p) + σ√(2 log(1/δ₀))`, `σ > 0`, `0 < δ₀ ≤ 1`, `1 ≤ p`.
Indeed with `a = √(2 log 2p)`, `b = √(2 log(1/δ₀))` one has
`exp(−t²/(2σ²)) = exp(−a²/2)·exp(−b²/2)·exp(−ab) = (2p)⁻¹·δ₀·exp(−ab)`. -/
private lemma threshold_bound {p : ℕ} (hp : 1 ≤ p) {σ δ0 : ℝ} (hσ : 0 < σ) (hδ0 : 0 < δ0)
    (hδ1 : δ0 ≤ 1) :
    (2 * (p : ℝ)) * Real.exp
        (-(σ * Real.sqrt (2 * Real.log (2 * (p : ℝ))) + σ * Real.sqrt (2 * Real.log (1 / δ0))) ^ 2
          / (2 * σ ^ 2)) ≤ δ0 := by
  set a : ℝ := Real.sqrt (2 * Real.log (2 * (p : ℝ))) with ha_def
  set b : ℝ := Real.sqrt (2 * Real.log (1 / δ0)) with hb_def
  have hApos : 0 < 2 * (p : ℝ) := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hBpos : 0 < 1 / δ0 := by positivity
  have hA1 : 1 ≤ 2 * (p : ℝ) := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hB1 : 1 ≤ 1 / δ0 := by rw [one_le_div hδ0]; exact hδ1
  have ha : 0 ≤ a := by rw [ha_def]; exact Real.sqrt_nonneg _
  have hb : 0 ≤ b := by rw [hb_def]; exact Real.sqrt_nonneg _
  have hsa : a ^ 2 = 2 * Real.log (2 * (p : ℝ)) := by
    rw [ha_def, Real.sq_sqrt (mul_nonneg (by norm_num) (Real.log_nonneg hA1))]
  have hsb : b ^ 2 = 2 * Real.log (1 / δ0) := by
    rw [hb_def, Real.sq_sqrt (mul_nonneg (by norm_num) (Real.log_nonneg hB1))]
  have harg : -(σ * a + σ * b) ^ 2 / (2 * σ ^ 2) = -(a ^ 2 / 2) - b ^ 2 / 2 - a * b := by
    have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero _ hσ.ne'
    field_simp
    ring
  have e1 : Real.exp (-(a ^ 2 / 2)) = (2 * (p : ℝ))⁻¹ := by
    rw [show -(a ^ 2 / 2) = -Real.log (2 * (p : ℝ)) by rw [hsa]; ring,
      Real.exp_neg, Real.exp_log hApos]
  have e2 : Real.exp (-(b ^ 2 / 2)) = δ0 := by
    rw [show -(b ^ 2 / 2) = -Real.log (1 / δ0) by rw [hsb]; ring,
      Real.exp_neg, Real.exp_log hBpos, one_div, inv_inv]
  have esplit : Real.exp (-(a ^ 2 / 2) - b ^ 2 / 2 - a * b) =
      Real.exp (-(a ^ 2 / 2)) * Real.exp (-(b ^ 2 / 2)) * Real.exp (-(a * b)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [show σ * Real.sqrt (2 * Real.log (2 * (p : ℝ))) + σ * Real.sqrt (2 * Real.log (1 / δ0))
      = σ * a + σ * b from by rw [ha_def, hb_def], harg, esplit, e1, e2]
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hexp : Real.exp (-(a * b)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  calc (2 * (p : ℝ)) * ((2 * (p : ℝ))⁻¹ * δ0 * Real.exp (-(a * b)))
      = δ0 * Real.exp (-(a * b)) := by field_simp
    _ ≤ δ0 * 1 := by gcongr
    _ = δ0 := by ring

theorem solution {n p : ℕ} (hp : 1 ≤ p) (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (σ : ℝ) (hσ : 0 < σ) (δ0 : ℝ) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1) :
    MeasurableSet (H X σ δ0) ∧ 1 - δ0 ≤ (noiseLaw n σ (H X σ δ0)).toReal := by
  rw [noiseLaw_eq]
  -- measurability of `ε ↦ lInf (Xᵀ ϵ)`
  have hYmeas : ∀ j : Fin p, Measurable (fun ε : Fin n → ℝ => ∑ i, X i j * ε i) := by
    intro j; fun_prop
  have hlInf_meas : Measurable (fun ε : Fin n → ℝ => lInf (X.transpose.mulVec ε)) := by
    have h : (fun ε : Fin n → ℝ => lInf (X.transpose.mulVec ε)) =
        fun ε : Fin n → ℝ => ⨆ j, |∑ i, X i j * ε i| := by
      funext ε
      simp only [lInf, Matrix.mulVec_apply, dotProduct, Matrix.row, Matrix.transpose_apply]
    rw [h]
    exact Measurable.iSup (fun j => (hYmeas j).abs)
  have hHmeas : MeasurableSet (H X σ δ0) := by
    unfold H
    exact measurableSet_le hlInf_meas measurable_const
  refine ⟨hHmeas, ?_⟩
  set t : ℝ := σ * Real.sqrt (2 * Real.log (2 * (p : ℝ))) + σ * Real.sqrt (2 * Real.log (1 / δ0))
    with ht_def
  have ht_nonneg : 0 ≤ t := by rw [ht_def]; positivity
  -- per-coordinate two-sided Gaussian tail
  have htail_j : ∀ j : Fin p,
      (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real
          {ε : Fin n → ℝ | t < |∑ i, X i j * ε i|} ≤
        2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)) := by
    intro j
    have hY := linear_subG X hX σ j
    have hA : (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real
        {ε : Fin n → ℝ | t ≤ ∑ i, X i j * ε i} ≤ Real.exp (-(t ^ 2) / (2 * σ ^ 2)) :=
      hY.measure_ge_le ht_nonneg
    have hB : (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real
        {ε : Fin n → ℝ | t ≤ -(∑ i, X i j * ε i)} ≤ Real.exp (-(t ^ 2) / (2 * σ ^ 2)) := by
      exact hY.neg.measure_ge_le (ε := t) ht_nonneg
    calc (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real
            {ε : Fin n → ℝ | t < |∑ i, X i j * ε i|}
        ≤ (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real
            ({ε : Fin n → ℝ | t ≤ ∑ i, X i j * ε i} ∪
              {ε : Fin n → ℝ | t ≤ -(∑ i, X i j * ε i)}) := by
          refine measureReal_mono ?_ (by finiteness)
          intro ε hε
          simp only [Set.mem_ofPred_eq, Set.mem_union] at hε ⊢
          rcases lt_or_ge (∑ i, X i j * ε i) 0 with h | h
          · right
            rw [abs_of_neg h] at hε
            linarith [hε]
          · left
            rw [abs_of_nonneg h] at hε
            exact hε.le
      _ ≤ (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real
            {ε : Fin n → ℝ | t ≤ ∑ i, X i j * ε i} +
          (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real
            {ε : Fin n → ℝ | t ≤ -(∑ i, X i j * ε i)} := measureReal_union_le _ _
      _ ≤ Real.exp (-(t ^ 2) / (2 * σ ^ 2)) + Real.exp (-(t ^ 2) / (2 * σ ^ 2)) :=
          add_le_add hA hB
      _ = 2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)) := by ring
  -- union bound on `𝓗ᶜ`
  have hHc : (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real (H X σ δ0)ᶜ ≤ δ0 := by
    have : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
    have hincl : (H X σ δ0)ᶜ ⊆
        ⋃ j : Fin p, {ε : Fin n → ℝ | t < |∑ i, X i j * ε i|} := by
      intro ε hε
      simp only [Set.mem_compl_iff, H, Set.mem_ofPred_eq, not_le] at hε
      rw [← ht_def] at hε
      rw [lInf] at hε
      obtain ⟨j, hj⟩ := (lt_ciSup_iff (Set.finite_range _).bddAbove).mp hε
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      simp only [Set.mem_ofPred_eq,
        Matrix.mulVec_apply, dotProduct, Matrix.row, Matrix.transpose_apply] at hj ⊢
      exact hj
    calc (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real (H X σ δ0)ᶜ
        ≤ (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real
            (⋃ j : Fin p, {ε : Fin n → ℝ | t < |∑ i, X i j * ε i|}) := measureReal_mono hincl
      _ ≤ ∑ j : Fin p, (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real
            {ε : Fin n → ℝ | t < |∑ i, X i j * ε i|} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin p, 2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)) :=
          Finset.sum_le_sum (fun j _ => htail_j j)
      _ = (2 * (p : ℝ)) * Real.exp (-(t ^ 2) / (2 * σ ^ 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ δ0 := by
          rw [ht_def]
          exact threshold_bound hp hσ hδ0 hδ1
  have huniv : (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real Set.univ = 1 := by
    simp [measureReal_def]
  have hcompl := measureReal_compl
    (μ := Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))) hHmeas
  rw [huniv] at hcompl
  show 1 - δ0 ≤ (Measure.pi (fun _ : Fin n => gaussianReal 0 (sigNN σ))).real (H X σ δ0)
  linarith [hHc, hcompl]
