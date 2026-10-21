-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P31.characteristicDynamics_L2Contraction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:11:49.356798+00:00
-- url     : https://prove2.me/submissions/c88156bd-4d51-4c62-9e53-5760c948d82a

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P31
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Next46.P31

open QAlgorithms.PeriodicSchrodinger (Position)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace)

theorem g62i_shear_pres {d : ℕ} (t : ℝ) :
    MeasurePreserving (phaseShear (d := d) t) (volume : Measure (PhasePoint d)) volume := by
  have h1 : MeasurePreserving (fun p : Position d × Position d => (p.1, p.2 + t • p.1))
      ((volume : Measure (Position d)).prod volume) ((volume : Measure (Position d)).prod volume) := by
    refine MeasurePreserving.skew_product (g := fun p x => x + t • p) (MeasurePreserving.id _)
      (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun p => map_add_right_eq_self _ _
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure (Position d))) (ν := volume)).comp
    (h1.comp (Measure.measurePreserving_swap (μ := (volume : Measure (Position d))) (ν := volume)))
  have e : phaseShear (d := d) t = Prod.swap ∘ (fun p : Position d × Position d => (p.1, p.2 + t • p.1)) ∘ Prod.swap := by
    funext z; rfl
  rw [e]
  exact h2

theorem g62i_shear_add {d : ℕ} (a b : ℝ) (z : PhasePoint d) :
    phaseShear a (phaseShear b z) = phaseShear (b + a) z := by
  simp [phaseShear, add_smul, add_assoc]

theorem g62i_shear_zero {d : ℕ} (z : PhasePoint d) : phaseShear 0 z = z := by
  simp [phaseShear]

theorem g62i_nq_cont {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) :
    Continuous (noiseQuadratic A) := by
  have hc : ∀ i, Continuous fun z : PhasePoint d => phaseCoordinates z i := by
    intro i
    cases i with
    | inl j => simp only [phaseCoordinates, Sum.elim_inl]; fun_prop
    | inr j => simp only [phaseCoordinates, Sum.elim_inr]; fun_prop
  unfold noiseQuadratic
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((hc i).mul continuous_const).mul (hc j)

theorem g62i_nq_nonneg {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ)
    (hA : A.PosSemidef) (z : PhasePoint d) : 0 ≤ noiseQuadratic A z := by
  have := hA.dotProduct_mulVec_nonneg (phaseCoordinates z)
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at this
  unfold noiseQuadratic
  simpa [mul_assoc] using this

theorem g62i_je_nonpos {d : ℕ} (mu : Measure (PhasePoint d)) (z : PhasePoint d) :
    jumpExponent mu z ≤ 0 := by
  unfold jumpExponent
  exact integral_nonpos fun y => by simp only [Pi.zero_apply]; linarith [Real.cos_le_one (∑ j, (z.1 j * y.2 j + z.2 j * y.1 j))]

theorem g62i_cs {d : ℕ} (a b : Position d) : |∑ j, a j * b j| ≤ ‖a‖ * ‖b‖ := by
  have := abs_real_inner_le_norm a b
  simpa [PiLp.inner_apply, mul_comm] using this

theorem g62i_je_cont {d : ℕ} (mu : Measure (PhasePoint d))
    (hint : Integrable (fun z : PhasePoint d => ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) mu) :
    Continuous (jumpExponent mu) := by
  rw [continuous_iff_continuousAt]
  intro z0
  set R := ‖z0‖ + 1
  have hR : 0 ≤ R := by positivity
  unfold jumpExponent
  refine continuousAt_of_dominated (bound := fun y => R ^ 2 * (‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)) ?_ ?_
    (hint.const_mul _) ?_
  · exact Filter.Eventually.of_forall fun z => (by fun_prop : Continuous fun y : PhasePoint d =>
      Real.cos (∑ j, (z.1 j * y.2 j + z.2 j * y.1 j)) - 1).aestronglyMeasurable
  · have hball : Metric.ball z0 1 ∈ 𝓝 z0 := Metric.ball_mem_nhds _ one_pos
    filter_upwards [hball] with z hz
    refine Filter.Eventually.of_forall fun y => ?_
    have hzR : ‖z‖ ≤ R := by
      have : ‖z - z0‖ < 1 := by rw [← dist_eq_norm]; exact hz
      have h3 := norm_le_norm_add_norm_sub' z z0
      have h4 : ‖z‖ ≤ ‖z0‖ + ‖z - z0‖ := by
        calc ‖z‖ = ‖z0 + (z - z0)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      simp only [R]; linarith
    have h1 : ‖z.1‖ ≤ R := (norm_fst_le z).trans hzR
    have h2 : ‖z.2‖ ≤ R := (norm_snd_le z).trans hzR
    set L := ∑ j, (z.1 j * y.2 j + z.2 j * y.1 j)
    have hL : |L| ≤ R * ‖y.2‖ + R * ‖y.1‖ := by
      have e : L = (∑ j, z.1 j * y.2 j) + ∑ j, z.2 j * y.1 j := Finset.sum_add_distrib
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (g62i_cs _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
      · exact (g62i_cs _ _).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    have hcos := Real.one_sub_sq_div_two_le_cos (x := L)
    have hc1 := Real.cos_le_one L
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    have hL2 : L ^ 2 ≤ (R * ‖y.2‖ + R * ‖y.1‖) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hL 2
    nlinarith [sq_nonneg (‖y.1‖ - ‖y.2‖), sq_nonneg R]
  · exact Filter.Eventually.of_forall fun y => (by fun_prop : Continuous fun z : PhasePoint d =>
      Real.cos (∑ j, (z.1 j * y.2 j + z.2 j * y.1 j)) - 1).continuousAt

def g62i_phi {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (mu : Measure (PhasePoint d))
    (z : PhasePoint d) : ℝ :=
  -noiseQuadratic A z / 2 + jumpExponent mu z

def g62i_I {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (mu : Measure (PhasePoint d))
    (t : ℝ) (z : PhasePoint d) : ℝ :=
  ∫ s in (0 : ℝ)..t, g62i_phi A mu (phaseShear (t - s) z)

theorem g62i_evol {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (mu : Measure (PhasePoint d))
    (t : ℝ) (f : PhasePoint d → ℂ) (z : PhasePoint d) :
    characteristicEvolution A mu t f z = (Real.exp (g62i_I A mu t z) : ℂ) * f (phaseShear t z) := rfl

theorem g62i_phi_cont {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ)
    (mu : Measure (PhasePoint d))
    (hint : Integrable (fun z : PhasePoint d => ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) mu) :
    Continuous (g62i_phi A mu) := by
  unfold g62i_phi
  exact ((g62i_nq_cont A).neg.div_const _).add (g62i_je_cont mu hint)

theorem g62i_shear_cont {d : ℕ} : Continuous fun p : ℝ × PhasePoint d => phaseShear p.1 p.2 := by
  unfold phaseShear; fun_prop

theorem g62i_I_cont {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ)
    (mu : Measure (PhasePoint d))
    (hint : Integrable (fun z : PhasePoint d => ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) mu) (t : ℝ) :
    Continuous (g62i_I A mu t) := by
  unfold g62i_I
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have := (g62i_phi_cont A mu hint).comp
    (g62i_shear_cont.comp (by fun_prop : Continuous fun p : PhasePoint d × ℝ => (t - p.2, p.1)))
  exact this

theorem g62i_I_nonpos {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (hA : A.PosSemidef)
    (mu : Measure (PhasePoint d)) (t : ℝ) (ht : 0 ≤ t) (z : PhasePoint d) :
    g62i_I A mu t z ≤ 0 := by
  unfold g62i_I
  have := intervalIntegral.integral_nonneg (μ := volume) ht
    (f := fun u => -g62i_phi A mu (phaseShear (t - u) z)) (fun u _ => by
      unfold g62i_phi
      linarith [g62i_nq_nonneg A hA (phaseShear (t - u) z), g62i_je_nonpos mu (phaseShear (t - u) z)])
  rw [intervalIntegral.integral_neg] at this
  linarith

theorem g62i_I_zero {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ)
    (mu : Measure (PhasePoint d)) (z : PhasePoint d) : g62i_I A mu 0 z = 0 := by
  simp [g62i_I]

theorem g62i_I_add {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ)
    (mu : Measure (PhasePoint d))
    (hint : Integrable (fun z : PhasePoint d => ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) mu) (s t : ℝ) (z : PhasePoint d) :
    g62i_I A mu (s + t) z = g62i_I A mu s z + g62i_I A mu t (phaseShear s z) := by
  unfold g62i_I
  set g : ℝ → ℝ := fun u => g62i_phi A mu (phaseShear (s + t - u) z) with hg
  have hgc : Continuous g := (g62i_phi_cont A mu hint).comp
    (g62i_shear_cont.comp (by fun_prop : Continuous fun u : ℝ => (s + t - u, z)))
  have e1 : (∫ u in (0:ℝ)..s + t, g62i_phi A mu (phaseShear (s + t - u) z)) =
      (∫ u in (0:ℝ)..t, g u) + ∫ u in t..s + t, g u :=
    (intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)).symm
  have e2 : (∫ u in (0:ℝ)..t, g62i_phi A mu (phaseShear (t - u) (phaseShear s z))) =
      ∫ u in (0:ℝ)..t, g u := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hg, g62i_shear_add]
    congr 2; ring
  have e3 : (∫ u in (0:ℝ)..s, g62i_phi A mu (phaseShear (s - u) z)) = ∫ u in t..s + t, g u := by
    have := intervalIntegral.integral_comp_add_right g t (a := 0) (b := s)
    rw [zero_add] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hg]
    congr 2; ring
  rw [e1, e2, e3]; ring

theorem g62i_memLp {d : ℕ} (m : PhasePoint d → ℝ) (hm : Continuous m) (hb : ∀ z, |m z| ≤ 1)
    (f : Lp ℂ 2 (volume : Measure (PhasePoint d))) :
    MemLp (fun z => (m z : ℂ) * f z) 2 (volume : Measure (PhasePoint d)) := by
  refine (Lp.memLp f).of_le ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact ((Complex.continuous_ofReal.comp hm).aestronglyMeasurable).mul (Lp.aestronglyMeasurable f)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb z)

def g62i_mulLin {d : ℕ} (m : PhasePoint d → ℝ) (hm : Continuous m) (hb : ∀ z, |m z| ≤ 1) :
    Lp ℂ 2 (volume : Measure (PhasePoint d)) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (PhasePoint d)) where
  toFun f := (g62i_memLp m hm hb f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(g62i_memLp m hm hb (f + g)).coeFn_toLp, (g62i_memLp m hm hb f).coeFn_toLp,
      (g62i_memLp m hm hb g).coeFn_toLp, Lp.coeFn_add f g,
      Lp.coeFn_add ((g62i_memLp m hm hb f).toLp _) ((g62i_memLp m hm hb g).toLp _)] with z h1 h2 h3 h4 h5
    rw [h5, Pi.add_apply, h1, h2, h3, h4, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(g62i_memLp m hm hb (c • f)).coeFn_toLp, (g62i_memLp m hm hb f).coeFn_toLp,
      Lp.coeFn_smul c f, Lp.coeFn_smul c ((g62i_memLp m hm hb f).toLp _)] with z h1 h2 h3 h4
    rw [RingHom.id_apply, h4, Pi.smul_apply, h1, h2, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

def g62i_mulOp {d : ℕ} (m : PhasePoint d → ℝ) (hm : Continuous m) (hb : ∀ z, |m z| ≤ 1) :
    Lp ℂ 2 (volume : Measure (PhasePoint d)) →L[ℂ] Lp ℂ 2 (volume : Measure (PhasePoint d)) :=
  (g62i_mulLin m hm hb).mkContinuous 1 fun f => by
    rw [one_mul]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(g62i_memLp m hm hb f).coeFn_toLp] with z h1
    change ‖((g62i_memLp m hm hb f).toLp _ : PhasePoint d → ℂ) z‖ ≤ ‖f z‖
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb z)

theorem g62i_mulOp_ae {d : ℕ} (m : PhasePoint d → ℝ) (hm : Continuous m) (hb : ∀ z, |m z| ≤ 1)
    (f : Lp ℂ 2 (volume : Measure (PhasePoint d))) :
    (g62i_mulOp m hm hb f : PhasePoint d → ℂ) =ᵐ[volume] fun z => (m z : ℂ) * f z :=
  (g62i_memLp m hm hb f).coeFn_toLp

theorem g62i_mulOp_norm {d : ℕ} (m : PhasePoint d → ℝ) (hm : Continuous m) (hb : ∀ z, |m z| ≤ 1)
    (f : Lp ℂ 2 (volume : Measure (PhasePoint d))) : ‖g62i_mulOp m hm hb f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [g62i_mulOp_ae m hm hb f] with z h1
  rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb z)

/-- Clark, PDF p.14, unnumbered Section 3 assertion: the formula defines a
semigroup of contractions on the full L2 space. The actual bounded linear maps,
identity, semigroup law, norm bound, and agreement with (1.19) are conclusions. -/
theorem solution {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (mu : Measure (PhasePoint d))
    (hnoise : FiniteVarianceLevyNoise A mu) :
    ∃ G : ℝ≥0 → (Lp ℂ 2 (volume : Measure (PhasePoint d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (PhasePoint d))),
      (∀ t f, (G t f : PhasePoint d → ℂ) =ᵐ[volume]
        characteristicEvolution A mu (t : ℝ) (f : PhasePoint d → ℂ)) ∧
      G 0 = ContinuousLinearMap.id ℂ _ ∧
      (∀ s t, G (s + t) = (G s).comp (G t)) ∧
      (∀ t f, ‖G t f‖ ≤ ‖f‖) := by
  have hA := hnoise.1
  have hint := hnoise.2.2.2
  let m : ℝ≥0 → PhasePoint d → ℝ := fun t z => Real.exp (g62i_I A mu t z)
  have hm : ∀ t, Continuous (m t) := fun t => Real.continuous_exp.comp (g62i_I_cont A mu hint t)
  have hb : ∀ t z, |m t z| ≤ 1 := fun t z => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (g62i_I_nonpos A hA mu t t.2 z)
  let C : ℝ≥0 → (Lp ℂ 2 (volume : Measure (PhasePoint d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (PhasePoint d))) := fun t =>
    (Lp.compMeasurePreservingₗᵢ ℂ (phaseShear (t : ℝ)) (g62i_shear_pres (t : ℝ))).toContinuousLinearMap
  have hC : ∀ t f, (C t f : PhasePoint d → ℂ) =ᵐ[volume] fun z => f (phaseShear (t : ℝ) z) :=
    fun t f => Lp.coeFn_compMeasurePreserving f (g62i_shear_pres (t : ℝ))
  let G : ℝ≥0 → (Lp ℂ 2 (volume : Measure (PhasePoint d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (PhasePoint d))) := fun t => (g62i_mulOp (m t) (hm t) (hb t)).comp (C t)
  have h1 : ∀ t f, (G t f : PhasePoint d → ℂ) =ᵐ[volume]
      characteristicEvolution A mu (t : ℝ) (f : PhasePoint d → ℂ) := by
    intro t f
    filter_upwards [g62i_mulOp_ae (m t) (hm t) (hb t) (C t f), hC t f] with z h h'
    simp only [G, ContinuousLinearMap.comp_apply]
    rw [h, h', g62i_evol]
  refine ⟨G, h1, ?_, ?_, ?_⟩
  · ext1 f
    apply Lp.ext
    filter_upwards [h1 0 f] with z h
    rw [h, g62i_evol, NNReal.coe_zero, g62i_I_zero, g62i_shear_zero, ContinuousLinearMap.id_apply]
    simp
  · intro s t
    ext1 f
    apply Lp.ext
    have h2 := (g62i_shear_pres (d := d) (s : ℝ)).quasiMeasurePreserving.ae_eq_comp (h1 t f)
    filter_upwards [h1 (s + t) f, h1 s (G t f), h2] with z ha hb' hc
    change ((G (s + t)) f : PhasePoint d → ℂ) z = ((G s) ((G t) f) : PhasePoint d → ℂ) z
    rw [hb', ha, g62i_evol, g62i_evol]
    simp only [Function.comp_apply] at hc
    rw [hc, g62i_evol, g62i_shear_add, NNReal.coe_add, g62i_I_add A mu hint, Real.exp_add]
    push_cast
    ring
  · intro t f
    simp only [G, ContinuousLinearMap.comp_apply]
    refine (g62i_mulOp_norm _ _ _ _).trans ?_
    simp only [C, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
    exact le_rfl

end
