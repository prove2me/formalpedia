-- Prove2me | solution 1 for SmoothedSimplex.TwoPhase.smoothed_complexity_polynomial
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T18:02:00.351892+00:00
-- url     : https://prove2.me/submissions/50cb7637-9671-4865-9a38-ccaa99af6a4d

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

/-! Disproof skeleton for b1b2e73e (SmoothedSimplex.TwoPhase.smoothed_complexity_polynomial).
Counterexample: free sum of m simplices (block k: e_1..e_b, -(e_1+..+e_b)) in R^(m b), n = m (b+1), rhs centres 0,
tiny noise. TwoPhase.shadow includes q = 0, so firstPhaseSteps = number of exposed facets of conv(0, a_i / y'_i),
which is (b+1)^m on a high-probability event; m is chosen above the degree of P. -/

set_option autoImplicit false

namespace B1B2
open SmoothedSimplex.TwoPhase MeasureTheory

/-- vertex `i = (k, j)`: `j < b` gives `e_(k,j)`, `j = b` gives `-(sum_j e_(k,j))`. -/
noncomputable def ctr (m b : ℕ) (i : Fin (m * (b + 1))) : Point (m * b) :=
  WithLp.toLp 2 (fun q : Fin (m * b) =>
    if (finProdFinEquiv.symm q).1 = (finProdFinEquiv.symm i).1 then
      (if ((finProdFinEquiv.symm i).2 : ℕ) = ((finProdFinEquiv.symm q).2 : ℕ) then 1
       else if ((finProdFinEquiv.symm i).2 : ℕ) = b then -1 else 0)
    else 0)

/-- the good `d`-set omitting vertex `f k` of every block `k`. -/
def goodSet (m b : ℕ) (f : Fin m → Fin (b + 1)) : Finset (Fin (m * (b + 1))) :=
  Finset.univ.filter (fun i => (finProdFinEquiv.symm i).2 ≠ f (finProdFinEquiv.symm i).1)

/-- the closeness event. -/
def close (m b : ℕ) (θ : ℝ) (p : (Fin (m * (b + 1)) → Point (m * b)) × (Fin (m * (b + 1)) → ℝ)) : Prop :=
  (∀ i q, |p.1 i q - ctr m b i q| ≤ θ) ∧ ∀ i, |p.2 i| ≤ θ

/-- the good-draw event. -/
def goodDraw (m b : ℕ) (draw : Fin (sampleCount (m * (b + 1)) (m * b)) → DSet (m * (b + 1)) (m * b)) : Prop :=
  ∃ t f, (draw t).1 = goodSet m b f

noncomputable def θ0 (m b : ℕ) : ℝ := 1 / (1000 * ((m * b : ℕ) + 1 : ℝ) ^ 8)

/-- noise standard deviation actually used. -/
noncomputable def σ' (m b : ℕ) : ℝ := θ0 m b / (4 * ((m * b : ℕ) + 1 : ℝ))

/-! ## Obligations (each is a separate relay step; see scratch/probe/b1b2e73e.progress.md) -/

theorem gv_prob {d : ℕ} (c : Point d) (σ : ℝ) : IsProbabilityMeasure (gaussianVector c σ) := by
  have : ∀ k, IsProbabilityMeasure (ProbabilityTheory.gaussianReal (c k) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    fun k => ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  have h1 : IsProbabilityMeasure (Measure.pi fun k : Fin d =>
      ProbabilityTheory.gaussianReal (c k) ⟨σ ^ 2, sq_nonneg σ⟩) := Measure.pi.instIsProbabilityMeasure _
  unfold gaussianVector
  exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

theorem gi_prob {n d : ℕ} (c : Fin n → Point d) (y : Fin n → ℝ) (σ : ℝ) :
    IsProbabilityMeasure (gaussianInput c y σ) := by
  have : ∀ i, IsProbabilityMeasure (gaussianVector (c i) σ) := fun i => gv_prob _ _
  have h1 : IsProbabilityMeasure (Measure.pi fun i => gaussianVector (c i) σ) := inferInstance
  have : ∀ i, IsProbabilityMeasure (ProbabilityTheory.gaussianReal (y i) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    fun i => ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  have h2 : IsProbabilityMeasure (Measure.pi fun i : Fin n =>
      ProbabilityTheory.gaussianReal (y i) ⟨σ ^ 2, sq_nonneg σ⟩) := Measure.pi.instIsProbabilityMeasure _
  unfold gaussianInput gaussianFamily
  infer_instance

theorem alg_prob (n d : ℕ) (hdn : d ≤ n) : IsFiniteMeasure (algorithmLaw n d) := by
  haveI := ProbabilityTheory.isProbabilityMeasure_expMeasure (r := (1 : ℝ)) one_pos
  have : IsFiniteMeasure ((1 / (Nat.choose n d : ENNReal)) • (Measure.count : Measure (DSet n d))) :=
    Measure.smul_finite _ (by simp; exact_mod_cast (Nat.choose_pos hdn).ne')
  unfold algorithmLaw sampleLaw
  infer_instance

theorem gauss_tail (c σ θ : ℝ) (hθ : 0 < θ) :
    (ProbabilityTheory.gaussianReal c ⟨σ ^ 2, sq_nonneg σ⟩).real {x | θ ≤ |x - c|} ≤ σ ^ 2 / θ ^ 2 := by
  have := ProbabilityTheory.instIsProbabilityMeasureGaussianReal c ⟨σ ^ 2, sq_nonneg σ⟩
  have h := ProbabilityTheory.meas_ge_le_variance_div_sq
    (μ := ProbabilityTheory.gaussianReal c ⟨σ ^ 2, sq_nonneg σ⟩) (X := id)
    (ProbabilityTheory.memLp_id_gaussianReal' 2 (by norm_num)) hθ
  have hv : ProbabilityTheory.variance id (ProbabilityTheory.gaussianReal c ⟨σ ^ 2, sq_nonneg σ⟩) = σ ^ 2 := by
    have := ProbabilityTheory.variance_id_gaussianReal (μ := c) (v := ⟨σ ^ 2, sq_nonneg σ⟩)
    exact this
  have hi : ∫ x, id x ∂(ProbabilityTheory.gaussianReal c ⟨σ ^ 2, sq_nonneg σ⟩) = c :=
    ProbabilityTheory.integral_id_gaussianReal
  rw [hv, hi] at h
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (by simpa using h)

theorem marg1 {n d : ℕ} (c : Fin n → Point d) (y : Fin n → ℝ) (σ : ℝ) (i : Fin n) (q : Fin d)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (gaussianInput c y σ) {p | p.1 i q ∈ B} =
      ProbabilityTheory.gaussianReal (c i q) ⟨σ ^ 2, sq_nonneg σ⟩ B := by
  have : ∀ i, IsProbabilityMeasure (gaussianVector (c i) σ) := fun i => gv_prob _ _
  have : ∀ i, IsProbabilityMeasure (ProbabilityTheory.gaussianReal (y i) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    fun i => ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  have : ∀ k, IsProbabilityMeasure (ProbabilityTheory.gaussianReal (c i k) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    fun k => ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  have h2 : IsProbabilityMeasure (Measure.pi fun i : Fin n =>
      ProbabilityTheory.gaussianReal (y i) ⟨σ ^ 2, sq_nonneg σ⟩) := Measure.pi.instIsProbabilityMeasure _
  have hS : MeasurableSet {v : Point d | v q ∈ B} := (PiLp.continuous_apply 2 _ q).measurable hB
  have hset : {p : (Fin n → Point d) × (Fin n → ℝ) | p.1 i q ∈ B} =
      (Function.eval i ⁻¹' {v : Point d | v q ∈ B}) ×ˢ Set.univ := by
    ext p; simp
  rw [hset]
  unfold gaussianInput gaussianFamily
  rw [Measure.prod_prod, measure_univ, mul_one,
    (measurePreserving_eval (fun i => gaussianVector (c i) σ) i).measure_preimage hS.nullMeasurableSet]
  unfold gaussianVector
  rw [Measure.map_apply (by fun_prop) hS]
  have hpre : (WithLp.toLp 2 ⁻¹' {v : Point d | v q ∈ B}) = Function.eval q ⁻¹' B := by
    ext f; simp
  rw [hpre, (measurePreserving_eval (fun k : Fin d =>
    ProbabilityTheory.gaussianReal (c i k) ⟨σ ^ 2, sq_nonneg σ⟩) q).measure_preimage hB.nullMeasurableSet]

theorem marg2 {n d : ℕ} (c : Fin n → Point d) (y : Fin n → ℝ) (σ : ℝ) (i : Fin n)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (gaussianInput c y σ) {p | p.2 i ∈ B} =
      ProbabilityTheory.gaussianReal (y i) ⟨σ ^ 2, sq_nonneg σ⟩ B := by
  have : ∀ i, IsProbabilityMeasure (gaussianVector (c i) σ) := fun i => gv_prob _ _
  have : ∀ i, IsProbabilityMeasure (ProbabilityTheory.gaussianReal (y i) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    fun i => ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  have h1 : IsProbabilityMeasure (Measure.pi fun i => gaussianVector (c i) σ) :=
    Measure.pi.instIsProbabilityMeasure _
  have hset : {p : (Fin n → Point d) × (Fin n → ℝ) | p.2 i ∈ B} =
      Set.univ ×ˢ (Function.eval i ⁻¹' B) := by
    ext p; simp
  rw [hset]
  unfold gaussianInput gaussianFamily
  rw [Measure.prod_prod, measure_univ, one_mul,
    (measurePreserving_eval (fun i : Fin n =>
      ProbabilityTheory.gaussianReal (y i) ⟨σ ^ 2, sq_nonneg σ⟩) i).measure_preimage hB.nullMeasurableSet]

/-- O3 probability of a good draw, for `b` large in terms of `m`. -/
theorem card_DSet (n d : ℕ) : Fintype.card (DSet n d) = n.choose d := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun I : Finset (Fin n) =>
    (Finset.mem_powersetCard_univ (s := I) (k := d)).symm)), Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem mem_goodSet (m b : ℕ) (f : Fin m → Fin (b + 1)) (k : Fin m) (j : Fin (b + 1)) :
    finProdFinEquiv (k, j) ∈ goodSet m b f ↔ j ≠ f k := by
  simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]

theorem goodSet_card (m b : ℕ) (f : Fin m → Fin (b + 1)) : (goodSet m b f).card = m * b := by
  have h1 : goodSet m b f = (Finset.univ.filter (fun x : Fin m × Fin (b + 1) => x.2 ≠ f x.1)).map
      finProdFinEquiv.toEmbedding := by
    ext i
    obtain ⟨⟨k, j⟩, rfl⟩ := finProdFinEquiv.surjective i
    rw [mem_goodSet]
    simp
  rw [h1, Finset.card_map, Finset.card_filter, Fintype.sum_prod_type]
  have h2 : ∀ k : Fin m, (∑ j : Fin (b + 1), if j ≠ f k then 1 else 0) = b := by
    intro k
    rw [Finset.sum_boole, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem goodSet_inj (m b : ℕ) : Function.Injective (goodSet m b) := by
  intro f g h
  funext k
  by_contra hne
  have h1 : finProdFinEquiv (k, f k) ∉ goodSet m b f := by rw [mem_goodSet]; simp
  have h2 : finProdFinEquiv (k, f k) ∈ goodSet m b g := by rw [mem_goodSet]; exact hne
  rw [h] at h1
  exact h1 h2

/-- the good sets as elements of `DSet`. -/
def goodD (m b : ℕ) (f : Fin m → Fin (b + 1)) : DSet (m * (b + 1)) (m * b) := ⟨goodSet m b f, goodSet_card m b f⟩

set_option maxHeartbeats 1000000 in
theorem prob_goodDraw (m : ℕ) (hm : 1 ≤ m) : ∃ B : ℕ, ∀ b, B ≤ b →
    (1 / 2 : ENNReal) ≤ sampleLaw (m * (b + 1)) (m * b) {draw | goodDraw m b draw} := by
  refine ⟨m ^ m + 3, fun b hb => ?_⟩
  set n := m * (b + 1) with hn
  set d := m * b with hd
  have hdn : d ≤ n := Nat.mul_le_mul_left m (Nat.le_succ b)
  have hC : 0 < n.choose d := Nat.choose_pos hdn
  set u : Measure (DSet n d) := (1 / (Nat.choose n d : ENNReal)) • (Measure.count : Measure (DSet n d)) with hu
  have huniv : u Set.univ = 1 := by
    rw [hu, Measure.smul_apply, Measure.count_univ, ENat.card_eq_coe_fintype_card, card_DSet]
    simp only [smul_eq_mul, ENat.toENNReal_coe]
    rw [one_div, ENNReal.inv_mul_cancel (by exact_mod_cast hC.ne') (ENNReal.natCast_ne_top _)]
  haveI : IsProbabilityMeasure u := ⟨huniv⟩
  set S : Set (DSet n d) := {J | ∃ f, J.1 = goodSet m b f} with hS
  -- lower bound on u S
  have hSge : ((b + 1 : ℝ) ^ m) / (n.choose d : ℝ) ≤ u.real S := by
    have hsub : ((Finset.univ.image (goodD m b) : Finset (DSet n d)) : Set (DSet n d)) ⊆ S := by
      intro J hJ
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hJ
      obtain ⟨f, rfl⟩ := hJ
      exact ⟨f, rfl⟩
    have hinj : Function.Injective (goodD m b) := by
      intro f g h
      exact goodSet_inj m b (congrArg Subtype.val h)
    have hval : u ((Finset.univ.image (goodD m b) : Finset (DSet n d)) : Set (DSet n d)) =
        (1 / (n.choose d : ENNReal)) * ((b + 1) ^ m : ℕ) := by
      rw [hu, Measure.smul_apply, Measure.count_apply_finset, Finset.card_image_of_injective _ hinj,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, smul_eq_mul]
    calc ((b + 1 : ℝ) ^ m) / (n.choose d : ℝ)
        = u.real ((Finset.univ.image (goodD m b) : Finset (DSet n d)) : Set (DSet n d)) := by
          rw [measureReal_def, hval, ENNReal.toReal_mul, ENNReal.toReal_natCast, one_div,
            ENNReal.toReal_inv, ENNReal.toReal_natCast]
          push_cast; ring
      _ ≤ u.real S := measureReal_mono hsub
  have hSm : MeasurableSet S := (Set.toFinite S).measurableSet
  set T := sampleCount n d with hT
  have hcomp : {draw : Fin T → DSet n d | goodDraw m b draw}ᶜ = Set.pi Set.univ (fun _ => Sᶜ) := by
    ext draw
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, goodDraw, hS,
      not_exists]
    exact Iff.rfl
  have hlaw : sampleLaw n d = Measure.pi (fun _ : Fin T => u) := rfl
  have hcompv : (sampleLaw n d).real {draw : Fin T → DSet n d | goodDraw m b draw}ᶜ = (u.real Sᶜ) ^ T := by
    rw [hcomp, hlaw, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, measureReal_def]
  have hSc : u.real Sᶜ = 1 - u.real S := by rw [measureReal_compl hSm, probReal_univ]
  -- g T ≥ 1
  have hnr : (4 : ℝ) ≤ (n : ℝ) := by
    have : 4 ≤ n := by rw [hn]; nlinarith [Nat.one_le_pow m m (by omega)]
    exact_mod_cast this
  have hCle : (n.choose d : ℝ) ≤ (m : ℝ) ^ m * ((b : ℝ) + 1) ^ m := by
    have h1 : n.choose d = n.choose m := by
      rw [Nat.choose_symm_of_eq_add]; rw [hn, hd]; ring
    have h2 : n.choose m ≤ n ^ m := Nat.choose_le_pow n m
    have h3 : ((n ^ m : ℕ) : ℝ) = (m : ℝ) ^ m * ((b : ℝ) + 1) ^ m := by
      rw [hn, ← mul_pow]; push_cast; ring
    rw [h1, ← h3]; exact_mod_cast h2
  have hCpos : (0 : ℝ) < (n.choose d : ℝ) := by exact_mod_cast hC
  have hmm : (1 : ℝ) ≤ (m : ℝ) ^ m := one_le_pow₀ (by exact_mod_cast hm)
  have hg : 1 / (m : ℝ) ^ m ≤ ((b + 1 : ℝ) ^ m) / (n.choose d : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hCpos]; linarith
  have hTge : (m : ℝ) ^ m ≤ (T : ℝ) := by
    have hlog : 1 ≤ Real.log (n : ℝ) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
      have : 1 ≤ d := by rw [hd]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      exact_mod_cast this
    have hmb : (m : ℝ) ^ m ≤ (n : ℝ) := by
      have : m ^ m ≤ n := by rw [hn]; nlinarith
      exact_mod_cast this
    have hc : 3 * (n : ℝ) * (d : ℝ) * Real.log n ≤ (T : ℝ) := by
      rw [hT]; unfold sampleCount; exact Nat.le_ceil _
    have : (n : ℝ) ≤ 3 * (n : ℝ) * (d : ℝ) * Real.log n := by
      have h0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
      have : (1 : ℝ) ≤ 3 * (d : ℝ) * Real.log n := by nlinarith
      nlinarith
    linarith
  set g' := u.real S with hg'
  have hg'1 : g' ≤ 1 := by rw [hg']; exact measureReal_le_one
  have hgT : 1 ≤ g' * (T : ℝ) := by
    have h1 : 1 / (m : ℝ) ^ m ≤ g' := le_trans hg hSge
    have h2 : 1 / (m : ℝ) ^ m * (m : ℝ) ^ m = 1 := by field_simp
    have h3 : 0 ≤ 1 / (m : ℝ) ^ m := by positivity
    nlinarith
  have hpow : (1 - g') ^ T ≤ Real.exp (-1) := by
    calc (1 - g') ^ T ≤ (Real.exp (-g')) ^ T :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-g')]) T
      _ = Real.exp (-(g' * T)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
  have hmeas : MeasurableSet {draw : Fin T → DSet n d | goodDraw m b draw} := (Set.toFinite _).measurableSet
  haveI : IsProbabilityMeasure (sampleLaw n d) := by rw [hlaw]; infer_instance
  have hge : (1 / 2 : ℝ) ≤ (sampleLaw n d).real {draw | goodDraw m b draw} := by
    have hc := measureReal_compl (μ := sampleLaw n d) hmeas
    rw [probReal_univ, hcompv, hSc] at hc
    linarith
  rw [← ofReal_measureReal (measure_ne_top (sampleLaw n d) _)]
  have : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos]; simp
  rw [this]
  exact ENNReal.ofReal_le_ofReal hge

theorem ctr_apply (m b : ℕ) (k : Fin m) (j : Fin (b + 1)) (k' : Fin m) (j' : Fin b) :
    ctr m b (finProdFinEquiv (k, j)) (finProdFinEquiv (k', j')) =
      if k' = k then (if (j : ℕ) = (j' : ℕ) then 1 else if (j : ℕ) = b then -1 else 0) else 0 := by
  show (if (finProdFinEquiv.symm (finProdFinEquiv (k', j'))).1 =
          (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1 then
        (if ((finProdFinEquiv.symm (finProdFinEquiv (k, j))).2 : ℕ) =
            ((finProdFinEquiv.symm (finProdFinEquiv (k', j'))).2 : ℕ) then (1 : ℝ)
         else if ((finProdFinEquiv.symm (finProdFinEquiv (k, j))).2 : ℕ) = b then -1 else 0) else 0) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- every coordinate of a centre has absolute value at most one. -/
theorem ctr_abs_le (m b : ℕ) (i : Fin (m * (b + 1))) (q : Fin (m * b)) : |ctr m b i q| ≤ 1 := by
  obtain ⟨⟨k, j⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨k', j'⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [ctr_apply]
  split_ifs <;> norm_num

theorem norm_ctr_le (m b : ℕ) (i : Fin (m * (b + 1))) : ‖ctr m b i‖ ≤ ((m * b : ℕ) : ℝ) := by
  have hsq : ‖ctr m b i‖ ^ 2 ≤ ((m * b : ℕ) : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ q, ‖ctr m b i q‖ ^ 2 ≤ ∑ _q : Fin (m * b), (1 : ℝ) := by
          apply Finset.sum_le_sum; intro q _
          have h := ctr_abs_le m b i q
          rw [Real.norm_eq_abs]
          have h0 := abs_nonneg (ctr m b i q)
          nlinarith
      _ = ((m * b : ℕ) : ℝ) := by simp
  by_cases h0 : m * b = 0
  · have : ‖ctr m b i‖ ^ 2 ≤ 0 := by simpa [h0] using hsq
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg _))
    rw [this]; positivity
  · have h1 : (1 : ℝ) ≤ ((m * b : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    have hn := norm_nonneg (ctr m b i)
    nlinarith

/-- O4 the data norm of the centres. -/
theorem mdn_ctr (m b : ℕ) (hm : 1 ≤ m) (hb : 1 ≤ b) :
    0 < maxDataNorm (ctr m b) (fun _ => 0) ∧ maxDataNorm (ctr m b) (fun _ => 0) ≤ ((m * b : ℕ) : ℝ) := by
  unfold maxDataNorm
  have hfun : (fun i : Fin (m * (b + 1)) => Real.sqrt (((fun _ => (0 : ℝ)) i) ^ 2 + ‖ctr m b i‖ ^ 2)) =
      fun i => ‖ctr m b i‖ := by
    funext i; simp [Real.sqrt_sq (norm_nonneg _)]
  rw [hfun]
  have hbdd : BddAbove (Set.range fun i : Fin (m * (b + 1)) => ‖ctr m b i‖) := (Set.finite_range _).bddAbove
  have hm0 : 0 < m := hm
  have hb0 : 0 < b := hb
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin (m * (b + 1)), i0 = finProdFinEquiv (⟨0, hm0⟩, ⟨0, by omega⟩) := ⟨_, rfl⟩
  obtain ⟨q0, hq0⟩ : ∃ q0 : Fin (m * b), q0 = finProdFinEquiv (⟨0, hm0⟩, ⟨0, hb0⟩) := ⟨_, rfl⟩
  refine ⟨?_, ?_⟩
  · have hq : ctr m b i0 q0 = 1 := by
      rw [hi0, hq0, ctr_apply]; simp
    have hle : |ctr m b i0 q0| ≤ ‖ctr m b i0‖ := by
      have := PiLp.norm_apply_le (ctr m b i0) q0
      simpa [Real.norm_eq_abs] using this
    rw [hq, abs_one] at hle
    exact lt_of_lt_of_le one_pos (le_trans hle (le_csSup hbdd ⟨i0, rfl⟩))
  · have : Nonempty (Fin (m * (b + 1))) := ⟨i0⟩
    exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨i, rfl⟩; exact norm_ctr_le m b i)

/-- O5 polynomial growth bound. -/
theorem eval_bound (P : MvPolynomial (Fin 3) ℝ) : ∃ C : ℝ, ∃ D : ℕ, 0 ≤ C ∧ ∀ x : Fin 3 → ℝ,
    |MvPolynomial.eval x P| ≤ C * (1 + |x 0| + |x 1| + |x 2|) ^ D := by
  refine ⟨∑ s ∈ P.support, |P.coeff s|, P.totalDegree, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro x
  set R : ℝ := 1 + |x 0| + |x 1| + |x 2| with hR
  have hR1 : 1 ≤ R := by have := abs_nonneg (x 0); have := abs_nonneg (x 1); have := abs_nonneg (x 2); linarith
  have hxi : ∀ i : Fin 3, |x i| ≤ R := by
    intro i; fin_cases i <;> simp [hR] <;> linarith [abs_nonneg (x 0), abs_nonneg (x 1), abs_nonneg (x 2)]
  rw [MvPolynomial.eval_eq, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun s hs => ?_)
  rw [abs_mul, Finset.abs_prod]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ∏ i ∈ s.support, |x i ^ s i| ≤ ∏ i ∈ s.support, R ^ s i := by
        apply Finset.prod_le_prod (fun i _ => abs_nonneg _)
        intro i _
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hxi i) _
    _ = R ^ (∑ i ∈ s.support, s i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ R ^ P.totalDegree := by
        apply pow_le_pow_right₀ hR1
        have := MvPolynomial.le_totalDegree hs
        simpa [Finsupp.sum] using this

/-- O6 measurability of the events (needed for the integral bounds). -/
theorem measurableSet_close (m b : ℕ) (θ : ℝ) : MeasurableSet {p | close m b θ p} := by
  have h1 : ∀ i q, Measurable (fun p : (Fin (m * (b + 1)) → Point (m * b)) × (Fin (m * (b + 1)) → ℝ) =>
      |p.1 i q - ctr m b i q|) := by
    intro i q
    have : Continuous (fun p : (Fin (m * (b + 1)) → Point (m * b)) × (Fin (m * (b + 1)) → ℝ) =>
        |p.1 i q - ctr m b i q|) := by
      have hc : Continuous (fun v : Point (m * b) => v q) := PiLp.continuous_apply 2 _ q
      fun_prop
    exact this.measurable
  have h2 : ∀ i, Measurable (fun p : (Fin (m * (b + 1)) → Point (m * b)) × (Fin (m * (b + 1)) → ℝ) =>
      |p.2 i|) := by
    intro i
    have : Continuous (fun p : (Fin (m * (b + 1)) → Point (m * b)) × (Fin (m * (b + 1)) → ℝ) => |p.2 i|) := by
      fun_prop
    exact this.measurable
  have : {p | close m b θ p} = (⋂ i, ⋂ q, {p | |p.1 i q - ctr m b i q| ≤ θ}) ∩ ⋂ i, {p | |p.2 i| ≤ θ} := by
    ext p; simp [close]
  rw [this]
  exact MeasurableSet.inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun q => measurableSet_le (h1 i q) measurable_const)
    (MeasurableSet.iInter fun i => measurableSet_le (h2 i) measurable_const)

set_option maxHeartbeats 1000000 in
/-- O2 probability of the closeness event. -/
theorem prob_close (m b : ℕ) (hm : 1 ≤ m) (hb : 1 ≤ b) :
    (1 / 2 : ENNReal) ≤ gaussianInput (ctr m b) (fun _ => 0) (σ' m b) {p | close m b (θ0 m b) p} := by
  haveI := gi_prob (ctr m b) (fun _ => 0) (σ' m b)
  set μ := gaussianInput (ctr m b) (fun _ => 0) (σ' m b) with hμ
  set θ := θ0 m b with hθdef
  have hθ : 0 < θ := by rw [hθdef]; unfold θ0; positivity
  set s : ℝ := (σ' m b) ^ 2 / θ ^ 2 with hs
  have hBm : ∀ c : ℝ, MeasurableSet {x : ℝ | θ ≤ |x - c|} := fun c =>
    measurableSet_le measurable_const (by fun_prop)
  set A : Fin (m * (b + 1)) × Fin (m * b) → Set ((Fin (m * (b + 1)) → Point (m * b)) × (Fin (m * (b + 1)) → ℝ)) :=
    fun iq => {p | p.1 iq.1 iq.2 ∈ {x : ℝ | θ ≤ |x - ctr m b iq.1 iq.2|}} with hA
  set Bs : Fin (m * (b + 1)) → Set ((Fin (m * (b + 1)) → Point (m * b)) × (Fin (m * (b + 1)) → ℝ)) :=
    fun i => {p | p.2 i ∈ {x : ℝ | θ ≤ |x - 0|}} with hBs
  have hAle : ∀ iq, μ.real (A iq) ≤ s := by
    intro iq
    rw [measureReal_def, hμ, hA]
    simp only
    rw [marg1 _ _ _ _ _ _ (hBm _), ← measureReal_def]
    exact gauss_tail _ _ _ hθ
  have hBle : ∀ i, μ.real (Bs i) ≤ s := by
    intro i
    rw [measureReal_def, hμ, hBs]
    simp only
    rw [marg2 _ _ _ _ _ (hBm _), ← measureReal_def]
    exact gauss_tail _ _ _ hθ
  have hsub : {p | close m b θ p}ᶜ ⊆ (⋃ iq, A iq) ∪ ⋃ i, Bs i := by
    intro p hp
    by_contra h
    apply hp
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, hA, hBs, Set.mem_ofPred_eq,
      not_le, sub_zero] at h
    exact ⟨fun i q => (h.1 (i, q)).le, fun i => (h.2 i).le⟩
  have hc1 : μ.real {p | close m b θ p}ᶜ ≤
      (Fintype.card (Fin (m * (b + 1)) × Fin (m * b)) : ℝ) * s + (Fintype.card (Fin (m * (b + 1))) : ℝ) * s := by
    calc μ.real {p | close m b θ p}ᶜ ≤ μ.real ((⋃ iq, A iq) ∪ ⋃ i, Bs i) := measureReal_mono hsub
      _ ≤ μ.real (⋃ iq, A iq) + μ.real (⋃ i, Bs i) := measureReal_union_le _ _
      _ ≤ (∑ iq, μ.real (A iq)) + ∑ i, μ.real (Bs i) :=
          add_le_add (measureReal_iUnion_fintype_le _) (measureReal_iUnion_fintype_le _)
      _ ≤ (∑ _iq : Fin (m * (b + 1)) × Fin (m * b), s) + ∑ _i : Fin (m * (b + 1)), s :=
          add_le_add (Finset.sum_le_sum fun iq _ => hAle iq) (Finset.sum_le_sum fun i _ => hBle i)
      _ = _ := by simp
  have hcard : (Fintype.card (Fin (m * (b + 1)) × Fin (m * b)) : ℝ) * s +
      (Fintype.card (Fin (m * (b + 1))) : ℝ) * s ≤ 1 / 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have hN : (0 : ℝ) < ((m * b : ℕ) : ℝ) + 1 := by positivity
    have hsv : s = 1 / (16 * (((m * b : ℕ) : ℝ) + 1) ^ 2) := by
      rw [hs]; unfold σ'; rw [← hθdef]; field_simp; ring
    have hn : ((m * (b + 1) : ℕ) : ℝ) ≤ 2 * ((m * b : ℕ) : ℝ) := by
      have : m * (b + 1) ≤ 2 * (m * b) := by nlinarith
      exact_mod_cast this
    rw [hsv]
    push_cast [Nat.cast_mul] at hN hn ⊢
    have hmb0 : (0 : ℝ) ≤ (m : ℝ) * (b : ℝ) := by positivity
    have key : (m : ℝ) * ((b : ℝ) + 1) * ((m : ℝ) * (b : ℝ)) * (1 / (16 * ((m : ℝ) * (b : ℝ) + 1) ^ 2)) +
        (m : ℝ) * ((b : ℝ) + 1) * (1 / (16 * ((m : ℝ) * (b : ℝ) + 1) ^ 2)) =
        (m : ℝ) * ((b : ℝ) + 1) / (16 * ((m : ℝ) * (b : ℝ) + 1)) := by
      field_simp
    rw [key, div_le_iff₀ (by positivity)]
    nlinarith
  have hmeas := measurableSet_close m b θ
  have hcl : μ.real {p | close m b θ p} = 1 - μ.real {p | close m b θ p}ᶜ := by
    rw [measureReal_compl hmeas, probReal_univ]; ring
  have hge : (1 / 2 : ℝ) ≤ μ.real {p | close m b θ p} := by rw [hcl]; linarith
  rw [← ofReal_measureReal (measure_ne_top μ _)]
  have : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos]; simp
  rw [this]
  exact ENNReal.ofReal_le_ofReal hge

/-! ## O1 sub-lemmas (geometry of the perturbed free sum) -/

/-- O1a near-identity bound: if `ψ l (v i)` is within `ε` of the identity matrix, coefficients are
controlled by the functionals. -/
theorem near_id {ι E : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup E] [Module ℝ E] (v : ι → E)
    (ψ : ι → E →ₗ[ℝ] ℝ) (ε : ℝ) (hε : (Fintype.card ι : ℝ) * ε ≤ 1 / 2)
    (hψ : ∀ l i, |ψ l (v i) - if l = i then 1 else 0| ≤ ε) (c : ι → ℝ) (K : ℝ)
    (hK : ∀ l, |ψ l (∑ i, c i • v i)| ≤ K) (l : ι) : |c l| ≤ 2 * K := by
  haveI : Nonempty ι := ⟨l⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => |c i|)
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hψ l l)
  have hgen : ∀ l', |c l'| ≤ K + |c i0| / 2 := by
    intro l'
    have hexp : c l' = ψ l' (∑ i, c i • v i) -
        ∑ i, c i * (ψ l' (v i) - if l' = i then 1 else 0) := by
      simp only [map_sum, map_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    rw [hexp]
    have h1 : |∑ i, c i * (ψ l' (v i) - if l' = i then 1 else 0)| ≤
        (Fintype.card ι : ℝ) * ε * |c i0| := by
      calc _ ≤ ∑ i, |c i * (ψ l' (v i) - if l' = i then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : ι, |c i0| * ε := Finset.sum_le_sum fun i _ => by
              rw [abs_mul]; exact mul_le_mul (hi0 i) (hψ l' i) (abs_nonneg _) (abs_nonneg _)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    have h2 : (Fintype.card ι : ℝ) * ε * |c i0| ≤ |c i0| / 2 := by nlinarith [abs_nonneg (c i0)]
    calc _ ≤ |ψ l' (∑ i, c i • v i)| + |∑ i, c i * (ψ l' (v i) - if l' = i then 1 else 0)| :=
          abs_sub _ _
      _ ≤ K + |c i0| / 2 := by linarith [hK l']
  have h3 := hgen i0
  have h4 : |c i0| ≤ 2 * K := by linarith
  linarith [hi0 l]


theorem θ0_le (m b : ℕ) : 0 < θ0 m b ∧ (((m * b : ℕ) : ℝ) + 1) * θ0 m b ≤ 1 / 1000 := by
  have hN : (1 : ℝ) ≤ ((m * b : ℕ) : ℝ) + 1 := by have : (0 : ℝ) ≤ ((m * b : ℕ) : ℝ) := by positivity
                                                  linarith
  refine ⟨by unfold θ0; positivity, ?_⟩
  unfold θ0
  rw [show (((m * b : ℕ) : ℝ) + 1) * (1 / (1000 * (((m * b : ℕ) : ℝ) + 1) ^ 8)) =
    1 / (1000 * (((m * b : ℕ) : ℝ) + 1) ^ 7) by field_simp]
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (1 : ℝ) ≤ (((m * b : ℕ) : ℝ) + 1) ^ 7 := one_le_pow₀ hN
  linarith

/-! ## dual functionals for the good sets -/

/-- coordinate functional `x ↦ x_(k,j)` (zero for `j = b`). -/
noncomputable def cfL (m b : ℕ) (k : Fin m) (j : Fin (b + 1)) : Point (m * b) →ₗ[ℝ] ℝ where
  toFun x := if h : (j : ℕ) < b then x (finProdFinEquiv (k, ⟨j, h⟩)) else 0
  map_add' x y := by split_ifs <;> simp
  map_smul' c x := by split_ifs <;> simp

theorem cfL_apply (m b : ℕ) (k : Fin m) (j : Fin (b + 1)) (x : Point (m * b)) :
    cfL m b k j x = if h : (j : ℕ) < b then x (finProdFinEquiv (k, ⟨j, h⟩)) else 0 := rfl

/-- the dual functional attached to the good index `l`. -/
noncomputable def psi (m b : ℕ) (f : Fin m → Fin (b + 1)) (l : Fin (m * (b + 1))) :
    Point (m * b) →ₗ[ℝ] ℝ :=
  cfL m b (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2 -
    cfL m b (finProdFinEquiv.symm l).1 (f (finProdFinEquiv.symm l).1)

theorem cfL_abs (m b : ℕ) (k : Fin m) (j : Fin (b + 1)) (x : Point (m * b)) (M : ℝ) (hM0 : 0 ≤ M)
    (hx : ∀ q, |x q| ≤ M) : |cfL m b k j x| ≤ M := by
  rw [cfL_apply]
  split_ifs
  · exact hx _
  · simpa using hM0

theorem psi_abs (m b : ℕ) (f : Fin m → Fin (b + 1)) (l : Fin (m * (b + 1))) (x : Point (m * b))
    (M : ℝ) (hM0 : 0 ≤ M) (hx : ∀ q, |x q| ≤ M) : |psi m b f l x| ≤ 2 * M := by
  have h1 := cfL_abs m b (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2 x M hM0 hx
  have h2 := cfL_abs m b (finProdFinEquiv.symm l).1 (f (finProdFinEquiv.symm l).1) x M hM0 hx
  simp only [psi, LinearMap.sub_apply]
  calc _ ≤ |cfL m b (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2 x| +
        |cfL m b (finProdFinEquiv.symm l).1 (f (finProdFinEquiv.symm l).1) x| := abs_sub _ _
    _ ≤ 2 * M := by linarith

theorem psi_ctr (m b : ℕ) (f : Fin m → Fin (b + 1)) (l i : Fin (m * (b + 1)))
    (hl : l ∈ goodSet m b f) (hi : i ∈ goodSet m b f) :
    psi m b f l (ctr m b i) = if l = i then 1 else 0 := by
  obtain ⟨⟨k, j⟩, rfl⟩ := finProdFinEquiv.surjective l
  obtain ⟨⟨k', j'⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [mem_goodSet] at hl hi
  have hl' : (j : ℕ) ≠ (f k : ℕ) := fun h => hl (Fin.ext h)
  have hi' : (j' : ℕ) ≠ (f k' : ℕ) := fun h => hi (Fin.ext h)
  have hj := j.isLt
  have hj' := j'.isLt
  have hfk := (f k).isLt
  simp only [psi, LinearMap.sub_apply, Equiv.symm_apply_apply, cfL_apply, ctr_apply,
    finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
  by_cases hk : k = k'
  · subst hk
    simp only [true_and, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · have hk' : k' ≠ k := Ne.symm hk
    simp [hk]

theorem psi_near (m b : ℕ) (a : Fin (m * (b + 1)) → Point (m * b)) (y : Fin (m * (b + 1)) → ℝ)
    (θ : ℝ) (hc : close m b θ (a, y)) (f : Fin m → Fin (b + 1)) (l i : Fin (m * (b + 1)))
    (hl : l ∈ goodSet m b f) (hi : i ∈ goodSet m b f) :
    |psi m b f l (a i) - (if l = i then 1 else 0)| ≤ 2 * θ := by
  rw [← psi_ctr m b f l i hl hi, ← map_sub]
  have hθ : 0 ≤ θ := le_trans (abs_nonneg _) (hc.2 i)
  exact psi_abs m b f l _ θ hθ (fun q => by simpa using hc.1 i q)

theorem psi_near' (m b : ℕ) (a : Fin (m * (b + 1)) → Point (m * b)) (y : Fin (m * (b + 1)) → ℝ)
    (θ : ℝ) (hc : close m b θ (a, y)) (f : Fin m → Fin (b + 1)) (l i : goodSet m b f) :
    |psi m b f l.1 (a i.1) - (if l = i then 1 else 0)| ≤ 2 * θ := by
  have h := psi_near m b a y θ hc f l.1 i.1 l.2 i.2
  by_cases hli : l = i
  · subst hli; simpa using h
  · have : l.1 ≠ i.1 := fun h' => hli (Subtype.ext h')
    simpa [hli, this] using h

theorem card_good_eps (m b : ℕ) (f : Fin m → Fin (b + 1)) :
    (Fintype.card (goodSet m b f) : ℝ) * (2 * θ0 m b) ≤ 1 / 2 := by
  rw [Fintype.card_coe, goodSet_card]
  obtain ⟨h0, h1⟩ := θ0_le m b
  nlinarith

theorem cfL_sum_ctr (m b : ℕ) (k k0 : Fin m) (j0 : Fin (b + 1)) :
    ∑ j : Fin (b + 1), cfL m b k0 j0 (ctr m b (finProdFinEquiv (k, j))) = 0 := by
  simp only [cfL_apply]
  split_ifs with h
  · simp only [ctr_apply]
    by_cases hk : k0 = k
    · simp only [hk, if_true]
      rw [Fin.sum_univ_castSucc]
      have hc : ∀ i : Fin b, (if ((Fin.castSucc i : Fin (b + 1)) : ℕ) = (j0 : ℕ) then (1 : ℝ)
          else if ((Fin.castSucc i : Fin (b + 1)) : ℕ) = b then -1 else 0) =
          if i = ⟨j0, h⟩ then 1 else 0 := by
        intro i
        have := i.isLt
        simp only [Fin.val_castSucc, Fin.ext_iff]
        split_ifs <;> first | (exfalso; omega) | norm_num
      rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true, Fin.val_last]
      have : b ≠ (j0 : ℕ) := by omega
      simp [this]
    · simp [hk]
  · simp

theorem psi_sum_ctr (m b : ℕ) (f : Fin m → Fin (b + 1)) (l : Fin (m * (b + 1))) (k : Fin m) :
    ∑ j : Fin (b + 1), psi m b f l (ctr m b (finProdFinEquiv (k, j))) = 0 := by
  simp only [psi, LinearMap.sub_apply, Finset.sum_sub_distrib, cfL_sum_ctr, sub_self]

set_option maxHeartbeats 1000000 in
/-- O1b the smallest singular value of a good set is bounded below on the closeness event. -/
theorem sMin_good (m b : ℕ) (hm : 1 ≤ m) (hb : 1 ≤ b)
    (a : Fin (m * (b + 1)) → Point (m * b)) (y : Fin (m * (b + 1)) → ℝ)
    (hc : close m b (θ0 m b) (a, y)) (f : Fin m → Fin (b + 1)) :
    1 / (4 * ((m * b : ℕ) : ℝ)) ≤ sMin a (goodSet m b f) := by
  have hd : 0 < m * b := Nat.mul_pos hm hb
  have hcard : Fintype.card (goodSet m b f) = m * b := by rw [Fintype.card_coe, goodSet_card]
  have hne : (goodSet m b f).Nonempty := by
    rw [← Finset.card_pos, goodSet_card]; exact hd
  obtain ⟨i0, hi0⟩ := hne
  apply le_csInf
  · exact ⟨_, EuclideanSpace.single (⟨i0, hi0⟩ : goodSet m b f) (1 : ℝ), by simp, rfl⟩
  · rintro r ⟨u, hu, rfl⟩
    have hK : ∀ l : goodSet m b f, |psi m b f l.1 (∑ i : goodSet m b f, u i • a i.1)| ≤
        2 * ‖∑ i : goodSet m b f, u i • a i.1‖ := fun l =>
      psi_abs m b f l.1 _ _ (norm_nonneg _) (fun q => by
        have := PiLp.norm_apply_le (∑ i : goodSet m b f, u i • a i.1) q
        simpa [Real.norm_eq_abs] using this)
    have hu' : ∀ l : goodSet m b f, |u l| ≤ 2 * (2 * ‖∑ i : goodSet m b f, u i • a i.1‖) := fun l =>
      near_id (fun i : goodSet m b f => a i.1) (fun l => psi m b f l.1) (2 * θ0 m b)
        (card_good_eps m b f) (psi_near' m b a y _ hc f) (fun i => u i) _ hK l
    set X := ‖∑ i : goodSet m b f, u i • a i.1‖ with hX
    have hX0 : 0 ≤ X := norm_nonneg _
    have hsq : (1 : ℝ) ≤ ((m * b : ℕ) : ℝ) * (4 * X) ^ 2 := by
      have h1 : ‖u‖ ^ 2 = 1 := by rw [hu]; norm_num
      rw [EuclideanSpace.norm_sq_eq] at h1
      rw [← h1]
      calc ∑ i, ‖u i‖ ^ 2 ≤ ∑ _i : goodSet m b f, (4 * X) ^ 2 := by
            apply Finset.sum_le_sum; intro i _
            rw [Real.norm_eq_abs]
            have := hu' i
            exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    have hd1 : (1 : ℝ) ≤ ((m * b : ℕ) : ℝ) := by exact_mod_cast hd
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- a functional equal to one on `S` and below one on `T` exposes `conv S` in `conv (S ∪ T)`. -/
theorem exposed_of_functional {d : ℕ} (S T : Set (Point d)) (φ : Point d →L[ℝ] ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty) (hS1 : ∀ x ∈ S, φ x = 1) (hT1 : ∀ x ∈ T, φ x < 1) :
    IsExposed ℝ (convexHull ℝ (S ∪ T)) (convexHull ℝ S) := by
  have hlin : IsLinearMap ℝ (φ : Point d → ℝ) := φ.toLinearMap.isLinear
  have hSle : convexHull ℝ S ⊆ {x | φ x = 1} := by
    intro x hx
    have h1 := convexHull_min (fun z hz => (show φ z ≤ 1 from (hS1 z hz).le))
      (convex_halfSpace_le hlin 1) hx
    have h2 := convexHull_min (fun z hz => (show 1 ≤ φ z from (hS1 z hz).ge))
      (convex_halfSpace_ge hlin 1) hx
    exact le_antisymm h1 h2
  have hTlt : convexHull ℝ T ⊆ {x | φ x < 1} := convexHull_min hT1 (convex_halfSpace_lt hlin 1)
  have hAle : convexHull ℝ (S ∪ T) ⊆ {x | φ x ≤ 1} := convexHull_min (by
      rintro z (hz | hz)
      exacts [(hS1 z hz).le, (hT1 z hz).le]) (convex_halfSpace_le hlin 1)
  intro _
  refine ⟨φ, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    refine ⟨convexHull_mono Set.subset_union_left hx, fun z hz => ?_⟩
    have := hSle hx
    simp only [Set.mem_setOf_eq] at this
    rw [this]; exact hAle hz
  · rintro x ⟨hx, hmax⟩
    have ⟨s0, hs0⟩ := hS
    have hge : 1 ≤ φ x := by
      have := hmax s0 (subset_convexHull ℝ _ (Or.inl hs0)); rwa [hS1 s0 hs0] at this
    rw [convexHull_union hS hT, mem_convexJoin] at hx
    obtain ⟨p, hp, r, hr, α, β, hα, hβ, hαβ, rfl⟩ := hx
    have hp1 := hSle hp
    have hr1 := hTlt hr
    simp only [Set.mem_setOf_eq] at hp1 hr1
    simp only [map_add, map_smul, smul_eq_mul, hp1] at hge
    have hβ0 : β = 0 := by nlinarith
    subst hβ0
    have : α = 1 := by linarith
    subst this
    simpa using hp

set_option maxHeartbeats 1000000 in
/-- O1c the facet lemma: on the closeness event, with well-balanced right-hand sides,
every good set is an exposed simplicial facet. -/
theorem facet_core (m b : ℕ) (hm : 1 ≤ m) (hb : 1 ≤ b)
    (a : Fin (m * (b + 1)) → Point (m * b)) (y : Fin (m * (b + 1)) → ℝ)
    (hc : close m b (θ0 m b) (a, y)) (y' : Fin (m * (b + 1)) → ℝ) (Ylo Yhi : ℝ) (hlo : 0 < Ylo)
    (hy : ∀ i, Ylo ≤ y' i ∧ y' i ≤ Yhi)
    (hr : 4 * ((m * b : ℕ) : ℝ) * ((b : ℝ) + 1) * θ0 m b * Yhi < Ylo) (f : Fin m → Fin (b + 1)) :
    goodSet m b f ∈ optSimp a y' 0 := by
  classical
  have hd : 0 < m * b := Nat.mul_pos hm hb
  have hθ := (θ0_le m b).1
  have hcardG : Fintype.card (goodSet m b f) = m * b := by rw [Fintype.card_coe, goodSet_card]
  have hε := card_good_eps m b f
  have hnear := psi_near' m b a y _ hc f
  have hli : LinearIndependent ℝ (fun i : goodSet m b f => a i.1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have h := near_id (fun i : goodSet m b f => a i.1) (fun l => psi m b f l.1) _ hε hnear g 0
      (fun l => by simp only [hg, map_zero, abs_zero, le_refl]) l
    have : |g l| ≤ 0 := by linarith
    exact abs_nonpos_iff.mp this
  have hcardF : Fintype.card (goodSet m b f) = Module.finrank ℝ (Point (m * b)) := by
    rw [hcardG, finrank_euclideanSpace_fin]
  set B := basisOfLinearIndependentOfCardEqFinrank' _ hli hcardF with hBdef
  have hB : ∀ i, B i = a i.1 := fun i => by simp [B, basisOfLinearIndependentOfCardEqFinrank']
  set φ : Point (m * b) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (∑ l : goodSet m b f, y' l.1 • B.coord l) with hφdef
  have hφ : ∀ x, φ x = ∑ l : goodSet m b f, y' l.1 * B.repr x l := by
    intro x; simp [φ]
  have hφG : ∀ i (hi : i ∈ goodSet m b f), φ (a i) = y' i := by
    intro i hi
    rw [hφ, ← hB ⟨i, hi⟩, B.repr_self]
    simp [Finsupp.single_apply]
  have hyp : ∀ i, 0 < y' i := fun i => lt_of_lt_of_le hlo (hy i).1
  have hφoff : ∀ j, j ∉ goodSet m b f → φ (a j) < y' j := by
    intro j hj
    obtain ⟨⟨k, jj⟩, rfl⟩ := finProdFinEquiv.surjective j
    rw [mem_goodSet, not_not] at hj
    subst hj
    set e := ∑ j'' : Fin (b + 1), a (finProdFinEquiv (k, j'')) with he
    have hKe : ∀ l : goodSet m b f, |psi m b f l.1 e| ≤ ((b : ℝ) + 1) * (2 * θ0 m b) := by
      intro l
      have h0 := psi_sum_ctr m b f l.1 k
      have hpe : psi m b f l.1 e = ∑ jj, psi m b f l.1
          (a (finProdFinEquiv (k, jj)) - ctr m b (finProdFinEquiv (k, jj))) := by
        simp only [he, map_sum, map_sub, Finset.sum_sub_distrib, h0, sub_zero]
      rw [hpe]
      calc _ ≤ ∑ jj : Fin (b + 1), |psi m b f l.1
            (a (finProdFinEquiv (k, jj)) - ctr m b (finProdFinEquiv (k, jj)))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _jj : Fin (b + 1), 2 * θ0 m b := Finset.sum_le_sum fun jj _ =>
            psi_abs m b f l.1 _ _ hθ.le (fun q => by simpa using hc.1 _ q)
        _ = _ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
    have hsum : ∑ l : goodSet m b f, B.repr e l • a l.1 = e := by
      conv_rhs => rw [← B.sum_repr e]
      simp only [hB]
    have hcoef : ∀ l, |B.repr e l| ≤ 2 * (((b : ℝ) + 1) * (2 * θ0 m b)) := fun l =>
      near_id (fun i : goodSet m b f => a i.1) (fun l => psi m b f l.1) _ hε hnear
        (fun l => B.repr e l) _ (fun l => by rw [hsum]; exact hKe l) l
    have hφe : φ e < Ylo := by
      rw [hφ]
      calc _ ≤ |∑ l : goodSet m b f, y' l.1 * B.repr e l| := le_abs_self _
        _ ≤ ∑ l : goodSet m b f, |y' l.1 * B.repr e l| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _l : goodSet m b f, Yhi * (2 * (((b : ℝ) + 1) * (2 * θ0 m b))) :=
            Finset.sum_le_sum fun l _ => by
              rw [abs_mul, abs_of_pos (hyp _)]
              exact mul_le_mul (hy _).2 (hcoef l) (abs_nonneg _) (le_trans (hyp l.1).le (hy l.1).2)
        _ = 4 * ((m * b : ℕ) : ℝ) * ((b : ℝ) + 1) * θ0 m b * Yhi := by
            rw [Finset.sum_const, Finset.card_univ, hcardG, nsmul_eq_mul]; ring
        _ < Ylo := hr
    have hsplit : φ e = φ (a (finProdFinEquiv (k, f k))) +
        ∑ jj ∈ Finset.univ.erase (f k), y' (finProdFinEquiv (k, jj)) := by
      rw [he, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (f k))]
      congr 1
      apply Finset.sum_congr rfl
      intro jj hjj
      exact hφG _ ((mem_goodSet m b f k jj).mpr (Finset.ne_of_mem_erase hjj))
    have hlow : Ylo ≤ ∑ jj ∈ Finset.univ.erase (f k), y' (finProdFinEquiv (k, jj)) := by
      have h1 := Finset.card_nsmul_le_sum (Finset.univ.erase (f k))
        (fun jj => y' (finProdFinEquiv (k, jj))) Ylo (fun jj _ => (hy _).1)
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at h1
      have hb1 : (1 : ℝ) ≤ ((b + 1 - 1 : ℕ) : ℝ) := by
        rw [Nat.add_sub_cancel]; exact_mod_cast hb
      nlinarith
    have := hyp (finProdFinEquiv (k, f k))
    linarith
  set sc : Fin (m * (b + 1)) → Point (m * b) := fun i => (y' i)⁻¹ • a i with hsc
  have hS1 : ∀ x ∈ sc '' (goodSet m b f : Set (Fin (m * (b + 1)))), φ x = 1 := by
    rintro _ ⟨i, hi, rfl⟩
    simp only [hsc, map_smul, smul_eq_mul, hφG i hi]
    exact inv_mul_cancel₀ (hyp i).ne'
  have hT1 : ∀ x ∈ ({0} ∪ sc '' (goodSet m b f : Set (Fin (m * (b + 1))))ᶜ), φ x < 1 := by
    rintro x (h0 | ⟨j, hj, rfl⟩)
    · rw [Set.mem_singleton_iff] at h0; rw [h0, map_zero]; norm_num
    · simp only [hsc, map_smul, smul_eq_mul]
      have := hφoff j hj
      rw [inv_mul_lt_iff₀ (hyp j)]; linarith
  have hSne : (sc '' (goodSet m b f : Set (Fin (m * (b + 1))))).Nonempty := by
    obtain ⟨i0, hi0⟩ : (goodSet m b f).Nonempty := by
      rw [← Finset.card_pos, goodSet_card]; exact hd
    exact ⟨_, i0, hi0, rfl⟩
  have hunion : ({0} ∪ Set.range sc : Set (Point (m * b))) =
      sc '' (goodSet m b f : Set (Fin (m * (b + 1)))) ∪
        ({0} ∪ sc '' (goodSet m b f : Set (Fin (m * (b + 1))))ᶜ) := by
    rw [← Set.image_univ, ← Set.union_compl_self (goodSet m b f : Set (Fin (m * (b + 1)))),
      Set.image_union, Set.union_left_comm]
  have hexp := exposed_of_functional _ _ φ hSne ⟨0, Or.inl rfl⟩ hS1 hT1
  rw [← hunion] at hexp
  have hlin : IsLinearMap ℝ (φ : Point (m * b) → ℝ) := φ.toLinearMap.isLinear
  have hne : convexHull ℝ (sc '' (goodSet m b f : Set (Fin (m * (b + 1))))) ≠
      convexHull ℝ ({0} ∪ Set.range sc) := by
    intro heq
    have h0 : (0 : Point (m * b)) ∈ convexHull ℝ (sc '' (goodSet m b f : Set (Fin (m * (b + 1))))) := by
      rw [heq]; exact subset_convexHull ℝ _ (Or.inl rfl)
    have := convexHull_min (fun z hz => (show 1 ≤ φ z from (hS1 z hz).ge))
      (convex_halfSpace_ge hlin 1) h0
    have h1 : (1 : ℝ) ≤ φ 0 := this
    rw [map_zero] at h1
    norm_num at h1
  unfold optSimp
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  exact ⟨goodSet_card m b f, hli, hexp, hSne.mono (subset_convexHull ℝ _), hne,
    ⟨0, fun _ => le_refl _, fun _ _ => rfl, by simp⟩⟩


theorem fold_spec {n d : ℕ} (a : Fin n → Point d) (L : List (DSet n d)) (b0 : Finset (Fin n))
    (hb0 : b0.card = d) :
    (L.foldl (fun best J => if best.card = d ∧ sMin a J.1 ≤ sMin a best then best else J.1) b0).card = d ∧
    sMin a b0 ≤ sMin a (L.foldl (fun best J =>
      if best.card = d ∧ sMin a J.1 ≤ sMin a best then best else J.1) b0) ∧
    ∀ J ∈ L, sMin a J.1 ≤ sMin a (L.foldl (fun best J =>
      if best.card = d ∧ sMin a J.1 ≤ sMin a best then best else J.1) b0) := by
  induction L generalizing b0 with
  | nil => exact ⟨hb0, le_refl _, fun J hJ => absurd hJ (List.not_mem_nil)⟩
  | cons J L ih =>
    rw [List.foldl_cons]
    set b1 := (if b0.card = d ∧ sMin a J.1 ≤ sMin a b0 then b0 else J.1) with hb1
    have hb1c : b1.card = d ∧ sMin a b0 ≤ sMin a b1 ∧ sMin a J.1 ≤ sMin a b1 := by
      rw [hb1]
      split_ifs with h
      · exact ⟨hb0, le_refl _, h.2⟩
      · have : ¬ sMin a J.1 ≤ sMin a b0 := fun h' => h ⟨hb0, h'⟩
        exact ⟨J.2, le_of_lt (lt_of_not_ge this), le_refl _⟩
    obtain ⟨h1, h2, h3⟩ := ih b1 hb1c.1
    refine ⟨h1, le_trans hb1c.2.1 h2, fun J' hJ' => ?_⟩
    rcases List.mem_cons.mp hJ' with rfl | hJ'
    · exact le_trans hb1c.2.2 h2
    · exact h3 J' hJ'

/-- O1d argmax property of `bestSample`. -/
theorem bestSample_spec {n d : ℕ} (a : Fin n → Point d) (draw : Fin (sampleCount n d) → DSet n d)
    (hd : 1 ≤ d) (t : Fin (sampleCount n d)) :
    (bestSample a draw).card = d ∧ sMin a (draw t).1 ≤ sMin a (bestSample a draw) := by
  unfold bestSample
  have hmem : draw t ∈ List.ofFn draw := List.mem_ofFn.mpr ⟨t, rfl⟩
  obtain ⟨J, L, hL⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  rw [hL] at hmem ⊢
  rw [List.foldl_cons]
  have h0 : ¬ ((∅ : Finset (Fin n)).card = d ∧ sMin a J.1 ≤ sMin a ∅) := by
    rintro ⟨h, -⟩; simp at h; omega
  rw [if_neg h0]
  obtain ⟨h1, h2, h3⟩ := fold_spec a L J.1 J.2
  refine ⟨h1, ?_⟩
  rcases List.mem_cons.mp hmem with h | h
  · rw [h]; exact h2
  · exact h3 _ h

/-- O1e power-of-two scale bounds. -/
theorem scaleK_bounds {n d : ℕ} (a : Fin n → Point d) (I : Finset (Fin n)) (h : 0 < sMin a I) :
    sMin a I / 2 < scaleK a I ∧ scaleK a I ≤ sMin a I := by
  unfold scaleK
  set s := sMin a I with hs
  set L := Real.logb 2 s with hL
  have hpow : (2 : ℝ) ^ L = s := Real.rpow_logb (by norm_num) (by norm_num) h
  have hk : (2 : ℝ) ^ (Int.floor L) = (2 : ℝ) ^ ((Int.floor L : ℝ)) := (Real.rpow_intCast 2 _).symm
  rw [hk]
  constructor
  · have h1 : (2 : ℝ) ^ L < (2 : ℝ) ^ ((Int.floor L : ℝ) + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (Int.lt_floor_add_one L)
    rw [Real.rpow_add_one (by norm_num), hpow] at h1
    linarith
  · calc (2 : ℝ) ^ ((Int.floor L : ℝ)) ≤ (2 : ℝ) ^ L :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.floor_le L)
      _ = s := hpow

theorem scaleM_bounds {n d : ℕ} (a : Fin n → Point d) (y : Fin n → ℝ) (h : 0 < maxDataNorm a y) :
    4 * maxDataNorm a y ≤ scaleM a y ∧ scaleM a y ≤ 8 * maxDataNorm a y := by
  unfold scaleM
  set s := maxDataNorm a y with hs
  set L := Real.logb 2 s with hL
  have hpow : (2 : ℝ) ^ L = s := Real.rpow_logb (by norm_num) (by norm_num) h
  have hk : (2 : ℝ) ^ (Int.ceil L + 2) = (2 : ℝ) ^ ((Int.ceil L : ℝ) + 2) := by
    rw [← Real.rpow_intCast]; push_cast; rfl
  rw [hk]
  have e1 : (2 : ℝ) ^ (L + 2) = 4 * s := by
    rw [Real.rpow_add (by norm_num), hpow]; norm_num; ring
  have e2 : (2 : ℝ) ^ (L + 3) = 8 * s := by
    rw [Real.rpow_add (by norm_num), hpow]; norm_num; ring
  constructor
  · rw [← e1]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [Int.le_ceil L])
  · rw [← e2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [Int.ceil_lt_add_one L])

/-- O1f `sMin` is at most the norm of any selected column. -/
theorem sMin_le_norm {n d : ℕ} (a : Fin n → Point d) (I : Finset (Fin n)) (i : Fin n) (hi : i ∈ I) :
    sMin a I ≤ ‖a i‖ := by
  classical
  unfold sMin
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨u, -, rfl⟩
    exact norm_nonneg _
  · refine ⟨EuclideanSpace.single (⟨i, hi⟩ : I) 1, by simp, ?_⟩
    simp [EuclideanSpace.single_apply, ite_smul]

theorem dev_norm (m b : ℕ) (a : Fin (m * (b + 1)) → Point (m * b)) (y : Fin (m * (b + 1)) → ℝ)
    (hc : close m b (θ0 m b) (a, y)) (i : Fin (m * (b + 1))) : ‖a i - ctr m b i‖ ≤ 1 := by
  obtain ⟨hθ, hθd⟩ := θ0_le m b
  have hd0 : (0 : ℝ) ≤ ((m * b : ℕ) : ℝ) := by positivity
  have hθ1 : θ0 m b ≤ 1 := by nlinarith
  have hdθ : ((m * b : ℕ) : ℝ) * θ0 m b ≤ 1 := by nlinarith
  have hsq : ‖a i - ctr m b i‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ q, ‖(a i - ctr m b i) q‖ ^ 2 ≤ ∑ _q : Fin (m * b), θ0 m b ^ 2 := by
          apply Finset.sum_le_sum; intro q _
          rw [Real.norm_eq_abs, sq_abs]
          have h := hc.1 i q
          have : (a i - ctr m b i) q = a i q - ctr m b i q := rfl
          rw [this]
          have h0 := abs_nonneg (a i q - ctr m b i q)
          rw [← sq_abs]; nlinarith
      _ = ((m * b : ℕ) : ℝ) * θ0 m b ^ 2 := by simp
      _ ≤ 1 := by nlinarith
  nlinarith [norm_nonneg (a i - ctr m b i)]

/-- O1g data norm on the closeness event. -/
theorem mdn_close (m b : ℕ) (hm : 1 ≤ m) (hb : 1 ≤ b)
    (a : Fin (m * (b + 1)) → Point (m * b)) (y : Fin (m * (b + 1)) → ℝ)
    (hc : close m b (θ0 m b) (a, y)) :
    (∀ i, ‖a i‖ ≤ maxDataNorm a y) ∧ maxDataNorm a y ≤ ((m * b : ℕ) : ℝ) + 2 := by
  unfold maxDataNorm
  have hbdd : BddAbove (Set.range fun i : Fin (m * (b + 1)) => Real.sqrt (y i ^ 2 + ‖a i‖ ^ 2)) :=
    (Set.finite_range _).bddAbove
  obtain ⟨hθ, hθd⟩ := θ0_le m b
  have hd0 : (0 : ℝ) ≤ ((m * b : ℕ) : ℝ) := by positivity
  refine ⟨fun i => ?_, ?_⟩
  · refine le_trans ?_ (le_csSup hbdd ⟨i, rfl⟩)
    have := Real.sqrt_le_sqrt (show ‖a i‖ ^ 2 ≤ y i ^ 2 + ‖a i‖ ^ 2 by nlinarith [sq_nonneg (y i)])
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  · have hne : Nonempty (Fin (m * (b + 1))) := ⟨⟨0, by positivity⟩⟩
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨i, rfl⟩
    have hy : |y i| ≤ 1 := le_trans (hc.2 i) (by nlinarith)
    have ha : ‖a i‖ ≤ ((m * b : ℕ) : ℝ) + 1 := by
      have h1 := norm_ctr_le m b i
      have h2 := dev_norm m b a y hc i
      have h3 : ‖a i‖ ≤ ‖a i - ctr m b i‖ + ‖ctr m b i‖ := by
        have := norm_add_le (a i - ctr m b i) (ctr m b i)
        simpa using this
      linarith
    rw [Real.sqrt_le_left (by positivity)]
    have h4 : y i ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (y i)]
    have h5 : ‖a i‖ ^ 2 ≤ (((m * b : ℕ) : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
    nlinarith

/-- O1h the final inequality on the scales. -/
theorem hr_arith (X Bb sq M κ θ : ℝ) (hX : 1 ≤ X) (hB : 0 ≤ Bb) (hBX : Bb ≤ X) (hsq0 : 0 ≤ sq)
    (hsq : sq ≤ X) (hM0 : 0 < M) (hM : M ≤ 8 * (X + 2)) (hκ : 1 / (8 * X) < κ)
    (hθ : θ = 1 / (1000 * (X + 1) ^ 8)) :
    4 * X * (Bb + 1) * θ * (sq * M ^ 2 / (4 * κ)) < M := by
  have hκp : 0 < κ := lt_trans (by positivity) hκ
  have hθp : 0 < θ := by rw [hθ]; positivity
  have hX0 : 0 ≤ X := by linarith
  have k1 : X * (Bb + 1) * θ * sq * M ≤ X * (X + 1) * θ * X * (8 * (X + 2)) := by
    have a1 : X * (Bb + 1) ≤ X * (X + 1) := by nlinarith
    have a2 : X * (Bb + 1) * θ ≤ X * (X + 1) * θ := by nlinarith
    have a3 : X * (Bb + 1) * θ * sq ≤ X * (X + 1) * θ * X := by
      apply mul_le_mul a2 hsq hsq0 (by positivity)
    exact mul_le_mul a3 hM hM0.le (by positivity)
  have k2 : X * (X + 1) * θ * X * (8 * (X + 2)) < 1 / (8 * X) := by
    rw [hθ]
    have hp : (0 : ℝ) < (X + 1) := by linarith
    rw [show X * (X + 1) * (1 / (1000 * (X + 1) ^ 8)) * X * (8 * (X + 2)) =
      8 * X ^ 2 * (X + 2) / (1000 * (X + 1) ^ 7) by field_simp]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have q1 : X ^ 3 ≤ (X + 1) ^ 3 := pow_le_pow_left₀ hX0 (by linarith) 3
    have q2 : (X + 1) ^ 4 ≥ 1 := one_le_pow₀ (by linarith)
    have q3 : X + 2 ≤ 2 * (X + 1) := by linarith
    have q4 : 8 * X ^ 2 * (X + 2) * (8 * X) ≤ 128 * (X + 1) ^ 3 * (X + 1) := by
      have : 8 * X ^ 2 * (X + 2) * (8 * X) = 64 * X ^ 3 * (X + 2) := by ring
      rw [this]
      have : 64 * X ^ 3 * (X + 2) ≤ 64 * (X + 1) ^ 3 * (2 * (X + 1)) :=
        mul_le_mul (by nlinarith) q3 (by linarith) (by positivity)
      linarith
    have q5 : 128 * (X + 1) ^ 3 * (X + 1) < 1 * (1000 * (X + 1) ^ 7) := by
      have : (X + 1) ^ 7 = (X + 1) ^ 4 * (X + 1) ^ 3 := by ring
      rw [this]
      have : (X + 1) ^ 3 * (X + 1) ≤ (X + 1) ^ 4 * (X + 1) ^ 3 := by nlinarith [pow_pos hp 3]
      nlinarith [pow_pos hp 3, pow_pos hp 4]
    linarith
  have key : X * (Bb + 1) * θ * sq * M < κ := by linarith
  rw [show 4 * X * (Bb + 1) * θ * (sq * M ^ 2 / (4 * κ)) = (X * (Bb + 1) * θ * sq * M) * M / κ by
    field_simp]
  rw [div_lt_iff₀ hκp]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- O1 geometry: on the closeness event, with a good draw, the first-phase shadow has `(b+1)^m` elements. -/
theorem firstPhase_lb (m b : ℕ) (hm : 1 ≤ m) (hb : 1 ≤ b)
    (a : Fin (m * (b + 1)) → Point (m * b)) (y : Fin (m * (b + 1)) → ℝ)
    (hc : close m b (θ0 m b) (a, y))
    (draw : Fin (sampleCount (m * (b + 1)) (m * b)) → DSet (m * (b + 1)) (m * b))
    (hg : goodDraw m b draw) (z : Point (m * b)) (w : Fin (m * (b + 1)) → ℝ) :
    ((b + 1) ^ m : ℕ) ≤ firstPhaseSteps a y z draw w := by
  have hd1 : 1 ≤ m * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨t0, f0, hf0⟩ := hg
  obtain ⟨hIc, hIs⟩ := bestSample_spec a draw hd1 t0
  set I := bestSample a draw with hI
  have hdpos : (0 : ℝ) < ((m * b : ℕ) : ℝ) := by exact_mod_cast hd1
  have hs0 : 1 / (4 * ((m * b : ℕ) : ℝ)) ≤ sMin a I := by
    have := sMin_good m b hm hb a y hc f0
    rw [← hf0] at this
    exact le_trans this hIs
  have hsp : 0 < sMin a I := lt_of_lt_of_le (by positivity) hs0
  obtain ⟨hk1, hk2⟩ := scaleK_bounds a I hsp
  obtain ⟨i0, hi0⟩ : I.Nonempty := Finset.card_pos.mp (by omega)
  have hsn := sMin_le_norm a I i0 hi0
  obtain ⟨hDn, hDu⟩ := mdn_close m b hm hb a y hc
  have hD := hDn i0
  have hDp : 0 < maxDataNorm a y := by linarith
  obtain ⟨hM1, hM2⟩ := scaleM_bounds a y hDp
  set κ := scaleK a I with hκ
  set M := scaleM a y with hM
  set X : ℝ := ((m * b : ℕ) : ℝ) with hX
  have hX1 : (1 : ℝ) ≤ X := by rw [hX]; exact_mod_cast hd1
  have hsq1 : (1 : ℝ) ≤ Real.sqrt X := Real.one_le_sqrt.mpr hX1
  have hsqX : Real.sqrt X ≤ X := by
    have h1 := Real.sqrt_le_sqrt (show X ≤ X ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h1
  have hκp : 0 < κ := by linarith
  have hMp : 0 < M := by linarith
  set Yhi : ℝ := Real.sqrt X * M ^ 2 / (4 * κ) with hYhi
  have hMY : M ≤ Yhi := by
    rw [hYhi, le_div_iff₀ (by positivity)]
    have h4 : 4 * κ ≤ M := by linarith
    have h5 : M ≤ Real.sqrt X * M := by nlinarith
    nlinarith
  have hy : ∀ i, M ≤ relaxedRhs (d := m * b) I κ M i ∧ relaxedRhs (d := m * b) I κ M i ≤ Yhi := by
    intro i
    unfold relaxedRhs
    split_ifs
    · exact ⟨le_refl _, hMY⟩
    · exact ⟨hMY, le_refl _⟩
  have hBX : (b : ℝ) ≤ X := by
    rw [hX]; push_cast
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have : (0 : ℝ) ≤ (b : ℝ) := by positivity
    nlinarith
  have hr : 4 * X * ((b : ℝ) + 1) * θ0 m b * Yhi < M := by
    refine hr_arith X (b : ℝ) (Real.sqrt X) M κ (θ0 m b) hX1 (by positivity) hBX (Real.sqrt_nonneg _)
      hsqX hMp (by linarith) ?_ (by unfold θ0; rfl)
    have : 1 / (8 * X) = (1 / (4 * X)) / 2 := by field_simp; ring
    rw [this]; linarith
  have hmem : ∀ f : Fin m → Fin (b + 1), goodSet m b f ∈
      shadow a (relaxedRhs (d := m * b) I κ M)
        (∑ i ∈ I, (sampledCoefficients (d := m * b) I w i) • a i) z := by
    intro f
    classical
    unfold shadow
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard_univ.mpr (goodSet_card m b f), 0,
      Submodule.zero_mem _, ?_⟩
    exact facet_core m b hm hb a y hc _ M Yhi hMp hy hr f
  have hsub : Finset.univ.image (goodSet m b) ⊆
      shadow a (relaxedRhs (d := m * b) I κ M)
        (∑ i ∈ I, (sampledCoefficients (d := m * b) I w i) • a i) z := by
    intro J hJ
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hJ
    exact hmem f
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (goodSet_inj m b), Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin] at hcard
  exact hcard

theorem cb_nonneg {n d : ℕ} (a : Fin n → Point d) (y : Fin n → ℝ) (z : Point d) :
    0 ≤ complexityBound a y z := by
  unfold complexityBound
  exact MeasureTheory.integral_nonneg (fun p => by positivity)

/-- inner bound: on the closeness event the algorithm average is at least `(b+1)^m / 2`. -/
theorem cb_lb (m b : ℕ) (hm : 1 ≤ m) (hb : 1 ≤ b) (z : Point (m * b))
    (hdraw : (1 / 2 : ENNReal) ≤ sampleLaw (m * (b + 1)) (m * b) {draw | goodDraw m b draw})
    (a : (Fin (m * (b + 1)) → Point (m * b)) × (Fin (m * (b + 1)) → ℝ))
    (hc : close m b (θ0 m b) a)
    (hint : Integrable (fun p =>
          ((firstPhaseSteps a.1 a.2 z p.1 p.2 : ℝ) +
            (secondPhaseSteps a.1 a.2 z p.1 : ℝ) + 2)) (algorithmLaw (m * (b + 1)) (m * b))) :
    ((b + 1 : ℝ) ^ m) / 2 ≤ complexityBound a.1 a.2 z := by
  haveI := alg_prob (m * (b + 1)) (m * b) (Nat.mul_le_mul_left m (Nat.le_succ b))
  haveI := ProbabilityTheory.isProbabilityMeasure_expMeasure (r := (1 : ℝ)) one_pos
  unfold complexityBound
  set G := {draw | goodDraw m b draw} ×ˢ (Set.univ : Set (Fin (m * (b + 1)) → ℝ)) with hGdef
  have hG : MeasurableSet G := (Set.toFinite _).measurableSet.prod MeasurableSet.univ
  have hGm : (algorithmLaw (m * (b + 1)) (m * b)) G =
      sampleLaw (m * (b + 1)) (m * b) {draw | goodDraw m b draw} := by
    unfold algorithmLaw
    rw [hGdef, Measure.prod_prod, measure_univ, mul_one]
  have hGr : (1 / 2 : ℝ) ≤ (algorithmLaw (m * (b + 1)) (m * b)).real G := by
    rw [measureReal_def, hGm]
    have hne : sampleLaw (m * (b + 1)) (m * b) {draw | goodDraw m b draw} ≠ ⊤ := by
      rw [← hGm]; exact measure_ne_top _ _
    have := ENNReal.toReal_mono hne hdraw
    simpa using this
  have hlow : ∀ p ∈ G, ((b + 1 : ℝ) ^ m) ≤
      ((firstPhaseSteps a.1 a.2 z p.1 p.2 : ℝ) + (secondPhaseSteps a.1 a.2 z p.1 : ℝ) + 2) := by
    intro p hp
    have h1 := firstPhase_lb m b hm hb a.1 a.2 hc p.1 hp.1 z p.2
    have h2 : ((b + 1 : ℝ) ^ m) ≤ (firstPhaseSteps a.1 a.2 z p.1 p.2 : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr h1
      push_cast at this; exact this
    have : (0 : ℝ) ≤ (secondPhaseSteps a.1 a.2 z p.1 : ℝ) := by positivity
    linarith
  have hset := setIntegral_ge_of_const_le_real hG (measure_ne_top _ _) hlow hint.integrableOn
  have hall := setIntegral_le_integral (s := G) hint (Filter.Eventually.of_forall (fun p => by
    show (0 : ℝ) ≤ _; positivity))
  have hpos : (0 : ℝ) ≤ (b + 1 : ℝ) ^ m := by positivity
  have : ((b + 1 : ℝ) ^ m) / 2 ≤ ((b + 1 : ℝ) ^ m) * (algorithmLaw (m * (b + 1)) (m * b)).real G := by
    nlinarith
  linarith

/-- O7 integral lower bound: assembly of O1-O3 with the integrability hypotheses of the target. -/
theorem integral_lb (m b : ℕ) (hm : 1 ≤ m) (hb : 1 ≤ b) (z : Point (m * b))
    (hdraw : (1 / 2 : ENNReal) ≤ sampleLaw (m * (b + 1)) (m * b) {draw | goodDraw m b draw})
    (hin : ∀ a : (Fin (m * (b + 1)) → Point (m * b)) × (Fin (m * (b + 1)) → ℝ),
        Integrable (fun p =>
          ((firstPhaseSteps a.1 a.2 z p.1 p.2 : ℝ) +
            (secondPhaseSteps a.1 a.2 z p.1 : ℝ) + 2)) (algorithmLaw (m * (b + 1)) (m * b)))
    (hout : Integrable (fun a => complexityBound a.1 a.2 z)
        (gaussianInput (ctr m b) (fun _ => 0) (σ' m b))) :
    ((b + 1 : ℝ) ^ m) / 4 ≤
      ∫ a, complexityBound a.1 a.2 z ∂(gaussianInput (ctr m b) (fun _ => 0) (σ' m b)) := by
  haveI := gi_prob (ctr m b) (fun _ => 0) (σ' m b)
  set μ := gaussianInput (ctr m b) (fun _ => 0) (σ' m b) with hμ
  have hC := measurableSet_close m b (θ0 m b)
  have hCr : (1 / 2 : ℝ) ≤ μ.real {p | close m b (θ0 m b) p} := by
    rw [measureReal_def]
    have := ENNReal.toReal_mono (measure_ne_top μ _) (prob_close m b hm hb)
    simpa using this
  have hlow : ∀ a ∈ {p | close m b (θ0 m b) p}, ((b + 1 : ℝ) ^ m) / 2 ≤ complexityBound a.1 a.2 z :=
    fun a ha => cb_lb m b hm hb z hdraw a ha (hin a)
  have hset := setIntegral_ge_of_const_le_real hC (measure_ne_top _ _) hlow hout.integrableOn
  have hall := setIntegral_le_integral (s := {p | close m b (θ0 m b) p}) hout (Filter.Eventually.of_forall (fun a => cb_nonneg a.1 a.2 z))
  have hpos : (0 : ℝ) ≤ (b + 1 : ℝ) ^ m := by positivity
  have : ((b + 1 : ℝ) ^ m) / 4 ≤ ((b + 1 : ℝ) ^ m) / 2 * μ.real {p | close m b (θ0 m b) p} := by
    nlinarith
  linarith

theorem one_div_min_le (u v : ℝ) (hu : 0 < u) (hv : 0 < v) : 1 / min u v ≤ 1 / u + 1 / v := by
  have h1 : 0 < 1 / u := one_div_pos.mpr hu
  have h2 : 0 < 1 / v := one_div_pos.mpr hv
  rcases le_total u v with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

theorem σ'_eq (m b : ℕ) : σ' m b = 1 / (4000 * (((m * b : ℕ) : ℝ) + 1) ^ 9) := by
  unfold σ' θ0
  have : (0 : ℝ) < ((m * b : ℕ) : ℝ) + 1 := by positivity
  field_simp
  ring

/-- O8 final arithmetic: `(b+1)^m / 4` beats the polynomial for suitable `m` and all large `b`. -/
theorem beats_poly (C : ℝ) (D : ℕ) (σ₀ : ℝ) (hσ₀ : 0 < σ₀) : ∃ m : ℕ, 1 ≤ m ∧ ∀ B : ℕ, ∃ b : ℕ, B ≤ b ∧ 1 ≤ b ∧
    3 ≤ m * b ∧
    C * (1 + |((m * b : ℕ) : ℝ)| + |((m * (b + 1) : ℕ) : ℝ)| +
      |1 / min ((σ' m b) / maxDataNorm (ctr m b) (fun _ => 0)) σ₀|) ^ D < ((b + 1 : ℝ) ^ m) / 4 := by
  refine ⟨10 * D + 1, by omega, fun B => ?_⟩
  set m := 10 * D + 1 with hm_def
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  set K : ℝ := (4003 + 1 / σ₀) * (m : ℝ) ^ 10 with hK
  obtain ⟨b0, hb0⟩ := exists_nat_gt (4 * |C| * K ^ D)
  set b := max (max B 3) b0 with hb_def
  have hbB : B ≤ b := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb3 : 3 ≤ b := le_trans (le_max_right _ _) (le_max_left _ _)
  have hbb0 : b0 ≤ b := le_max_right _ _
  refine ⟨b, hbB, by omega, le_trans hb3 (Nat.le_mul_of_pos_left b (by omega)), ?_⟩
  obtain ⟨hpos, hle⟩ := mdn_ctr m b (by omega) (by omega)
  set mdn := maxDataNorm (ctr m b) (fun _ => 0) with hmdn
  set x : ℝ := (b : ℝ) + 1 with hx
  have hb3r : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb3
  have hx1 : 1 ≤ x := by linarith
  have hxb0 : 4 * |C| * K ^ D < x := by
    have : (b0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbb0
    linarith
  have hmb : ((m * b : ℕ) : ℝ) = (m : ℝ) * (b : ℝ) := by push_cast; ring
  have hmb1 : ((m * (b + 1) : ℕ) : ℝ) = (m : ℝ) * x := by push_cast; ring
  set Mx : ℝ := (m : ℝ) * x with hMx
  have hMx1 : 1 ≤ Mx := by nlinarith
  have hmbMx : (m : ℝ) * (b : ℝ) ≤ Mx := by rw [hMx, hx]; nlinarith
  have hb0r : (0 : ℝ) ≤ (b : ℝ) := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hmb0 : 0 ≤ (m : ℝ) * (b : ℝ) := by positivity
  have hN : (m : ℝ) * (b : ℝ) + 1 ≤ Mx := by rw [hMx, hx]; nlinarith
  have hσpos : 0 < σ' m b := by rw [σ'_eq]; positivity
  have hq : 0 < σ' m b / mdn := div_pos hσpos hpos
  have hinv : 1 / (σ' m b / mdn) = mdn * (4000 * ((m : ℝ) * (b : ℝ) + 1) ^ 9) := by
    rw [σ'_eq, hmb]; field_simp
  have hT : |1 / min (σ' m b / mdn) σ₀| ≤ 4000 * Mx ^ 10 + 1 / σ₀ := by
    have hmin : 0 < min (σ' m b / mdn) σ₀ := lt_min hq hσ₀
    rw [abs_of_pos (one_div_pos.mpr hmin)]
    refine le_trans (one_div_min_le _ _ hq hσ₀) ?_
    rw [hinv]
    have h1 : mdn ≤ Mx := by rw [hmb] at hle; linarith
    have h2 : ((m : ℝ) * (b : ℝ) + 1) ^ 9 ≤ Mx ^ 9 := pow_le_pow_left₀ (by positivity) hN 9
    have h3 : mdn * (4000 * ((m : ℝ) * (b : ℝ) + 1) ^ 9) ≤ Mx * (4000 * Mx ^ 9) :=
      mul_le_mul h1 (by linarith) (by positivity) (by linarith)
    have : Mx * (4000 * Mx ^ 9) = 4000 * Mx ^ 10 := by ring
    linarith
  set S : ℝ := 1 + |((m * b : ℕ) : ℝ)| + |((m * (b + 1) : ℕ) : ℝ)| +
      |1 / min (σ' m b / mdn) σ₀| with hS
  have hS0 : 0 ≤ S := by positivity
  have hMx10 : Mx ≤ Mx ^ 10 := le_self_pow₀ hMx1 (by norm_num)
  have hMx10' : 1 ≤ Mx ^ 10 := one_le_pow₀ hMx1
  have hSK : S ≤ K * x ^ 10 := by
    have e1 : |((m * b : ℕ) : ℝ)| = (m : ℝ) * (b : ℝ) := by rw [hmb]; exact abs_of_nonneg hmb0
    have e2 : |((m * (b + 1) : ℕ) : ℝ)| = Mx := by rw [hmb1]; exact abs_of_nonneg (by linarith)
    have e3 : K * x ^ 10 = (4003 + 1 / σ₀) * Mx ^ 10 := by rw [hK, hMx]; ring
    rw [hS, e1, e2, e3]
    have hσinv : 0 < 1 / σ₀ := one_div_pos.mpr hσ₀
    nlinarith
  have hK0 : 0 ≤ K := by positivity
  have hpow : S ^ D ≤ K ^ D * x ^ (10 * D) := by
    calc S ^ D ≤ (K * x ^ 10) ^ D := pow_le_pow_left₀ hS0 hSK D
      _ = K ^ D * x ^ (10 * D) := by rw [mul_pow, ← pow_mul]
  have hxD : 0 < x ^ (10 * D) := by positivity
  have hCS : C * S ^ D ≤ |C| * (K ^ D * x ^ (10 * D)) := by
    calc C * S ^ D ≤ |C| * S ^ D := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (K ^ D * x ^ (10 * D)) := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
  have hfin : x ^ m / 4 = x ^ (10 * D) * (x / 4) := by
    rw [hm_def, pow_succ]; ring
  have h4 : |C| * K ^ D < x / 4 := by linarith
  have h5 : |C| * K ^ D * x ^ (10 * D) < x / 4 * x ^ (10 * D) := mul_lt_mul_of_pos_right h4 hxD
  have h6 : |C| * (K ^ D * x ^ (10 * D)) = |C| * K ^ D * x ^ (10 * D) := by ring
  have h7 : x ^ (10 * D) * (x / 4) = x / 4 * x ^ (10 * D) := by ring
  show C * S ^ D < x ^ m / 4
  rw [hfin, h7]
  rw [h6] at hCS
  exact lt_of_le_of_lt hCS h5

end B1B2

open SmoothedSimplex.TwoPhase in
theorem solution : ¬ (∃ P : MvPolynomial (Fin 3) ℝ, ∃ σ₀ : ℝ, 0 < σ₀ ∧
    ∀ (n d : ℕ), 3 ≤ d → d < n →
    ∀ (c : Fin n → Point d) (b : Fin n → ℝ) (z : Point d)
      (σ : ℝ), 0 < σ → 0 < maxDataNorm c b →
      (∀ a : (Fin n → Point d) × (Fin n → ℝ),
        MeasureTheory.Integrable (fun p =>
          ((firstPhaseSteps a.1 a.2 z p.1 p.2 : ℝ) +
            (secondPhaseSteps a.1 a.2 z p.1 : ℝ) + 2)) (algorithmLaw n d)) ∧
      MeasureTheory.Integrable (fun a => complexityBound a.1 a.2 z)
        (gaussianInput c b (σ * maxDataNorm c b)) ∧
      (∫ a, complexityBound a.1 a.2 z
        ∂(gaussianInput c b (σ * maxDataNorm c b))) ≤
        min (MvPolynomial.eval ![(d : ℝ), (n : ℝ), 1 / min σ σ₀] P)
          ((Nat.choose n d : ℝ) + Nat.choose n (d + 1) + 2)) := by
  rintro ⟨P, σ₀, hσ₀, hP⟩
  obtain ⟨C, D, hC0, hC⟩ := B1B2.eval_bound P
  obtain ⟨m, hm, hmB⟩ := B1B2.beats_poly C D σ₀ hσ₀
  obtain ⟨B, hB⟩ := B1B2.prob_goodDraw m hm
  obtain ⟨b, hBb, hb, hd3, hlt⟩ := hmB B
  obtain ⟨hpos, -⟩ := B1B2.mdn_ctr m b hm hb
  have hσ'pos : 0 < B1B2.σ' m b := by
    unfold B1B2.σ' B1B2.θ0; positivity
  have hdn : m * b < m * (b + 1) := by
    have : m * (b + 1) = m * b + m := by ring
    omega
  have hσ : 0 < B1B2.σ' m b / maxDataNorm (B1B2.ctr m b) (fun _ => 0) := div_pos hσ'pos hpos
  obtain ⟨hin, hout, hle⟩ := hP (m * (b + 1)) (m * b) hd3 hdn (B1B2.ctr m b) (fun _ => 0) 0
    (B1B2.σ' m b / maxDataNorm (B1B2.ctr m b) (fun _ => 0)) hσ hpos
  have hmul : B1B2.σ' m b / maxDataNorm (B1B2.ctr m b) (fun _ => 0) *
      maxDataNorm (B1B2.ctr m b) (fun _ => 0) = B1B2.σ' m b := by
    field_simp
  rw [hmul] at hout hle
  have hlb := B1B2.integral_lb m b hm hb 0 (hB b hBb) hin hout
  have h1 := le_trans hlb (le_trans hle (min_le_left _ _))
  have h2 := le_trans h1 (le_abs_self _)
  have h3 := hC ![((m * b : ℕ) : ℝ), ((m * (b + 1) : ℕ) : ℝ),
    1 / min (B1B2.σ' m b / maxDataNorm (B1B2.ctr m b) (fun _ => 0)) σ₀]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h3
  linarith
