-- Prove2me | solution 1 for UnderstandingML.agnostic_lower_bound_log
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T19:28:51.020983+00:00
-- url     : https://prove2.me/submissions/d2550895-dcdf-41dd-a40a-d4f311844208

import Definitions.Def_UnderstandingML_FundamentalProof
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory Finset

namespace UnderstandingML.LBAux

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {d : ℕ}

/-- The label probabilities of `D_b`: `(1+ρ)/2` for the label `β`, `(1-ρ)/2` for `¬β`. -/
noncomputable def qlab (ρ : ℝ) (β y : Bool) : ℝ := if y = β then (1 + ρ) / 2 else (1 - ρ) / 2

/-- The weight of the atom `(C i, y)` under `D_b`. -/
noncomputable def wt (ρ : ℝ) (b : Fin d → Bool) (p : Fin d × Bool) : ℝ :=
  qlab ρ (b p.1) p.2 / d

/-- `D_b` as a measure on the index set `Fin d × Bool`. -/
noncomputable def nu (ρ : ℝ) (b : Fin d → Bool) : Measure (Fin d × Bool) :=
  ∑ p : Fin d × Bool, ENNReal.ofReal (wt ρ b p) • Measure.dirac p

/-- The embedding of the index set into `X × Bool`. -/
def phi (C : Fin d → X) : Fin d × Bool → X × Bool := fun p ↦ (C p.1, p.2)

lemma qlab_nonneg {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ0 : 0 ≤ ρ) (β y : Bool) : 0 ≤ qlab ρ β y := by
  unfold qlab; split_ifs <;> linarith

lemma wt_nonneg {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ0 : 0 ≤ ρ) (b : Fin d → Bool) (p : Fin d × Bool) :
    0 ≤ wt ρ b p := div_nonneg (qlab_nonneg hρ1 hρ0 _ _) (Nat.cast_nonneg _)

lemma flipEta_C (C : Fin d → X) (hC : Function.Injective C) (ρ : ℝ) (b : Fin d → Bool)
    (i : Fin d) : flipEta C ρ b (C i) = qlab ρ (b i) true := by
  unfold flipEta qlab
  by_cases hb : b i = true
  · rw [if_pos ⟨i, rfl, hb⟩]; simp [hb]
  · have h1 : ¬ ∃ j, C i = C j ∧ b j = true := by
      rintro ⟨j, hj, hbj⟩; rw [hC hj] at hb; exact hb hbj
    rw [if_neg h1, if_pos ⟨i, rfl⟩]
    simp at hb; simp [hb]

lemma measurable_flipEta (C : Fin d → X) (ρ : ℝ) (b : Fin d → Bool) :
    Measurable (flipEta C ρ b) := by
  unfold flipEta
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
  · exact ((Set.finite_range C).subset (by rintro x ⟨i, rfl, _⟩; exact ⟨i, rfl⟩)).measurableSet
  · exact ((Set.finite_range C).subset (by rintro x ⟨i, rfl⟩; exact ⟨i, rfl⟩)).measurableSet

lemma bernoulliLaw_apply (p : ℝ) (A : Set Bool) :
    bernoulliLaw p A = ENNReal.ofReal p * A.indicator 1 true +
      ENNReal.ofReal (1 - p) * A.indicator 1 false := by
  simp [bernoulliLaw, Measure.dirac_apply' _ (Set.toFinite A).measurableSet]

lemma measurable_kernel (η : X → ℝ) (hη : Measurable η) :
    Measurable (fun x ↦ (bernoulliLaw (η x)).map (fun y ↦ (x, y))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have : (fun x ↦ ((bernoulliLaw (η x)).map (fun y ↦ (x, y))) s) = fun x ↦
      ENNReal.ofReal (η x) * s.indicator 1 (x, true) +
        ENNReal.ofReal (1 - η x) * s.indicator 1 (x, false) := by
    funext x
    rw [Measure.map_apply measurable_prodMk_left hs, bernoulliLaw_apply]
    simp only [Set.indicator, Pi.one_apply, mul_ite, mul_one, mul_zero]
    rfl
  rw [this]
  have h1 : Measurable (fun x : X ↦ s.indicator (1 : X × Bool → ENNReal) (x, true)) :=
    (measurable_one.indicator hs).comp (measurable_id.prodMk measurable_const)
  have h2 : Measurable (fun x : X ↦ s.indicator (1 : X × Bool → ENNReal) (x, false)) :=
    (measurable_one.indicator hs).comp (measurable_id.prodMk measurable_const)
  exact ((ENNReal.measurable_ofReal.comp hη).mul h1).add
    ((ENNReal.measurable_ofReal.comp (measurable_const.sub hη)).mul h2)

lemma measurable_phi (C : Fin d → X) : Measurable (phi C) := measurable_of_countable _

/-- `D_b` is the image of `nu` under `phi`. -/
lemma lowerBoundLaw_eq (C : Fin d → X) (hC : Function.Injective C) (ρ : ℝ)
    (b : Fin d → Bool) :
    lowerBoundLaw C ρ b = (nu ρ b).map (phi C) := by
  ext s hs
  rw [Measure.map_apply (measurable_phi C) hs]
  unfold lowerBoundLaw condLaw
  rw [Measure.bind_apply hs (measurable_kernel _ (measurable_flipEta C ρ b)).aemeasurable]
  unfold uniformOn nu
  rw [lintegral_smul_measure, lintegral_finset_sum_measure]
  simp only [lintegral_dirac]
  rw [Measure.coe_finset_sum, Finset.sum_apply, Fintype.sum_prod_type, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hd : (0 : ℝ) < d := by exact_mod_cast (Fin.pos i)
  rw [Measure.map_apply measurable_prodMk_left hs, bernoulliLaw_apply, flipEta_C C hC]
  simp only [Measure.smul_apply, smul_eq_mul, Fintype.sum_bool]
  simp only [Measure.dirac_apply' _ ((measurable_phi C) hs)]
  have hw : ∀ y, ENNReal.ofReal (wt ρ b (i, y)) = (d : ENNReal)⁻¹ * ENNReal.ofReal (qlab ρ (b i) y) := by
    intro y
    rw [wt, ENNReal.ofReal_div_of_pos hd, ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]
  rw [hw, hw]
  have hq : 1 - qlab ρ (b i) true = qlab ρ (b i) false := by
    unfold qlab; cases b i <;> simp <;> ring
  rw [hq]
  simp only [Set.indicator, Pi.one_apply, mul_ite, mul_one, mul_zero, mul_add]
  rfl

instance nu_finite (ρ : ℝ) (b : Fin d → Bool) : IsFiniteMeasure (nu ρ b) := ⟨by
  unfold nu
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  exact ENNReal.sum_lt_top.mpr fun p _ ↦ by simp [ENNReal.mul_lt_top]⟩

lemma nu_singleton (ρ : ℝ) (b : Fin d → Bool) (p : Fin d × Bool) :
    nu ρ b {p} = ENNReal.ofReal (wt ρ b p) := by
  unfold nu
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem, Measure.dirac_apply]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp only [Set.indicator, Set.mem_singleton_iff, hq, if_false, mul_zero]
  · simp

/-- The embedding of index sequences into samples. -/
def phiPi (C : Fin d → X) {m : ℕ} : (Fin m → Fin d × Bool) → (Fin m → X × Bool) :=
  fun ω r ↦ phi C (ω r)

lemma phi_injective (C : Fin d → X) (hC : Function.Injective C) : Function.Injective (phi C) := by
  intro p q h
  simp only [phi, Prod.mk.injEq] at h
  exact Prod.ext (hC h.1) h.2

lemma measurableEmbedding_phi (C : Fin d → X) (hC : Function.Injective C) :
    MeasurableEmbedding (phi C) :=
  ⟨phi_injective C hC, measurable_phi C, fun s _ ↦ (s.toFinite.image _).measurableSet⟩

lemma measurableEmbedding_phiPi (C : Fin d → X) (hC : Function.Injective C) (m : ℕ) :
    MeasurableEmbedding (phiPi C (m := m)) := by
  refine ⟨?_, measurable_of_countable _, fun s _ ↦ (s.toFinite.image _).measurableSet⟩
  intro ω ω' h
  funext r
  exact phi_injective C hC (congrFun h r)

lemma iidLaw_eq (C : Fin d → X) (hC : Function.Injective C) (ρ : ℝ) (b : Fin d → Bool)
    (m : ℕ) :
    iidLaw (lowerBoundLaw C ρ b) m = (Measure.pi fun _ : Fin m ↦ nu ρ b).map (phiPi C) := by
  unfold iidLaw
  rw [lowerBoundLaw_eq C hC ρ b]
  exact (Measure.pi_map_pi (f := fun _ ↦ phi C) (fun _ ↦ (measurable_phi C).aemeasurable)).symm

/-- The weight of an index sequence. -/
noncomputable def W (ρ : ℝ) (b : Fin d → Bool) {m : ℕ} (ω : Fin m → Fin d × Bool) : ℝ :=
  ∏ r, wt ρ b (ω r)

lemma W_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (b : Fin d → Bool) {m : ℕ}
    (ω : Fin m → Fin d × Bool) : 0 ≤ W ρ b ω :=
  Finset.prod_nonneg fun r _ ↦ wt_nonneg hρ1 hρ0 b (ω r)

lemma pi_nu_singleton {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (b : Fin d → Bool) {m : ℕ}
    (ω : Fin m → Fin d × Bool) :
    (Measure.pi fun _ : Fin m ↦ nu ρ b) {ω} = ENNReal.ofReal (W ρ b ω) := by
  rw [Measure.pi_singleton, W, ENNReal.ofReal_prod_of_nonneg (fun r _ ↦ wt_nonneg hρ1 hρ0 b _)]
  simp [nu_singleton]

open Classical in
/-- The `D_b^m`-measure of any set of samples, as a finite sum. -/
lemma iidLaw_apply (C : Fin d → X) (hC : Function.Injective C) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (b : Fin d → Bool) (m : ℕ) (E : Set (Fin m → X × Bool)) :
    iidLaw (lowerBoundLaw C ρ b) m E =
      ENNReal.ofReal (∑ ω ∈ univ.filter (fun ω ↦ phiPi C ω ∈ E), W ρ b ω) := by
  rw [iidLaw_eq C hC, (measurableEmbedding_phiPi C hC m).map_apply,
    ENNReal.ofReal_sum_of_nonneg (fun ω _ ↦ W_nonneg hρ0 hρ1 b ω)]
  have : phiPi C ⁻¹' E = ↑(univ.filter (fun ω ↦ phiPi C ω ∈ E)) := by
    ext ω; simp
  rw [this, ← sum_measure_singleton]
  exact Finset.sum_congr rfl fun ω _ ↦ pi_nu_singleton hρ0 hρ1 b ω

/-- Integrals against `D_b^m`, as finite sums. -/
lemma integral_iidLaw (C : Fin d → X) (hC : Function.Injective C) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (b : Fin d → Bool) (m : ℕ) (F : (Fin m → X × Bool) → ℝ) :
    ∫ S, F S ∂(iidLaw (lowerBoundLaw C ρ b) m) = ∑ ω, W ρ b ω * F (phiPi C ω) := by
  rw [iidLaw_eq C hC, (measurableEmbedding_phiPi C hC m).integral_map,
    integral_fintype (Integrable.of_finite)]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [smul_eq_mul, measureReal_def, pi_nu_singleton hρ0 hρ1,
    ENNReal.toReal_ofReal (W_nonneg hρ0 hρ1 b ω)]

/-- The risk under `D_b`, as a finite sum. -/
lemma risk_eq (C : Fin d → X) (hC : Function.Injective C) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (b : Fin d → Bool) (h : X → Bool) :
    risk loss01 (lowerBoundLaw C ρ b) h = ∑ p, wt ρ b p * loss01 h (phi C p) := by
  unfold risk
  rw [lowerBoundLaw_eq C hC, (measurableEmbedding_phi C hC).integral_map,
    integral_fintype (Integrable.of_finite)]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [smul_eq_mul, measureReal_def, nu_singleton,
    ENNReal.toReal_ofReal (wt_nonneg hρ1 hρ0 b p)]

/-- Hellinger / Le Cam: `(∑ √(pq))² ≤ s (2 - s)` where `s = ∑ min(p,q)`. -/
lemma hellinger {Ω : Type*} [Fintype Ω] (p q : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hp1 : ∑ ω, p ω = 1) (hq1 : ∑ ω, q ω = 1) :
    (∑ ω, Real.sqrt (p ω * q ω)) ^ 2 ≤
      (∑ ω, min (p ω) (q ω)) * (2 - ∑ ω, min (p ω) (q ω)) := by
  have hmax : ∑ ω, max (p ω) (q ω) = 2 - ∑ ω, min (p ω) (q ω) := by
    have : ∀ ω, max (p ω) (q ω) = p ω + q ω - min (p ω) (q ω) := by
      intro ω; rcases le_total (p ω) (q ω) with h | h <;> simp [h]
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp1, hq1]; ring
  rw [← hmax]
  have key : ∀ ω, Real.sqrt (p ω * q ω) =
      Real.sqrt (min (p ω) (q ω)) * Real.sqrt (max (p ω) (q ω)) := by
    intro ω
    rw [← Real.sqrt_mul (le_min (hp ω) (hq ω))]
    congr 1
    rcases le_total (p ω) (q ω) with h | h <;> simp [h, mul_comm]
  simp_rw [key]
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (le_of_eq ?_)
  congr 1
  · exact Finset.sum_congr rfl fun ω _ ↦ Real.sq_sqrt (le_min (hp ω) (hq ω))
  · exact Finset.sum_congr rfl fun ω _ ↦ Real.sq_sqrt (le_max_of_le_left (hp ω))

lemma sum_prod_eq_pow {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (m : ℕ) (f : Ω' → ℝ) :
    ∑ ω : Fin m → Ω', ∏ r, f (ω r) = (∑ p, f p) ^ m := by
  rw [show (∑ p, f p) ^ m = ∏ _r : Fin m, ∑ p, f p by simp, Finset.prod_univ_sum]
  simp

end UnderstandingML.LBAux

open UnderstandingML UnderstandingML.LBAux

theorem solution {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (H : Set (X → Bool)) (c : X) (hcT : ∃ h ∈ H, h c = true) (hcF : ∃ h ∈ H, h c = false)
    (ε δ : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / Real.sqrt 2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (A : Learner (X × Bool) (X → Bool)) (m : ℕ)
    (hm : (m : ℝ) ≤ 0.5 * Real.log (1 / (4 * δ)) / ε ^ 2) :
    ∃ b : Fin 1 → Bool, ENNReal.ofReal δ ≤
      iidLaw (lowerBoundLaw (fun _ ↦ c) ε b) m {S | ∃ h ∈ H,
        risk loss01 (lowerBoundLaw (fun _ ↦ c) ε b) h + ε ≤
          risk loss01 (lowerBoundLaw (fun _ ↦ c) ε b) (A m S)} := by
  classical
  set C : Fin 1 → X := fun _ ↦ c with hCdef
  have hC : Function.Injective C := fun i j _ ↦ Subsingleton.elim i j
  have hsqrt2 : 0 < Real.sqrt 2 := by positivity
  have hε2' : ε ^ 2 < 1 / 2 := by
    have h1 : ε * Real.sqrt 2 < 1 := by rwa [lt_div_iff₀ hsqrt2] at hε2
    have h2 : (ε * Real.sqrt 2) ^ 2 < 1 := by nlinarith [mul_pos hε hsqrt2]
    rw [mul_pow, Real.sq_sqrt (by norm_num)] at h2
    linarith
  have hε1 : ε ≤ 1 := by nlinarith
  -- the risk under `D_b`
  have hrisk : ∀ (b : Fin 1 → Bool) (g : X → Bool),
      risk loss01 (lowerBoundLaw C ε b) g = qlab ε (b 0) (!(g c)) := by
    intro b g
    rw [risk_eq C hC hε.le hε1 b g]
    simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool, wt, phi, loss01,
      hCdef, Nat.cast_one, div_one]
    have h0 : (default : Fin 1) = 0 := rfl
    rw [h0]
    cases g c <;> simp
  -- the bad event contains all samples on which `A` errs at `c`
  set E : (Fin 1 → Bool) → Set (Fin m → X × Bool) := fun b ↦ {S | ∃ h ∈ H,
      risk loss01 (lowerBoundLaw C ε b) h + ε ≤ risk loss01 (lowerBoundLaw C ε b) (A m S)}
    with hE
  have hsub : ∀ (b : Fin 1 → Bool) (ω : Fin m → Fin 1 × Bool),
      A m (phiPi C ω) c ≠ b 0 → phiPi C ω ∈ E b := by
    intro b ω hω
    have hω' : A m (phiPi C ω) c = !(b 0) := by
      cases h : b 0 <;> cases h' : A m (phiPi C ω) c <;> simp_all
    obtain ⟨h, hH, hh⟩ : ∃ h ∈ H, h c = b 0 := by
      cases hb : b 0
      · exact hcF
      · exact hcT
    refine ⟨h, hH, ?_⟩
    rw [hrisk, hrisk, hh, hω', Bool.not_not]
    unfold qlab
    cases b 0 <;> simp <;> linarith
  have hmeas : ∀ b : Fin 1 → Bool,
      ENNReal.ofReal (∑ ω ∈ univ.filter (fun ω ↦ A m (phiPi C ω) c ≠ b 0), W ε b ω) ≤
        iidLaw (lowerBoundLaw C ε b) m (E b) := by
    intro b
    rw [iidLaw_apply C hC hε.le hε1 b m]
    apply ENNReal.ofReal_le_ofReal
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact hsub b ω hω
    · intro ω _ _; exact W_nonneg hε.le hε1 b ω
  -- the two hypotheses of the test
  set p : (Fin m → Fin 1 × Bool) → ℝ := W ε (fun _ ↦ true) with hp
  set q : (Fin m → Fin 1 × Bool) → ℝ := W ε (fun _ ↦ false) with hq
  have hp0 : ∀ ω, 0 ≤ p ω := fun ω ↦ W_nonneg hε.le hε1 _ ω
  have hq0 : ∀ ω, 0 ≤ q ω := fun ω ↦ W_nonneg hε.le hε1 _ ω
  have hsum1 : ∀ b : Fin 1 → Bool, ∑ ω : Fin m → Fin 1 × Bool, W ε b ω = 1 := by
    intro b
    unfold W
    rw [sum_prod_eq_pow]
    simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool, wt, Nat.cast_one,
      div_one]
    unfold qlab
    cases b default <;> simp <;> ring_nf <;> simp
  have hBC : ∑ ω, Real.sqrt (p ω * q ω) = (Real.sqrt (1 - ε ^ 2)) ^ m := by
    have hfac : ∀ ω, Real.sqrt (p ω * q ω) =
        ∏ r, Real.sqrt (wt ε (fun _ ↦ true) (ω r) * wt ε (fun _ ↦ false) (ω r)) := by
      intro ω
      rw [hp, hq, W, W, ← Finset.prod_mul_distrib]
      rw [Real.sqrt_eq_iff_mul_self_eq (Finset.prod_nonneg fun r _ ↦
        mul_nonneg (wt_nonneg hε1 hε.le _ _) (wt_nonneg hε1 hε.le _ _))
        (Finset.prod_nonneg fun r _ ↦ Real.sqrt_nonneg _)]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r _ ↦ ?_
      rw [Real.mul_self_sqrt (mul_nonneg (wt_nonneg hε1 hε.le _ _) (wt_nonneg hε1 hε.le _ _))]
    simp_rw [hfac]
    rw [sum_prod_eq_pow m (fun p ↦ Real.sqrt (wt ε (fun _ ↦ true) p * wt ε (fun _ ↦ false) p))]
    congr 1
    simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool, wt, Nat.cast_one,
      div_one, qlab]
    simp only [Bool.true_eq_false, Bool.false_eq_true, if_true, if_false, ↓reduceIte]
    have h4 : Real.sqrt ((1 - ε ^ 2) / 4) = Real.sqrt (1 - ε ^ 2) / 2 := by
      rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4), show (4:ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    try rw [show (1 + ε) / 2 * ((1 - ε) / 2) = (1 - ε ^ 2) / 4 by ring]
    try rw [show (1 - ε) / 2 * ((1 + ε) / 2) = (1 - ε ^ 2) / 4 by ring]
    rw [h4]; ring
  -- lower bound on the overlap
  set s := ∑ ω, min (p ω) (q ω) with hs
  have hhel : (1 - ε ^ 2) ^ m ≤ s * (2 - s) := by
    have := hellinger p q hp0 hq0 (hsum1 _) (hsum1 _)
    rwa [hBC, ← pow_mul, mul_comm m 2, pow_mul, Real.sq_sqrt (by nlinarith)] at this
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun ω _ ↦ le_min (hp0 ω) (hq0 ω)
  have hs1 : s ≤ 1 := by
    rw [← hsum1 (fun _ ↦ true)]
    exact Finset.sum_le_sum fun ω _ ↦ min_le_left _ _
  -- total error of the two hypotheses
  set T : (Fin 1 → Bool) → ℝ := fun b ↦
    ∑ ω ∈ univ.filter (fun ω ↦ A m (phiPi C ω) c ≠ b 0), W ε b ω with hT
  have hTsum : s ≤ T (fun _ ↦ true) + T (fun _ ↦ false) := by
    simp only [hT, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ω _ ↦ ?_
    cases A m (phiPi C ω) c
    · simp only [ne_eq, Bool.false_eq_true, not_false_eq_true, if_true, not_true_eq_false,
        if_false, add_zero]
      exact min_le_left _ _
    · simp only [ne_eq, not_true_eq_false, if_false, Bool.true_eq_false, not_false_eq_true,
        if_true, zero_add]
      exact min_le_right _ _
  have hTle : ∀ b, ENNReal.ofReal (T b) ≤ iidLaw (lowerBoundLaw C ε b) m (E b) := hmeas
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- no samples: the learner's output is fixed
    subst hm0
    let S0 : Fin 0 → X × Bool := Fin.elim0
    refine ⟨fun _ ↦ !(A 0 S0 c), le_trans ?_ (hTle _)⟩
    apply ENNReal.ofReal_le_ofReal
    have hall : univ.filter (fun ω : Fin 0 → Fin 1 × Bool ↦
        A 0 (phiPi C ω) c ≠ (fun _ ↦ !(A 0 S0 c)) (0 : Fin 1)) = univ := by
      apply Finset.filter_true_of_mem
      intro ω _
      have : phiPi C ω = S0 := funext fun r ↦ Fin.elim0 r
      rw [this]; cases A 0 S0 c <;> simp
    simp only [hT]
    rw [hall, hsum1]; linarith
  · -- many samples: the overlap is large
    have hlog : 0 < Real.log (1 / (4 * δ)) := by
      have : (0:ℝ) < m := by exact_mod_cast hmpos
      have h2 : 0 < 0.5 * Real.log (1 / (4 * δ)) / ε ^ 2 := lt_of_lt_of_le this hm
      have := (div_pos_iff_of_pos_right (by positivity : (0:ℝ) < ε ^ 2)).mp h2
      linarith
    have hexp : Real.exp (-(2 * ε ^ 2)) ≤ 1 - ε ^ 2 := by
      have h1 : 1 + 2 * ε ^ 2 ≤ Real.exp (2 * ε ^ 2) := by
        have := Real.add_one_le_exp (2 * ε ^ 2); linarith
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
      nlinarith [sq_nonneg ε]
    have hpow : 4 * δ ≤ (1 - ε ^ 2) ^ m := by
      have h1 : Real.exp (-(2 * ε ^ 2)) ^ m ≤ (1 - ε ^ 2) ^ m :=
        pow_le_pow_left₀ (Real.exp_pos _).le hexp m
      rw [← Real.exp_nat_mul] at h1
      have h2 : Real.log (4 * δ) ≤ m * -(2 * ε ^ 2) := by
        have hm' : (m : ℝ) * ε ^ 2 ≤ 0.5 * Real.log (1 / (4 * δ)) := by
          rwa [le_div_iff₀ (by positivity)] at hm
        rw [one_div, Real.log_inv] at hm'
        nlinarith
      have h3 := Real.exp_le_exp.mpr h2
      rw [Real.exp_log (by positivity)] at h3
      linarith
    have hs2 : 2 * δ ≤ s := by nlinarith
    by_cases htrue : δ ≤ T (fun _ ↦ true)
    · exact ⟨_, le_trans (ENNReal.ofReal_le_ofReal htrue) (hTle _)⟩
    · exact ⟨_, le_trans (ENNReal.ofReal_le_ofReal (by linarith)) (hTle (fun _ ↦ false))⟩
