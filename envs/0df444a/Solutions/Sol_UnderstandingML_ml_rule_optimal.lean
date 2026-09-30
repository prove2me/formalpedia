-- Prove2me | solution 1 for UnderstandingML.ml_rule_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T19:32:24.798764+00:00
-- url     : https://prove2.me/submissions/96cdf406-6c42-4bef-91dc-16fa7509e2d3

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

namespace UnderstandingML.MLAux

open UnderstandingML UnderstandingML.LBAux

variable {d : ℕ}

/-- Flip the `i`-th coordinate of `b`. -/
def flipAt (i : Fin d) (b : Fin d → Bool) : Fin d → Bool := Function.update b i (!b i)

lemma flipAt_self (i : Fin d) (b : Fin d → Bool) : flipAt i b i = !b i := by
  simp [flipAt]

lemma flipAt_ne {i j : Fin d} (h : j ≠ i) (b : Fin d → Bool) : flipAt i b j = b j := by
  simp [flipAt, h]

lemma flipAt_flipAt (i : Fin d) (b : Fin d → Bool) : flipAt i (flipAt i b) = b := by
  funext j
  by_cases h : j = i
  · subst h; simp [flipAt_self]
  · simp [flipAt_ne h]

def flipEquiv (i : Fin d) : (Fin d → Bool) ≃ (Fin d → Bool) :=
  ⟨flipAt i, flipAt i, flipAt_flipAt i, flipAt_flipAt i⟩

open Classical in
/-- Number of sample indices `r` with `ω r = (i, y)`. -/
noncomputable def cnt {m : ℕ} (ω : Fin m → Fin d × Bool) (i : Fin d) (y : Bool) : ℕ :=
  (univ.filter (fun r ↦ ω r = (i, y))).card

lemma pow_swap_le {a c : ℝ} (hc : 0 ≤ c) (hca : c ≤ a) {N1 N2 : ℕ} (h : N2 ≤ N1) :
    c ^ N1 * a ^ N2 ≤ a ^ N1 * c ^ N2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have ha : 0 ≤ a := hc.trans hca
  have h1 : c ^ k ≤ a ^ k := pow_le_pow_left₀ hc hca k
  have h2 : 0 ≤ (a * c) ^ N2 := pow_nonneg (mul_nonneg ha hc) _
  calc c ^ (N2 + k) * a ^ N2 = (a * c) ^ N2 * c ^ k := by ring
    _ ≤ (a * c) ^ N2 * a ^ k := mul_le_mul_of_nonneg_left h1 h2
    _ = a ^ (N2 + k) * c ^ N2 := by ring

open Classical in
lemma W_flip_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (b : Fin d → Bool) (i : Fin d) {m : ℕ}
    (ω : Fin m → Fin d × Bool) (h : cnt ω i (!b i) ≤ cnt ω i (b i)) :
    W ρ (flipAt i b) ω ≤ W ρ b ω := by
  unfold W
  rw [← prod_filter_mul_prod_filter_not univ (fun r ↦ (ω r).1 = i),
    ← prod_filter_mul_prod_filter_not univ (fun r ↦ (ω r).1 = i) (f := fun r ↦ wt ρ b (ω r))]
  have hoff : ∏ r ∈ univ.filter (fun r ↦ ¬ (ω r).1 = i), wt ρ (flipAt i b) (ω r) =
      ∏ r ∈ univ.filter (fun r ↦ ¬ (ω r).1 = i), wt ρ b (ω r) := by
    refine prod_congr rfl fun r hr ↦ ?_
    simp only [mem_filter, mem_univ, true_and] at hr
    simp [wt, flipAt_ne hr]
  rw [hoff]
  refine mul_le_mul_of_nonneg_right ?_ (prod_nonneg fun r _ ↦ wt_nonneg hρ1 hρ0 _ _)
  set a := (1 + ρ) / 2 / d
  set c := (1 - ρ) / 2 / d
  have hb : ∀ r ∈ univ.filter (fun r ↦ (ω r).1 = i), wt ρ b (ω r) =
      if (ω r).2 = b i then a else c := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    simp only [wt, qlab, hr, a, c, ite_div]
  have hf : ∀ r ∈ univ.filter (fun r ↦ (ω r).1 = i), wt ρ (flipAt i b) (ω r) =
      if (ω r).2 = b i then c else a := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    simp only [wt, qlab, hr, flipAt_self, a, c]
    cases b i <;> cases (ω r).2 <;> simp
  rw [prod_congr rfl hb, prod_congr rfl hf, prod_ite, prod_ite, prod_const, prod_const,
    prod_const, prod_const, filter_filter, filter_filter]
  have e1 : (univ.filter (fun r ↦ (ω r).1 = i ∧ (ω r).2 = b i)).card = cnt ω i (b i) := by
    unfold cnt; congr 1; ext r; simp [Prod.ext_iff]
  have e2 : (univ.filter (fun r ↦ (ω r).1 = i ∧ ¬ (ω r).2 = b i)).card = cnt ω i (!b i) := by
    unfold cnt; congr 1; ext r
    simp only [mem_filter, mem_univ, true_and, Prod.ext_iff]
    cases (ω r).2 <;> cases b i <;> simp
  rw [e1, e2]
  have hc : 0 ≤ c := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hca : c ≤ a := div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  exact pow_swap_le hc hca h

lemma F_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (i : Fin d) {m : ℕ}
    (ω : Fin m → Fin d × Bool) (z : Bool) (h : cnt ω i (!z) ≤ cnt ω i z) :
    ∑ b, W ρ b ω * wt ρ b (i, !z) ≤ ∑ b, W ρ b ω * wt ρ b (i, z) := by
  set g : (Fin d → Bool) → ℝ := fun b ↦ W ρ b ω * wt ρ b (i, !z) - W ρ b ω * wt ρ b (i, z)
    with hg
  suffices hs : ∑ b, g b ≤ 0 by
    simp only [hg, sum_sub_distrib] at hs; linarith
  have hperm : ∑ b, g b = ∑ b, g (flipAt i b) :=
    (Equiv.sum_comp (flipEquiv i) g).symm
  have h2 : 2 * ∑ b, g b = ∑ b, (g b + g (flipAt i b)) := by
    rw [sum_add_distrib, ← hperm]; ring
  have hpt : ∀ b, g b + g (flipAt i b) ≤ 0 := by
    intro b
    have hd : (0 : ℝ) ≤ ρ / d := div_nonneg hρ0 (Nat.cast_nonneg _)
    by_cases hbz : b i = z
    · have hW := W_flip_le hρ0 hρ1 b i ω (by rw [hbz]; exact h)
      have e : g b + g (flipAt i b) = ρ / d * (W ρ (flipAt i b) ω - W ρ b ω) := by
        simp only [hg, wt, qlab, flipAt_self, hbz]
        cases z <;> simp <;> ring
      rw [e]; exact mul_nonpos_of_nonneg_of_nonpos hd (by linarith)
    · have hbz' : b i = !z := by cases z <;> simpa using hbz
      have hW := W_flip_le hρ0 hρ1 (flipAt i b) i ω
        (by rw [flipAt_self, hbz']; simpa only [Bool.not_not] using h)
      rw [flipAt_flipAt] at hW
      have e : g b + g (flipAt i b) = ρ / d * (W ρ b ω - W ρ (flipAt i b) ω) := by
        simp only [hg, wt, qlab, flipAt_self, hbz']
        cases z <;> simp <;> ring
      rw [e]; exact mul_nonpos_of_nonneg_of_nonpos hd (by linarith)
  have : 2 * ∑ b, g b ≤ 0 := h2 ▸ sum_nonpos fun b _ ↦ hpt b
  linarith

end UnderstandingML.MLAux

open UnderstandingML UnderstandingML.LBAux UnderstandingML.MLAux

theorem solution {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {d : ℕ}
    (C : Fin d → X) (hC : Function.Injective C) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (m : ℕ)
    (AML A : Learner (X × Bool) (X → Bool)) (hML : IsMajorityRule C AML) :
    ∑ b : Fin d → Bool, ∫ S, risk loss01 (lowerBoundLaw C ρ b) (AML m S)
        ∂(iidLaw (lowerBoundLaw C ρ b) m) ≤
      ∑ b : Fin d → Bool, ∫ S, risk loss01 (lowerBoundLaw C ρ b) (A m S)
        ∂(iidLaw (lowerBoundLaw C ρ b) m) := by
  classical
  have hre : ∀ G : Learner (X × Bool) (X → Bool),
      ∑ b : Fin d → Bool, ∫ S, risk loss01 (lowerBoundLaw C ρ b) (G m S)
        ∂(iidLaw (lowerBoundLaw C ρ b) m) =
      ∑ ω : Fin m → Fin d × Bool, ∑ i, ∑ b,
        W ρ b ω * wt ρ b (i, !(G m (phiPi C ω) (C i))) := by
    intro G
    simp_rw [integral_iidLaw C hC hρ hρ1.le, risk_eq C hC hρ hρ1.le, Fintype.sum_prod_type,
      mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun ω _ ↦ ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun b _ ↦ ?_
    cases hG : G m (phiPi C ω) (C i) <;> simp [loss01, phi, hG]
  rw [hre, hre]
  refine sum_le_sum fun ω _ ↦ sum_le_sum fun i _ ↦ ?_
  have hcnt : ∀ y, (univ.filter (fun r ↦ (phiPi C ω r).1 = C i ∧ (phiPi C ω r).2 = y)).card =
      cnt ω i y := by
    intro y; unfold cnt; congr 1; ext r
    simp [phiPi, phi, hC.eq_iff, Prod.ext_iff]
  have hmaj : cnt ω i (!(AML m (phiPi C ω) (C i))) ≤ cnt ω i (AML m (phiPi C ω) (C i)) := by
    have h1 := hML m (phiPi C ω) i
    rw [hcnt, hcnt] at h1
    by_contra hlt
    push_neg at hlt
    cases hz : AML m (phiPi C ω) (C i) <;> rw [hz] at hlt h1 <;> simp at hlt h1 <;> omega
  have key : ∀ z0 z : Bool, cnt ω i (!z0) ≤ cnt ω i z0 →
      ∑ b, W ρ b ω * wt ρ b (i, !z0) ≤ ∑ b, W ρ b ω * wt ρ b (i, !z) := by
    intro z0 z h
    by_cases hz : z = z0
    · rw [hz]
    · have : z = !z0 := by cases z <;> cases z0 <;> simp_all
      rw [this, Bool.not_not]; exact F_le hρ hρ1.le i ω z0 h
  exact key _ _ hmaj
