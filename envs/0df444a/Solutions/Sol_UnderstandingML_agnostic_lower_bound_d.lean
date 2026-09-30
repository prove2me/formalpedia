-- Prove2me | solution 1 for UnderstandingML.agnostic_lower_bound_d
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T19:37:16.97874+00:00
-- url     : https://prove2.me/submissions/a6149be7-d71c-4bee-84b0-c46c046555ad

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

namespace UnderstandingML.LBDAux

open UnderstandingML UnderstandingML.LBAux UnderstandingML.MLAux

variable {d : ℕ}

lemma sum_wt {ρ : ℝ} (hd : 0 < d) (b : Fin d → Bool) : ∑ p, wt ρ b p = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, wt, qlab]
  have : ∀ j : Fin d, (if true = b j then (1 + ρ) / 2 else (1 - ρ) / 2) / d +
      (if false = b j then (1 + ρ) / 2 else (1 - ρ) / 2) / d = 1 / d := by
    intro j; cases b j <;> simp <;> ring
  simp_rw [this]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma sum_W {ρ : ℝ} (hd : 0 < d) (b : Fin d → Bool) (m : ℕ) :
    ∑ ω : Fin m → Fin d × Bool, W ρ b ω = 1 := by
  unfold W
  rw [sum_prod_eq_pow m (fun p ↦ wt ρ b p), sum_wt hd, one_pow]

lemma sum_sqrt_wt {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hd : 0 < d) (b : Fin d → Bool)
    (i : Fin d) :
    ∑ p, Real.sqrt (wt ρ b p * wt ρ (flipAt i b) p) =
      1 - (1 - Real.sqrt (1 - ρ ^ 2)) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have key : Real.sqrt ((1 + ρ) / 2 / d * ((1 - ρ) / 2 / d)) = Real.sqrt (1 - ρ ^ 2) / (2 * d) := by
    rw [show (1 + ρ) / 2 / d * ((1 - ρ) / 2 / d) = (1 - ρ ^ 2) / (2 * d) ^ 2 by
      field_simp; ring, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  have key' : Real.sqrt ((1 - ρ) / 2 / d * ((1 + ρ) / 2 / d)) =
      Real.sqrt (1 - ρ ^ 2) / (2 * d) := by rw [mul_comm, key]
  have hj : ∀ j, ∑ y, Real.sqrt (wt ρ b (j, y) * wt ρ (flipAt i b) (j, y)) =
      1 / d + if j = i then (Real.sqrt (1 - ρ ^ 2) - 1) / d else 0 := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp only [Fintype.sum_bool, wt, qlab, flipAt_self, if_true]
      cases b j <;> simp [key, key'] <;> field_simp <;> ring
    · simp only [wt, flipAt_ne hji, if_neg hji, add_zero]
      simp_rw [Real.sqrt_mul_self (div_nonneg (qlab_nonneg hρ1 hρ0 _ _) hdR.le)]
      simp only [Fintype.sum_bool, qlab]
      cases b j <;> simp <;> field_simp <;> ring
  rw [Fintype.sum_prod_type]
  simp_rw [hj]
  rw [sum_add_distrib, sum_ite_eq' univ i, if_pos (mem_univ _), sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

lemma BC_ge {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hd : 0 < d) (b : Fin d → Bool)
    (i : Fin d) (m : ℕ) :
    1 - m * ρ ^ 2 / d ≤ ∑ ω : Fin m → Fin d × Bool,
      Real.sqrt (W ρ b ω * W ρ (flipAt i b) ω) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hfac : ∀ ω : Fin m → Fin d × Bool, Real.sqrt (W ρ b ω * W ρ (flipAt i b) ω) =
      ∏ r, Real.sqrt (wt ρ b (ω r) * wt ρ (flipAt i b) (ω r)) := by
    intro ω
    rw [W, W, ← Finset.prod_mul_distrib]
    rw [Real.sqrt_eq_iff_mul_self_eq (Finset.prod_nonneg fun r _ ↦
      mul_nonneg (wt_nonneg hρ1 hρ0 _ _) (wt_nonneg hρ1 hρ0 _ _))
      (Finset.prod_nonneg fun r _ ↦ Real.sqrt_nonneg _)]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ ↦ ?_
    rw [Real.mul_self_sqrt (mul_nonneg (wt_nonneg hρ1 hρ0 _ _) (wt_nonneg hρ1 hρ0 _ _))]
  simp_rw [hfac]
  rw [sum_prod_eq_pow m (fun p ↦ Real.sqrt (wt ρ b p * wt ρ (flipAt i b) p)),
    sum_sqrt_wt hρ0 hρ1 hd b i]
  have hs0 := Real.sqrt_nonneg (1 - ρ ^ 2)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - ρ ^ 2 by nlinarith)
  have hs : 1 - ρ ^ 2 ≤ Real.sqrt (1 - ρ ^ 2) := by nlinarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht : ρ ^ 2 / d ≤ 1 := by rw [div_le_one hdR]; nlinarith
  have hbase : 1 + (-(ρ ^ 2 / d)) ≤ 1 - (1 - Real.sqrt (1 - ρ ^ 2)) / d := by
    have : (1 - Real.sqrt (1 - ρ ^ 2)) / d ≤ ρ ^ 2 / d :=
      div_le_div_of_nonneg_right (by linarith) hdR.le
    linarith
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(ρ ^ 2 / d) by linarith) m
  have hp := pow_le_pow_left₀ (by linarith) hbase m
  have e : 1 - m * ρ ^ 2 / d = 1 + m * (-(ρ ^ 2 / d)) := by ring
  rw [e]; linarith

/-- Pair lemma: the error probabilities at coordinate `i` under `b` and its flip add up to
at least `1/2`. -/
lemma pair_ge {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hd : 0 < d) (b : Fin d → Bool)
    (i : Fin d) (m : ℕ) (hm : 8 * (m * ρ ^ 2) < d) (err : (Fin m → Fin d × Bool) → Bool) :
    1 / 2 ≤ ∑ ω, W ρ b ω * (if err ω ≠ b i then 1 else 0) +
      ∑ ω, W ρ (flipAt i b) ω * (if err ω ≠ flipAt i b i then 1 else 0) := by
  set p := W ρ b (m := m) with hp
  set q := W ρ (flipAt i b) (m := m) with hq
  have hp0 : ∀ ω, 0 ≤ p ω := fun ω ↦ W_nonneg hρ0 hρ1 _ ω
  have hq0 : ∀ ω, 0 ≤ q ω := fun ω ↦ W_nonneg hρ0 hρ1 _ ω
  have hs : ∑ ω, min (p ω) (q ω) ≤ ∑ ω, p ω * (if err ω ≠ b i then 1 else 0) +
      ∑ ω, q ω * (if err ω ≠ flipAt i b i then 1 else 0) := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun ω _ ↦ ?_
    rw [flipAt_self]
    cases err ω <;> cases b i <;> simp
  have hhel := hellinger p q hp0 hq0 (sum_W hd _ _) (sum_W hd _ _)
  have hbc := BC_ge hρ0 hρ1 hd b i m
  have hs0 : 0 ≤ ∑ ω, min (p ω) (q ω) := sum_nonneg fun ω _ ↦ le_min (hp0 ω) (hq0 ω)
  have hs1 : ∑ ω, min (p ω) (q ω) ≤ 1 := by
    rw [← sum_W hd b m]; exact sum_le_sum fun ω _ ↦ min_le_left _ _
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : m * ρ ^ 2 / d < 1 / 8 := by
    rw [div_lt_iff₀ hdpos]; linarith
  have ht0 : 0 ≤ m * ρ ^ 2 / d := by positivity
  have hsq : (1 - m * ρ ^ 2 / d) ^ 2 ≤ (∑ ω, Real.sqrt (p ω * q ω)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hbc 2
  nlinarith

end UnderstandingML.LBDAux

open UnderstandingML UnderstandingML.LBAux UnderstandingML.MLAux UnderstandingML.LBDAux

theorem solution {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (H : Set (X → Bool)) {d : ℕ} (C : Fin d → X) (hC : Function.Injective C)
    (hshat : ∀ g : Fin d → Bool, ∃ h ∈ H, ∀ i, h (C i) = g i) (ε : ℝ) (hε : 0 < ε)
    (hε2 : ε < 1 / (8 * Real.sqrt 2)) (m : ℕ) (hm : (m : ℝ) < d / (512 * ε ^ 2))
    (A : Learner (X × Bool) (X → Bool)) :
    ∃ b : Fin d → Bool, ENNReal.ofReal (1 / 8) ≤
      iidLaw (lowerBoundLaw C (8 * ε) b) m {S | ∃ h ∈ H,
        risk loss01 (lowerBoundLaw C (8 * ε) b) h + ε ≤
          risk loss01 (lowerBoundLaw C (8 * ε) b) (A m S)} := by
  classical
  have hsqrt2 : 0 < Real.sqrt 2 := by positivity
  have hε2' : (8 * ε) ^ 2 < 1 / 2 := by
    have h1 : 8 * ε * Real.sqrt 2 < 1 := by
      rw [lt_div_iff₀ (by positivity)] at hε2; linarith
    have h2 : (8 * ε * Real.sqrt 2) ^ 2 < 1 := by nlinarith [mul_pos hε hsqrt2]
    rw [mul_pow, Real.sq_sqrt (by norm_num)] at h2
    linarith
  set ρ := 8 * ε with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by nlinarith
  have hdR : (0 : ℝ) < d := by
    have : (0 : ℝ) < d / (512 * ε ^ 2) := lt_of_le_of_lt (Nat.cast_nonneg m) hm
    have := (div_pos_iff_of_pos_right (by positivity : (0:ℝ) < 512 * ε ^ 2)).mp this
    exact this
  have hd : 0 < d := by exact_mod_cast hdR
  have hm' : 8 * (m * ρ ^ 2) < d := by
    rw [lt_div_iff₀ (by positivity)] at hm
    rw [hρdef]; nlinarith
  -- the risk under `D_b`
  have hrisk : ∀ (b : Fin d → Bool) (g : X → Bool), risk loss01 (lowerBoundLaw C ρ b) g =
      (1 - ρ) / 2 + ρ / d * ∑ i, (if g (C i) ≠ b i then (1 : ℝ) else 0) := by
    intro b g
    rw [risk_eq C hC hρ0 hρ1, Fintype.sum_prod_type]
    have : ∀ i, ∑ y, wt ρ b (i, y) * loss01 g (phi C (i, y)) =
        ((1 - ρ) / 2 + ρ * (if g (C i) ≠ b i then (1 : ℝ) else 0)) / d := by
      intro i
      simp only [Fintype.sum_bool, wt, qlab, loss01, phi]
      cases b i <;> by_cases hg : g (C i) = true <;> simp [hg] <;> ring
    simp_rw [this]
    rw [← sum_div, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_sum]
    field_simp
  -- number of mistakes on `C`
  set Z : (Fin d → Bool) → (Fin m → Fin d × Bool) → ℝ := fun b ω ↦
    ∑ i, (if A m (phiPi C ω) (C i) ≠ b i then (1 : ℝ) else 0) with hZ
  have hZle : ∀ b ω, Z b ω ≤ d := by
    intro b ω
    calc Z b ω ≤ ∑ _i : Fin d, (1 : ℝ) := sum_le_sum fun i _ ↦ by split_ifs <;> norm_num
      _ = d := by simp
  set E : (Fin d → Bool) → Set (Fin m → X × Bool) := fun b ↦ {S | ∃ h ∈ H,
      risk loss01 (lowerBoundLaw C ρ b) h + ε ≤ risk loss01 (lowerBoundLaw C ρ b) (A m S)}
    with hE
  have hsub : ∀ b ω, (d : ℝ) / 8 ≤ Z b ω → phiPi C ω ∈ E b := by
    intro b ω hZω
    obtain ⟨h, hH, hh⟩ := hshat b
    refine ⟨h, hH, ?_⟩
    rw [hrisk, hrisk]
    have h0 : ∑ i, (if h (C i) ≠ b i then (1 : ℝ) else 0) = 0 := by simp [hh]
    rw [h0]
    have : ρ / d * (d / 8) ≤ ρ / d * Z b ω :=
      mul_le_mul_of_nonneg_left hZω (div_nonneg hρ0 hdR.le)
    have e : ρ / d * (d / 8) = ε := by rw [hρdef]; field_simp
    simp only [hZ] at this
    linarith
  have hmeas : ∀ b : Fin d → Bool,
      ENNReal.ofReal (∑ ω ∈ univ.filter (fun ω ↦ (d : ℝ) / 8 ≤ Z b ω), W ρ b ω) ≤
        iidLaw (lowerBoundLaw C ρ b) m (E b) := by
    intro b
    rw [iidLaw_apply C hC hρ0 hρ1 b m]
    apply ENNReal.ofReal_le_ofReal
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact hsub b ω hω
    · intro ω _ _; exact W_nonneg hρ0 hρ1 b ω
  have hmarkov : ∀ b, ∑ ω, W ρ b ω * Z b ω ≤
      d * ∑ ω ∈ univ.filter (fun ω ↦ (d : ℝ) / 8 ≤ Z b ω), W ρ b ω + d / 8 := by
    intro b
    have e : (d : ℝ) / 8 = ∑ ω : Fin m → Fin d × Bool, W ρ b ω * (d / 8) := by rw [← sum_mul, sum_W hd, one_mul]
    rw [sum_filter, mul_sum, e, ← sum_add_distrib]
    refine sum_le_sum fun ω _ ↦ ?_
    have hW := W_nonneg hρ0 hρ1 b ω
    split_ifs with h
    · nlinarith [hZle b ω]
    · push_neg at h; nlinarith
  have havg : ∀ i, (2 : ℝ) ^ d / 4 ≤
      ∑ b, ∑ ω, W ρ b ω * (if A m (phiPi C ω) (C i) ≠ b i then (1 : ℝ) else 0) := by
    intro i
    set T : (Fin d → Bool) → ℝ := fun b ↦
      ∑ ω, W ρ b ω * (if A m (phiPi C ω) (C i) ≠ b i then (1 : ℝ) else 0) with hT
    have hperm : ∑ b, T b = ∑ b, T (flipAt i b) := (Equiv.sum_comp (flipEquiv i) T).symm
    have h2 : 2 * ∑ b, T b = ∑ b, (T b + T (flipAt i b)) := by
      rw [sum_add_distrib, ← hperm]; ring
    have h3 : ∑ _b : Fin d → Bool, (1 / 2 : ℝ) ≤ ∑ b, (T b + T (flipAt i b)) :=
      sum_le_sum fun b _ ↦ pair_ge hρ0 hρ1 hd b i m hm' (fun ω ↦ A m (phiPi C ω) (C i))
    simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h3
    linarith
  have htot : ∑ _b : Fin d → Bool, (d : ℝ) / 4 ≤ ∑ b, ∑ ω, W ρ b ω * Z b ω := by
    have e : ∑ b, ∑ ω, W ρ b ω * Z b ω = ∑ i, ∑ b, ∑ ω,
        W ρ b ω * (if A m (phiPi C ω) (C i) ≠ b i then (1 : ℝ) else 0) := by
      simp only [hZ, mul_sum]
      exact (sum_congr rfl fun b _ ↦ Finset.sum_comm).trans Finset.sum_comm
    rw [e]
    calc ∑ _b : Fin d → Bool, (d : ℝ) / 4 = ∑ _i : Fin d, (2 : ℝ) ^ d / 4 := by
          simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]; ring
      _ ≤ _ := sum_le_sum fun i _ ↦ havg i
  obtain ⟨b, -, hb⟩ := Finset.exists_le_of_sum_le univ_nonempty htot
  refine ⟨b, le_trans (ENNReal.ofReal_le_ofReal ?_) (hmeas b)⟩
  have := (hmarkov b)
  have h8 : (d : ℝ) * (1 / 8) ≤ d * ∑ ω ∈ univ.filter (fun ω ↦ (d : ℝ) / 8 ≤ Z b ω), W ρ b ω := by
    linarith
  exact le_of_mul_le_mul_left h8 hdR
