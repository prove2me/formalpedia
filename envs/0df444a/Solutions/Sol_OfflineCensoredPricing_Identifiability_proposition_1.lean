-- Prove2me | solution 1 for OfflineCensoredPricing.Identifiability.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:22:22.172987+00:00
-- url     : https://prove2.me/submissions/eba6ff6e-a55e-48a8-8f7b-83a17f3f9fa7

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model

open MeasureTheory Set OfflineCensoredPricing.Identifiability

namespace OCPProp1Aux

/-- pointwise concavity of `q ↦ q · min(ξ − b q, y)` on `q ≥ 0`. -/
lemma pt_concave (b ξ y x z a c : ℝ) (hb : 0 ≤ b) (hx : 0 ≤ x) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hac : a + c = 1) :
    a * (x * min (ξ - b * x) y) + c * (z * min (ξ - b * z) y) ≤
      (a * x + c * z) * min (ξ - b * (a * x + c * z)) y := by
  have h1 : x * min (ξ - b * x) y ≤ x * (ξ - b * x) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hx
  have h2 : x * min (ξ - b * x) y ≤ x * y := mul_le_mul_of_nonneg_left (min_le_right _ _) hx
  have h3 : z * min (ξ - b * z) y ≤ z * (ξ - b * z) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hz
  have h4 : z * min (ξ - b * z) y ≤ z * y := mul_le_mul_of_nonneg_left (min_le_right _ _) hz
  rcases min_cases (ξ - b * (a * x + c * z)) y with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
    have hc' : c = 1 - a := by linarith
    subst hc'
    have key : a * (x * (ξ - b * x)) + (1 - a) * (z * (ξ - b * z)) ≤
        (a * x + (1 - a) * z) * (ξ - b * (a * x + (1 - a) * z)) := by
      have : (a * x + (1 - a) * z) * (ξ - b * (a * x + (1 - a) * z)) -
          (a * (x * (ξ - b * x)) + (1 - a) * (z * (ξ - b * z))) = b * (a * (1 - a)) * (x - z) ^ 2 := by
        ring
      have : 0 ≤ b * (a * (1 - a)) * (x - z) ^ 2 := by positivity
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h3 hc]
  · rw [h]
    nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h4 hc]

section General

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (b y m : ℝ)

/-- `G(q) = E[min(ξ − b q, y)]`. -/
noncomputable def G (q : ℝ) : ℝ := ∫ ξ, min (ξ - b * q) y ∂μ

variable {μ b y m}

lemma integrable_min (hm : ∀ᵐ ξ ∂μ, m ≤ ξ) (q : ℝ) :
    Integrable (fun ξ => min (ξ - b * q) y) μ := by
  refine Integrable.of_bound (by fun_prop) (|y| + |m - b * q|) ?_
  filter_upwards [hm] with ξ hξ
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have : min (m - b * q) y ≤ min (ξ - b * q) y := min_le_min_right _ (by linarith)
    have h1 : -(|y| + |m - b * q|) ≤ min (m - b * q) y := by
      rcases min_cases (m - b * q) y with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
        linarith [neg_abs_le y, neg_abs_le (m - b * q), abs_nonneg y, abs_nonneg (m - b * q)]
    linarith
  · linarith [min_le_right (ξ - b * q) y, le_abs_self y, abs_nonneg (m - b * q)]

lemma G_lip (hb : 0 ≤ b) (hm : ∀ᵐ ξ ∂μ, m ≤ ξ) (q q' : ℝ) :
    |G μ b y q - G μ b y q'| ≤ b * |q - q'| := by
  unfold G
  rw [← integral_sub (integrable_min hm q) (integrable_min hm q')]
  have := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ξ => min (ξ - b * q) y - min (ξ - b * q') y) (C := b * |q - q'|)
    (Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs]
      refine le_trans (abs_min_sub_min_le_max _ _ _ _) ?_
      rw [sub_self, abs_zero]
      refine max_le ?_ (by positivity)
      rw [show ξ - b * q - (ξ - b * q') = b * (q' - q) by ring, abs_mul, abs_of_nonneg hb,
        abs_sub_comm]))
  simpa [probReal_univ] using this

lemma G_cont (hb : 0 ≤ b) (hm : ∀ᵐ ξ ∂μ, m ≤ ξ) : Continuous (G μ b y) := by
  rw [Metric.continuous_iff]
  intro q ε hε
  refine ⟨ε / (b + 1), by positivity, fun q' hq' => ?_⟩
  rw [Real.dist_eq] at hq' ⊢
  have h := G_lip (y := y) hb hm q' q
  have h2 : b * |q' - q| ≤ b * (ε / (b + 1)) := mul_le_mul_of_nonneg_left hq'.le hb
  have h3 : b * (ε / (b + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

lemma R_concave (hb : 0 ≤ b) (hm : ∀ᵐ ξ ∂μ, m ≤ ξ) :
    ConcaveOn ℝ (Ici 0) (fun q => q * G μ b y q) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx z hz a c ha hc hac
  simp only [smul_eq_mul]
  simp only [mem_Ici] at hx hz
  have e1 : a * (x * G μ b y x) = ∫ ξ, a * x * min (ξ - b * x) y ∂μ := by
    unfold G; rw [integral_const_mul]; ring
  have e2 : c * (z * G μ b y z) = ∫ ξ, c * z * min (ξ - b * z) y ∂μ := by
    unfold G; rw [integral_const_mul]; ring
  have e3 : (a * x + c * z) * G μ b y (a * x + c * z) =
      ∫ ξ, (a * x + c * z) * min (ξ - b * (a * x + c * z)) y ∂μ := by
    unfold G; rw [integral_const_mul]
  rw [e1, e2, e3, ← integral_add ((integrable_min hm x).const_mul _)
    ((integrable_min hm z).const_mul _)]
  refine integral_mono (((integrable_min hm x).const_mul _).add
    ((integrable_min hm z).const_mul _)) ((integrable_min hm _).const_mul _) (fun ξ => ?_)
  have := pt_concave b ξ y x z a c hb hx hz ha hc hac
  simp only
  linarith [show a * (x * min (ξ - b * x) y) = a * x * min (ξ - b * x) y by ring,
    show c * (z * min (ξ - b * z) y) = c * z * min (ξ - b * z) y by ring]

lemma R_nonpos (hb : 0 ≤ b) (hy : 0 ≤ y) (hm0 : 0 ≤ m) (hm : ∀ᵐ ξ ∂μ, m ≤ ξ) (q : ℝ)
    (hq : q ≤ 0) : q * G μ b y q ≤ 0 := by
  have : 0 ≤ G μ b y q := by
    unfold G
    refine integral_nonneg_of_ae ?_
    filter_upwards [hm] with ξ hξ
    have := mul_nonpos_of_nonneg_of_nonpos hb hq
    show 0 ≤ min (ξ - b * q) y
    exact le_min (by linarith) hy
  nlinarith

lemma G_tail (hb : 0 < b) (hy : 0 ≤ y) :
    ∃ Q, 0 ≤ Q ∧ ∀ q, Q < q → (hm : ∀ᵐ ξ ∂μ, m ≤ ξ) → G μ b y q < 0 := by
  have ht := ProbabilityTheory.tendsto_cdf_atTop (μ := μ)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (ht.eventually (lt_mem_nhds (by norm_num :
    (1 / 2 : ℝ) < 1)))
  refine ⟨max 0 ((y + T) / b), le_max_left _ _, fun q hq hm => ?_⟩
  have hq' : y + T < b * q := by
    have := lt_of_le_of_lt (le_max_right _ _) hq
    rw [div_lt_iff₀ hb] at this
    linarith [mul_comm q b]
  have hP : 1 / 2 < μ.real (Iic T) := by
    have := hT T le_rfl
    rwa [ProbabilityTheory.cdf_eq_real] at this
  have hbound : ∀ ξ, min (ξ - b * q) y ≤ y + (Iic T).indicator (fun _ => T - b * q - y) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ Iic T
    · rw [indicator_of_mem hξ]
      have : ξ ≤ T := hξ
      linarith [min_le_left (ξ - b * q) y]
    · rw [indicator_of_notMem hξ]
      linarith [min_le_right (ξ - b * q) y]
  have hint : Integrable (fun ξ => y + (Iic T).indicator (fun _ => T - b * q - y) ξ) μ :=
    (integrable_const y).add ((integrable_const _).indicator measurableSet_Iic)
  have h1 := integral_mono (integrable_min hm q) hint hbound
  rw [integral_add (integrable_const y) ((integrable_const _).indicator measurableSet_Iic),
    integral_indicator_const _ measurableSet_Iic, integral_const] at h1
  simp only [probReal_univ, smul_eq_mul, one_mul] at h1
  unfold G
  have hneg : T - b * q - y < 0 := by linarith
  nlinarith

end General

lemma concave_three (R : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ici 0) R) (u v w : ℝ) (hu : 0 ≤ u)
    (huv : u ≤ v) (hvw : v ≤ w) (huw : u < w) :
    (w - v) * R u + (v - u) * R w ≤ (w - u) * R v := by
  have hwu : 0 < w - u := by linarith
  have hne : w - u ≠ 0 := hwu.ne'
  have h := hconc.2 (show u ∈ Ici (0 : ℝ) from hu) (show w ∈ Ici (0 : ℝ) by
      simp only [mem_Ici]; linarith)
    (show 0 ≤ (w - v) / (w - u) from div_nonneg (by linarith) hwu.le)
    (show 0 ≤ (v - u) / (w - u) from div_nonneg (by linarith) hwu.le)
    (by field_simp; ring)
  have hv : (w - v) / (w - u) * u + (v - u) / (w - u) * w = v := by
    field_simp; ring
  simp only [smul_eq_mul] at h
  rw [hv] at h
  have h2 := mul_le_mul_of_nonneg_left h hwu.le
  have e : (w - u) * ((w - v) / (w - u) * R u + (v - u) / (w - u) * R w) =
      (w - v) * R u + (v - u) * R w := by field_simp
  linarith

/-- Abstract projection lemma: a continuous function, concave on `[0, ∞)`, vanishing at `0`,
nonpositive on `(−∞, 0]`, and negative beyond some `Q ≥ 0`, has a largest global maximizer `p†`,
and its largest maximizer on `[lo, hi]` (`0 < lo ≤ hi`) is `min (max p† lo) hi`. -/
lemma argmax_proj (R : ℝ → ℝ) (hc : Continuous R) (hconc : ConcaveOn ℝ (Ici 0) R)
    (hR0 : R 0 = 0) (hnp : ∀ q ≤ 0, R q ≤ 0) (Q : ℝ) (hQ0 : 0 ≤ Q)
    (hQ : ∀ q, Q < q → R q < 0)
    (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    argmaxIcc lo hi R = min (max (sSup {q | ∀ q', R q' ≤ R q}) lo) hi := by
  set M := {q | ∀ q', R q' ≤ R q} with hMdef
  obtain ⟨m0, hm0, hm0max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Q)).exists_isMaxOn
    ⟨0, le_rfl, hQ0⟩ hc.continuousOn
  have hm0R : 0 ≤ R m0 := by
    have := hm0max (show (0 : ℝ) ∈ Icc 0 Q from ⟨le_rfl, hQ0⟩)
    simp only [mem_setOf_eq] at this
    linarith
  have hm0M : m0 ∈ M := by
    intro q'
    by_cases h1 : q' < 0
    · linarith [hnp q' h1.le]
    by_cases h2 : Q < q'
    · linarith [hQ q' h2]
    push_neg at h1 h2
    exact hm0max ⟨h1, h2⟩
  have hbdd : BddAbove M := by
    refine ⟨Q, fun q hq => ?_⟩
    by_contra h
    push_neg at h
    linarith [hQ q h, hq m0]
  have hclosed : IsClosed M := by
    have : M = ⋂ q', {q | R q' ≤ R q} := by ext q; simp [hMdef]
    rw [this]
    exact isClosed_iInter (fun q' => isClosed_le continuous_const hc)
  set pd := sSup M with hpd
  have hpdM : pd ∈ M := hclosed.csSup_mem ⟨m0, hm0M⟩ hbdd
  have hpd0 : 0 ≤ pd := le_trans hm0.1 (le_csSup hbdd hm0M)
  have hstrict : ∀ q, pd < q → R q < R pd := by
    intro q hq
    by_contra h
    push_neg at h
    have : q ∈ M := fun q' => le_trans (hpdM q') h
    linarith [le_csSup hbdd this]
  unfold argmaxIcc
  apply IsGreatest.csSup_eq
  rcases lt_or_ge pd lo with hlt | hge
  · -- p† < lo: the answer is lo
    rw [max_eq_right hlt.le, min_eq_left hlohi]
    refine ⟨⟨⟨le_rfl, hlohi⟩, fun q' hq' => ?_⟩, fun q hq => ?_⟩
    · rcases eq_or_lt_of_le hq'.1 with h | h
      · rw [h]
      · have := concave_three R hconc pd lo q' hpd0 hlt.le h.le (by linarith)
        have h1 := hpdM q'
        nlinarith
    · by_contra hql
      push_neg at hql
      have := concave_three R hconc pd lo q hpd0 hlt.le hql.le (by linarith)
      have h1 := hstrict q (by linarith)
      have h2 := hq.2 lo ⟨le_rfl, hlohi⟩
      nlinarith
  · rcases le_or_gt pd hi with hle | hgt
    · rw [max_eq_left hge, min_eq_left hle]
      refine ⟨⟨⟨hge, hle⟩, fun q' _ => hpdM q'⟩, fun q hq => ?_⟩
      by_contra h
      push_neg at h
      linarith [hstrict q h, hq.2 pd ⟨hge, hle⟩]
    · rw [max_eq_left hge, min_eq_right hgt.le]
      refine ⟨⟨⟨hlohi, le_rfl⟩, fun q' hq' => ?_⟩, fun q hq => hq.1.2⟩
      rcases eq_or_lt_of_le hq'.2 with h | h
      · rw [h]
      · have := concave_three R hconc q' hi pd (by linarith [hq'.1]) h.le hgt.le (by linarith)
        have h1 := hpdM q'
        nlinarith



lemma lam_pos {K : ℕ} (I : Instance K) (hI : I.Standing) : 0 < lam I := by
  obtain ⟨-, -, hplo, -, hblo, hbb, -, hK, -, hpi, hyh, -⟩ := hI
  have i : Fin K := ⟨0, by omega⟩
  have hle : I.yh i + I.b * I.p i ≤ lam I :=
    le_ciSup (Finite.bddAbove_range (fun i => I.yh i + I.b * I.p i)) i
  have hb : 0 < I.b := lt_of_lt_of_le hblo hbb
  have hp : 0 < I.p i := lt_of_lt_of_le hplo (hpi i).1
  have := hyh i
  have := mul_pos hb hp
  linarith

lemma ae_lower {K : ℕ} (I : Instance K) (hI : I.Standing) (μ : Measure ℝ) (hμ : μ ∈ Amb I) :
    ∀ᵐ ξ ∂μ, min (lam I) (I.b * I.phi) ≤ ξ := by
  set m := min (lam I) (I.b * I.phi) with hmdef
  have hnull : ∀ n : ℕ, μ (Iic (m - 1 / ((n : ℝ) + 1))) = 0 := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hx1 : m - 1 / ((n : ℝ) + 1) < lam I := by
      have := min_le_left (lam I) (I.b * I.phi); linarith
    have hx2 : m - 1 / ((n : ℝ) + 1) < I.b * I.phi := by
      have := min_le_right (lam I) (I.b * I.phi); linarith
    rw [hμ.2 _ hx1]
    exact measure_mono_null (Iic_subset_Iio.2 hx2) hI.2.2.2.2.2.2.2.2.2.2.2.1
  have hall : ∀ᵐ ξ ∂μ, ∀ n : ℕ, ξ ∉ Iic (m - 1 / ((n : ℝ) + 1)) :=
    ae_all_iff.2 (fun n => measure_eq_zero_iff_ae_notMem.1 (hnull n))
  filter_upwards [hall] with ξ hξ
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
  exact hξ n (show ξ ≤ m - 1 / ((n : ℝ) + 1) by linarith)

end OCPProp1Aux

open OCPProp1Aux in
theorem solution {K : ℕ} (I : Instance K) (hI : I.Standing) (μ : Measure ℝ) (hμ : μ ∈ Amb I) :
    ConcaveOn ℝ (Icc I.plo I.phi) (RF I μ) ∧
      pStar I μ = min (max (pDagger I μ) I.plo) I.phi := by
  haveI : IsProbabilityMeasure μ := hμ.1
  have hm := ae_lower I hI μ hμ
  have hlam := lam_pos I hI
  obtain ⟨-, hy, hplo, hlohi, hblo, hbb, -⟩ := hI
  have hb : 0 < I.b := lt_of_lt_of_le hblo hbb
  have hm0 : 0 ≤ min (lam I) (I.b * I.phi) :=
    le_min hlam.le (by nlinarith)
  have hRF : RF I μ = fun q => q * G μ I.b I.y q := rfl
  have hconc := R_concave (y := I.y) hb.le hm
  refine ⟨?_, ?_⟩
  · rw [hRF]
    exact hconc.subset (fun q hq => show (0 : ℝ) ≤ q by linarith [hq.1]) (convex_Icc _ _)
  · obtain ⟨Q, hQ0, hQ⟩ := G_tail (μ := μ) (m := min (lam I) (I.b * I.phi)) hb hy
    unfold pStar pDagger
    rw [hRF]
    refine argmax_proj _ ((continuous_id).mul (G_cont hb.le hm)) hconc (by simp)
      (fun q hq => R_nonpos hb.le hy hm0 hm q hq) Q hQ0 (fun q hq => ?_) I.plo I.phi hplo
      hlohi.le
    have hG := hQ q hq hm
    have hq0 : 0 < q := lt_of_le_of_lt hQ0 hq
    exact mul_neg_of_pos_of_neg hq0 hG
