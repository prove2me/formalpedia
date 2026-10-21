-- Prove2me | solution 1 for OppReturns.Menu.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T08:20:32.065183+00:00
-- url     : https://prove2.me/submissions/47c3f9a3-4104-4f29-b929-deee27b684fc

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

namespace OppAux
open MeasureTheory OppReturns.Menu

variable (P : Params)

lemma probL (hS : Standing P) : IsProbabilityMeasure P.νL := hS.2.2.2.2.2.2.1
lemma probS (hS : Standing P) : IsProbabilityMeasure P.νS := hS.2.2.2.2.2.2.2.1
lemma probD (hS : Standing P) : IsProbabilityMeasure P.D := hS.2.2.2.2.2.2.2.2.1

lemma GLf_nonneg (r : ℝ) : 0 ≤ GLf P r := ENNReal.toReal_nonneg
lemma GSf_nonneg (r : ℝ) : 0 ≤ GSf P r := ENNReal.toReal_nonneg
lemma GLf_le_one (hS : Standing P) (r : ℝ) : GLf P r ≤ 1 := by
  have := probL P hS
  unfold GLf; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
lemma GSf_le_one (hS : Standing P) (r : ℝ) : GSf P r ≤ 1 := by
  have := probS P hS
  unfold GSf; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

/-- a.e. `u ∈ [0, VL]` -/
lemma ae_L (hS : Standing P) : ∀ᵐ u ∂P.νL, u ∈ Set.Icc 0 P.VL := by
  have h := hS.2.2.2.2.2.2.2.2.2.1.1
  rw [ae_iff]; exact h

lemma ae_S (hS : Standing P) : ∀ᵐ u ∂P.νS, u ∈ Set.Icc 0 P.VS := by
  have h := hS.2.2.2.2.2.2.2.2.2.2.1.1
  rw [ae_iff]; exact h

lemma ae_D (hS : Standing P) : ∀ᵐ d ∂P.D, 0 < d := by
  have h := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ae_iff]; exact measure_mono_null (fun x hx => by simpa using hx) h

lemma integrable_D (hS : Standing P) : Integrable (fun x : ℝ => x) P.D :=
  hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma integrable_max (hS : Standing P) (r : ℝ) : Integrable (fun u => max u r) P.νL := by
  have := probL P hS
  refine Integrable.of_bound (C := P.VL + |r|) (by fun_prop) ?_
  filter_upwards [ae_L P hS] with u hu
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := le_max_right u r; have := neg_abs_le r; have := hu.1
    linarith [le_max_left u r, hu.2, abs_nonneg r]
  · rcases le_total u r with h | h
    · rw [max_eq_right h]; linarith [le_abs_self r, hu.1, hu.2]
    · rw [max_eq_left h]; linarith [abs_nonneg r, hu.2]

lemma Emax_mono (hS : Standing P) {a b : ℝ} (h : a ≤ b) : Emax P a ≤ Emax P b :=
  integral_mono (integrable_max P hS a) (integrable_max P hS b) (fun u => max_le_max le_rfl h)

/-- `E max{u,r} - r ≤ E max{u,0}` for `r ≥ 0`. -/
lemma Emax_sub_le (hS : Standing P) {r : ℝ} (hr : 0 ≤ r) : Emax P r - r ≤ Emax P 0 := by
  have := probL P hS
  have : Emax P r - r = ∫ u, (max u r - r) ∂P.νL := by
    rw [integral_sub (integrable_max P hS r) (integrable_const r)]; simp [Emax]
  rw [this]
  exact integral_mono ((integrable_max P hS r).sub (integrable_const r)) (integrable_max P hS 0)
    (fun u => by
      simp only
      rcases le_total u r with h | h
      · rw [max_eq_right h]; simp
      · rw [max_eq_left h]; linarith [le_max_left u 0])

lemma Emax_le (hS : Standing P) {r : ℝ} (hr : 0 ≤ r) : Emax P r ≤ P.VL + r := by
  have := probL P hS
  have : Emax P r ≤ ∫ _u, (P.VL + r) ∂P.νL := by
    apply integral_mono_ae (integrable_max P hS r) (integrable_const _)
    filter_upwards [ae_L P hS] with u hu
    exact max_le (by linarith [hu.2]) (by linarith [hu.1, hu.2])
  simpa using this

lemma Emax_ge (hS : Standing P) (r : ℝ) : r ≤ Emax P r := by
  have := probL P hS
  have : ∫ _u, r ∂P.νL ≤ Emax P r :=
    integral_mono (integrable_const _) (integrable_max P hS r) (fun u => le_max_right u r)
  simpa using this

lemma Emax_nonneg (hS : Standing P) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Emax P r :=
  hr.trans (Emax_ge P hS r)

/-- `G_L(r) = 1` for `r > V_L` -/
lemma GLf_eq_one (hS : Standing P) {r : ℝ} (hr : P.VL < r) : GLf P r = 1 := by
  have := probL P hS
  have h0 := hS.2.2.2.2.2.2.2.2.2.1.1
  have h1 : P.νL (Set.Icc 0 P.VL) = 1 := by
    rw [← prob_compl_eq_zero_iff (measurableSet_Icc)]; exact h0
  have : P.νL (Set.Iio r) = 1 := by
    apply le_antisymm prob_le_one
    rw [← h1]; apply measure_mono; intro x hx; exact lt_of_le_of_lt hx.2 hr
  simp [GLf, this]

lemma noAtom_S (hS : Standing P) (x : ℝ) : P.νS {x} = 0 := by
  obtain ⟨ψ, hψ, -⟩ := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hψ.2.1]
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

lemma noAtom_L (hS : Standing P) (x : ℝ) : P.νL {x} = 0 := by
  obtain ⟨ψ, hψ, -⟩ := hS.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hψ.2.1]
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

/-- `G_S(f) = 1` for `f ≥ V_S` -/
lemma GSf_eq_one (hS : Standing P) {f : ℝ} (hf : P.VS ≤ f) : GSf P f = 1 := by
  have := probS P hS
  have h0 := hS.2.2.2.2.2.2.2.2.2.2.1.1
  have h1 : P.νS (Set.Icc 0 P.VS) = 1 := by
    rw [← prob_compl_eq_zero_iff (measurableSet_Icc)]; exact h0
  have h2 : P.νS (Set.Iic f) = 1 := by
    apply le_antisymm prob_le_one
    rw [← h1]; apply measure_mono; intro x hx; exact le_trans hx.2 hf
  have : P.νS (Set.Iio f) = 1 := by
    rw [← Set.Iic_diff_right, measure_diff_null (noAtom_S P hS f), h2]
  simp [GSf, this]


/-! ### expected sales -/

lemma integrable_min (hS : Standing P) (y : ℝ) : Integrable (fun d => min y d) P.D := by
  have := probD P hS
  refine Integrable.mono' ((integrable_D P hS).norm.add (integrable_const |y|)) (by fun_prop) ?_
  refine Filter.Eventually.of_forall (fun d => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rcases le_total y d with h | h
  · rw [min_eq_left h]; linarith [abs_nonneg d, le_abs_self y, neg_abs_le y, abs_le.mp (le_refl |y|),
      show |y| ≤ |d| + |y| by linarith [abs_nonneg d]]
  · rw [min_eq_right h]; linarith [abs_nonneg y]

lemma expSales_nonneg (hS : Standing P) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ SupplyChainTheory.expSales P.D y := by
  unfold SupplyChainTheory.expSales
  apply integral_nonneg_of_ae
  filter_upwards [ae_D P hS] with d hd
  exact le_min hy hd.le

lemma expSales_le_mean (hS : Standing P) (y : ℝ) :
    SupplyChainTheory.expSales P.D y ≤ ∫ d, d ∂P.D :=
  integral_mono (integrable_min P hS y) (integrable_D P hS) (fun d => min_le_right y d)

lemma expSales_pos (hS : Standing P) {y : ℝ} (hy : 0 < y) :
    0 < SupplyChainTheory.expSales P.D y := by
  have := probD P hS
  unfold SupplyChainTheory.expSales
  have hpos : ∀ᵐ d ∂P.D, 0 < min y d := by
    filter_upwards [ae_D P hS] with d hd; exact lt_min hy hd
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun d hd => hd.le) (integrable_min P hS y)]
  have hbad : P.D {d | ¬ 0 < min y d} = 0 := ae_iff.mp hpos
  rw [pos_iff_ne_zero]
  intro h0
  have : P.D Set.univ ≤ P.D (Function.support fun d => min y d) + P.D {d | ¬ 0 < min y d} := by
    refine (measure_mono (fun d _ => ?_)).trans (measure_union_le _ _)
    by_cases hd : 0 < min y d
    · left; exact ne_of_gt hd
    · right; exact hd
  rw [h0, hbad, measure_univ] at this; simp at this

lemma expSales_zero (hS : Standing P) : SupplyChainTheory.expSales P.D 0 = 0 := by
  unfold SupplyChainTheory.expSales
  rw [integral_eq_zero_of_ae]
  filter_upwards [ae_D P hS] with d hd
  simp [min_eq_left hd.le]

lemma mean_nonneg (hS : Standing P) : 0 ≤ ∫ d, d ∂P.D :=
  (expSales_nonneg P hS le_rfl).trans (expSales_le_mean P hS 0)

lemma Nf_pos (hS : Standing P) (f : ℝ) : 0 < Nf P f := by
  unfold Nf
  have h1 := hS.2.1; have h0 := hS.1
  nlinarith [GSf_le_one P hS f, GSf_nonneg P f]

/-- profit is bounded by `B * E[D]` when `M ≤ B`. -/
lemma profit_le (hS : Standing P) {M N Q B : ℝ} (hN : 0 < N) (hQ : 0 ≤ Q) (hB : 0 ≤ B)
    (hM : M ≤ B) : profit P M N Q ≤ B * ∫ d, d ∂P.D := by
  unfold profit
  have hc : 0 ≤ P.c - P.s := by linarith [hS.2.2.2.1]
  have h1 := expSales_nonneg P hS (div_nonneg hQ hN.le)
  have h2 := expSales_le_mean P hS (Q / N)
  nlinarith [mul_le_mul_of_nonneg_right hM h1, mul_le_mul_of_nonneg_left h2 hB, mul_nonneg hc hQ]

lemma profit_mono (hS : Standing P) {M M' N Q : ℝ} (hN : 0 < N) (hQ : 0 ≤ Q) (hM : M ≤ M') :
    profit P M N Q ≤ profit P M' N Q := by
  unfold profit
  have h1 := expSales_nonneg P hS (div_nonneg hQ hN.le)
  nlinarith [mul_le_mul_of_nonneg_right hM h1]

lemma profit_strict (hS : Standing P) {M M' N Q : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hM : M < M') :
    profit P M N Q < profit P M' N Q := by
  unfold profit
  have h1 := expSales_pos P hS (div_pos hQ hN)
  nlinarith [mul_lt_mul_of_pos_right hM h1]

/-! ### margins -/

lemma honestMargin_eq (p r : ℝ) :
    honestMargin P p r = (p - r) + (r - P.s) * (1 - GLf P r) := by
  unfold honestMargin; ring

lemma Mu_eq (p r : ℝ) : Mu P p r = Mt P p r r := by
  unfold Mu Mt honestMargin; ring

lemma k_le (hS : Standing P) {r : ℝ} (hr : 0 ≤ r) : (r - P.s) * (1 - GLf P r) ≤ P.VL := by
  have hs := hS.2.2.1
  rcases le_or_gt r P.s with h | h
  · nlinarith [GLf_le_one P hS r, hS.2.2.2.2.1]
  rcases le_or_gt r P.VL with h' | h'
  · nlinarith [GLf_le_one P hS r, GLf_nonneg P r]
  · rw [GLf_eq_one P hS h']; simp; linarith [hS.2.2.2.2.1]

lemma honestMargin_le (hS : Standing P) {p r : ℝ} (hr : 0 ≤ r) (hp : p ≤ Emax P r) :
    honestMargin P p r ≤ 2 * P.VL := by
  rw [honestMargin_eq]
  have := Emax_le P hS hr
  linarith [k_le P hS hr]

lemma renter_le (hS : Standing P) {f : ℝ} (hf : 0 ≤ f) :
    P.X * f * (1 - GSf P f) ≤ f := by
  have := hS.1; have := hS.2.1
  nlinarith [GSf_le_one P hS f, GSf_nonneg P f, mul_nonneg hf (GSf_nonneg P f)]

lemma Mt_le (hS : Standing P) {p rR rH : ℝ} (hf : 0 ≤ p - rR) (hfV : p - rR ≤ P.VS + P.VL)
    (hr : 0 ≤ rH) (hp : p ≤ Emax P rH) : Mt P p rR rH ≤ P.VS + 3 * P.VL := by
  unfold Mt
  have h1 := renter_le P hS hf
  have h2 := honestMargin_le P hS hr hp
  have := hS.1; have := hS.2.1; have := hS.2.2.2.2.1
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 1 - P.X)]

lemma bound_nonneg (hS : Standing P) : 0 ≤ P.VS + 3 * P.VL := by
  linarith [hS.2.2.2.2.1, hS.2.2.2.2.2.1]


lemma Mm_eq (pR rR pH rH : ℝ) : Mm P pR rR pH rH = Mt P pH (pH - (pR - rR)) rH := by
  unfold Mm Mt; rw [sub_sub_cancel]

lemma GSf_min (hS : Standing P) (f : ℝ) : GSf P (min f P.VS) = GSf P f := by
  rcases le_total f P.VS with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, GSf_eq_one P hS le_rfl, GSf_eq_one P hS h]

lemma renter_min (hS : Standing P) (f : ℝ) :
    P.X * min f P.VS * (1 - GSf P (min f P.VS)) = P.X * f * (1 - GSf P f) := by
  rcases le_total f P.VS with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, GSf_eq_one P hS le_rfl, GSf_eq_one P hS h]; ring

lemma bddU (hS : Standing P) : BddAbove {π | ∃ Q p r, FeasU P Q p r ∧ π = profitU P Q p r} := by
  refine ⟨(P.VS + 3 * P.VL) * ∫ d, d ∂P.D, ?_⟩
  rintro π ⟨Q, p, r, ⟨hQ, hr, hrp, hp⟩, rfl⟩
  unfold profitU
  apply profit_le P hS (Nf_pos P hS _) hQ (bound_nonneg P hS)
  rw [Mu_eq]
  have h1 := Emax_sub_le P hS hr
  have h2 := Emax_le P hS (le_refl (0:ℝ))
  exact Mt_le P hS (by linarith) (by linarith [hS.2.2.2.2.2.1]) hr hp

lemma bddT (hS : Standing P) :
    BddAbove {π | ∃ Q p rR rH, FeasT P Q p rR rH ∧ π = profitT P Q p rR rH} := by
  refine ⟨(P.VS + 3 * P.VL) * ∫ d, d ∂P.D, ?_⟩
  rintro π ⟨Q, p, rR, rH, ⟨hQ, hrR, hrH, hf0, hfV, hE⟩, rfl⟩
  unfold profitT
  apply profit_le P hS (Nf_pos P hS _) hQ (bound_nonneg P hS)
  exact Mt_le P hS hf0 (by linarith [hS.2.2.2.2.1]) hrH (by linarith)

lemma bddM (hS : Standing P) :
    BddAbove {π | ∃ Q pH rH pR rR, FeasM P Q pH rH pR rR ∧ π = profitM P Q pH rH pR rR} := by
  refine ⟨(P.VS + 3 * P.VL) * ∫ d, d ∂P.D, ?_⟩
  rintro π ⟨Q, pH, rH, pR, rR, ⟨hQ, hrH, hrR, hrpH, hrpR, hIC, hfee⟩, rfl⟩
  unfold profitM
  apply profit_le P hS (Nf_pos P hS _) hQ (bound_nonneg P hS)
  rw [Mm_eq]
  have := le_trans (le_max_right _ _) hIC
  have h1 := min_le_right (pH - rH) P.VS
  exact Mt_le P hS (by rw [sub_sub_cancel]; linarith) (by rw [sub_sub_cancel]; linarith [hS.2.2.2.2.1])
    hrH (by linarith)

lemma neU (hS : Standing P) : ({π | ∃ Q p r, FeasU P Q p r ∧ π = profitU P Q p r} : Set ℝ).Nonempty :=
  ⟨_, 0, 0, 0, ⟨le_rfl, le_rfl, le_rfl, Emax_nonneg P hS le_rfl⟩, rfl⟩

lemma neM (hS : Standing P) :
    ({π | ∃ Q pH rH pR rR, FeasM P Q pH rH pR rR ∧ π = profitM P Q pH rH pR rR} : Set ℝ).Nonempty :=
  ⟨_, 0, 0, 0, 0, 0, ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
    by simp [Emax_nonneg P hS le_rfl], by simp [hS.2.2.2.2.2.1.le]⟩, rfl⟩

/-- every menu profit is matched by a targeted profit -/
lemma menu_le_T (hS : Standing P) {Q pH rH pR rR : ℝ} (h : FeasM P Q pH rH pR rR) :
    profitM P Q pH rH pR rR ≤ PiT P := by
  obtain ⟨hQ, hrH, hrR, hrpH, hrpR, hIC, hfee⟩ := h
  have hE := le_trans (le_max_right _ _) hIC
  have h1 := min_le_right (pH - rH) P.VS
  have h2 := min_le_left (pH - rH) P.VS
  refine le_csSup_of_le (bddT P hS)
    ⟨Q, Emax P rH, Emax P rH - (pR - rR), rH, ⟨hQ, by linarith, hrH, by linarith, by linarith,
      sub_self _⟩, rfl⟩ ?_
  unfold profitM profitT
  rw [sub_sub_cancel, Mm_eq]
  apply profit_mono P hS (Nf_pos P hS _) hQ
  unfold Mt; rw [sub_sub_cancel, sub_sub_cancel]
  have : honestMargin P pH rH ≤ honestMargin P (Emax P rH) rH := by
    unfold honestMargin; linarith
  nlinarith [hS.2.1]

lemma uniform_le_T (hS : Standing P) {Q p r : ℝ} (h : FeasU P Q p r) :
    profitU P Q p r ≤ PiT P := by
  obtain ⟨hQ, hr, hrp, hp⟩ := h
  have h1 := min_le_right (p - r) P.VS
  have h2 := min_le_left (p - r) P.VS
  have h3 : 0 ≤ min (p - r) P.VS := le_min (by linarith) hS.2.2.2.2.2.1.le
  refine le_csSup_of_le (bddT P hS)
    ⟨Q, Emax P r, Emax P r - min (p - r) P.VS, r, ⟨hQ, by linarith, hr, by linarith, by linarith,
      sub_self _⟩, rfl⟩ ?_
  unfold profitU profitT
  rw [sub_sub_cancel, show Nf P (min (p - r) P.VS) = Nf P (p - r) by unfold Nf; rw [GSf_min P hS]]
  apply profit_mono P hS (Nf_pos P hS _) hQ
  rw [Mu_eq]; unfold Mt; rw [sub_sub_cancel, renter_min P hS]
  have : honestMargin P p r ≤ honestMargin P (Emax P r) r := by
    unfold honestMargin; linarith
  nlinarith [hS.2.1]

theorem upper_bounds_proof (hS : Standing P) :
    BddAbove {π | ∃ Q p r, FeasU P Q p r ∧ π = profitU P Q p r} ∧
    BddAbove {π | ∃ Q p rR rH, FeasT P Q p rR rH ∧ π = profitT P Q p rR rH} ∧
    BddAbove {π | ∃ Q pH rH pR rR, FeasM P Q pH rH pR rR ∧ π = profitM P Q pH rH pR rR} ∧
    PiM P ≤ PiT P ∧ PiU P ≤ PiT P := by
  refine ⟨bddU P hS, bddT P hS, bddM P hS, ?_, ?_⟩
  · apply csSup_le (neM P hS)
    rintro π ⟨Q, pH, rH, pR, rR, h, rfl⟩; exact menu_le_T P hS h
  · apply csSup_le (neU P hS)
    rintro π ⟨Q, p, r, h, rfl⟩; exact uniform_le_T P hS h


lemma s_lt_VL (hS : Standing P) : P.s < P.VL := by
  by_contra h; push_neg at h
  have := probL P hS
  have hE : Emax P P.s ≤ ∫ _u, P.s ∂P.νL := by
    apply integral_mono_ae (integrable_max P hS _) (integrable_const _)
    filter_upwards [ae_L P hS] with u hu
    exact max_le (hu.2.trans h) le_rfl
  simp at hE
  have := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; have := hS.2.2.2.1; linarith

lemma phi_nonneg (r s u : ℝ) :
    0 ≤ max u s - max u r + (r - s) * (Set.Iio r).indicator 1 u := by
  by_cases hu : u < r
  · simp only [Set.indicator, Set.mem_Iio, hu, if_true, Pi.one_apply, mul_one]
    rw [max_eq_right hu.le]; linarith [le_max_right u s]
  · simp only [Set.indicator, Set.mem_Iio, hu, if_false, mul_zero, add_zero]
    push_neg at hu; rw [max_eq_left hu]; linarith [le_max_left u s]

lemma phi_pos (r s u : ℝ) (h : min r s < u) (h' : u < max r s) :
    0 < max u s - max u r + (r - s) * (Set.Iio r).indicator 1 u := by
  rcases lt_or_gt_of_ne (show r ≠ s by intro e; subst e; simp at h h'; linarith) with hrs | hrs
  · rw [min_eq_left hrs.le] at h; rw [max_eq_right hrs.le] at h'
    have hu : ¬ u < r := by linarith
    simp only [Set.indicator, Set.mem_Iio, hu, if_false, mul_zero, add_zero]
    rw [max_eq_left (by linarith : r ≤ u), max_eq_right h'.le]; linarith
  · rw [min_eq_right hrs.le] at h; rw [max_eq_left hrs.le] at h'
    simp only [Set.indicator, Set.mem_Iio, h', if_true, Pi.one_apply, mul_one]
    rw [max_eq_right h'.le, max_eq_left h.le]; linarith

theorem benchmark_proof (hS : Standing P) :
    ∀ r : ℝ, 0 ≤ r → r ≠ P.s →
      honestMargin P (Emax P r) r < honestMargin P (Emax P P.s) P.s := by
  intro r hr hne
  have := probL P hS
  have hint : Integrable (fun u => max u P.s - max u r + (r - P.s) * (Set.Iio r).indicator 1 u) P.νL :=
    ((integrable_max P hS _).sub (integrable_max P hS _)).add
      (((integrable_const (1:ℝ)).indicator measurableSet_Iio).const_mul _)
  have heq : honestMargin P (Emax P P.s) P.s - honestMargin P (Emax P r) r =
      ∫ u, (max u P.s - max u r + (r - P.s) * (Set.Iio r).indicator 1 u) ∂P.νL := by
    have hA : Integrable (fun u => max u P.s - max u r) P.νL :=
      (integrable_max P hS _).sub (integrable_max P hS _)
    have hB : Integrable (fun u => (r - P.s) * (Set.Iio r).indicator (1 : ℝ → ℝ) u) P.νL :=
      ((integrable_const (1:ℝ)).indicator measurableSet_Iio).const_mul _
    have e1 : ∫ u, (max u P.s - max u r + (r - P.s) * (Set.Iio r).indicator 1 u) ∂P.νL =
        (∫ u, (max u P.s - max u r) ∂P.νL) + ∫ u, (r - P.s) * (Set.Iio r).indicator (1 : ℝ → ℝ) u ∂P.νL :=
      integral_add hA hB
    have e2 : ∫ u, (max u P.s - max u r) ∂P.νL = Emax P P.s - Emax P r :=
      integral_sub (integrable_max P hS _) (integrable_max P hS _)
    have e3 : ∫ u, (r - P.s) * (Set.Iio r).indicator (1 : ℝ → ℝ) u ∂P.νL = (r - P.s) * GLf P r := by
      rw [integral_const_mul, integral_indicator_one measurableSet_Iio]; rfl
    rw [e1, e2, e3]
    unfold honestMargin; ring
  have hpos : 0 < ∫ u, (max u P.s - max u r + (r - P.s) * (Set.Iio r).indicator 1 u) ∂P.νL := by
    rw [integral_pos_iff_support_of_nonneg (fun u => phi_nonneg r P.s u) hint]
    have hsV := s_lt_VL P hS
    have hfs := hS.2.2.2.2.2.2.2.2.2.1.2
    have ha : 0 ≤ min r P.s := le_min hr hS.2.2.1.le
    have hab : min r P.s < min (max r P.s) P.VL := by
      rcases lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left h.le, max_eq_right h.le, min_eq_left hsV.le]; exact h
      · rw [min_eq_right h.le, max_eq_left h.le]; exact lt_min h hsV
    refine lt_of_lt_of_le (hfs _ _ ha hab (min_le_right _ _)) (measure_mono ?_)
    intro u hu
    exact ne_of_gt (phi_pos r P.s u hu.1 (lt_of_lt_of_le hu.2 (min_le_left _ _)))
  linarith


lemma exists_y (hS : Standing P) {a : ℝ} (ha : a < 1) :
    ∃ y : ℝ, 0 < y ∧ a * y < SupplyChainTheory.expSales P.D y := by
  have := probD P hS
  have hD0 : P.D (Set.Ioi 0) = 1 := by
    rw [← prob_compl_eq_zero_iff measurableSet_Ioi, Set.compl_Ioi]
    exact hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmono : Monotone (fun n : ℕ => Set.Ici (1 / ((n:ℝ) + 1))) := by
    intro m n hmn x hx
    simp only [Set.mem_Ici] at *
    refine le_trans ?_ hx
    apply one_div_le_one_div_of_le (by positivity); exact_mod_cast (by omega : m + 1 ≤ n + 1)
  have hU : (⋃ n : ℕ, Set.Ici (1 / ((n:ℝ) + 1))) = Set.Ioi 0 := by
    ext x; simp only [Set.mem_iUnion, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩; exact lt_of_lt_of_le (by positivity) hn
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact ⟨n, hn.le⟩
  have ht := tendsto_measure_iUnion_atTop (μ := P.D) hmono
  rw [hU, hD0] at ht
  have hlt : ENNReal.ofReal a < 1 := by
    rcases le_or_gt a 0 with h | h
    · rw [ENNReal.ofReal_of_nonpos h]; exact zero_lt_one
    · exact (ENNReal.ofReal_lt_one).mpr ha
  obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hlt)).exists
  set y : ℝ := 1 / ((n:ℝ) + 1) with hy
  have hy0 : 0 < y := by positivity
  refine ⟨y, hy0, ?_⟩
  have hm : a < P.D.real (Set.Ici y) := by
    rcases le_or_gt a 0 with h | h
    · refine lt_of_le_of_lt h ?_
      rw [Measure.real, ENNReal.toReal_pos_iff]
      exact ⟨lt_of_le_of_lt bot_le hn, measure_lt_top _ _⟩
    · rw [Measure.real]
      have := (ENNReal.ofReal_lt_iff_lt_toReal h.le (measure_ne_top _ _)).mp hn
      exact this
  have hS1 : y * P.D.real (Set.Ici y) ≤ SupplyChainTheory.expSales P.D y := by
    unfold SupplyChainTheory.expSales
    rw [← integral_indicator_one measurableSet_Ici, ← integral_const_mul]
    apply integral_mono_ae (((integrable_const (1:ℝ)).indicator measurableSet_Ici).const_mul _)
      (integrable_min P hS y)
    filter_upwards [ae_D P hS] with d hd
    by_cases h : d ∈ Set.Ici y
    · simp [Set.indicator, h]; exact h
    · simp [Set.indicator, h]; exact ⟨hy0.le, hd.le⟩
  nlinarith

/-- a targeted decision with positive profit -/
lemma PiT_pos (hS : Standing P) : 0 < PiT P := by
  set e := Emax P P.s - P.s with he
  have hce : P.c - P.s < e := by have := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; linarith
  have hcs : 0 < P.c - P.s := by linarith [hS.2.2.2.1]
  have he0 : 0 < e := by linarith
  set g := min e P.VS with hg
  have hg0 : 0 ≤ g := le_min he0.le hS.2.2.2.2.2.1.le
  have hge : g ≤ e := min_le_left _ _
  have hgV : g ≤ P.VS := min_le_right _ _
  have hM : Mt P (Emax P P.s) (Emax P P.s - g) P.s = e * Nf P g := by
    unfold Mt honestMargin Nf; rw [sub_sub_cancel]
    rcases le_total e P.VS with h | h
    · have : g = e := min_eq_left h
      rw [this]; ring
    · have : g = P.VS := min_eq_right h
      rw [this, GSf_eq_one P hS le_rfl]; ring
  obtain ⟨y, hy0, hy⟩ := exists_y P hS (a := (P.c - P.s) / e) ((div_lt_one he0).mpr hce)
  have hN := Nf_pos P hS g
  have hsp := hS.2.2.1
  refine lt_of_lt_of_le ?_ (le_csSup (bddT P hS)
    ⟨Nf P g * y, Emax P P.s, Emax P P.s - g, P.s, ⟨(mul_pos hN hy0).le, by linarith,
      hS.2.2.1.le, by linarith, by linarith, sub_self _⟩, rfl⟩)
  unfold profitT profit
  rw [sub_sub_cancel, hM, mul_div_cancel_left₀ _ hN.ne']
  rw [div_mul_eq_mul_div, div_lt_iff₀ he0] at hy
  nlinarith [mul_lt_mul_of_pos_left hy hN]

lemma PiU_eq {Q p r : ℝ} (hU : IsOptU P Q p r) : PiU P = profitU P Q p r := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨Q, p, r, hU.1, rfl⟩, ?_⟩
  rintro π ⟨Q', p', r', h, rfl⟩; exact hU.2 Q' p' r' h

theorem targeted_gain_proof (hS : Standing P) (Q p r : ℝ) (hU : IsOptU P Q p r)
    (hr : r ≠ P.s) : PiU P < PiT P := by
  rw [PiU_eq P hU]
  obtain ⟨⟨hQ, hr0, hrp, hp⟩, -⟩ := hU
  rcases hQ.lt_or_eq with hQ' | hQ'
  · have h1 := min_le_right (p - r) P.VS
    have h2 := min_le_left (p - r) P.VS
    have h3 : 0 ≤ min (p - r) P.VS := le_min (by linarith) hS.2.2.2.2.2.1.le
    have h4 := Emax_sub_le P hS hr0
    have h5 := Emax_mono P hS hS.2.2.1.le
    refine lt_of_lt_of_le ?_ (le_csSup (bddT P hS)
      ⟨Q, Emax P P.s, Emax P P.s - min (p - r) P.VS, P.s, ⟨hQ, by linarith, hS.2.2.1.le,
        by linarith, by linarith, sub_self _⟩, rfl⟩)
    unfold profitU profitT
    rw [sub_sub_cancel, show Nf P (min (p - r) P.VS) = Nf P (p - r) by unfold Nf; rw [GSf_min P hS]]
    apply profit_strict P hS (Nf_pos P hS _) hQ'
    rw [Mu_eq]; unfold Mt; rw [sub_sub_cancel, renter_min P hS]
    have hb := benchmark_proof P hS r hr0 hr
    have : honestMargin P p r ≤ honestMargin P (Emax P r) r := by
      unfold honestMargin; linarith
    nlinarith [hS.2.1]
  · subst hQ'
    unfold profitU profit
    rw [zero_div, expSales_zero P hS]
    simpa using PiT_pos P hS


/-! ### continuity -/

lemma Emax_lip (hS : Standing P) : LipschitzWith 1 (Emax P) := by
  have := probL P hS
  refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  unfold Emax
  rw [← integral_sub (integrable_max P hS a) (integrable_max P hS b)]
  have := norm_integral_le_of_norm_le_const (μ := P.νL) (C := |a - b|)
    (f := fun u => max u a - max u b) (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, max_comm u a, max_comm u b]; exact abs_max_sub_max_le_abs a b u)
  simpa using this

lemma expSales_lip (hS : Standing P) : LipschitzWith 1 (SupplyChainTheory.expSales P.D) := by
  have := probD P hS
  refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  unfold SupplyChainTheory.expSales
  rw [← integral_sub (integrable_min P hS a) (integrable_min P hS b)]
  have := norm_integral_le_of_norm_le_const (μ := P.D) (C := |a - b|)
    (f := fun u => min a u - min b u) (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]
      have := abs_min_sub_min_le_max a u b u
      simpa using this)
  simpa using this

lemma cdf_continuous (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ∀ x, ν {x} = 0) :
    Continuous (ProbabilityTheory.cdf ν) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hm := ProbabilityTheory.monotone_cdf ν
  rw [hm.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h1 := (ProbabilityTheory.cdf ν).measure_singleton x
  rw [ProbabilityTheory.measure_cdf, h x] at h1
  have h2 := hm.leftLim_le (le_refl x)
  have h3 : ProbabilityTheory.cdf ν x - Function.leftLim (ProbabilityTheory.cdf ν) x ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp h1.symm
  linarith

lemma Iio_eq_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ∀ x, ν {x} = 0) (r : ℝ) :
    (ν (Set.Iio r)).toReal = ProbabilityTheory.cdf ν r := by
  have : NullSingletonClass ν := ⟨h⟩
  rw [ProbabilityTheory.cdf_eq_real, Measure.real, measure_congr Iio_ae_eq_Iic]


lemma GLf_cont (hS : Standing P) : Continuous (GLf P) := by
  have := probL P hS
  have : GLf P = ProbabilityTheory.cdf P.νL := funext fun r => Iio_eq_cdf _ (noAtom_L P hS) r
  rw [this]; exact cdf_continuous _ (noAtom_L P hS)

lemma GSf_cont (hS : Standing P) : Continuous (GSf P) := by
  have := probS P hS
  have : GSf P = ProbabilityTheory.cdf P.νS := funext fun r => Iio_eq_cdf _ (noAtom_S P hS) r
  rw [this]; exact cdf_continuous _ (noAtom_S P hS)

lemma profitU_cont (hS : Standing P) :
    Continuous (fun x : ℝ × ℝ × ℝ =>
      profitU P x.1 (x.2.1 + x.2.2 * (Emax P x.2.1 - x.2.1)) x.2.1) := by
  have hE := (Emax_lip P hS).continuous
  have hL := GLf_cont P hS
  have hG := GSf_cont P hS
  have hSa := (expSales_lip P hS).continuous
  have hN : Continuous (fun x : ℝ × ℝ × ℝ =>
      Nf P (x.2.1 + x.2.2 * (Emax P x.2.1 - x.2.1) - x.2.1)) := by
    unfold Nf; fun_prop
  have hQN : Continuous (fun x : ℝ × ℝ × ℝ =>
      x.1 / Nf P (x.2.1 + x.2.2 * (Emax P x.2.1 - x.2.1) - x.2.1)) :=
    continuous_fst.div hN (fun x => (Nf_pos P hS _).ne')
  unfold profitU profit Mu
  have := hSa.comp hQN
  simp only [Function.comp_def] at this
  unfold Nf at this ⊢
  fun_prop

lemma profit_le' (hS : Standing P) {M N Q B : ℝ} (hN : 0 < N) (hQ : 0 ≤ Q) (hB : 0 ≤ B)
    (hM : M ≤ B) : profit P M N Q ≤ B * ∫ d, d ∂P.D - (P.c - P.s) * Q := by
  unfold profit
  have h1 := expSales_nonneg P hS (div_nonneg hQ hN.le)
  have h2 := expSales_le_mean P hS (Q / N)
  nlinarith [mul_le_mul_of_nonneg_right hM h1, mul_le_mul_of_nonneg_left h2 hB]

lemma Emax_eq_of_ge (hS : Standing P) {r : ℝ} (hr : P.VL ≤ r) : Emax P r = r := by
  have := probL P hS
  apply le_antisymm _ (Emax_ge P hS r)
  have : Emax P r ≤ ∫ _u, r ∂P.νL := by
    apply integral_mono_ae (integrable_max P hS r) (integrable_const _)
    filter_upwards [ae_L P hS] with u hu
    exact max_le (hu.2.trans hr) le_rfl
  simpa using this

theorem uniform_optimum_exists_proof (hS : Standing P) : ∃ Q p r, IsOptU P Q p r := by
  set B := P.VS + 3 * P.VL
  have hB := bound_nonneg P hS
  have hcs : 0 < P.c - P.s := by linarith [hS.2.2.2.1]
  set Qm := B * (∫ d, d ∂P.D) / (P.c - P.s)
  have hQm : 0 ≤ Qm := div_nonneg (mul_nonneg hB (mean_nonneg P hS)) hcs.le
  set K : Set (ℝ × ℝ × ℝ) := Set.Icc 0 Qm ×ˢ (Set.Icc 0 P.VL ×ˢ Set.Icc 0 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hVL := hS.2.2.2.2.1
  have h0K : ((0:ℝ), (0:ℝ), (0:ℝ)) ∈ K := ⟨⟨le_rfl, hQm⟩, ⟨le_rfl, hVL.le⟩, ⟨le_rfl, zero_le_one⟩⟩
  obtain ⟨x, hxK, hmax⟩ := hK.exists_isMaxOn ⟨_, h0K⟩ (profitU_cont P hS).continuousOn
  obtain ⟨⟨hQ0, hQ1⟩, ⟨hr0, hr1⟩, ⟨ht0, ht1⟩⟩ := hxK
  have hd := Emax_ge P hS x.2.1
  have hF0 : profitU P 0 (0 + 0 * (Emax P 0 - 0)) 0 = 0 := by
    unfold profitU profit; rw [zero_div, expSales_zero P hS]; ring
  have hge0 : 0 ≤ profitU P x.1 (x.2.1 + x.2.2 * (Emax P x.2.1 - x.2.1)) x.2.1 := by
    have := hmax h0K; simp only [Set.mem_setOf_eq] at this; rw [hF0] at this; exact this
  refine ⟨x.1, x.2.1 + x.2.2 * (Emax P x.2.1 - x.2.1), x.2.1,
    ⟨hQ0, hr0, by nlinarith, by nlinarith⟩, ?_⟩
  intro Q p r ⟨hQ, hr, hrp, hp⟩
  -- the bound on the uniform margin
  have hMu : Mu P p r ≤ B := by
    rw [Mu_eq]
    have h1 := Emax_sub_le P hS hr
    have h2 := Emax_le P hS (le_refl (0:ℝ))
    exact Mt_le P hS (by linarith) (by linarith [hS.2.2.2.2.2.1]) hr hp
  by_cases hQm' : Qm < Q
  · refine le_trans ?_ hge0
    have := profit_le' P hS (Nf_pos P hS (p - r)) hQ hB hMu
    have h3 : B * ∫ d, d ∂P.D = (P.c - P.s) * Qm := by
      simp only [Qm]; field_simp
    unfold profitU; nlinarith
  push_neg at hQm'
  by_cases hrV : P.VL < r
  · refine le_trans ?_ hge0
    have hpr : p = r := le_antisymm (hp.trans (Emax_eq_of_ge P hS hrV.le).le) hrp
    subst hpr
    unfold profitU profit Mu; rw [GLf_eq_one P hS hrV]
    have := expSales_nonneg P hS (div_nonneg hQ (Nf_pos P hS (p - p)).le)
    simp; nlinarith
  push_neg at hrV
  have hdr := Emax_ge P hS r
  rcases (sub_nonneg.mpr hdr).lt_or_eq with hpos | hzero
  · set t := (p - r) / (Emax P r - r)
    have ht : r + t * (Emax P r - r) = p := by simp only [t]; field_simp; ring
    have := @hmax (Q, r, t) ⟨⟨hQ, hQm'⟩, ⟨hr, hrV⟩, ⟨div_nonneg (by linarith) hpos.le,
      (div_le_one hpos).mpr (by linarith)⟩⟩
    simp only [Set.mem_setOf_eq] at this
    rw [ht] at this; exact this
  · have hpr : p = r := by linarith
    have := @hmax (Q, r, 0) ⟨⟨hQ, hQm'⟩, ⟨hr, hrV⟩, ⟨le_rfl, zero_le_one⟩⟩
    simp only [Set.mem_setOf_eq, zero_mul, add_zero] at this
    rw [hpr]; exact this


lemma GLf_mono (hS : Standing P) {a b : ℝ} (h : a ≤ b) : GLf P a ≤ GLf P b := by
  have := probL P hS
  unfold GLf
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iio_subset_Iio h))

/-! ### derivative of `E max{u, r}` -/

lemma pt_bound (u r h : ℝ) :
    |max u (r + h) - max u r - h * (Set.Iio r).indicator 1 u| ≤
      |h| * (Set.Ico (min r (r + h)) (max r (r + h))).indicator 1 u := by
  rcases le_total 0 h with h0 | h0
  · have e1 : min r (r + h) = r := min_eq_left (by linarith)
    have e2 : max r (r + h) = r + h := max_eq_right (by linarith)
    rw [abs_of_nonneg h0, e1, e2]
    rcases lt_or_ge u r with h1 | h1
    · have m1 : u ∉ Set.Ico r (r + h) := fun hm => absurd hm.1 (not_le.mpr h1)
      rw [max_eq_right (by linarith : u ≤ r + h), max_eq_right h1.le,
        Set.indicator_of_mem (Set.mem_Iio.mpr h1), Set.indicator_of_notMem m1]
      simp
    · have m0 : u ∉ Set.Iio r := not_lt.mpr h1
      rcases lt_or_ge u (r + h) with h2 | h2
      · rw [max_eq_right h2.le, max_eq_left h1, Set.indicator_of_notMem m0,
          Set.indicator_of_mem (Set.mem_Ico.mpr ⟨h1, h2⟩)]
        simp only [Pi.one_apply, mul_zero, mul_one, sub_zero]
        rw [abs_le]; constructor <;> linarith
      · have m1 : u ∉ Set.Ico r (r + h) := fun hm => absurd hm.2 (not_lt.mpr h2)
        rw [max_eq_left h2, max_eq_left h1, Set.indicator_of_notMem m0, Set.indicator_of_notMem m1]
        simp
  · have e1 : min r (r + h) = r + h := min_eq_right (by linarith)
    have e2 : max r (r + h) = r := max_eq_left (by linarith)
    rw [abs_of_nonpos h0, e1, e2]
    rcases lt_or_ge u (r + h) with h1 | h1
    · have m1 : u ∉ Set.Ico (r + h) r := fun hm => absurd hm.1 (not_le.mpr h1)
      have hu : u < r := by linarith
      rw [max_eq_right h1.le, max_eq_right hu.le,
        Set.indicator_of_mem (Set.mem_Iio.mpr hu), Set.indicator_of_notMem m1]
      simp
    · rcases lt_or_ge u r with h2 | h2
      · rw [max_eq_left h1, max_eq_right h2.le, Set.indicator_of_mem (Set.mem_Iio.mpr h2),
          Set.indicator_of_mem (Set.mem_Ico.mpr ⟨h1, h2⟩)]
        simp only [Pi.one_apply, mul_one]
        rw [abs_le]; constructor <;> linarith
      · have m0 : u ∉ Set.Iio r := not_lt.mpr h2
        have m1 : u ∉ Set.Ico (r + h) r := fun hm => absurd hm.2 (not_lt.mpr h2)
        rw [max_eq_left h1, max_eq_left h2, Set.indicator_of_notMem m0, Set.indicator_of_notMem m1]
        simp

lemma Ico_meas (hS : Standing P) {a b : ℝ} (hab : a ≤ b) :
    P.νL.real (Set.Ico a b) = GLf P b - GLf P a := by
  have := probL P hS
  have hset : Set.Ico a b = Set.Iio b \ Set.Iio a := by
    ext x; simp only [Set.mem_Ico, Set.mem_diff, Set.mem_Iio, not_lt]; tauto
  rw [hset, Measure.real, measure_diff (Set.Iio_subset_Iio hab)
    measurableSet_Iio.nullMeasurableSet (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le (measure_mono (Set.Iio_subset_Iio hab)) (measure_ne_top _ _)]
  rfl

theorem Emax_hasDerivAt (hS : Standing P) (r : ℝ) : HasDerivAt (Emax P) (GLf P r) r := by
  have := probL P hS
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hGc := (GLf_cont P hS).continuousAt (x := r)
  refine Asymptotics.IsLittleO.of_bound (fun c hc => ?_)
  have hev : ∀ᶠ h in nhds (0:ℝ), |GLf P (r + h) - GLf P r| ≤ c := by
    have : Filter.Tendsto (fun h => GLf P (r + h)) (nhds 0) (nhds (GLf P r)) := by
      have := hGc.tendsto.comp ((continuous_add_left r).tendsto' (0:ℝ) r (by simp))
      simpa [Function.comp_def] using this
    have := (Metric.tendsto_nhds.mp this) c hc
    filter_upwards [this] with h hh; rw [Real.dist_eq] at hh; exact hh.le
  filter_upwards [hev] with h hh
  have hint : Integrable (fun u => max u (r + h) - max u r - h * (Set.Iio r).indicator (1 : ℝ → ℝ) u) P.νL :=
    ((integrable_max P hS _).sub (integrable_max P hS _)).sub
      (((integrable_const (1:ℝ)).indicator measurableSet_Iio).const_mul _)
  have heq : Emax P (r + h) - Emax P r - h • GLf P r =
      ∫ u, (max u (r + h) - max u r - h * (Set.Iio r).indicator (1 : ℝ → ℝ) u) ∂P.νL := by
    have hA : Integrable (fun u => max u (r + h) - max u r) P.νL :=
      (integrable_max P hS _).sub (integrable_max P hS _)
    have hB : Integrable (fun u => h * (Set.Iio r).indicator (1 : ℝ → ℝ) u) P.νL :=
      ((integrable_const (1:ℝ)).indicator measurableSet_Iio).const_mul _
    have e1 : ∫ u, (max u (r + h) - max u r - h * (Set.Iio r).indicator (1 : ℝ → ℝ) u) ∂P.νL =
        (∫ u, (max u (r + h) - max u r) ∂P.νL) - ∫ u, h * (Set.Iio r).indicator (1 : ℝ → ℝ) u ∂P.νL :=
      integral_sub hA hB
    have e2 : ∫ u, (max u (r + h) - max u r) ∂P.νL = Emax P (r + h) - Emax P r :=
      integral_sub (integrable_max P hS _) (integrable_max P hS _)
    have e3 : ∫ u, h * (Set.Iio r).indicator (1 : ℝ → ℝ) u ∂P.νL = h * GLf P r := by
      rw [integral_const_mul, integral_indicator_one measurableSet_Iio]; rfl
    rw [e1, e2, e3, smul_eq_mul]
  rw [heq]
  have hI : Integrable (fun u => |h| * (Set.Ico (min r (r + h)) (max r (r + h))).indicator (1 : ℝ → ℝ) u) P.νL :=
    ((integrable_const (1:ℝ)).indicator measurableSet_Ico).const_mul _
  refine (norm_integral_le_of_norm_le hI (Filter.Eventually.of_forall fun u => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact pt_bound u r h
  rw [integral_const_mul, integral_indicator_one measurableSet_Ico,
    Ico_meas P hS (min_le_max)]
  rw [Real.norm_eq_abs]
  have : GLf P (max r (r + h)) - GLf P (min r (r + h)) = |GLf P (r + h) - GLf P r| := by
    rcases le_total 0 h with h0 | h0
    · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      rw [abs_of_nonneg]; linarith [(GLf_mono P hS (by linarith : r ≤ r + h))]
    · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      rw [abs_of_nonpos]; · ring
      linarith [(GLf_mono P hS (by linarith : r + h ≤ r))]
  rw [this]
  nlinarith [abs_nonneg h, abs_nonneg (GLf P (r + h) - GLf P r)]


theorem eq_5b_proof (hS : Standing P) :
    ∀ r ∈ Set.Icc 0 P.VL, Emax P r = P.VL - ∫ u in r..P.VL, GLf P u := by
  intro r _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => Emax_hasDerivAt P hS x)
    ((GLf_cont P hS).intervalIntegrable _ _), Emax_eq_of_ge P hS le_rfl]
  ring

theorem lemma_1_proof (hS : Standing P) :
    ∀ r ∈ Set.Ioo 0 P.VL, ∃ d : ℝ, HasDerivAt (Emax P) d r ∧ 0 < d ∧ d ≤ 1 ∧
      HasDerivAt (fun x => Emax P x - x) (d - 1) r ∧ d - 1 < 0 := by
  intro r ⟨hr0, hrV⟩
  have := probL P hS
  have hfs := hS.2.2.2.2.2.2.2.2.2.1.2
  have hd := Emax_hasDerivAt P hS r
  refine ⟨GLf P r, hd, ?_, GLf_le_one P hS r, hd.sub (hasDerivAt_id r), ?_⟩
  · unfold GLf
    have h1 := hfs 0 r le_rfl hr0 hrV.le
    exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le h1 (measure_mono Set.Ioo_subset_Iio_self)))
      (measure_ne_top _ _)
  · have h1 := hfs r P.VL hr0.le hrV le_rfl
    have hdisj : Disjoint (Set.Iio r) (Set.Ioo r P.VL) :=
      Set.disjoint_left.mpr fun x hx hy => absurd hx (not_lt.mpr hy.1.le)
    have hsum : P.νL (Set.Iio r) + P.νL (Set.Ioo r P.VL) ≤ 1 := by
      rw [← measure_union hdisj measurableSet_Ioo]; exact prob_le_one
    have hlt : P.νL (Set.Iio r) < 1 := by
      have hne : P.νL (Set.Iio r) ≠ ⊤ := measure_ne_top _ _
      calc P.νL (Set.Iio r) < P.νL (Set.Iio r) + P.νL (Set.Ioo r P.VL) :=
            ENNReal.lt_add_right hne (ne_of_gt h1)
        _ ≤ 1 := hsum
    have : GLf P r < 1 := by
      unfold GLf
      have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hlt
      simpa using this
    linarith

end OppAux

open OppReturns.Menu in
theorem solution (P : Params) (hS : Standing P) :
    ∀ r ∈ Set.Ioo 0 P.VL, ∃ d : ℝ, HasDerivAt (Emax P) d r ∧ 0 < d ∧ d ≤ 1 ∧
      HasDerivAt (fun x => Emax P x - x) (d - 1) r ∧ d - 1 < 0 :=
  OppAux.lemma_1_proof P hS
