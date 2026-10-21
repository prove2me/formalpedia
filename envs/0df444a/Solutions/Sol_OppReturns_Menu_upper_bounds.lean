-- Prove2me | solution 1 for OppReturns.Menu.upper_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T08:05:12.617268+00:00
-- url     : https://prove2.me/submissions/365a7deb-8b2f-4ab5-988d-f92b7e8d65fa

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

end OppAux

open OppReturns.Menu in
theorem solution (P : Params) (hS : Standing P) :
    BddAbove {π | ∃ Q p r, FeasU P Q p r ∧ π = profitU P Q p r} ∧
    BddAbove {π | ∃ Q p rR rH, FeasT P Q p rR rH ∧ π = profitT P Q p rR rH} ∧
    BddAbove {π | ∃ Q pH rH pR rR, FeasM P Q pH rH pR rR ∧ π = profitM P Q pH rH pR rR} ∧
    PiM P ≤ PiT P ∧ PiU P ≤ PiT P :=
  OppAux.upper_bounds_proof P hS
