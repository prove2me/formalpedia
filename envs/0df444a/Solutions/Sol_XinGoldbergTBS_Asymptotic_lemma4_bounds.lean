-- Prove2me | solution 1 for XinGoldbergTBS.Asymptotic.lemma4_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T13:28:30.13823+00:00
-- url     : https://prove2.me/submissions/3c52cad5-092b-4361-b061-c168dcff66dd

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_SingleSource

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XGLB

open XinGoldbergTBS.Asymptotic

instance pathLaw_isProb (μ : DemandLaw) : IsProbabilityMeasure (pathLaw μ) := by
  unfold pathLaw; infer_instance

/-! ## The cost function `G` -/

lemma continuous_G (κ : Costs) : Continuous (G κ) := by
  unfold G
  exact (continuous_const.mul (continuous_id.max continuous_const)).add
    (continuous_const.mul (continuous_neg.max continuous_const))

lemma G_nonneg (κ : Costs) (z : ℝ) : 0 ≤ G κ z := by
  unfold G
  have := κ.h_pos; have := κ.b_pos
  have h1 : 0 ≤ max z 0 := le_max_right _ _
  have h2 : 0 ≤ max (-z) 0 := le_max_right _ _
  positivity

lemma G_le (κ : Costs) (z : ℝ) : G κ z ≤ max κ.b κ.h * |z| := by
  unfold G
  have hb := le_max_left κ.b κ.h
  have hh := le_max_right κ.b κ.h
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (by linarith : -z ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (by linarith : 0 ≤ -z)]
    nlinarith

lemma G_ge (κ : Costs) (z : ℝ) : min κ.b κ.h * |z| ≤ G κ z := by
  unfold G
  have hb := min_le_left κ.b κ.h
  have hh := min_le_right κ.b κ.h
  have hm : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (by linarith : -z ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (by linarith : 0 ≤ -z)]
    nlinarith

lemma G_convex (κ : Costs) (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    G κ (a * u + b * v) ≤ a * G κ u + b * G κ v := by
  unfold G
  have h1 : max (a * u + b * v) 0 ≤ a * max u 0 + b * max v 0 := by
    apply max_le
    · nlinarith [le_max_left u 0, le_max_left v 0]
    · nlinarith [le_max_right u 0, le_max_right v 0]
  have h2 : max (-(a * u + b * v)) 0 ≤ a * max (-u) 0 + b * max (-v) 0 := by
    apply max_le
    · nlinarith [le_max_left (-u) 0, le_max_left (-v) 0]
    · nlinarith [le_max_right (-u) 0, le_max_right (-v) 0]
  have := κ.h_pos; have := κ.b_pos
  nlinarith [mul_le_mul_of_nonneg_left h1 κ.h_pos.le, mul_le_mul_of_nonneg_left h2 κ.b_pos.le]

/-! ## The demand law -/

lemma ae_nonneg (μ : DemandLaw) : ∀ᵐ d ∂μ.law, 0 ≤ d := by
  have h := μ.nonneg
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with d hd
  simpa using hd

lemma mean_nonneg (μ : DemandLaw) : 0 ≤ μ.mean :=
  integral_nonneg_of_ae (ae_nonneg μ)

lemma mp_eval (μ : DemandLaw) (k : ℕ) :
    MeasurePreserving (fun x : Path => x k) (pathLaw μ) μ.law :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => μ.law) k

lemma path_ae_nonneg (μ : DemandLaw) : ∀ᵐ d ∂pathLaw μ, ∀ k, 0 ≤ d k := by
  rw [ae_all_iff]
  intro k
  have hmp := mp_eval μ k
  have h : ∀ᵐ y ∂(pathLaw μ).map (fun x : Path => x k), 0 ≤ y := by
    rw [hmp.map_eq]; exact ae_nonneg μ
  exact ae_of_ae_map hmp.measurable.aemeasurable h

lemma lintegral_law (μ : DemandLaw) :
    ∫⁻ y, ENNReal.ofReal y ∂μ.law = ENNReal.ofReal μ.mean := by
  rw [DemandLaw.mean]
  refine (ofReal_integral_eq_lintegral_ofReal (f := fun y : ℝ => y) μ.integrable ?_).symm
  filter_upwards [ae_nonneg μ] with y hy
  exact hy

lemma lintegral_coord (μ : DemandLaw) (k : ℕ) :
    ∫⁻ d, ENNReal.ofReal (d k) ∂pathLaw μ = ENNReal.ofReal μ.mean := by
  have h := (mp_eval μ k).lintegral_comp (f := fun y : ℝ => ENNReal.ofReal y)
    ENNReal.measurable_ofReal
  rw [show (∫⁻ d, ENNReal.ofReal (d k) ∂pathLaw μ) = ∫⁻ y, ENNReal.ofReal y ∂μ.law from h,
    lintegral_law]

/-- `𝔼|D_k - r| ≤ |r| + 𝔼D`. -/
lemma lintegral_abs_coord (μ : DemandLaw) (r : ℝ) (k : ℕ) :
    ∫⁻ d, ENNReal.ofReal |d k - r| ∂pathLaw μ ≤ ENNReal.ofReal (|r| + μ.mean) := by
  have hpt : ∀ᵐ d ∂pathLaw μ, ENNReal.ofReal |d k - r| ≤
      ENNReal.ofReal |r| + ENNReal.ofReal (d k) := by
    filter_upwards [path_ae_nonneg μ] with d hd
    rw [← ENNReal.ofReal_add (abs_nonneg _) (hd k)]
    apply ENNReal.ofReal_le_ofReal
    have := hd k
    rw [abs_le]; constructor <;> [linarith [neg_abs_le r, le_abs_self r];
      linarith [neg_abs_le r, le_abs_self r]]
  calc ∫⁻ d, ENNReal.ofReal |d k - r| ∂pathLaw μ
      ≤ ∫⁻ d, (ENNReal.ofReal |r| + ENNReal.ofReal (d k)) ∂pathLaw μ := lintegral_mono_ae hpt
    _ = ENNReal.ofReal |r| + ENNReal.ofReal μ.mean := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_coord]
    _ = ENNReal.ofReal (|r| + μ.mean) := (ENNReal.ofReal_add (abs_nonneg _) (mean_nonneg μ)).symm

/-- `𝔼 ∑_{k<N} |D_{m+k} - r| ≤ N (|r| + 𝔼D)`. -/
lemma lintegral_sum_abs (μ : DemandLaw) (r : ℝ) (N : ℕ) (f : ℕ → ℕ) :
    ∫⁻ d, ENNReal.ofReal (∑ k ∈ Finset.range N, |d (f k) - r|) ∂pathLaw μ ≤
      ENNReal.ofReal (N * (|r| + μ.mean)) := by
  have hm : ∀ k, Measurable (fun d : Path => ENNReal.ofReal |d (f k) - r|) := fun k =>
    ((measurable_pi_apply (f k)).sub measurable_const).abs.ennreal_ofReal
  calc ∫⁻ d, ENNReal.ofReal (∑ k ∈ Finset.range N, |d (f k) - r|) ∂pathLaw μ
      = ∫⁻ d, ∑ k ∈ Finset.range N, ENNReal.ofReal |d (f k) - r| ∂pathLaw μ := by
        congr 1; funext d
        exact ENNReal.ofReal_sum_of_nonneg (fun k _ => abs_nonneg _)
    _ = ∑ k ∈ Finset.range N, ∫⁻ d, ENNReal.ofReal |d (f k) - r| ∂pathLaw μ :=
        lintegral_finsetSum _ (fun k _ => hm k)
    _ ≤ ∑ k ∈ Finset.range N, ENNReal.ofReal (|r| + μ.mean) :=
        Finset.sum_le_sum fun k _ => lintegral_abs_coord μ r (f k)
    _ = ENNReal.ofReal (N * (|r| + μ.mean)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-! ## Splitting off the first demand -/

def consP (a : ℝ) (d : Path) : Path := fun n => Nat.casesOn n a (fun k => d k)

def sh (d : Path) : Path := fun n => d (n + 1)

@[simp] lemma consP_zero (a : ℝ) (d : Path) : consP a d 0 = a := rfl
@[simp] lemma consP_succ (a : ℝ) (d : Path) (n : ℕ) : consP a d (n + 1) = d n := rfl
@[simp] lemma sh_consP (a : ℝ) (d : Path) : sh (consP a d) = d := rfl

lemma measurable_consP : Measurable (fun p : ℝ × Path => consP p.1 p.2) := by
  refine measurable_pi_lambda _ fun n => ?_
  cases n with
  | zero => exact measurable_fst
  | succ k => exact (measurable_pi_apply k).comp measurable_snd

lemma measurable_sh : Measurable sh :=
  measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1)

lemma mp_cons (μ : DemandLaw) :
    MeasurePreserving (fun p : ℝ × Path => consP p.1 p.2) (μ.law.prod (pathLaw μ))
      (pathLaw μ) := by
  refine ⟨measurable_consP, ?_⟩
  conv_rhs => rw [pathLaw]
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  obtain ⟨N, hN⟩ : ∃ N, s ⊆ Finset.range (N + 1) := by
    refine ⟨s.sup id, fun i hi => ?_⟩
    rw [Finset.mem_range]
    have := Finset.le_sup (f := id) hi
    simp only [id] at this
    omega
  set T : ℕ → Set ℝ := fun n => if n ∈ s then t n else Set.univ with hTdef
  have hTm : ∀ n, MeasurableSet (T n) := by
    intro n; simp only [hTdef]; split_ifs
    · exact ht n
    · exact MeasurableSet.univ
  have hpi : Set.pi (↑s) t = Set.pi (↑(Finset.range (N + 1))) T := by
    ext p
    simp only [Set.mem_pi, Finset.mem_coe, hTdef]
    constructor
    · intro h i _
      split_ifs with his
      · exact h i his
      · exact Set.mem_univ _
    · intro h i hi
      have := h i (hN hi)
      simpa [hi] using this
  have hpre : (fun p : ℝ × Path => consP p.1 p.2) ⁻¹' Set.pi (↑(Finset.range (N + 1))) T =
      T 0 ×ˢ Set.pi (↑(Finset.range N)) (fun k => T (k + 1)) := by
    ext ⟨a, d⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_range, Set.mem_Iio, Set.mem_prod]
    constructor
    · intro h
      exact ⟨h 0 (by omega), fun k hk => h (k + 1) (by omega)⟩
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => exact h0
      | succ k => exact h1 k (by omega)
  rw [Measure.map_apply measurable_consP (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)),
    hpi, hpre, Measure.prod_prod]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun n _ => hTm (n + 1))]
  have hsub : ∏ i ∈ Finset.range (N + 1), μ.law (T i) = ∏ i ∈ s, μ.law (t i) := by
    symm
    rw [← Finset.prod_subset hN]
    · exact Finset.prod_congr rfl fun i hi => by simp [hTdef, hi]
    · intro i _ hi
      simp [hTdef, hi]
  rw [← hsub, Finset.prod_range_succ', mul_comm]

lemma lintegral_cons (μ : DemandLaw) {F : Path → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ d, F d ∂pathLaw μ = ∫⁻ a, ∫⁻ d', F (consP a d') ∂pathLaw μ ∂μ.law := by
  rw [← (mp_cons μ).lintegral_comp hF]
  exact lintegral_prod (fun p : ℝ × Path => F (consP p.1 p.2))
    (hF.comp measurable_consP).aemeasurable

/-! ## Measurability of single-source quantities -/

lemma measurable_prefix (n : ℕ) : Measurable (fun d : Path => fun i : Fin n => d i) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply _

lemma measurable_ssOrder (π : SSPolicy) (n : ℕ) : Measurable (fun d : Path => ssOrder π d n) :=
  measurable_coe_nnreal_real.comp ((π.measurable_order n).comp (measurable_prefix n))

lemma measurable_ssPosition (π : SSPolicy) (r x : ℝ) (n : ℕ) :
    Measurable (fun d : Path => ssPosition π r x d n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [ssPosition]
    exact (ih.add (measurable_ssOrder π n)).sub ((measurable_pi_apply n).sub measurable_const)

lemma measurable_ssOrderUpTo (π : SSPolicy) (r x : ℝ) (n : ℕ) :
    Measurable (fun d : Path => ssOrderUpTo π r x d n) :=
  (measurable_ssPosition π r x n).add (measurable_ssOrder π n)

lemma measurable_wsum (r : ℝ) (L₀ n : ℕ) :
    Measurable (fun d : Path => ∑ k ∈ Finset.range (L₀ + 1), (d (n + k) - r)) :=
  Finset.measurable_sum _ fun k _ => (measurable_pi_apply _).sub measurable_const

lemma measurable_ssCost (κ : Costs) (L₀ : ℕ) (π : SSPolicy) (r x : ℝ) (n : ℕ) :
    Measurable (fun d : Path => ssCost κ L₀ π r x d n) :=
  ((continuous_G κ).measurable.comp
    ((measurable_ssOrderUpTo π r x n).sub (measurable_wsum r L₀ n))).ennreal_ofReal

lemma measurable_disc (κ : Costs) (L₀ : ℕ) (α : ℝ) (π : SSPolicy) (r x : ℝ) :
    Measurable (fun d : Path => ssDiscCost κ L₀ α π r x d) :=
  Measurable.ennreal_tsum fun i => (measurable_ssCost κ L₀ π r x i).const_mul _

/-! ## The first order and the tail policy -/

/-- The (constant) first order of `π`. -/
def u0 (π : SSPolicy) : ℝ := (π.order 0 (fun i => Fin.elim0 i) : ℝ)

lemma u0_nonneg (π : SSPolicy) : 0 ≤ u0 π := NNReal.coe_nonneg _

lemma ssOrder_zero (π : SSPolicy) (d : Path) : ssOrder π d 0 = u0 π := by
  unfold ssOrder u0
  congr 2
  funext i
  exact Fin.elim0 i

lemma measurable_finCons (n : ℕ) (a : ℝ) :
    Measurable (fun w : Fin n → ℝ => (Fin.cons a w : Fin (n + 1) → ℝ)) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact measurable_const
  · simp only [Fin.cons_succ]; exact measurable_pi_apply j

/-- The policy that `π` follows from period 1 on, after the first demand was `a`. -/
def tailPol (π : SSPolicy) (a : ℝ) : SSPolicy where
  order n w := π.order (n + 1) (Fin.cons a w)
  measurable_order n := (π.measurable_order (n + 1)).comp (measurable_finCons n a)

lemma ssOrder_tail (π : SSPolicy) (d : Path) (n : ℕ) :
    ssOrder π d (n + 1) = ssOrder (tailPol π (d 0)) (sh d) n := by
  unfold ssOrder tailPol
  simp only
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [sh]

lemma ssPosition_tail (π : SSPolicy) (r x : ℝ) (d : Path) (n : ℕ) :
    ssPosition π r x d (n + 1) =
      ssPosition (tailPol π (d 0)) r (x + u0 π - (d 0 - r)) (sh d) n := by
  induction n with
  | zero => simp only [ssPosition, ssOrder_zero]
  | succ n ih =>
    rw [ssPosition, ih, ssPosition, ssOrder_tail]
    rfl

lemma ssOrderUpTo_tail (π : SSPolicy) (r x : ℝ) (d : Path) (n : ℕ) :
    ssOrderUpTo π r x d (n + 1) =
      ssOrderUpTo (tailPol π (d 0)) r (x + u0 π - (d 0 - r)) (sh d) n := by
  unfold ssOrderUpTo
  rw [ssPosition_tail, ssOrder_tail]

lemma ssCost_tail (κ : Costs) (L₀ : ℕ) (π : SSPolicy) (r x : ℝ) (d : Path) (n : ℕ) :
    ssCost κ L₀ π r x d (n + 1) =
      ssCost κ L₀ (tailPol π (d 0)) r (x + u0 π - (d 0 - r)) (sh d) n := by
  unfold ssCost
  rw [ssOrderUpTo_tail]
  congr 3
  apply Finset.sum_congr rfl
  intro k _
  simp only [sh]
  congr 2
  omega

lemma ssOrderUpTo_zero (π : SSPolicy) (r x : ℝ) (d : Path) :
    ssOrderUpTo π r x d 0 = x + u0 π := by
  simp [ssOrderUpTo, ssPosition, ssOrder_zero]

/-! ## The one-period expected cost `ĝ` -/

/-- `ĝ(y) = 𝔼 G(y - ∑_{k ≤ L₀} (D_k - r))`. -/
def ghat (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r y : ℝ) : ℝ≥0∞ :=
  ∫⁻ d, ENNReal.ofReal (G κ (y - ∑ k ∈ Finset.range (L₀ + 1), (d k - r))) ∂pathLaw μ

lemma measurable_ghat (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r : ℝ) :
    Measurable (fun y => ghat μ κ L₀ r y) := by
  unfold ghat
  refine Measurable.lintegral_prod_right'
    (f := fun p : ℝ × Path => ENNReal.ofReal (G κ (p.1 - ∑ k ∈ Finset.range (L₀ + 1),
      (p.2 k - r)))) ?_
  refine ((continuous_G κ).measurable.comp (measurable_fst.sub ?_)).ennreal_ofReal
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply k).comp measurable_snd).sub measurable_const

lemma ssCost_zero_int (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (π : SSPolicy) (r x : ℝ) :
    ∫⁻ d, ssCost κ L₀ π r x d 0 ∂pathLaw μ = ghat μ κ L₀ r (x + u0 π) := by
  unfold ssCost ghat
  simp only [ssOrderUpTo_zero, zero_add]

/-- The expected period-`i` cost is `𝔼 ĝ(y_i)`. -/
lemma cost_eq_ghat (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r : ℝ) (i : ℕ) :
    ∀ (π : SSPolicy) (x : ℝ), ∫⁻ d, ssCost κ L₀ π r x d i ∂pathLaw μ =
      ∫⁻ d, ghat μ κ L₀ r (ssOrderUpTo π r x d i) ∂pathLaw μ := by
  induction i with
  | zero =>
    intro π x
    rw [ssCost_zero_int]
    simp only [ssOrderUpTo_zero, lintegral_const, measure_univ, mul_one]
  | succ i ih =>
    intro π x
    have hm : Measurable (fun d => ghat μ κ L₀ r (ssOrderUpTo π r x d (i + 1))) :=
      (measurable_ghat μ κ L₀ r).comp (measurable_ssOrderUpTo π r x (i + 1))
    rw [lintegral_cons μ (measurable_ssCost κ L₀ π r x (i + 1)), lintegral_cons μ hm]
    refine lintegral_congr fun a => ?_
    simp only [ssCost_tail, ssOrderUpTo_tail, consP_zero, sh_consP]
    exact ih _ _


/-! ## Policies ordering up to a nonanticipative target -/

/-- Position under "order up to `max(x_n, T_n)`". -/
def tpos (T : ℕ → Path → ℝ) (r x : ℝ) (d : Path) : ℕ → ℝ
  | 0 => x
  | n + 1 => max (tpos T r x d n) (T n d) - (d n - r)

lemma measurable_tpos (T : ℕ → Path → ℝ) (hT : ∀ n, Measurable (T n)) (r x : ℝ) (n : ℕ) :
    Measurable (fun d => tpos T r x d n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [tpos]
    exact (ih.max (hT n)).sub ((measurable_pi_apply n).sub measurable_const)

def pad (n : ℕ) (z : Fin n → ℝ) : Path := fun l => if h : l < n then z ⟨l, h⟩ else 0

lemma measurable_pad (n : ℕ) : Measurable (pad n) := by
  refine measurable_pi_lambda _ fun l => ?_
  by_cases h : l < n
  · simp only [pad, h, dif_pos]; exact measurable_pi_apply _
  · simp only [pad, h, dif_neg, not_false_eq_true]; exact measurable_const

lemma pad_prefix (n : ℕ) (d : Path) : ∀ j < n, pad n (fun i : Fin n => d i) j = d j := by
  intro j hj; simp [pad, hj]

def NonAnt (T : ℕ → Path → ℝ) : Prop := ∀ n (d d' : Path), (∀ j < n, d j = d' j) → T n d = T n d'

lemma tpos_local (T : ℕ → Path → ℝ) (hN : NonAnt T) (r x : ℝ) :
    ∀ n (d d' : Path), (∀ j < n, d j = d' j) → tpos T r x d n = tpos T r x d' n := by
  intro n
  induction n with
  | zero => intro d d' _; rfl
  | succ n ih =>
    intro d d' h
    simp only [tpos]
    rw [ih d d' (fun j hj => h j (by omega)), hN n d d' (fun j hj => h j (by omega)),
      h n (by omega)]

def tPol (T : ℕ → Path → ℝ) (hT : ∀ n, Measurable (T n)) (r x : ℝ) : SSPolicy where
  order n w := (T n (pad n w) - tpos T r x (pad n w) n).toNNReal
  measurable_order n := (((hT n).comp (measurable_pad n)).sub
    ((measurable_tpos T hT r x n).comp (measurable_pad n))).real_toNNReal

lemma tPol_order (T : ℕ → Path → ℝ) (hT : ∀ n, Measurable (T n)) (hN : NonAnt T) (r x : ℝ)
    (d : Path) (n : ℕ) :
    ssOrder (tPol T hT r x) d n = ((T n d - tpos T r x d n).toNNReal : ℝ) := by
  unfold ssOrder tPol
  simp only
  rw [hN n _ d (pad_prefix n d), tpos_local T hN r x n _ d (pad_prefix n d)]

lemma tPol_pos (T : ℕ → Path → ℝ) (hT : ∀ n, Measurable (T n)) (hN : NonAnt T) (r x : ℝ)
    (d : Path) (n : ℕ) : ssPosition (tPol T hT r x) r x d n = tpos T r x d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ssPosition, ih, tPol_order T hT hN, tpos, Real.coe_toNNReal']
    rcases le_total (T n d) (tpos T r x d n) with h | h
    · rw [max_eq_right (by linarith : T n d - tpos T r x d n ≤ 0), max_eq_left h]; ring
    · rw [max_eq_left (by linarith : 0 ≤ T n d - tpos T r x d n), max_eq_right h]; ring

lemma tPol_upTo (T : ℕ → Path → ℝ) (hT : ∀ n, Measurable (T n)) (hN : NonAnt T) (r x : ℝ)
    (d : Path) (n : ℕ) :
    ssOrderUpTo (tPol T hT r x) r x d n = max (tpos T r x d n) (T n d) := by
  unfold ssOrderUpTo
  rw [tPol_pos T hT hN, tPol_order T hT hN, Real.coe_toNNReal']
  rcases le_total (T n d) (tpos T r x d n) with h | h
  · rw [max_eq_right (by linarith : T n d - tpos T r x d n ≤ 0), max_eq_left h]; ring
  · rw [max_eq_left (by linarith : 0 ≤ T n d - tpos T r x d n), max_eq_right h]; ring

/-- `∑_{k<n} |D_k - r|`. -/
def asum (r : ℝ) (d : Path) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, |d k - r|

lemma asum_nonneg (r : ℝ) (d : Path) (n : ℕ) : 0 ≤ asum r d n :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma asum_succ (r : ℝ) (d : Path) (n : ℕ) : asum r d (n + 1) = asum r d n + |d n - r| := by
  simp [asum, Finset.sum_range_succ]

lemma tpos_bounds (T : ℕ → Path → ℝ) (r x B : ℝ)
    (hT : ∀ n d, T n d ≤ max x B + asum r d n) (d : Path) (n : ℕ) :
    x - asum r d n ≤ tpos T r x d n ∧ tpos T r x d n ≤ max x B + asum r d n := by
  induction n with
  | zero => simp [tpos, asum]
  | succ n ih =>
    simp only [tpos, asum_succ]
    have h1 := neg_abs_le (d n - r)
    have h2 := le_abs_self (d n - r)
    have hm1 := le_max_left (tpos T r x d n) (T n d)
    have hm2 : max (tpos T r x d n) (T n d) ≤ max x B + asum r d n := max_le ih.2 (hT n d)
    constructor <;> linarith [ih.1]

lemma upTo_abs_le (T : ℕ → Path → ℝ) (r x B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ n d, T n d ≤ max x B + asum r d n) (d : Path) (n : ℕ) :
    |max (tpos T r x d n) (T n d)| ≤ |x| + B + asum r d n := by
  have hb := tpos_bounds T r x B hT d n
  have hm1 := le_max_left (tpos T r x d n) (T n d)
  have hm2 : max (tpos T r x d n) (T n d) ≤ max x B + asum r d n := max_le hb.2 (hT n d)
  have hx1 := le_abs_self x
  have hx2 := neg_abs_le x
  have hmx : max x B ≤ |x| + B := max_le (by linarith) (by linarith [abs_nonneg x])
  have := asum_nonneg r d n
  rw [abs_le]; constructor <;> linarith [hb.1]

/-! ## Cost bounds from linear growth -/

lemma cost_le_growth (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (π : SSPolicy) (r x A : ℝ)
    (hA0 : 0 ≤ A) (i : ℕ) (hA : ∀ d, |ssOrderUpTo π r x d i| ≤ A + asum r d i) :
    ∫⁻ d, ssCost κ L₀ π r x d i ∂pathLaw μ ≤
      ENNReal.ofReal (max κ.b κ.h * (A + ((i : ℝ) + L₀ + 1) * (|r| + μ.mean))) := by
  set M := max κ.b κ.h with hMdef
  have hM : 0 ≤ M := le_trans κ.b_pos.le (le_max_left _ _)
  have hpt : ∀ d, ssCost κ L₀ π r x d i ≤ ENNReal.ofReal (M * A) +
      ENNReal.ofReal M * ENNReal.ofReal (∑ k ∈ Finset.range (i + (L₀ + 1)), |d (id k) - r|) := by
    intro d
    rw [← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_add (mul_nonneg hM hA0)
      (mul_nonneg hM (Finset.sum_nonneg fun _ _ => abs_nonneg _))]
    unfold ssCost
    apply ENNReal.ofReal_le_ofReal
    refine (G_le κ _).trans ?_
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ hM
    have hs := Finset.sum_range_add (fun k => |d (id k) - r|) i (L₀ + 1)
    beta_reduce at hs
    rw [hs]
    have h1 := hA d
    have h2 : |∑ k ∈ Finset.range (L₀ + 1), (d (i + k) - r)| ≤
        ∑ k ∈ Finset.range (L₀ + 1), |d (i + k) - r| := Finset.abs_sum_le_sum_abs _ _
    have h3 := abs_sub (ssOrderUpTo π r x d i) (∑ k ∈ Finset.range (L₀ + 1), (d (i + k) - r))
    simp only [id, asum] at h1 ⊢
    linarith
  have hmeas : Measurable (fun d : Path =>
      ENNReal.ofReal (∑ k ∈ Finset.range (i + (L₀ + 1)), |d (id k) - r|)) := by
    apply Measurable.ennreal_ofReal
    exact Finset.measurable_sum _ fun k _ => by fun_prop
  calc ∫⁻ d, ssCost κ L₀ π r x d i ∂pathLaw μ
      ≤ ∫⁻ d, (ENNReal.ofReal (M * A) + ENNReal.ofReal M *
          ENNReal.ofReal (∑ k ∈ Finset.range (i + (L₀ + 1)), |d (id k) - r|)) ∂pathLaw μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (M * A) + ENNReal.ofReal M *
          ∫⁻ d, ENNReal.ofReal (∑ k ∈ Finset.range (i + (L₀ + 1)), |d (id k) - r|) ∂pathLaw μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ hmeas]
    _ ≤ ENNReal.ofReal (M * A) + ENNReal.ofReal M *
          ENNReal.ofReal (((i + (L₀ + 1) : ℕ) : ℝ) * (|r| + μ.mean)) := by
        gcongr
        exact lintegral_sum_abs μ r _ id
    _ = ENNReal.ofReal (M * (A + ((i : ℝ) + L₀ + 1) * (|r| + μ.mean))) := by
        have hc : 0 ≤ |r| + μ.mean := add_nonneg (abs_nonneg _) (mean_nonneg μ)
        rw [← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_add (mul_nonneg hM hA0)
          (mul_nonneg hM (mul_nonneg (Nat.cast_nonneg _) hc))]
        congr 1
        push_cast
        ring

lemma inv_facts (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    1 ≤ (1 - α)⁻¹ ∧ α * (1 - α)⁻¹ = (1 - α)⁻¹ - 1 := by
  have hp : 0 < 1 - α := by linarith
  have e : (1 - α)⁻¹ * (1 - α) = 1 := inv_mul_cancel₀ hp.ne'
  have ht : 0 < (1 - α)⁻¹ := inv_pos.mpr hp
  have e2 : α * (1 - α)⁻¹ = (1 - α)⁻¹ - 1 := by linarith [e, mul_comm α (1 - α)⁻¹]
  refine ⟨?_, e2⟩
  have : 0 ≤ α * (1 - α)⁻¹ := mul_nonneg hα0.le ht.le
  linarith

lemma tail_real (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (M A c : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hc : 0 ≤ c) (N : ℝ) (hN : 1 ≤ N) :
    (A + N * c) * (1 - α)⁻¹ + c * (α / (1 - α) ^ 2) ≤ (A + c) * N * ((1 - α) ^ 2)⁻¹ := by
  obtain ⟨ht1, e⟩ := inv_facts α hα0 hα1
  set t := (1 - α)⁻¹ with htdef
  have h2 : ((1 - α) ^ 2)⁻¹ = t ^ 2 := by rw [htdef, inv_pow]
  have h3 : α / (1 - α) ^ 2 = (t - 1) * t := by
    rw [div_eq_mul_inv, h2, ← e]; ring
  rw [h2, h3]
  have k1 : 0 ≤ A * t * (N * t - 1) := mul_nonneg (mul_nonneg hA (by linarith)) (by nlinarith)
  have k2 : 0 ≤ c * t * ((t - 1) * (N - 1)) :=
    mul_nonneg (mul_nonneg hc (by linarith)) (mul_nonneg (by linarith) (by linarith))
  nlinarith [k1, k2]

lemma tail_sum (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (M A c : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hc : 0 ≤ c) (L₀ n : ℕ) :
    ∑' j : ℕ, ENNReal.ofReal (α ^ (j + n)) *
        ENNReal.ofReal (M * (A + (((j + n : ℕ) : ℝ) + L₀ + 1) * c)) ≤
      ENNReal.ofReal (M * (A + c) * (1 + L₀ + n) * ((1 - α) ^ 2)⁻¹ * α ^ n) := by
  set f : ℕ → ℝ := fun j => α ^ (j + n) * (M * (A + (((j + n : ℕ) : ℝ) + L₀ + 1) * c)) with hf
  have hfnn : ∀ j, 0 ≤ f j := fun j => by
    simp only [hf]
    have := pow_nonneg hα0.le (j + n)
    have : (0 : ℝ) ≤ ((j + n : ℕ) : ℝ) := Nat.cast_nonneg _
    have : 0 ≤ A + (((j + n : ℕ) : ℝ) + L₀ + 1) * c := by positivity
    positivity
  have hnorm : ‖α‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hα0]; exact hα1
  set X := A + ((n : ℝ) + L₀ + 1) * c with hX
  have hsum : HasSum f (α ^ n * M * (X * (1 - α)⁻¹ + c * (α / (1 - α) ^ 2))) := by
    have h1 := (hasSum_geometric_of_lt_one hα0.le hα1).mul_left X
    have h2 := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left c
    have h3 := (h1.add h2).mul_left (α ^ n * M)
    have hfe : f = fun j : ℕ => α ^ n * M * (X * α ^ j + c * ((j : ℝ) * α ^ j)) := by
      funext j
      simp only [hf, hX]
      push_cast
      ring
    rw [hfe]
    exact h3
  calc ∑' j : ℕ, ENNReal.ofReal (α ^ (j + n)) *
        ENNReal.ofReal (M * (A + (((j + n : ℕ) : ℝ) + L₀ + 1) * c))
      = ∑' j, ENNReal.ofReal (f j) := by
        congr 1; funext j
        rw [hf, ENNReal.ofReal_mul (pow_nonneg hα0.le _)]
    _ = ENNReal.ofReal (∑' j, f j) := (ENNReal.ofReal_tsum_of_nonneg hfnn hsum.summable).symm
    _ ≤ _ := by
      rw [hsum.tsum_eq]
      apply ENNReal.ofReal_le_ofReal
      have hN : (1 : ℝ) ≤ 1 + L₀ + n := by
        have : (0 : ℝ) ≤ L₀ := Nat.cast_nonneg _
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        linarith
      have key := tail_real α hα0 hα1 M A c hM hA hc (1 + L₀ + n) hN
      have hX' : X = A + (1 + L₀ + n) * c := by rw [hX]; ring
      rw [hX']
      have hp : 0 ≤ α ^ n * M := mul_nonneg (pow_nonneg hα0.le _) hM
      calc α ^ n * M * ((A + (1 + ↑L₀ + ↑n) * c) * (1 - α)⁻¹ + c * (α / (1 - α) ^ 2))
          ≤ α ^ n * M * ((A + c) * (1 + L₀ + n) * ((1 - α) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left key hp
        _ = _ := by ring

lemma disc_int (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (π : SSPolicy) (r x : ℝ) :
    ∫⁻ d, ssDiscCost κ L₀ α π r x d ∂pathLaw μ =
      ∑' i, ENNReal.ofReal (α ^ i) * ∫⁻ d, ssCost κ L₀ π r x d i ∂pathLaw μ := by
  unfold ssDiscCost
  rw [lintegral_tsum fun i => ((measurable_ssCost κ L₀ π r x i).const_mul _).aemeasurable]
  congr 1; funext i
  exact lintegral_const_mul _ (measurable_ssCost κ L₀ π r x i)

/-- Linear growth of the order-up-to levels bounds the discounted cost. -/
lemma disc_le_growth (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (π : SSPolicy) (r x A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i d, |ssOrderUpTo π r x d i| ≤ A + asum r d i) :
    ∫⁻ d, ssDiscCost κ L₀ α π r x d ∂pathLaw μ ≤
      ENNReal.ofReal (max κ.b κ.h * (A + (|r| + μ.mean)) * (1 + L₀) * ((1 - α) ^ 2)⁻¹) := by
  have hM : 0 ≤ max κ.b κ.h := le_trans κ.b_pos.le (le_max_left _ _)
  have hc : 0 ≤ |r| + μ.mean := add_nonneg (abs_nonneg _) (mean_nonneg μ)
  rw [disc_int]
  calc ∑' i, ENNReal.ofReal (α ^ i) * ∫⁻ d, ssCost κ L₀ π r x d i ∂pathLaw μ
      ≤ ∑' i : ℕ, ENNReal.ofReal (α ^ (i + 0)) *
          ENNReal.ofReal (max κ.b κ.h * (A + (((i + 0 : ℕ) : ℝ) + L₀ + 1) * (|r| + μ.mean))) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        simp only [add_zero]
        gcongr
        exact cost_le_growth μ κ L₀ π r x A hA0 i (hA i)
    _ ≤ _ := by
        have := tail_sum α hα0 hα1 (max κ.b κ.h) A (|r| + μ.mean) hM hA0 hc L₀ 0
        simpa using this

/-! ## The zero policy: `V^∞_α` is finite -/

def zeroPol : SSPolicy := ⟨fun _ _ => 0, fun _ => measurable_const⟩

lemma zero_upTo (r x : ℝ) (d : Path) (n : ℕ) :
    ssOrderUpTo zeroPol r x d n = x - ∑ k ∈ Finset.range n, (d k - r) := by
  have hp : ∀ n, ssPosition zeroPol r x d n = x - ∑ k ∈ Finset.range n, (d k - r) := by
    intro n
    induction n with
    | zero => simp [ssPosition]
    | succ n ih =>
      rw [ssPosition, ih, Finset.sum_range_succ]
      simp only [ssOrder, zeroPol, NNReal.coe_zero]
      ring
  unfold ssOrderUpTo
  rw [hp]
  simp [ssOrder, zeroPol]

lemma Vinf_le_zero (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r x : ℝ) :
    Vinf μ κ L₀ α r x ≤
      ENNReal.ofReal (max κ.b κ.h * (|x| + (|r| + μ.mean)) * (1 + L₀) * ((1 - α) ^ 2)⁻¹) := by
  refine (iInf_le _ zeroPol).trans ?_
  refine disc_le_growth μ κ L₀ α hα0 hα1 zeroPol r x |x| (abs_nonneg _) fun i d => ?_
  rw [zero_upTo]
  have := Finset.abs_sum_le_sum_abs (fun k => d k - r) (Finset.range i)
  have := abs_sub x (∑ k ∈ Finset.range i, (d k - r))
  unfold asum
  linarith

lemma Vinf_ne_top (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r x : ℝ) : Vinf μ κ L₀ α r x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (Vinf_le_zero μ κ L₀ α hα0 hα1 r x)


/-! ## `V^∞_α` is nondecreasing -/

lemma disc_congr (κ : Costs) (L₀ : ℕ) (α : ℝ) (π π' : SSPolicy) (r x x' : ℝ) (d : Path)
    (h : ∀ i, ssOrderUpTo π r x d i = ssOrderUpTo π' r x' d i) :
    ssDiscCost κ L₀ α π r x d = ssDiscCost κ L₀ α π' r x' d := by
  unfold ssDiscCost ssCost
  simp_rw [h]

def bumpPol (π : SSPolicy) (c : ℝ≥0) : SSPolicy where
  order k v := π.order k v + if k = 0 then c else 0
  measurable_order k := (π.measurable_order k).add measurable_const

lemma bump_upTo (π : SSPolicy) (r x : ℝ) (c : ℝ≥0) (d : Path) (i : ℕ) :
    ssOrderUpTo (bumpPol π c) r x d i = ssOrderUpTo π r (x + c) d i := by
  have hord : ∀ k, ssOrder (bumpPol π c) d k = ssOrder π d k + if k = 0 then (c : ℝ) else 0 := by
    intro k
    unfold ssOrder bumpPol
    split_ifs <;> simp [*]
  induction i with
  | zero =>
    simp only [ssOrderUpTo, ssPosition, hord, if_true]
    ring
  | succ i ih =>
    have e1 : ∀ (ρ : SSPolicy) (y : ℝ), ssOrderUpTo ρ r y d (i + 1) =
        ssOrderUpTo ρ r y d i - (d i - r) + ssOrder ρ d (i + 1) := by
      intro ρ y
      simp only [ssOrderUpTo, ssPosition]
    rw [e1, e1, ih, hord]
    simp

lemma Vinf_mono (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r : ℝ) :
    Monotone (fun x => Vinf μ κ L₀ α r x) := by
  intro x x' hxx
  refine le_iInf fun π => ?_
  refine (iInf_le _ (bumpPol π (x' - x).toNNReal)).trans (le_of_eq ?_)
  refine lintegral_congr fun d => disc_congr κ L₀ α _ _ r x x' d fun i => ?_
  rw [bump_upTo, Real.coe_toNNReal _ (by linarith)]
  ring_nf

lemma measurable_Vinf_comp (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r y : ℝ) :
    Measurable (fun a : ℝ => Vinf μ κ L₀ α r (y - (a - r))) :=
  (Vinf_mono μ κ L₀ α r).measurable.comp (measurable_const.sub (measurable_id.sub measurable_const))

/-! ## `V^∞_α` is convex -/

def mixPol (a b : ℝ) (π₁ π₂ : SSPolicy) : SSPolicy where
  order n w := a.toNNReal * π₁.order n w + b.toNNReal * π₂.order n w
  measurable_order n := (measurable_const.mul (π₁.measurable_order n)).add
    (measurable_const.mul (π₂.measurable_order n))

lemma mix_upTo (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (π₁ π₂ : SSPolicy)
    (r x y : ℝ) (d : Path) (n : ℕ) :
    ssOrderUpTo (mixPol a b π₁ π₂) r (a * x + b * y) d n =
      a * ssOrderUpTo π₁ r x d n + b * ssOrderUpTo π₂ r y d n := by
  have hord : ∀ k, ssOrder (mixPol a b π₁ π₂) d k = a * ssOrder π₁ d k + b * ssOrder π₂ d k := by
    intro k
    simp [ssOrder, mixPol, Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb]
  have hpos : ∀ k, ssPosition (mixPol a b π₁ π₂) r (a * x + b * y) d k =
      a * ssPosition π₁ r x d k + b * ssPosition π₂ r y d k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [ssPosition]
      rw [ih, hord]
      linear_combination (d k - r) * hab
  unfold ssOrderUpTo
  rw [hpos, hord]
  ring

lemma mix_cost (κ : Costs) (L₀ : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (π₁ π₂ : SSPolicy) (r x y : ℝ) (d : Path) (i : ℕ) :
    ssCost κ L₀ (mixPol a b π₁ π₂) r (a * x + b * y) d i ≤
      ENNReal.ofReal a * ssCost κ L₀ π₁ r x d i + ENNReal.ofReal b * ssCost κ L₀ π₂ r y d i := by
  unfold ssCost
  rw [mix_upTo a b ha hb hab]
  set S := ∑ k ∈ Finset.range (L₀ + 1), (d (i + k) - r)
  have e : a * ssOrderUpTo π₁ r x d i + b * ssOrderUpTo π₂ r y d i - S =
      a * (ssOrderUpTo π₁ r x d i - S) + b * (ssOrderUpTo π₂ r y d i - S) := by
    linear_combination S * hab
  rw [e, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_add (mul_nonneg ha (G_nonneg _ _)) (mul_nonneg hb (G_nonneg _ _))]
  exact ENNReal.ofReal_le_ofReal (G_convex κ a b _ _ ha hb hab)

lemma mix_disc (κ : Costs) (L₀ : ℕ) (α : ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (π₁ π₂ : SSPolicy) (r x y : ℝ) (d : Path) :
    ssDiscCost κ L₀ α (mixPol a b π₁ π₂) r (a * x + b * y) d ≤
      ENNReal.ofReal a * ssDiscCost κ L₀ α π₁ r x d +
        ENNReal.ofReal b * ssDiscCost κ L₀ α π₂ r y d := by
  unfold ssDiscCost
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  calc ENNReal.ofReal (α ^ i) * ssCost κ L₀ (mixPol a b π₁ π₂) r (a * x + b * y) d i
      ≤ ENNReal.ofReal (α ^ i) * (ENNReal.ofReal a * ssCost κ L₀ π₁ r x d i +
          ENNReal.ofReal b * ssCost κ L₀ π₂ r y d i) := by
        gcongr; exact mix_cost κ L₀ a b ha hb hab π₁ π₂ r x y d i
    _ = _ := by ring

lemma Vinf_convex (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r : ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (x y : ℝ) :
    Vinf μ κ L₀ α r (a * x + b * y) ≤
      ENNReal.ofReal a * Vinf μ κ L₀ α r x + ENNReal.ofReal b * Vinf μ κ L₀ α r y := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (ε : ℝ≥0∞) ≠ 0 := by simpa using hε.ne'
  have hx : (⨅ π : SSPolicy, ∫⁻ d, ssDiscCost κ L₀ α π r x d ∂pathLaw μ) <
      Vinf μ κ L₀ α r x + ε := ENNReal.lt_add_right (Vinf_ne_top μ κ L₀ α hα0 hα1 r x) hε'
  have hy : (⨅ π : SSPolicy, ∫⁻ d, ssDiscCost κ L₀ α π r y d ∂pathLaw μ) <
      Vinf μ κ L₀ α r y + ε := ENNReal.lt_add_right (Vinf_ne_top μ κ L₀ α hα0 hα1 r y) hε'
  obtain ⟨π₁, h1⟩ := iInf_lt_iff.1 hx
  obtain ⟨π₂, h2⟩ := iInf_lt_iff.1 hy
  calc Vinf μ κ L₀ α r (a * x + b * y)
      ≤ ∫⁻ d, ssDiscCost κ L₀ α (mixPol a b π₁ π₂) r (a * x + b * y) d ∂pathLaw μ :=
        iInf_le _ _
    _ ≤ ∫⁻ d, (ENNReal.ofReal a * ssDiscCost κ L₀ α π₁ r x d +
          ENNReal.ofReal b * ssDiscCost κ L₀ α π₂ r y d) ∂pathLaw μ :=
        lintegral_mono fun d => mix_disc κ L₀ α a b ha hb hab π₁ π₂ r x y d
    _ = ENNReal.ofReal a * ∫⁻ d, ssDiscCost κ L₀ α π₁ r x d ∂pathLaw μ +
          ENNReal.ofReal b * ∫⁻ d, ssDiscCost κ L₀ α π₂ r y d ∂pathLaw μ := by
        rw [lintegral_add_left ((measurable_disc κ L₀ α π₁ r x).const_mul _),
          lintegral_const_mul _ (measurable_disc κ L₀ α π₁ r x),
          lintegral_const_mul _ (measurable_disc κ L₀ α π₂ r y)]
    _ ≤ ENNReal.ofReal a * (Vinf μ κ L₀ α r x + ε) + ENNReal.ofReal b * (Vinf μ κ L₀ α r y + ε) := by
        gcongr
    _ = ENNReal.ofReal a * Vinf μ κ L₀ α r x + ENNReal.ofReal b * Vinf μ κ L₀ α r y +
          (ENNReal.ofReal a + ENNReal.ofReal b) * ε := by ring
    _ = _ := by rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul]

/-! ## The Bellman lower bound -/

lemma disc_split_pt (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα : 0 ≤ α) (π : SSPolicy) (r x : ℝ)
    (d : Path) :
    ssDiscCost κ L₀ α π r x d = ssCost κ L₀ π r x d 0 +
      ENNReal.ofReal α * ∑' i, ENNReal.ofReal (α ^ i) * ssCost κ L₀ π r x d (i + 1) := by
  unfold ssDiscCost
  rw [tsum_eq_zero_add' ENNReal.summable, ← ENNReal.tsum_mul_left]
  simp only [pow_zero, ENNReal.ofReal_one, one_mul]
  congr 1
  refine tsum_congr fun i => ?_
  rw [pow_succ', ENNReal.ofReal_mul hα, mul_assoc]

lemma disc_tail_pt (κ : Costs) (L₀ : ℕ) (α : ℝ) (π : SSPolicy) (r x : ℝ) (d : Path) :
    ∑' i, ENNReal.ofReal (α ^ i) * ssCost κ L₀ π r x d (i + 1) =
      ssDiscCost κ L₀ α (tailPol π (d 0)) r (x + u0 π - (d 0 - r)) (sh d) := by
  unfold ssDiscCost
  simp_rw [ssCost_tail]

lemma disc_split (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα : 0 ≤ α) (π : SSPolicy)
    (r x : ℝ) :
    ∫⁻ d, ssDiscCost κ L₀ α π r x d ∂pathLaw μ = ghat μ κ L₀ r (x + u0 π) +
      ENNReal.ofReal α * ∫⁻ a, ∫⁻ d', ssDiscCost κ L₀ α (tailPol π a) r (x + u0 π - (a - r)) d'
        ∂pathLaw μ ∂μ.law := by
  have hF : Measurable (fun d : Path =>
      ∑' i, ENNReal.ofReal (α ^ i) * ssCost κ L₀ π r x d (i + 1)) :=
    Measurable.ennreal_tsum fun i => (measurable_ssCost κ L₀ π r x (i + 1)).const_mul _
  simp_rw [disc_split_pt κ L₀ α hα π r x]
  rw [lintegral_add_left (measurable_ssCost κ L₀ π r x 0), ssCost_zero_int,
    lintegral_const_mul _ hF, lintegral_cons μ hF]
  congr 2
  refine lintegral_congr fun a => lintegral_congr fun d' => ?_
  rw [disc_tail_pt]
  rfl

/-- `J(y) = ĝ(y) + α 𝔼 V^∞_α(y - (D - r))`. -/
def Jf (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r y : ℝ) : ℝ≥0∞ :=
  ghat μ κ L₀ r y + ENNReal.ofReal α * ∫⁻ a, Vinf μ κ L₀ α r (y - (a - r)) ∂μ.law

lemma bellman_lb (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα : 0 ≤ α) (π : SSPolicy)
    (r x : ℝ) :
    Jf μ κ L₀ α r (x + u0 π) ≤ ∫⁻ d, ssDiscCost κ L₀ α π r x d ∂pathLaw μ := by
  rw [disc_split μ κ L₀ α hα π r x, Jf]
  gcongr with a
  exact iInf_le _ _

/-! ## Base-stock policies -/

def bsT (S : ℝ) : ℕ → Path → ℝ := fun _ _ => S

lemma bs_nonant (S : ℝ) : NonAnt (bsT S) := fun _ _ _ _ => rfl

def bsPol (S r x : ℝ) : SSPolicy := tPol (bsT S) (fun _ => measurable_const) r x

lemma bs_upTo (S r x : ℝ) (d : Path) (n : ℕ) :
    ssOrderUpTo (bsPol S r x) r x d n = max (tpos (bsT S) r x d n) S :=
  tPol_upTo (bsT S) _ (bs_nonant S) r x d n

lemma bs_u0 (S r x : ℝ) : x + u0 (bsPol S r x) = max x S := by
  have h := ssOrderUpTo_zero (bsPol S r x) r x (fun _ => 0)
  rw [bs_upTo] at h
  rw [← h]
  rfl

lemma bs_tpos_cons (S r x a : ℝ) (d' : Path) (n : ℕ) :
    tpos (bsT S) r x (consP a d') (n + 1) = tpos (bsT S) r (max x S - (a - r)) d' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tpos, ih]
    rfl

lemma bs_tail_upTo (S r x a : ℝ) (d' : Path) (i : ℕ) :
    ssOrderUpTo (tailPol (bsPol S r x) a) r (max x S - (a - r)) d' i =
      ssOrderUpTo (bsPol S r (max x S - (a - r))) r (max x S - (a - r)) d' i := by
  have h := ssOrderUpTo_tail (bsPol S r x) r x (consP a d') i
  simp only [consP_zero, sh_consP, bs_u0] at h
  rw [← h, bs_upTo, bs_upTo, bs_tpos_cons]

lemma bs_markov (S r x : ℝ) : IsStationaryMarkov (bsPol S r x) (baseStockRule S) r x := by
  refine ⟨(measurable_const.sub measurable_id).real_toNNReal, fun n d => ?_⟩
  have h1 : ssOrder (bsPol S r x) d n = ((S - tpos (bsT S) r x d n).toNNReal : ℝ) :=
    tPol_order (bsT S) _ (bs_nonant S) r x d n
  have h2 : ssPosition (bsPol S r x) r x d n = tpos (bsT S) r x d n :=
    tPol_pos (bsT S) _ (bs_nonant S) r x d n
  rw [h1, h2]
  rfl

/-- Cost of the base-stock policy with level `S` from `x`. -/
def cS (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r S x : ℝ) : ℝ≥0∞ :=
  ∫⁻ d, ssDiscCost κ L₀ α (bsPol S r x) r x d ∂pathLaw μ

lemma cS_rec (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα : 0 ≤ α) (r S x : ℝ) :
    cS μ κ L₀ α r S x = ghat μ κ L₀ r (max x S) +
      ENNReal.ofReal α * ∫⁻ a, cS μ κ L₀ α r S (max x S - (a - r)) ∂μ.law := by
  unfold cS
  rw [disc_split μ κ L₀ α hα, bs_u0]
  congr 2
  refine lintegral_congr fun a => lintegral_congr fun d' => ?_
  exact disc_congr κ L₀ α _ _ r _ _ d' (bs_tail_upTo S r x a d')

lemma bs_growth (S r z : ℝ) (i : ℕ) (d : Path) :
    |ssOrderUpTo (bsPol S r z) r z d i| ≤ (|z| + |S|) + asum r d i := by
  rw [bs_upTo]
  refine upTo_abs_le (bsT S) r z |S| (abs_nonneg _) (fun n d => ?_) d i
  have := asum_nonneg r d n
  have := le_abs_self S
  have := le_max_right z |S|
  simp only [bsT]
  linarith

lemma cS_le (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r S z : ℝ) :
    cS μ κ L₀ α r S z ≤ ENNReal.ofReal (max κ.b κ.h * ((|z| + |S|) + (|r| + μ.mean)) *
      (1 + L₀) * ((1 - α) ^ 2)⁻¹) :=
  disc_le_growth μ κ L₀ α hα0 hα1 _ r z _ (by positivity) fun i d => bs_growth S r z i d


/-! ## Properties of `ĝ` and `J` -/

lemma measurable_Gpath (κ : Costs) (L₀ : ℕ) (r y : ℝ) :
    Measurable (fun d : Path =>
      ENNReal.ofReal (G κ (y - ∑ k ∈ Finset.range (L₀ + 1), (d k - r)))) :=
  ((continuous_G κ).measurable.comp (measurable_const.sub
    (Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).sub measurable_const))).ennreal_ofReal

lemma ghat_le (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r y : ℝ) :
    ghat μ κ L₀ r y ≤
      ENNReal.ofReal (max κ.b κ.h * (|y| + ((L₀ : ℝ) + 1) * (|r| + μ.mean))) := by
  have h := ssCost_zero_int μ κ L₀ zeroPol r y
  have hu : u0 zeroPol = 0 := by simp [u0, zeroPol]
  rw [hu, add_zero] at h
  rw [← h]
  have := cost_le_growth μ κ L₀ zeroPol r y |y| (abs_nonneg _) 0
    (fun d => by rw [zero_upTo]; simp [asum])
  refine this.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring

lemma ghat_ne_top (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r y : ℝ) : ghat μ κ L₀ r y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (ghat_le μ κ L₀ r y)

lemma ghat_ge (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r y : ℝ) :
    ENNReal.ofReal (min κ.b κ.h * |y|) ≤
      ghat μ κ L₀ r y + ENNReal.ofReal (min κ.b κ.h * (((L₀ : ℝ) + 1) * (|r| + μ.mean))) := by
  set m := min κ.b κ.h with hmdef
  have hm : 0 < m := lt_min κ.b_pos κ.h_pos
  have hpt : ∀ d : Path, ENNReal.ofReal (m * |y|) ≤
      ENNReal.ofReal (G κ (y - ∑ k ∈ Finset.range (L₀ + 1), (d k - r))) +
        ENNReal.ofReal m * ENNReal.ofReal (∑ k ∈ Finset.range (L₀ + 1), |d (id k) - r|) := by
    intro d
    rw [← ENNReal.ofReal_mul hm.le, ← ENNReal.ofReal_add (G_nonneg _ _)
      (mul_nonneg hm.le (Finset.sum_nonneg fun _ _ => abs_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    set S := ∑ k ∈ Finset.range (L₀ + 1), (d k - r)
    have h1 := G_ge κ (y - S)
    have h2 : |S| ≤ ∑ k ∈ Finset.range (L₀ + 1), |d (id k) - r| :=
      Finset.abs_sum_le_sum_abs _ _
    have h3 : |y| ≤ |y - S| + |S| := by
      have := abs_add_le (y - S) S
      simpa using this
    nlinarith [mul_le_mul_of_nonneg_left h2 hm.le, mul_le_mul_of_nonneg_left h3 hm.le]
  have hmeas : Measurable (fun d : Path =>
      ENNReal.ofReal (∑ k ∈ Finset.range (L₀ + 1), |d (id k) - r|)) := by
    apply Measurable.ennreal_ofReal
    exact Finset.measurable_sum _ fun k _ => by fun_prop
  calc ENNReal.ofReal (m * |y|) = ∫⁻ _d, ENNReal.ofReal (m * |y|) ∂pathLaw μ := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ d, (ENNReal.ofReal (G κ (y - ∑ k ∈ Finset.range (L₀ + 1), (d k - r))) +
        ENNReal.ofReal m * ENNReal.ofReal (∑ k ∈ Finset.range (L₀ + 1), |d (id k) - r|))
          ∂pathLaw μ := lintegral_mono hpt
    _ = ghat μ κ L₀ r y + ENNReal.ofReal m *
          ∫⁻ d, ENNReal.ofReal (∑ k ∈ Finset.range (L₀ + 1), |d (id k) - r|) ∂pathLaw μ := by
        rw [lintegral_add_left (measurable_Gpath κ L₀ r y), lintegral_const_mul _ hmeas]
        rfl
    _ ≤ ghat μ κ L₀ r y + ENNReal.ofReal m *
          ENNReal.ofReal (((L₀ + 1 : ℕ) : ℝ) * (|r| + μ.mean)) := by
        gcongr
        exact lintegral_sum_abs μ r (L₀ + 1) id
    _ = _ := by
        rw [← ENNReal.ofReal_mul hm.le]
        push_cast
        rfl

lemma ghat_convex (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r : ℝ) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) (y₁ y₂ : ℝ) :
    ghat μ κ L₀ r (a * y₁ + b * y₂) ≤
      ENNReal.ofReal a * ghat μ κ L₀ r y₁ + ENNReal.ofReal b * ghat μ κ L₀ r y₂ := by
  unfold ghat
  rw [← lintegral_const_mul _ (measurable_Gpath κ L₀ r y₁),
    ← lintegral_const_mul _ (measurable_Gpath κ L₀ r y₂),
    ← lintegral_add_left ((measurable_Gpath κ L₀ r y₁).const_mul _)]
  refine lintegral_mono fun d => ?_
  set S := ∑ k ∈ Finset.range (L₀ + 1), (d k - r)
  have e : a * y₁ + b * y₂ - S = a * (y₁ - S) + b * (y₂ - S) := by linear_combination S * hab
  rw [e, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_add (mul_nonneg ha (G_nonneg _ _)) (mul_nonneg hb (G_nonneg _ _))]
  exact ENNReal.ofReal_le_ofReal (G_convex κ a b _ _ ha hb hab)

lemma Jf_le (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r y : ℝ) :
    Jf μ κ L₀ α r y ≤ ghat μ κ L₀ r y + ENNReal.ofReal α * Vinf μ κ L₀ α r (y + r) := by
  unfold Jf
  gcongr
  calc ∫⁻ a, Vinf μ κ L₀ α r (y - (a - r)) ∂μ.law ≤ ∫⁻ _a, Vinf μ κ L₀ α r (y + r) ∂μ.law := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_nonneg μ] with a ha
        exact Vinf_mono μ κ L₀ α r (by linarith)
    _ = Vinf μ κ L₀ α r (y + r) := by rw [lintegral_const, measure_univ, mul_one]

lemma Jf_ne_top (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r y : ℝ) : Jf μ κ L₀ α r y ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ghat_ne_top μ κ L₀ r y,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Vinf_ne_top μ κ L₀ α hα0 hα1 r _)⟩)
    (Jf_le μ κ L₀ α r y)

lemma Jf_convex (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r : ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (y₁ y₂ : ℝ) :
    Jf μ κ L₀ α r (a * y₁ + b * y₂) ≤
      ENNReal.ofReal a * Jf μ κ L₀ α r y₁ + ENNReal.ofReal b * Jf μ κ L₀ α r y₂ := by
  have hI : ∫⁻ s, Vinf μ κ L₀ α r (a * y₁ + b * y₂ - (s - r)) ∂μ.law ≤
      ENNReal.ofReal a * ∫⁻ s, Vinf μ κ L₀ α r (y₁ - (s - r)) ∂μ.law +
        ENNReal.ofReal b * ∫⁻ s, Vinf μ κ L₀ α r (y₂ - (s - r)) ∂μ.law := by
    rw [← lintegral_const_mul _ (measurable_Vinf_comp μ κ L₀ α r y₁),
      ← lintegral_const_mul _ (measurable_Vinf_comp μ κ L₀ α r y₂),
      ← lintegral_add_left ((measurable_Vinf_comp μ κ L₀ α r y₁).const_mul _)]
    refine lintegral_mono fun s => ?_
    have e : a * y₁ + b * y₂ - (s - r) = a * (y₁ - (s - r)) + b * (y₂ - (s - r)) := by
      linear_combination (s - r) * hab
    rw [e]
    exact Vinf_convex μ κ L₀ α hα0 hα1 r a b ha hb hab _ _
  unfold Jf
  calc ghat μ κ L₀ r (a * y₁ + b * y₂) +
        ENNReal.ofReal α * ∫⁻ s, Vinf μ κ L₀ α r (a * y₁ + b * y₂ - (s - r)) ∂μ.law
      ≤ (ENNReal.ofReal a * ghat μ κ L₀ r y₁ + ENNReal.ofReal b * ghat μ κ L₀ r y₂) +
        ENNReal.ofReal α * (ENNReal.ofReal a * ∫⁻ s, Vinf μ κ L₀ α r (y₁ - (s - r)) ∂μ.law +
          ENNReal.ofReal b * ∫⁻ s, Vinf μ κ L₀ α r (y₂ - (s - r)) ∂μ.law) := by
        gcongr
        · exact ghat_convex μ κ L₀ r a b ha hb hab y₁ y₂
    _ = _ := by ring

/-- Real-valued `J`. -/
def Jr (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r y : ℝ) : ℝ := (Jf μ κ L₀ α r y).toReal

lemma Jr_convex (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r : ℝ) : ConvexOn ℝ Set.univ (fun y => Jr μ κ L₀ α r y) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, Jr]
  have h := Jf_convex μ κ L₀ α hα0 hα1 r a b ha hb hab x y
  have hx := Jf_ne_top μ κ L₀ α hα0 hα1 r x
  have hy := Jf_ne_top μ κ L₀ α hα0 hα1 r y
  have hfin : ENNReal.ofReal a * Jf μ κ L₀ α r x + ENNReal.ofReal b * Jf μ κ L₀ α r y ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy⟩
  calc (Jf μ κ L₀ α r (a * x + b * y)).toReal
      ≤ (ENNReal.ofReal a * Jf μ κ L₀ α r x + ENNReal.ofReal b * Jf μ κ L₀ α r y).toReal :=
        ENNReal.toReal_mono hfin h
    _ = a * (Jf μ κ L₀ α r x).toReal + b * (Jf μ κ L₀ α r y).toReal := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy), ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

lemma Jr_ge (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r y : ℝ) :
    min κ.b κ.h * |y| - min κ.b κ.h * (((L₀ : ℝ) + 1) * (|r| + μ.mean)) ≤ Jr μ κ L₀ α r y := by
  have hm : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  have hc : 0 ≤ |r| + μ.mean := add_nonneg (abs_nonneg _) (mean_nonneg μ)
  have h1 := ghat_ge μ κ L₀ r y
  have h2 : ghat μ κ L₀ r y ≤ Jf μ κ L₀ α r y := le_self_add
  have h3 : ENNReal.ofReal (min κ.b κ.h * |y|) ≤ Jf μ κ L₀ α r y +
      ENNReal.ofReal (min κ.b κ.h * (((L₀ : ℝ) + 1) * (|r| + μ.mean))) :=
    h1.trans (by gcongr)
  have h4 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨Jf_ne_top μ κ L₀ α hα0 hα1 r y,
    ENNReal.ofReal_ne_top⟩) h3
  rw [ENNReal.toReal_add (Jf_ne_top μ κ L₀ α hα0 hα1 r y) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at h4
  unfold Jr
  linarith

lemma exists_S (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r : ℝ) : ∃ S : ℝ, (∀ y, Jr μ κ L₀ α r S ≤ Jr μ κ L₀ α r y) ∧
      (∀ y, Jr μ κ L₀ α r y ≤ Jr μ κ L₀ α r S → y ≤ S) := by
  set f := fun y => Jr μ κ L₀ α r y with hf
  have hm : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  set m := min κ.b κ.h
  set C := m * (((L₀ : ℝ) + 1) * (|r| + μ.mean))
  have hcont : Continuous f :=
    continuousOn_univ.1 ((Jr_convex μ κ L₀ α hα0 hα1 r).continuousOn isOpen_univ)
  set R := (f 0 + C) / m
  have hbd : ∀ y, f y ≤ f 0 → |y| ≤ R := by
    intro y hy
    have := Jr_ge μ κ L₀ α hα0 hα1 r y
    rw [le_div_iff₀ hm]
    have : m * |y| - C ≤ f y := this
    nlinarith
  have hK : IsCompact {y | f y ≤ f 0} := by
    refine (isCompact_Icc (a := -R) (b := R)).of_isClosed_subset
      (isClosed_le hcont continuous_const) fun y hy => ?_
    have := hbd y hy
    rw [abs_le] at this
    exact ⟨this.1, this.2⟩
  obtain ⟨y₀, _, hmin⟩ := hK.exists_isMinOn ⟨0, show f 0 ≤ f 0 from le_refl _⟩ hcont.continuousOn
  have hglob : ∀ y, f y₀ ≤ f y := by
    intro y
    by_cases hy : f y ≤ f 0
    · exact isMinOn_iff.1 hmin y hy
    · push_neg at hy
      exact (isMinOn_iff.1 hmin 0 (show f 0 ≤ f 0 from le_refl _)).trans hy.le
  set A := {y | f y ≤ f y₀}
  have hAcl : IsClosed A := isClosed_le hcont continuous_const
  have hAbdd : BddAbove A := by
    refine ⟨R, fun y hy => ?_⟩
    have := hbd y (le_trans hy (hglob 0))
    exact (le_abs_self y).trans this
  have hS : sSup A ∈ A := hAcl.csSup_mem ⟨y₀, show f y₀ ≤ f y₀ from le_refl _⟩ hAbdd
  refine ⟨sSup A, fun y => le_trans hS (hglob y), fun y hy => le_csSup hAbdd (le_trans hy hS)⟩

/-! ## Verification: the base-stock policy at `S` is optimal -/

lemma Jf_le_iff (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r y y' : ℝ) : Jf μ κ L₀ α r y ≤ Jf μ κ L₀ α r y' ↔ Jr μ κ L₀ α r y ≤ Jr μ κ L₀ α r y' :=
  (ENNReal.toReal_le_toReal (Jf_ne_top μ κ L₀ α hα0 hα1 r y)
    (Jf_ne_top μ κ L₀ α hα0 hα1 r y')).symm

lemma J_le_of (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r S : ℝ) (hmin : ∀ y, Jr μ κ L₀ α r S ≤ Jr μ κ L₀ α r y) (x y : ℝ) (hxy : x ≤ y) :
    Jf μ κ L₀ α r (max x S) ≤ Jf μ κ L₀ α r y := by
  rw [Jf_le_iff μ κ L₀ α hα0 hα1]
  rcases le_total x S with h | h
  · rw [max_eq_right h]; exact hmin y
  · rw [max_eq_left h]
    have hseg : x ∈ segment ℝ S y := by
      rw [segment_eq_Icc (h.trans hxy)]; exact ⟨h, hxy⟩
    have := (Jr_convex μ κ L₀ α hα0 hα1 r).le_on_segment (Set.mem_univ S) (Set.mem_univ y) hseg
    exact this.trans (max_le (hmin y) le_rfl)

lemma Vinf_ge (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r S : ℝ) (hmin : ∀ y, Jr μ κ L₀ α r S ≤ Jr μ κ L₀ α r y) (x : ℝ) :
    Jf μ κ L₀ α r (max x S) ≤ Vinf μ κ L₀ α r x :=
  le_iInf fun π => (J_le_of μ κ L₀ α hα0 hα1 r S hmin x (x + u0 π)
    (by linarith [u0_nonneg π])).trans (bellman_lb μ κ L₀ α hα0.le π r x)

def phi (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r S z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (max κ.b κ.h * ((|z| + |S|) + (|r| + μ.mean)) * (1 + L₀) * ((1 - α) ^ 2)⁻¹)

lemma measurable_phi (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r S : ℝ) :
    Measurable (fun z => phi μ κ L₀ α r S z) := by
  unfold phi
  apply Measurable.ennreal_ofReal
  fun_prop

lemma D_step (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r S : ℝ) (hmin : ∀ y, Jr μ κ L₀ α r S ≤ Jr μ κ L₀ α r y) (x : ℝ) :
    cS μ κ L₀ α r S x - Vinf μ κ L₀ α r x ≤ ENNReal.ofReal α *
      ∫⁻ a, (cS μ κ L₀ α r S (max x S - (a - r)) - Vinf μ κ L₀ α r (max x S - (a - r))) ∂μ.law := by
  apply tsub_le_iff_left.2
  calc cS μ κ L₀ α r S x
      = ghat μ κ L₀ r (max x S) +
          ENNReal.ofReal α * ∫⁻ a, cS μ κ L₀ α r S (max x S - (a - r)) ∂μ.law :=
        cS_rec μ κ L₀ α hα0.le r S x
    _ ≤ ghat μ κ L₀ r (max x S) + ENNReal.ofReal α * ∫⁻ a,
          (Vinf μ κ L₀ α r (max x S - (a - r)) + (cS μ κ L₀ α r S (max x S - (a - r)) -
            Vinf μ κ L₀ α r (max x S - (a - r)))) ∂μ.law := by
        gcongr with a
        exact le_add_tsub
    _ = Jf μ κ L₀ α r (max x S) + ENNReal.ofReal α * ∫⁻ a,
          (cS μ κ L₀ α r S (max x S - (a - r)) - Vinf μ κ L₀ α r (max x S - (a - r))) ∂μ.law := by
        rw [lintegral_add_left (measurable_Vinf_comp μ κ L₀ α r _), Jf]
        ring
    _ ≤ _ := by
        gcongr
        exact Vinf_ge μ κ L₀ α hα0 hα1 r S hmin x

lemma D_iter (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r S : ℝ) (hmin : ∀ y, Jr μ κ L₀ α r S ≤ Jr μ κ L₀ α r y) (n : ℕ) :
    ∀ x, cS μ κ L₀ α r S x - Vinf μ κ L₀ α r x ≤ ENNReal.ofReal (α ^ n) *
      ∫⁻ d, phi μ κ L₀ α r S (tpos (bsT S) r x d n) ∂pathLaw μ := by
  induction n with
  | zero =>
    intro x
    simp only [pow_zero, ENNReal.ofReal_one, one_mul, tpos, lintegral_const, measure_univ,
      mul_one]
    exact tsub_le_self.trans (cS_le μ κ L₀ α hα0 hα1 r S x)
  | succ n ih =>
    intro x
    have hm : Measurable (fun d => phi μ κ L₀ α r S (tpos (bsT S) r x d (n + 1))) :=
      (measurable_phi μ κ L₀ α r S).comp (measurable_tpos _ (fun _ => measurable_const) r x _)
    calc cS μ κ L₀ α r S x - Vinf μ κ L₀ α r x
        ≤ ENNReal.ofReal α * ∫⁻ a, (cS μ κ L₀ α r S (max x S - (a - r)) -
            Vinf μ κ L₀ α r (max x S - (a - r))) ∂μ.law := D_step μ κ L₀ α hα0 hα1 r S hmin x
      _ ≤ ENNReal.ofReal α * ∫⁻ a, (ENNReal.ofReal (α ^ n) * ∫⁻ d',
            phi μ κ L₀ α r S (tpos (bsT S) r (max x S - (a - r)) d' n) ∂pathLaw μ) ∂μ.law := by
          gcongr with a
          exact ih _
      _ = ENNReal.ofReal (α ^ (n + 1)) *
            ∫⁻ d, phi μ κ L₀ α r S (tpos (bsT S) r x d (n + 1)) ∂pathLaw μ := by
          rw [lintegral_cons μ hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
            ← ENNReal.ofReal_mul hα0.le, ← pow_succ']
          simp_rw [bs_tpos_cons]

lemma phi_int (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r S x : ℝ) (n : ℕ) :
    ∫⁻ d, phi μ κ L₀ α r S (tpos (bsT S) r x d n) ∂pathLaw μ ≤
      ENNReal.ofReal (max κ.b κ.h * (1 + L₀) * ((1 - α) ^ 2)⁻¹ *
        ((|x| + |S| + |S| + (|r| + μ.mean)) + n * (|r| + μ.mean))) := by
  set K := max κ.b κ.h * (1 + L₀) * ((1 - α) ^ 2)⁻¹ with hK
  have hM : 0 ≤ max κ.b κ.h := le_trans κ.b_pos.le (le_max_left _ _)
  have hK0 : 0 ≤ K := by positivity
  have hc : 0 ≤ |r| + μ.mean := add_nonneg (abs_nonneg _) (mean_nonneg μ)
  have hpt : ∀ d, phi μ κ L₀ α r S (tpos (bsT S) r x d n) ≤
      ENNReal.ofReal (K * (|x| + |S| + |S| + (|r| + μ.mean))) +
        ENNReal.ofReal K * ENNReal.ofReal (asum r d n) := by
    intro d
    rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_add (by positivity)
      (mul_nonneg hK0 (asum_nonneg r d n))]
    unfold phi
    apply ENNReal.ofReal_le_ofReal
    have hb := tpos_bounds (bsT S) r x |S| (fun k d => by
      have := asum_nonneg r d k
      have := le_abs_self S
      have := le_max_right x |S|
      simp only [bsT]; linarith) d n
    have habs : |tpos (bsT S) r x d n| ≤ |x| + |S| + asum r d n := by
      have := le_abs_self x; have := neg_abs_le x
      have hmx : max x |S| ≤ |x| + |S| := max_le (by linarith [abs_nonneg S]) (by linarith [abs_nonneg x])
      rw [abs_le]; constructor <;> linarith [hb.1, hb.2, asum_nonneg r d n, abs_nonneg S]
    have e : max κ.b κ.h * ((|tpos (bsT S) r x d n| + |S|) + (|r| + μ.mean)) * (1 + L₀) *
        ((1 - α) ^ 2)⁻¹ = K * (|tpos (bsT S) r x d n| + |S| + (|r| + μ.mean)) := by
      rw [hK]; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left habs hK0]
  have hmeas : Measurable (fun d : Path => ENNReal.ofReal (asum r d n)) := by
    apply Measurable.ennreal_ofReal
    exact Finset.measurable_sum _ fun k _ => by fun_prop
  calc ∫⁻ d, phi μ κ L₀ α r S (tpos (bsT S) r x d n) ∂pathLaw μ
      ≤ ∫⁻ d, (ENNReal.ofReal (K * (|x| + |S| + |S| + (|r| + μ.mean))) +
          ENNReal.ofReal K * ENNReal.ofReal (asum r d n)) ∂pathLaw μ := lintegral_mono hpt
    _ = ENNReal.ofReal (K * (|x| + |S| + |S| + (|r| + μ.mean))) +
          ENNReal.ofReal K * ∫⁻ d, ENNReal.ofReal (asum r d n) ∂pathLaw μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ hmeas]
    _ ≤ ENNReal.ofReal (K * (|x| + |S| + |S| + (|r| + μ.mean))) +
          ENNReal.ofReal K * ENNReal.ofReal (n * (|r| + μ.mean)) := by
        gcongr
        exact lintegral_sum_abs μ r n id
    _ = _ := by
        rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_add (by positivity)
          (mul_nonneg hK0 (mul_nonneg (Nat.cast_nonneg _) hc))]
        congr 1
        ring

lemma Vinf_eq_cS (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r S : ℝ) (hmin : ∀ y, Jr μ κ L₀ α r S ≤ Jr μ κ L₀ α r y) (x : ℝ) :
    Vinf μ κ L₀ α r x = cS μ κ L₀ α r S x := by
  set K := max κ.b κ.h * (1 + L₀) * ((1 - α) ^ 2)⁻¹
  set C0 := |x| + |S| + |S| + (|r| + μ.mean)
  set c := |r| + μ.mean
  have hb : ∀ n : ℕ, cS μ κ L₀ α r S x - Vinf μ κ L₀ α r x ≤
      ENNReal.ofReal (α ^ n * (K * (C0 + n * c))) := by
    intro n
    refine (D_iter μ κ L₀ α hα0 hα1 r S hmin n x).trans ?_
    rw [ENNReal.ofReal_mul (pow_nonneg hα0.le _)]
    gcongr
    exact phi_int μ κ L₀ α hα0 hα1 r S x n
  have hlim : Tendsto (fun n : ℕ => α ^ n * (K * (C0 + n * c))) atTop (nhds 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hα0.le hα1
    have h2 := tendsto_self_mul_const_pow_of_lt_one hα0.le hα1
    have h3 := (h1.const_mul (K * C0)).add (h2.const_mul (K * c))
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun n => ?_
    ring
  have hlim' : Tendsto (fun n : ℕ => ENNReal.ofReal (α ^ n * (K * (C0 + n * c)))) atTop
      (nhds 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hlim
    rw [ENNReal.ofReal_zero] at this
    exact this
  have hD : cS μ κ L₀ α r S x - Vinf μ κ L₀ α r x = 0 :=
    le_antisymm (ge_of_tendsto' hlim' hb) bot_le
  exact le_antisymm (iInf_le _ _) (tsub_eq_zero_iff_le.1 hD)

lemma Vinf_eq_J (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r S : ℝ) (hmin : ∀ y, Jr μ κ L₀ α r S ≤ Jr μ κ L₀ α r y) (x : ℝ) :
    Vinf μ κ L₀ α r x = Jf μ κ L₀ α r (max x S) := by
  rw [Vinf_eq_cS μ κ L₀ α hα0 hα1 r S hmin, cS_rec μ κ L₀ α hα0.le, Jf]
  congr 2
  refine lintegral_congr fun a => ?_
  exact (Vinf_eq_cS μ κ L₀ α hα0 hα1 r S hmin _).symm

lemma sbar_arith (m M c ρ L α t2 s : ℝ) (hm : 0 < m) (hmM : m ≤ M) (hc : 0 ≤ c) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ c) (hα0 : 0 < α) (hα1 : α < 1) (ht2 : 1 ≤ t2) (hL : 0 ≤ L)
    (h : m * s - m * ((L + 1) * c) ≤ M * ((L + 1) * c) + α * (M * (ρ + c) * (1 + L) * t2)) :
    s ≤ 4 * (L + 1) * (M / m) * c * t2 := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  rw [show 4 * (L + 1) * (M / m) * c * t2 = (4 * (L + 1) * M * c * t2) / m by ring,
    le_div_iff₀ hm]
  have k0 : 0 ≤ (L + 1) * c := by positivity
  have k1 : m * ((L + 1) * c) ≤ M * ((L + 1) * c) := mul_le_mul_of_nonneg_right hmM k0
  have k2 : M * ((L + 1) * c) ≤ M * ((L + 1) * c) * t2 :=
    le_mul_of_one_le_right (by positivity) ht2
  have hX : 0 ≤ M * (ρ + c) * (1 + L) * t2 := by positivity
  have k3 : α * (M * (ρ + c) * (1 + L) * t2) ≤ M * (ρ + c) * (1 + L) * t2 := by
    nlinarith
  have k4 : M * (ρ + c) * (1 + L) * t2 ≤ M * (2 * c) * (1 + L) * t2 := by
    have : 0 ≤ M * (1 + L) * t2 := by positivity
    nlinarith
  nlinarith


/-! ## Structure of `V^∞_α` -/

lemma Vinf_convexOn (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r : ℝ) : ConvexOn ℝ Set.univ (fun x => (Vinf μ κ L₀ α r x).toReal) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h := Vinf_convex μ κ L₀ α hα0 hα1 r a b ha hb hab x y
  have hx := Vinf_ne_top μ κ L₀ α hα0 hα1 r x
  have hy := Vinf_ne_top μ κ L₀ α hα0 hα1 r y
  have hfin : ENNReal.ofReal a * Vinf μ κ L₀ α r x + ENNReal.ofReal b * Vinf μ κ L₀ α r y ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy⟩
  calc (Vinf μ κ L₀ α r (a * x + b * y)).toReal
      ≤ (ENNReal.ofReal a * Vinf μ κ L₀ α r x + ENNReal.ofReal b * Vinf μ κ L₀ α r y).toReal :=
        ENNReal.toReal_mono hfin h
    _ = a * (Vinf μ κ L₀ α r x).toReal + b * (Vinf μ κ L₀ α r y).toReal := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy), ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

lemma minimizers_eq (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r S : ℝ) (hmin : ∀ y, Jr μ κ L₀ α r S ≤ Jr μ κ L₀ α r y)
    (hmax : ∀ y, Jr μ κ L₀ α r y ≤ Jr μ κ L₀ α r S → y ≤ S) :
    VinfMinimizers μ κ L₀ α r = Set.Iic S := by
  have hinf : (⨅ x' : ℝ, Vinf μ κ L₀ α r x') = Jf μ κ L₀ α r S := by
    refine le_antisymm (iInf_le_of_le S ?_) (le_iInf fun x' => ?_)
    · rw [Vinf_eq_J μ κ L₀ α hα0 hα1 r S hmin, max_self]
    · rw [Vinf_eq_J μ κ L₀ α hα0 hα1 r S hmin]
      have := J_le_of μ κ L₀ α hα0 hα1 r S hmin S (max x' S) (le_max_right _ _)
      rwa [max_self] at this
  ext x
  simp only [VinfMinimizers, Set.mem_setOf_eq, Set.mem_Iic]
  rw [hinf, Vinf_eq_J μ κ L₀ α hα0 hα1 r S hmin]
  constructor
  · intro h
    by_contra hx
    push_neg at hx
    rw [max_eq_left hx.le] at h
    have : Jr μ κ L₀ α r x ≤ Jr μ κ L₀ α r S := by simp only [Jr, h, le_refl]
    exact absurd (hmax x this) (not_le.2 hx)
  · intro hx
    rw [max_eq_right hx]

lemma S_le_Sbar (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r S : ℝ) (hmin : ∀ y, Jr μ κ L₀ α r S ≤ Jr μ κ L₀ α r y) :
    |S| ≤ Sbar μ κ L₀ α r := by
  have hm : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  have hM : 0 ≤ max κ.b κ.h := le_trans κ.b_pos.le (le_max_left _ _)
  have hc : 0 ≤ |r| + μ.mean := add_nonneg (abs_nonneg _) (mean_nonneg μ)
  obtain ⟨ht1, _⟩ := inv_facts α hα0 hα1
  have ht2 : 1 ≤ ((1 - α) ^ 2)⁻¹ := by
    rw [← inv_pow]; exact one_le_pow₀ ht1
  have h1 := Jr_ge μ κ L₀ α hα0 hα1 r S
  have h2 := hmin 0
  have h3 : Jr μ κ L₀ α r 0 ≤ max κ.b κ.h * ((L₀ + 1) * (|r| + μ.mean)) +
      α * (max κ.b κ.h * (|r| + (|r| + μ.mean)) * (1 + L₀) * ((1 - α) ^ 2)⁻¹) := by
    have e1 := Jf_le μ κ L₀ α r 0
    have e2 := ghat_le μ κ L₀ r 0
    have e3 := Vinf_le_zero μ κ L₀ α hα0 hα1 r (0 + r)
    have hY : 0 ≤ max κ.b κ.h * (|r| + (|r| + μ.mean)) * (1 + L₀) * ((1 - α) ^ 2)⁻¹ := by
      positivity
    have e4 : Jf μ κ L₀ α r 0 ≤ ENNReal.ofReal (max κ.b κ.h * ((L₀ + 1) * (|r| + μ.mean)) +
        α * (max κ.b κ.h * (|r| + (|r| + μ.mean)) * (1 + L₀) * ((1 - α) ^ 2)⁻¹)) := by
      rw [ENNReal.ofReal_add (by positivity) (mul_nonneg hα0.le hY), ENNReal.ofReal_mul hα0.le]
      refine e1.trans (add_le_add ?_ ?_)
      · refine e2.trans (le_of_eq ?_); simp
      · gcongr; simpa using e3
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) e4
  unfold Sbar
  have hL : (0 : ℝ) ≤ L₀ := Nat.cast_nonneg _
  exact sbar_arith (min κ.b κ.h) (max κ.b κ.h) (|r| + μ.mean) |r| L₀ α _ |S| hm
    (min_le_max) hc (abs_nonneg _) (by linarith [mean_nonneg μ]) hα0 hα1 ht2 hL
    (by linarith)

/-! ## `ĝ` is nondecreasing beyond `S̄` -/

lemma Sbar_nonneg (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r : ℝ) : 0 ≤ Sbar μ κ L₀ α r := by
  unfold Sbar
  have := mean_nonneg μ
  have hm : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  have hM : 0 ≤ max κ.b κ.h := le_trans κ.b_pos.le (le_max_left _ _)
  have : (0 : ℝ) ≤ L₀ := Nat.cast_nonneg _
  have : 0 ≤ |r| + μ.mean := add_nonneg (abs_nonneg _) (mean_nonneg μ)
  positivity

lemma Sbar_big (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r : ℝ) : max κ.b κ.h * (((L₀ : ℝ) + 1) * (|r| + μ.mean)) +
      min κ.b κ.h * (((L₀ : ℝ) + 1) * (|r| + μ.mean)) ≤ min κ.b κ.h * Sbar μ κ L₀ α r := by
  have hm : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  have hmM : min κ.b κ.h ≤ max κ.b κ.h := min_le_max
  have hM : 0 ≤ max κ.b κ.h := le_trans κ.b_pos.le (le_max_left _ _)
  have hc : 0 ≤ |r| + μ.mean := add_nonneg (abs_nonneg _) (mean_nonneg μ)
  obtain ⟨ht1, _⟩ := inv_facts α hα0 hα1
  have ht2 : 1 ≤ ((1 - α) ^ 2)⁻¹ := by
    rw [← inv_pow]; exact one_le_pow₀ ht1
  have e : min κ.b κ.h * Sbar μ κ L₀ α r =
      4 * max κ.b κ.h * (((L₀ : ℝ) + 1) * (|r| + μ.mean)) * ((1 - α) ^ 2)⁻¹ := by
    unfold Sbar
    field_simp
  rw [e]
  have k0 : 0 ≤ ((L₀ : ℝ) + 1) * (|r| + μ.mean) := by positivity
  have k1 : max κ.b κ.h * (((L₀ : ℝ) + 1) * (|r| + μ.mean)) ≤
      max κ.b κ.h * (((L₀ : ℝ) + 1) * (|r| + μ.mean)) * ((1 - α) ^ 2)⁻¹ :=
    le_mul_of_one_le_right (by positivity) ht2
  have k2 : min κ.b κ.h * (((L₀ : ℝ) + 1) * (|r| + μ.mean)) ≤
      max κ.b κ.h * (((L₀ : ℝ) + 1) * (|r| + μ.mean)) := mul_le_mul_of_nonneg_right hmM k0
  nlinarith

lemma ghat_mono_big (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r y y' : ℝ) (hy : Sbar μ κ L₀ α r ≤ y) (hyy : y ≤ y') :
    ghat μ κ L₀ r y ≤ ghat μ κ L₀ r y' := by
  rcases eq_or_lt_of_le hyy with h | h
  · rw [h]
  have hS0 := Sbar_nonneg μ κ L₀ α r
  have hy'0 : 0 < y' := lt_of_le_of_lt (hS0.trans hy) h
  have hm : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  have hM : 0 ≤ max κ.b κ.h := le_trans κ.b_pos.le (le_max_left _ _)
  have hc : 0 ≤ |r| + μ.mean := add_nonneg (abs_nonneg _) (mean_nonneg μ)
  have h0 : ghat μ κ L₀ r 0 ≤ ghat μ κ L₀ r y' := by
    have e1 := ghat_le μ κ L₀ r 0
    have e2 := ghat_ge μ κ L₀ r y'
    have e3 : ENNReal.ofReal (max κ.b κ.h * (((L₀ : ℝ) + 1) * (|r| + μ.mean))) +
        ENNReal.ofReal (min κ.b κ.h * (((L₀ : ℝ) + 1) * (|r| + μ.mean))) ≤
        ENNReal.ofReal (min κ.b κ.h * |y'|) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_pos hy'0]
      have := Sbar_big μ κ L₀ α hα0 hα1 r
      nlinarith [mul_le_mul_of_nonneg_left (hy.trans hyy) hm.le]
    have e4 := (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 (e3.trans e2)
    refine e1.trans (le_of_eq_of_le ?_ e4)
    simp
  set l := y / y' with hl
  have hl0 : 0 ≤ l := div_nonneg (hS0.trans hy) hy'0.le
  have hl1 : l ≤ 1 := (div_le_one hy'0).2 hyy
  have e : y = l * y' + (1 - l) * 0 := by
    rw [hl, mul_zero, add_zero, div_mul_cancel₀ _ hy'0.ne']
  calc ghat μ κ L₀ r y = ghat μ κ L₀ r (l * y' + (1 - l) * 0) := by rw [← e]
    _ ≤ ENNReal.ofReal l * ghat μ κ L₀ r y' + ENNReal.ofReal (1 - l) * ghat μ κ L₀ r 0 :=
        ghat_convex μ κ L₀ r l (1 - l) hl0 (by linarith) (by ring) y' 0
    _ ≤ ENNReal.ofReal l * ghat μ κ L₀ r y' + ENNReal.ofReal (1 - l) * ghat μ κ L₀ r y' := by
        gcongr
    _ = ghat μ κ L₀ r y' := by
        rw [← add_mul, ← ENNReal.ofReal_add hl0 (by linarith), add_sub_cancel,
          ENNReal.ofReal_one, one_mul]

/-! ## Bound (8): the clamped policy -/

lemma upTo_local (π : SSPolicy) (r x : ℝ) :
    ∀ i (d d' : Path), (∀ j < i, d j = d' j) → ssOrderUpTo π r x d i = ssOrderUpTo π r x d' i := by
  have hord : ∀ i (d d' : Path), (∀ j < i, d j = d' j) → ssOrder π d i = ssOrder π d' i := by
    intro i d d' h
    unfold ssOrder
    congr 2
    funext j
    exact h j j.isLt
  have hpos : ∀ i (d d' : Path), (∀ j < i, d j = d' j) →
      ssPosition π r x d i = ssPosition π r x d' i := by
    intro i
    induction i with
    | zero => intro _ _ _; rfl
    | succ i ih =>
      intro d d' h
      simp only [ssPosition]
      rw [ih d d' (fun j hj => h j (by omega)), hord i d d' (fun j hj => h j (by omega)),
        h i (by omega)]
  intro i d d' h
  unfold ssOrderUpTo
  rw [hpos i d d' h, hord i d d' h]

def Tc (π : SSPolicy) (r x B : ℝ) (n : ℕ) : ℕ → Path → ℝ := fun i d =>
  if i < n then min (ssOrderUpTo π r x d i) B else x - ∑ k ∈ Finset.range i, (d k - r)

lemma Tc_meas (π : SSPolicy) (r x B : ℝ) (n : ℕ) : ∀ i, Measurable (Tc π r x B n i) := by
  intro i
  unfold Tc
  split_ifs
  · exact (measurable_ssOrderUpTo π r x i).min measurable_const
  · exact measurable_const.sub
      (Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).sub measurable_const)

lemma Tc_nonant (π : SSPolicy) (r x B : ℝ) (n : ℕ) : NonAnt (Tc π r x B n) := by
  intro i d d' h
  unfold Tc
  split_ifs
  · rw [upTo_local π r x i d d' h]
  · congr 1
    exact Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.1 hk)]

lemma Tc_le (π : SSPolicy) (r x B : ℝ) (hB : 0 ≤ B) (n : ℕ) :
    ∀ i d, Tc π r x B n i d ≤ max x B + asum r d i := by
  intro i d
  have := asum_nonneg r d i
  unfold Tc
  split_ifs
  · exact (min_le_right _ _).trans ((le_max_right x B).trans (by linarith))
  · have h1 : -(∑ k ∈ Finset.range i, (d k - r)) ≤ asum r d i :=
      (neg_le_abs _).trans (Finset.abs_sum_le_sum_abs _ _)
    linarith [le_max_left x B]

def clampPol (π : SSPolicy) (r x B : ℝ) (n : ℕ) : SSPolicy :=
  tPol (Tc π r x B n) (Tc_meas π r x B n) r x

lemma ssOrder_nonneg (π : SSPolicy) (d : Path) (n : ℕ) : 0 ≤ ssOrder π d n := NNReal.coe_nonneg _

lemma clamp_pos_le (π : SSPolicy) (r x B : ℝ) (n : ℕ) (d : Path) :
    ∀ i, i ≤ n → tpos (Tc π r x B n) r x d i ≤ ssPosition π r x d i := by
  intro i
  induction i with
  | zero => intro _; exact le_refl _
  | succ i ih =>
    intro hi
    have hlt : i < n := by omega
    have h1 := ih (by omega)
    have hy : ssPosition π r x d i ≤ ssOrderUpTo π r x d i := by
      unfold ssOrderUpTo; linarith [ssOrder_nonneg π d i]
    have hT : Tc π r x B n i d = min (ssOrderUpTo π r x d i) B := if_pos hlt
    have hm : max (tpos (Tc π r x B n) r x d i) (Tc π r x B n i d) ≤ ssOrderUpTo π r x d i := by
      rw [hT]; exact max_le (h1.trans hy) (min_le_left _ _)
    simp only [tpos, ssPosition]
    unfold ssOrderUpTo at hm
    linarith

lemma clamp_cost_le (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (π : SSPolicy) (r x : ℝ) (n i : ℕ) (hi : i < n) :
    ∫⁻ d, ssCost κ L₀ (clampPol π r x (Sbar μ κ L₀ α r) n) r x d i ∂pathLaw μ ≤
      ∫⁻ d, ssCost κ L₀ π r x d i ∂pathLaw μ := by
  rw [cost_eq_ghat, cost_eq_ghat]
  refine lintegral_mono fun d => ?_
  unfold clampPol
  rw [tPol_upTo _ _ (Tc_nonant π r x _ n)]
  have hT : Tc π r x (Sbar μ κ L₀ α r) n i d = min (ssOrderUpTo π r x d i) (Sbar μ κ L₀ α r) :=
    if_pos hi
  rw [hT]
  have hy : ssPosition π r x d i ≤ ssOrderUpTo π r x d i := by
    unfold ssOrderUpTo; linarith [ssOrder_nonneg π d i]
  have hp := (clamp_pos_le π r x (Sbar μ κ L₀ α r) n d i hi.le).trans hy
  rcases le_total (ssOrderUpTo π r x d i) (Sbar μ κ L₀ α r) with h | h
  · rw [min_eq_left h, max_eq_right hp]
  · rw [min_eq_right h]
    exact ghat_mono_big μ κ L₀ α hα0 hα1 r _ _ (le_max_right _ _) (max_le hp h)

lemma bound8 (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (π : SSPolicy) (r x : ℝ) (n : ℕ) :
    Vinf μ κ L₀ α r x ≤
      ∫⁻ d, ∑ i ∈ Finset.range n, ENNReal.ofReal (α ^ i) * ssCost κ L₀ π r x d i ∂pathLaw μ +
        ENNReal.ofReal (max κ.b κ.h * (Sbar μ κ L₀ α r + |x| + |r| + μ.mean) * (1 + L₀ + n) *
          ((1 - α) ^ 2)⁻¹ * α ^ n) := by
  set B := Sbar μ κ L₀ α r with hBdef
  have hB : 0 ≤ B := Sbar_nonneg μ κ L₀ α r
  have hM : 0 ≤ max κ.b κ.h := le_trans κ.b_pos.le (le_max_left _ _)
  have hc : 0 ≤ |r| + μ.mean := add_nonneg (abs_nonneg _) (mean_nonneg μ)
  set π' := clampPol π r x B n with hπ'
  have hgrowth : ∀ i d, |ssOrderUpTo π' r x d i| ≤ (|x| + B) + asum r d i := by
    intro i d
    rw [hπ', clampPol, tPol_upTo _ _ (Tc_nonant π r x B n)]
    exact upTo_abs_le _ r x B hB (Tc_le π r x B hB n) d i
  set F : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (α ^ i) * ∫⁻ d, ssCost κ L₀ π' r x d i ∂pathLaw μ
    with hF
  have hsplit : ∑' i, F i = ∑ i ∈ Finset.range n, F i + ∑' j, F (j + n) :=
    (Summable.sum_add_tsum_nat_add' (f := F) (k := n) ENNReal.summable).symm
  have hfin : ∫⁻ d, ∑ i ∈ Finset.range n, ENNReal.ofReal (α ^ i) * ssCost κ L₀ π r x d i
      ∂pathLaw μ = ∑ i ∈ Finset.range n,
        ENNReal.ofReal (α ^ i) * ∫⁻ d, ssCost κ L₀ π r x d i ∂pathLaw μ := by
    rw [lintegral_finsetSum (f := fun i (d : Path) => ENNReal.ofReal (α ^ i) *
      ssCost κ L₀ π r x d i) _ (fun i _ => (measurable_ssCost κ L₀ π r x i).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact lintegral_const_mul _ (measurable_ssCost κ L₀ π r x i)
  calc Vinf μ κ L₀ α r x ≤ ∫⁻ d, ssDiscCost κ L₀ α π' r x d ∂pathLaw μ := iInf_le _ _
    _ = ∑' i, F i := disc_int μ κ L₀ α π' r x
    _ = ∑ i ∈ Finset.range n, F i + ∑' j, F (j + n) := hsplit
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (α ^ i) * ∫⁻ d, ssCost κ L₀ π r x d i ∂pathLaw μ +
          ∑' j : ℕ, ENNReal.ofReal (α ^ (j + n)) * ENNReal.ofReal (max κ.b κ.h *
            ((|x| + B) + (((j + n : ℕ) : ℝ) + L₀ + 1) * (|r| + μ.mean))) := by
        gcongr with i hi j
        · simp only [hF]
          exact mul_le_mul_of_nonneg_left
            (clamp_cost_le μ κ L₀ α hα0 hα1 π r x n i (Finset.mem_range.1 hi)) bot_le
        · simp only [hF]
          gcongr
          exact cost_le_growth μ κ L₀ π' r x (|x| + B) (by positivity) (j + n)
            (fun d => hgrowth (j + n) d)
    _ ≤ _ := by
        rw [hfin]
        gcongr
        refine (tail_sum α hα0 hα1 (max κ.b κ.h) (|x| + B) (|r| + μ.mean) hM (by positivity)
          hc L₀ n).trans (le_of_eq ?_)
        congr 1
        ring

lemma Vinf_le_Vn (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r x : ℝ) (n : ℕ) :
    Vinf μ κ L₀ α r x ≤ Vn μ κ L₀ α n r x +
      ENNReal.ofReal (max κ.b κ.h * (Sbar μ κ L₀ α r + |x| + |r| + μ.mean) * (1 + L₀ + n) *
        ((1 - α) ^ 2)⁻¹ * α ^ n) := by
  unfold Vn
  rw [ENNReal.iInf_add]
  exact le_iInf fun π => bound8 μ κ L₀ α hα0 hα1 π r x n

lemma Vn_le_Vinf (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r x : ℝ) (n : ℕ) :
    Vn μ κ L₀ α n r x ≤ Vinf μ κ L₀ α r x := by
  unfold Vn Vinf
  refine iInf_mono fun π => lintegral_mono fun d => ?_
  unfold ssDiscCost
  exact ENNReal.sum_le_tsum (Finset.range n)

lemma tendsto_Vn (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (r x : ℝ) :
    Tendsto (fun n => Vn μ κ L₀ α n r x) atTop (nhds (Vinf μ κ L₀ α r x)) := by
  set K := max κ.b κ.h * (Sbar μ κ L₀ α r + |x| + |r| + μ.mean) * ((1 - α) ^ 2)⁻¹
  set E : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (max κ.b κ.h * (Sbar μ κ L₀ α r + |x| + |r| +
    μ.mean) * (1 + L₀ + n) * ((1 - α) ^ 2)⁻¹ * α ^ n) with hE
  have hlim : Tendsto (fun n : ℕ => max κ.b κ.h * (Sbar μ κ L₀ α r + |x| + |r| +
      μ.mean) * (1 + L₀ + n) * ((1 - α) ^ 2)⁻¹ * α ^ n) atTop (nhds 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hα0.le hα1
    have h2 := tendsto_self_mul_const_pow_of_lt_one hα0.le hα1
    have h3 := (h1.const_mul (K * (1 + L₀))).add (h2.const_mul K)
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun n => ?_
    ring
  have hE0 : Tendsto E atTop (nhds 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hlim
    rw [ENNReal.ofReal_zero] at this
    exact this
  have hlow : Tendsto (fun n => Vinf μ κ L₀ α r x - E n) atTop
      (nhds (Vinf μ κ L₀ α r x - 0)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds hE0 (Or.inl (Vinf_ne_top μ κ L₀ α hα0 hα1 r x))
  rw [tsub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    (fun n => Vn_le_Vinf μ κ L₀ α r x n)
  exact tsub_le_iff_right.2 (Vinf_le_Vn μ κ L₀ α hα0 hα1 r x n)

end XGLB

open MeasureTheory ProbabilityTheory Filter ENNReal NNReal XinGoldbergTBS.Asymptotic in
theorem solution (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ (r x : ℝ) (n : ℕ), 1 ≤ n →
      Vn μ κ L₀ α n r x ≤ Vinf μ κ L₀ α r x ∧
      Vinf μ κ L₀ α r x ≤ Vn μ κ L₀ α n r x +
        ENNReal.ofReal (max κ.b κ.h * (Sbar μ κ L₀ α r + |x| + |r| + μ.mean) *
          (1 + L₀ + n) * ((1 - α) ^ 2)⁻¹ * α ^ n)) ∧
    (∀ r x : ℝ, Tendsto (fun n => Vn μ κ L₀ α n r x) atTop (nhds (Vinf μ κ L₀ α r x))) ∧
    (∀ r : ℝ,
      (∀ x : ℝ, Vinf μ κ L₀ α r x ≠ ⊤) ∧
      ConvexOn ℝ Set.univ (fun x => (Vinf μ κ L₀ α r x).toReal) ∧
      Monotone (fun x => Vinf μ κ L₀ α r x) ∧
      (VinfMinimizers μ κ L₀ α r).Nonempty ∧
      BddAbove (VinfMinimizers μ κ L₀ α r) ∧
      |Sinf μ κ L₀ α r| ≤ Sbar μ κ L₀ α r ∧
      ∀ x : ℝ, ∃ π : SSPolicy, IsStationaryMarkov π (baseStockRule (Sinf μ κ L₀ α r)) r x ∧
        ∫⁻ d, ssDiscCost κ L₀ α π r x d ∂pathLaw μ = Vinf μ κ L₀ α r x) := by
  refine ⟨fun r x n _ => ⟨XGLB.Vn_le_Vinf μ κ L₀ α r x n, XGLB.Vinf_le_Vn μ κ L₀ α hα0 hα1 r x n⟩,
    fun r x => XGLB.tendsto_Vn μ κ L₀ α hα0 hα1 r x, fun r => ?_⟩
  obtain ⟨S, hmin, hmax⟩ := XGLB.exists_S μ κ L₀ α hα0 hα1 r
  have hmz : VinfMinimizers μ κ L₀ α r = Set.Iic S :=
    XGLB.minimizers_eq μ κ L₀ α hα0 hα1 r S hmin hmax
  have hSinf : Sinf μ κ L₀ α r = S := by
    unfold Sinf
    rw [hmz, csSup_Iic]
  refine ⟨fun x => XGLB.Vinf_ne_top μ κ L₀ α hα0 hα1 r x, XGLB.Vinf_convexOn μ κ L₀ α hα0 hα1 r,
    XGLB.Vinf_mono μ κ L₀ α r, ?_, ?_, ?_, ?_⟩
  · rw [hmz]; exact Set.nonempty_Iic
  · rw [hmz]; exact bddAbove_Iic
  · rw [hSinf]; exact XGLB.S_le_Sbar μ κ L₀ α hα0 hα1 r S hmin
  · intro x
    rw [hSinf]
    exact ⟨XGLB.bsPol S r x, XGLB.bs_markov S r x,
      (XGLB.Vinf_eq_cS μ κ L₀ α hα0 hα1 r S hmin x).symm⟩
