-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.calculus_scalar_measure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:43:25.778578+00:00
-- url     : https://prove2.me/submissions/7fc2c477-9192-4ec0-93fb-39a3b17cec95

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05


noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05.X7C



variable {k : Type*} [RCLike k]
variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]

lemma bdd_graph {F : Symbol X k → Relation H} (hF : Calculus F) {f : Symbol X k}
    (hf : BoundedSymbol f) : ∃ T : H →L[k] H, F f = boundedGraph T :=
  ((hF.2.2.1 f hf).1)

lemma value_bg (T : H →L[k] H) (y : H) : value (boundedGraph T) y = T y := by
  have h : ∃ z, (y, z) ∈ boundedGraph T := ⟨T y, rfl⟩
  unfold value; rw [dif_pos h]
  exact (Classical.choose_spec h)

lemma mem_value {F : Symbol X k → Relation H} (hF : Calculus F) {f : Symbol X k}
    (hf : BoundedSymbol f) (y : H) : (y, value (F f) y) ∈ F f := by
  obtain ⟨T, hT⟩ := bdd_graph hF hf
  rw [hT, value_bg]; rfl

lemma eq_value {F : Symbol X k → Relation H} (hF : Calculus F) {f : Symbol X k}
    (hf : BoundedSymbol f) {y z : H} (h : (y, z) ∈ F f) : z = value (F f) y := by
  obtain ⟨T, hT⟩ := bdd_graph hF hf
  rw [hT] at h ⊢; rw [value_bg]; exact h

lemma bdd_plus {f g : Symbol X k} (hf : BoundedSymbol f) (hg : BoundedSymbol g) :
    BoundedSymbol (plus f g) := by
  obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := hg
  exact ⟨a + b, fun x => (norm_add_le _ _).trans (add_le_add (ha x) (hb x))⟩

lemma bdd_times {f g : Symbol X k} (hf : BoundedSymbol f) (hg : BoundedSymbol g) :
    BoundedSymbol (times f g) := by
  obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := hg
  refine ⟨a * b, fun x => ?_⟩
  show ‖f.val x * g.val x‖ ≤ a * b
  rw [norm_mul]
  exact mul_le_mul (ha x) (hb x) (norm_nonneg _) ((norm_nonneg _).trans (ha x))

lemma bdd_scalar (c : k) {f : Symbol X k} (hf : BoundedSymbol f) :
    BoundedSymbol (scalar c f) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨‖c‖ * a, fun x => by
    show ‖c * f.val x‖ ≤ ‖c‖ * a
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (ha x) (norm_nonneg _)⟩

lemma bdd_star {f : Symbol X k} (hf : BoundedSymbol f) : BoundedSymbol (starSymbol f) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, fun x => by show ‖star (f.val x)‖ ≤ a; rw [norm_star]; exact ha x⟩

lemma bdd_const (c : k) : BoundedSymbol (constant (X := X) c) := ⟨‖c‖, fun _ => le_rfl⟩

lemma bdd_ind (A : Set X) (hA : MeasurableSet A) : BoundedSymbol (indicator (k := k) A hA) :=
  ⟨1, fun x => by
    show ‖A.indicator (fun _ => (1 : k)) x‖ ≤ 1
    by_cases h : x ∈ A <;> simp [h]⟩

variable {F : Symbol X k → Relation H}

lemma val_plus (hF : Calculus F) {f g : Symbol X k} (hf : BoundedSymbol f)
    (hg : BoundedSymbol g) (y : H) :
    value (F (plus f g)) y = value (F f) y + value (F g) y := by
  have h : (y, value (F f) y + value (F g) y) ∈ F (plus f g) :=
    hF.2.1.2.1 f g ⟨_, _, mem_value hF hf y, mem_value hF hg y, rfl⟩
  exact (eq_value hF (bdd_plus hf hg) h).symm

lemma val_scalar (hF : Calculus F) (c : k) {f : Symbol X k} (hf : BoundedSymbol f) (y : H) :
    value (F (scalar c f)) y = c • value (F f) y := by
  have h : (y, c • value (F f) y) ∈ F (scalar c f) :=
    hF.2.1.2.2.1 c f ⟨_, mem_value hF hf y, rfl⟩
  exact (eq_value hF (bdd_scalar c hf) h).symm

lemma val_times (hF : Calculus F) {f g : Symbol X k} (hf : BoundedSymbol f)
    (hg : BoundedSymbol g) (y : H) :
    value (F (times f g)) y = value (F f) (value (F g) y) := by
  have h : (y, value (F f) (value (F g) y)) ∈ F (times f g) :=
    hF.2.1.2.2.2.1 f g ⟨_, mem_value hF hg y, mem_value hF hf _⟩
  exact (eq_value hF (bdd_times hf hg) h).symm

lemma val_one (hF : Calculus F) (y : H) : value (F (constant 1)) y = y := by
  have h : (y, y) ∈ F (constant 1) := by rw [hF.2.1.1]; rfl
  exact (eq_value hF (bdd_const 1) h).symm

lemma val_adj (hF : Calculus F) {f : Symbol X k} (hf : BoundedSymbol f) (y z : H) :
    inner k (value (F f) y) z = inner k y (value (F (starSymbol f)) z) := by
  have h : (z, value (F (starSymbol f)) z) ∈ graphAdjoint (k := k) (F f) := by
    rw [(hF.2.2.1 f hf).2]; exact mem_value hF (bdd_star hf) z
  exact ((h y (value (F f) y) (mem_value hF hf y))).symm

lemma val_weak (hF : Calculus F) {fn : ℕ → Symbol X k} {f : Symbol X k} (h : BP fn f) (y z : H) :
    Tendsto (fun n => inner k z (value (F (fn n)) y)) atTop (𝓝 (inner k z (value (F f) y))) :=
  (hF.2.2.2 fn f h).2.2 z y

lemma val_add_fn (hF : Calculus F) {f : Symbol X k} (hf : BoundedSymbol f) (y y' : H) :
    value (F f) (y + y') = value (F f) y + value (F f) y' := by
  obtain ⟨T, hT⟩ := bdd_graph hF hf
  rw [hT, value_bg, value_bg, value_bg, map_add]

lemma val_smul_fn (hF : Calculus F) {f : Symbol X k} (hf : BoundedSymbol f) (c : k) (y : H) :
    value (F f) (c • y) = c • value (F f) y := by
  obtain ⟨T, hT⟩ := bdd_graph hF hf
  rw [hT, value_bg, value_bg, map_smul]

end QAlgorithms.Papers.Independent.Claimed50.P05.X7C


noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05.X7C

variable {k : Type*} [RCLike k]
variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]
variable {F : Symbol X k → Relation H}

lemma ind_sq (A : Set X) (hA : MeasurableSet A) :
    times (indicator (k := k) A hA) (indicator A hA) = indicator A hA := by
  apply Subtype.ext; funext x
  by_cases h : x ∈ A <;> simp [times, indicator, h]

lemma ind_star (A : Set X) (hA : MeasurableSet A) :
    starSymbol (indicator (k := k) A hA) = indicator A hA := by
  apply Subtype.ext; funext x
  by_cases h : x ∈ A <;> simp [starSymbol, indicator, h]

lemma ind_union (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B) :
    indicator (k := k) (A ∪ B) (hA.union hB) = plus (indicator A hA) (indicator B hB) := by
  apply Subtype.ext; funext x
  show (A ∪ B).indicator (fun _ => (1 : k)) x =
    A.indicator (fun _ => (1 : k)) x + B.indicator (fun _ => (1 : k)) x
  rw [Set.indicator_union_of_disjoint hd]

lemma ind_univ : indicator (k := k) (Set.univ : Set X) MeasurableSet.univ = constant 1 := by
  apply Subtype.ext; funext x; simp [indicator, constant]

lemma ind_empty : indicator (k := k) (∅ : Set X) MeasurableSet.empty = scalar 0 (constant 1) := by
  apply Subtype.ext; funext x; simp [indicator, constant, scalar]

/-- ⟪x, P_A x⟫ = ‖P_A x‖². -/
lemma inner_P (hF : Calculus F) (A : Set X) (hA : MeasurableSet A) (x : H) :
    inner k x (value (F (indicator A hA)) x) =
      ((‖value (F (indicator A hA)) x‖ ^ 2 : ℝ) : k) := by
  have hb := bdd_ind (k := k) A hA
  have h1 : value (F (indicator A hA)) x =
      value (F (indicator A hA)) (value (F (indicator A hA)) x) := by
    rw [← val_times hF hb hb, ind_sq]
  have h2 : inner k (value (F (indicator A hA)) x) (value (F (indicator A hA)) x) =
      inner k x (value (F (indicator A hA)) (value (F (indicator A hA)) x)) := by
    rw [val_adj hF hb, ind_star]
  rw [← h1] at h2
  rw [← h2, inner_self_eq_norm_sq_to_K]; push_cast; rfl

lemma re_inner_P (hF : Calculus F) (A : Set X) (hA : MeasurableSet A) (x : H) :
    RCLike.re (inner k x (value (F (indicator A hA)) x)) = ‖value (F (indicator A hA)) x‖ ^ 2 := by
  rw [inner_P hF]; exact RCLike.ofReal_re _

/-- the scalar spectral measure -/
def specMeasure (hF : Calculus F) (x : H) : Measure X :=
  Measure.ofMeasurable
    (fun A hA => ENNReal.ofReal (RCLike.re (inner k x (value (F (indicator A hA)) x))))
    (by
      rw [re_inner_P hF]
      have : value (F (indicator (k := k) (∅ : Set X) MeasurableSet.empty)) x = 0 := by
        rw [ind_empty, val_scalar hF 0 (bdd_const 1), zero_smul]
      rw [this]; simp)
    (by
      intro A hA hd
      simp only [re_inner_P hF]
      -- partial unions
      set B : ℕ → Set X := fun n => ⋃ i ∈ Finset.range n, A i with hBdef
      have hBm : ∀ n, MeasurableSet (B n) := fun n =>
        Finset.measurableSet_biUnion _ (fun i _ => hA i)
      have hBsucc : ∀ n, B (n + 1) = B n ∪ A n := by
        intro n; simp only [hBdef, Finset.range_add_one, Finset.set_biUnion_insert]
        rw [Set.union_comm]
      have hBdisj : ∀ n, Disjoint (B n) (A n) := by
        intro n
        simp only [hBdef, Set.disjoint_iUnion_left]
        intro i hi
        exact hd (Finset.mem_range.1 hi).ne
      -- additivity of the inner product
      have hadd : ∀ n, inner k x (value (F (indicator (B n) (hBm n))) x) =
          ∑ i ∈ Finset.range n, inner k x (value (F (indicator (A i) (hA i))) x) := by
        intro n
        induction n with
        | zero =>
          have : indicator (k := k) (B 0) (hBm 0) = scalar 0 (constant 1) := by
            apply Subtype.ext; funext y; simp [indicator, constant, scalar, hBdef]
          rw [this, val_scalar hF 0 (bdd_const 1), zero_smul]; simp
        | succ n ih =>
          have e : indicator (k := k) (B (n + 1)) (hBm (n + 1)) =
              plus (indicator (B n) (hBm n)) (indicator (A n) (hA n)) := by
            rw [← ind_union _ _ (hBm n) (hA n) (hBdisj n)]
            apply Subtype.ext; funext y; simp only [indicator]; rw [hBsucc]
          rw [e, val_plus hF (bdd_ind _ _) (bdd_ind _ _), inner_add_right, ih,
            Finset.sum_range_succ]
      -- BP convergence
      have hBP : BP (fun n => indicator (k := k) (B n) (hBm n))
          (indicator (⋃ i, A i) (MeasurableSet.iUnion hA)) := by
        refine ⟨fun y => ?_, ⟨1, fun n y => by
          by_cases h : y ∈ B n <;> simp [indicator, h]⟩⟩
        · by_cases hy : y ∈ ⋃ i, A i
          · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
            have hev : ∀ᶠ n in atTop, y ∈ B n := by
              filter_upwards [eventually_gt_atTop i] with n hn
              simp only [hBdef, Set.mem_iUnion]
              exact ⟨i, Finset.mem_range.2 hn, hi⟩
            have : ∀ᶠ n in atTop, (indicator (k := k) (B n) (hBm n)).val y = 1 := by
              filter_upwards [hev] with n hn
              simp [indicator, hn]
            simp only [indicator, Set.indicator_of_mem hy]
            exact tendsto_const_nhds.congr' (this.mono fun n h => h.symm)
          · have h0 : ∀ n, (B n).indicator (fun _ => (1 : k)) y = 0 := by
              intro n
              have : y ∉ B n := by
                simp only [hBdef, Set.mem_iUnion, not_exists]
                intro i _ hi; exact hy (Set.mem_iUnion.2 ⟨i, hi⟩)
              simp [this]
            simp only [indicator, Set.indicator_of_notMem hy, h0]
            exact tendsto_const_nhds
      have hlim := val_weak hF hBP x x
      simp only [hadd] at hlim
      have hlim' := (RCLike.continuous_re.tendsto _).comp hlim
      simp only [Function.comp_def, map_sum, re_inner_P hF] at hlim'
      have hs : HasSum (fun i => ‖value (F (indicator (A i) (hA i))) x‖ ^ 2)
          (‖value (F (indicator (⋃ i, A i) (MeasurableSet.iUnion hA))) x‖ ^ 2) :=
        (hasSum_iff_tendsto_nat_of_nonneg (fun i => sq_nonneg _) _).2 hlim'
      rw [hs.tsum_eq.symm, ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hs.summable])

lemma specMeasure_apply (hF : Calculus F) (x : H) (A : Set X) (hA : MeasurableSet A) :
    specMeasure hF x A = ENNReal.ofReal (RCLike.re (inner k x (value (F (indicator A hA)) x))) :=
  Measure.ofMeasurable_apply A hA

lemma specMeasure_univ (hF : Calculus F) (x : H) :
    specMeasure hF x Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [specMeasure_apply hF x _ MeasurableSet.univ, re_inner_P hF, ind_univ, val_one hF]

instance (hF : Calculus F) (x : H) : IsFiniteMeasure (specMeasure hF x) :=
  ⟨by rw [specMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

end QAlgorithms.Papers.Independent.Claimed50.P05.X7C


noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05.X7C

variable {k : Type*} [RCLike k]
variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]
variable {F : Symbol X k → Relation H}

def sym (s : SimpleFunc X k) : Symbol X k := ⟨s, s.measurable⟩

lemma bdd_sym (s : SimpleFunc X k) : BoundedSymbol (sym s) := by
  refine ⟨∑ y ∈ s.range, ‖y‖, fun x => ?_⟩
  show ‖s x‖ ≤ ∑ y ∈ s.range, ‖y‖
  exact Finset.single_le_sum (f := fun y => ‖y‖) (fun _ _ => norm_nonneg _) (s.mem_range_self x)

lemma measure_real_eq (hF : Calculus F) (x : H) (A : Set X) (hA : MeasurableSet A) :
    (specMeasure hF x).real A = ‖value (F (indicator (k := k) A hA)) x‖ ^ 2 := by
  rw [Measure.real, specMeasure_apply hF x A hA, re_inner_P hF,
    ENNReal.toReal_ofReal (sq_nonneg _)]

lemma inner_sym (hF : Calculus F) (x : H) (s : SimpleFunc X k) :
    inner k x (value (F (sym s)) x) = ∫ t, s t ∂(specMeasure hF x) := by
  induction s using SimpleFunc.induction with
  | const c hs =>
    rename_i A
    have e : sym (SimpleFunc.piecewise A hs (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
        scalar c (indicator A hs) := by
      apply Subtype.ext; funext t
      simp only [sym, scalar, indicator, SimpleFunc.coe_piecewise, SimpleFunc.coe_const]
      by_cases h : t ∈ A <;> simp [h]
    rw [e, val_scalar hF c (bdd_ind A hs), inner_smul_right, inner_P hF]
    have : (fun t => (SimpleFunc.piecewise A hs (SimpleFunc.const X c) (SimpleFunc.const X 0)) t)
        = A.indicator (fun _ => c) := by
      funext t
      simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const]
      by_cases h : t ∈ A <;> simp [h]
    rw [this, integral_indicator_const c hs, measure_real_eq hF x A hs, RCLike.real_smul_eq_coe_mul]
    ring
  | @add f g hfg hf hg =>
    have e : sym (f + g) = plus (sym f) (sym g) := by
      apply Subtype.ext; funext t; simp [sym, plus]
    rw [e, val_plus hF (bdd_sym f) (bdd_sym g), inner_add_right, hf, hg, SimpleFunc.coe_add,
      ← integral_add (SimpleFunc.integrable_of_isFiniteMeasure f)
        (SimpleFunc.integrable_of_isFiniteMeasure g)]
    rfl

lemma integrable_bdd (μ : Measure X) [IsFiniteMeasure μ] {f : Symbol X k} (hf : BoundedSymbol f) :
    Integrable f.val μ := by
  obtain ⟨C, hC⟩ := hf
  exact Integrable.of_bound f.property.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

lemma inner_int (hF : Calculus F) (x : H) {f : Symbol X k} (hf : BoundedSymbol f) :
    inner k x (value (F f) x) = ∫ t, f.val t ∂(specMeasure hF x) := by
  obtain ⟨C0, hC0⟩ := hf
  set C := max C0 0
  have hC : ∀ t, ‖f.val t‖ ≤ C := fun t => (hC0 t).trans (le_max_left _ _)
  have h0 : (0 : k) ∈ Metric.closedBall (0 : k) C := Metric.mem_closedBall_self (le_max_right _ _)
  let s : ℕ → SimpleFunc X k := fun n =>
    SimpleFunc.approxOn f.val f.property (Metric.closedBall 0 C) 0 h0 n
  have hs_mem : ∀ n t, ‖s n t‖ ≤ C := fun n t => by
    have := SimpleFunc.approxOn_mem f.property h0 n t
    simpa [mem_closedBall_zero_iff] using this
  have hs_lim : ∀ t, Tendsto (fun n => s n t) atTop (𝓝 (f.val t)) := fun t =>
    SimpleFunc.tendsto_approxOn f.property h0
      (subset_closure (by simpa [mem_closedBall_zero_iff] using hC t))
  have hBP : BP (fun n => sym (s n)) f := ⟨hs_lim, C, hs_mem⟩
  have h1 := val_weak hF hBP x x
  simp only [inner_sym hF] at h1
  have h2 : Tendsto (fun n => ∫ t, s n t ∂(specMeasure hF x)) atTop
      (𝓝 (∫ t, f.val t ∂(specMeasure hF x))) :=
    tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (s n).aestronglyMeasurable) (integrable_const C)
      (fun n => Filter.Eventually.of_forall (hs_mem n)) (Filter.Eventually.of_forall hs_lim)
  exact tendsto_nhds_unique h1 h2

lemma integrable_sq (μ : Measure X) [IsFiniteMeasure μ] {f : Symbol X k} (hf : BoundedSymbol f) :
    Integrable (fun t => ‖f.val t‖ ^ 2) μ := by
  obtain ⟨C, hC⟩ := hf
  refine Integrable.of_bound ((f.property.norm.pow_const 2).aestronglyMeasurable) (C ^ 2)
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC t) 2

lemma norm_int (hF : Calculus F) (x : H) {f : Symbol X k} (hf : BoundedSymbol f) :
    ‖value (F f) x‖ ^ 2 = ∫ t, ‖f.val t‖ ^ 2 ∂(specMeasure hF x) := by
  have e1 : inner k (value (F f) x) (value (F f) x) =
      inner k x (value (F (times (starSymbol f) f)) x) := by
    rw [val_adj hF hf, val_times hF (bdd_star hf) hf]
  have e2 := inner_int hF x (bdd_times (bdd_star hf) hf)
  rw [← e1] at e2
  have e3 : ‖value (F f) x‖ ^ 2 = RCLike.re (inner k (value (F f) x) (value (F f) x)) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [e3, e2, ← integral_re (integrable_bdd _ (bdd_times (bdd_star hf) hf))]
  congr 1; funext t
  show RCLike.re (star (f.val t) * f.val t) = ‖f.val t‖ ^ 2
  rw [RCLike.star_def, RCLike.conj_mul]; norm_cast

end QAlgorithms.Papers.Independent.Claimed50.P05.X7C


noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05.X7C

variable {k : Type*} [RCLike k]
variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]
variable {F : Symbol X k → Relation H}

lemma memLp_bdd (μ : Measure X) [IsFiniteMeasure μ] {f : Symbol X k} (hf : BoundedSymbol f) :
    MemLp f.val 2 μ := by
  obtain ⟨C, hC⟩ := hf
  exact MemLp.of_bound f.property.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- class of a bounded symbol in L² -/
def iota (μ : Measure X) [IsFiniteMeasure μ] (f : Symbol X k) (hf : BoundedSymbol f) :
    Lp k 2 μ := (memLp_bdd μ hf).toLp f.val

lemma iota_norm_sq (μ : Measure X) [IsFiniteMeasure μ] {f : Symbol X k} (hf : BoundedSymbol f) :
    ‖iota μ f hf‖ ^ 2 = ∫ t, ‖f.val t‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner k, MeasureTheory.L2.inner_def]
  have hae : (fun a => inner k ((iota μ f hf : Lp k 2 μ) a) ((iota μ f hf : Lp k 2 μ) a)) =ᵐ[μ]
      fun a => ((‖f.val a‖ ^ 2 : ℝ) : k) := by
    filter_upwards [MemLp.coeFn_toLp (memLp_bdd μ hf)] with a ha
    simp only [iota] at ha ⊢
    rw [ha, inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [integral_congr_ae hae, integral_ofReal]
  exact RCLike.ofReal_re _

lemma iota_add (μ : Measure X) [IsFiniteMeasure μ] {f g : Symbol X k} (hf : BoundedSymbol f)
    (hg : BoundedSymbol g) :
    iota μ (plus f g) (bdd_plus hf hg) = iota μ f hf + iota μ g hg := by
  simp only [iota]
  rw [← MemLp.toLp_add]; rfl

lemma iota_smul (μ : Measure X) [IsFiniteMeasure μ] (c : k) {f : Symbol X k}
    (hf : BoundedSymbol f) :
    iota μ (scalar c f) (bdd_scalar c hf) = c • iota μ f hf := by
  simp only [iota]
  rw [← MemLp.toLp_const_smul]; rfl

/-- the isometry property, in difference form -/
lemma dist_eq (hF : Calculus F) (x : H) {f g : Symbol X k} (hf : BoundedSymbol f)
    (hg : BoundedSymbol g) :
    ‖value (F f) x - value (F g) x‖ =
      ‖iota (specMeasure hF x) f hf - iota (specMeasure hF x) g hg‖ := by
  have hng := bdd_scalar (-1 : k) hg
  have hd := bdd_plus hf hng
  have e1 : value (F f) x - value (F g) x = value (F (plus f (scalar (-1) g))) x := by
    rw [val_plus hF hf hng, val_scalar hF _ hg]; simp [sub_eq_add_neg]
  have e2 : iota (specMeasure hF x) f hf - iota (specMeasure hF x) g hg =
      iota (specMeasure hF x) (plus f (scalar (-1) g)) hd := by
    rw [iota_add _ hf hng, iota_smul _ _ hg]; simp [sub_eq_add_neg]
  rw [e1, e2]
  have h1 := norm_int hF x hd
  have h2 := iota_norm_sq (specMeasure hF x) hd
  rw [← h2] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

lemma wd (hF : Calculus F) (x : H) {f g : Symbol X k} (hf : BoundedSymbol f)
    (hg : BoundedSymbol g) (h : iota (specMeasure hF x) f hf = iota (specMeasure hF x) g hg) :
    value (F f) x = value (F g) x := by
  have := dist_eq hF x hf hg
  rw [h, sub_self, norm_zero] at this
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- the submodule of bounded classes -/
def Esub (hF : Calculus F) (x : H) : Submodule k (Lp k 2 (specMeasure hF x)) where
  carrier := {u | ∃ f : Symbol X k, ∃ hf : BoundedSymbol f, iota _ f hf = u}
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨_, bdd_plus hf hg, iota_add _ hf hg⟩
  zero_mem' := by
    refine ⟨scalar 0 (constant 1), bdd_scalar 0 (bdd_const 1), ?_⟩
    rw [iota_smul _ 0 (bdd_const 1), zero_smul]
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl⟩
    exact ⟨_, bdd_scalar c hf, iota_smul _ c hf⟩

/-- the map on bounded classes -/
def T0fun (hF : Calculus F) (x : H) (u : Esub hF x) : H :=
  value (F (Classical.choose u.2)) x

lemma T0fun_spec (hF : Calculus F) (x : H) {f : Symbol X k} (hf : BoundedSymbol f)
    (u : Esub hF x) (hu : (u : Lp k 2 (specMeasure hF x)) = iota _ f hf) :
    T0fun hF x u = value (F f) x := by
  obtain ⟨hg, hgu⟩ := Classical.choose_spec u.2
  exact wd hF x hg hf (hgu.trans hu)

def T0 (hF : Calculus F) (x : H) : Esub hF x →ₗ[k] H where
  toFun := T0fun hF x
  map_add' := by
    intro u v
    obtain ⟨f, hf, hfu⟩ := u.2
    obtain ⟨g, hg, hgv⟩ := v.2
    rw [T0fun_spec hF x hf u hfu.symm, T0fun_spec hF x hg v hgv.symm,
      T0fun_spec hF x (bdd_plus hf hg) (u + v) (by
        rw [Submodule.coe_add, iota_add _ hf hg, hfu, hgv]),
      val_plus hF hf hg]
  map_smul' := by
    intro c u
    obtain ⟨f, hf, hfu⟩ := u.2
    rw [T0fun_spec hF x hf u hfu.symm, T0fun_spec hF x (bdd_scalar c hf) (c • u) (by
        rw [Submodule.coe_smul, iota_smul _ c hf, hfu]),
      val_scalar hF c hf]
    rfl

lemma T0_norm (hF : Calculus F) (x : H) (u : Esub hF x) :
    ‖T0 hF x u‖ = ‖(u : Lp k 2 (specMeasure hF x))‖ := by
  obtain ⟨f, hf, hfu⟩ := u.2
  have h0 : value (F (scalar 0 (constant 1))) x = 0 := by
    rw [val_scalar hF 0 (bdd_const 1), zero_smul]
  have i0 : iota (specMeasure hF x) (scalar 0 (constant (X := X) (1 : k)))
      (bdd_scalar 0 (bdd_const 1)) = 0 := by
    rw [iota_smul _ 0 (bdd_const 1), zero_smul]
  show ‖T0fun hF x u‖ = _
  rw [T0fun_spec hF x hf u hfu.symm]
  have := dist_eq hF x hf (bdd_scalar 0 (bdd_const (X := X) (1 : k)))
  rw [h0, i0, sub_zero, sub_zero] at this
  rw [this, hfu]

end QAlgorithms.Papers.Independent.Claimed50.P05.X7C


noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05.X7C

variable {k : Type*} [RCLike k]
variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]
variable {F : Symbol X k → Relation H}

lemma Esub_dense (hF : Calculus F) (x : H) :
    DenseRange ((Esub hF x).subtypeL : Esub hF x →L[k] Lp k 2 (specMeasure hF x)) := by
  have hd := Lp.simpleFunc.denseRange (E := k) (μ := specMeasure hF x) (p := 2) (by simp)
  refine Dense.mono ?_ hd
  rintro _ ⟨g, rfl⟩
  refine ⟨⟨(g : Lp k 2 (specMeasure hF x)), ?_⟩, rfl⟩
  refine ⟨sym (Lp.simpleFunc.toSimpleFunc g), bdd_sym _, ?_⟩
  conv_rhs => rw [← Lp.simpleFunc.toLp_toSimpleFunc g, Lp.simpleFunc.toLp_eq_toLp]
  rfl

lemma Esub_ui (hF : Calculus F) (x : H) :
    IsUniformInducing ((Esub hF x).subtypeL : Esub hF x →L[k] Lp k 2 (specMeasure hF x)) :=
  isUniformEmbedding_subtype_val.isUniformInducing

def f0 (hF : Calculus F) (x : H) : Esub hF x →L[k] H :=
  (T0 hF x).mkContinuous 1 (fun u => by rw [T0_norm, one_mul]; rfl)

def ext (hF : Calculus F) (x : H) : Lp k 2 (specMeasure hF x) →L[k] H :=
  (f0 hF x).extend (Esub hF x).subtypeL

lemma ext_eq (hF : Calculus F) (x : H) (u : Esub hF x) :
    ext hF x (u : Lp k 2 (specMeasure hF x)) = T0 hF x u := by
  have := ContinuousLinearMap.extend_eq (f0 hF x) (Esub_dense hF x) (Esub_ui hF x) u
  exact this

lemma ext_norm (hF : Calculus F) (x : H) (v : Lp k 2 (specMeasure hF x)) :
    ‖ext hF x v‖ = ‖v‖ := by
  refine (Esub_dense hF x).induction_on v
    (isClosed_eq (continuous_norm.comp (ext hF x).continuous) continuous_norm) (fun u => ?_)
  show ‖ext hF x (u : Lp k 2 (specMeasure hF x))‖ = ‖(u : Lp k 2 (specMeasure hF x))‖
  rw [ext_eq, T0_norm]

lemma ext_iota (hF : Calculus F) (x : H) {f : Symbol X k} (hf : BoundedSymbol f) :
    ext hF x (iota (specMeasure hF x) f hf) = value (F f) x := by
  have := ext_eq hF x ⟨iota (specMeasure hF x) f hf, f, hf, rfl⟩
  rw [show ((⟨iota (specMeasure hF x) f hf, f, hf, rfl⟩ : Esub hF x) : Lp k 2 _) =
    iota (specMeasure hF x) f hf from rfl] at this
  rw [this]
  exact T0fun_spec hF x hf _ rfl

lemma ext_mem (hF : Calculus F) (x : H) (v : Lp k 2 (specMeasure hF x)) :
    ext hF x v ∈ cyclic F x := by
  refine (Esub_dense hF x).induction_on v
    ((Submodule.isClosed_topologicalClosure _).preimage (ext hF x).continuous) (fun u => ?_)
  obtain ⟨f, hf, hfu⟩ := u.2
  show ext hF x (u : Lp k 2 (specMeasure hF x)) ∈ cyclic F x
  rw [← hfu, ext_iota hF x hf]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, rfl⟩)

def W (hF : Calculus F) (x : H) : Lp k 2 (specMeasure hF x) →ₗᵢ[k] cyclic F x where
  toLinearMap := (ext hF x).toLinearMap.codRestrict (cyclic F x) (ext_mem hF x)
  norm_map' := fun v => ext_norm hF x v

lemma W_surj (hF : Calculus F) (x : H) : Function.Surjective (W hF x) := by
  have hiso : Isometry (ext hF x) :=
    AddMonoidHomClass.isometry_of_norm (ext hF x) (ext_norm hF x)
  have hcl : IsClosed (Set.range (ext hF x)) := hiso.isClosedEmbedding.isClosed_range
  let R : Submodule k H := LinearMap.range (ext hF x).toLinearMap
  have hR : IsClosed (R : Set H) := by
    have : (R : Set H) = Set.range (ext hF x) := LinearMap.coe_range _
    rw [this]; exact hcl
  have hle : cyclic F x ≤ R := by
    apply Submodule.topologicalClosure_minimal _ _ hR
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨iota (specMeasure hF x) f hf, ext_iota hF x hf⟩
  rintro ⟨y, hy⟩
  obtain ⟨v, hv⟩ := hle hy
  exact ⟨v, Subtype.ext hv⟩

end QAlgorithms.Papers.Independent.Claimed50.P05.X7C

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

open QAlgorithms.Papers.Independent.Claimed50.P05 QAlgorithms.Papers.Independent.Claimed50.P05.X7C in
theorem solution (F : QAlgorithms.Papers.Independent.Claimed50.P05.Symbol X k → Relation H) (hF : Calculus F) (x : H) :
    ∃ mu : Measure X,
      mu Set.univ < ⊤ ∧ mu Set.univ = ENNReal.ofReal (‖x‖ ^ 2) ∧
      (∀ A (hA : MeasurableSet A),
        mu A = ENNReal.ofReal (RCLike.re (inner k x (value (F (indicator A hA)) x)))) ∧
      (∀ f, BoundedSymbol f → Integrable f.val mu ∧
        inner k x (value (F f) x) = ∫ t, f.val t ∂mu) ∧
      (∀ f, BoundedSymbol f → Integrable (fun t => ‖f.val t‖ ^ 2) mu ∧
        ‖value (F f) x‖ ^ 2 = ∫ t, ‖f.val t‖ ^ 2 ∂mu) ∧
      (∃ V : Lp k 2 mu ≃ₗᵢ[k] cyclic F x,
        ∀ f, BoundedSymbol f → ∃ u : Lp k 2 mu,
          (∀ᵐ t ∂mu, u t = f.val t) ∧ (V u).val = value (F f) x) := by
  refine ⟨specMeasure hF x, measure_lt_top _ _, specMeasure_univ hF x,
    fun A hA => specMeasure_apply hF x A hA,
    fun f hf => ⟨integrable_bdd _ hf, inner_int hF x hf⟩,
    fun f hf => ⟨integrable_sq _ hf, norm_int hF x hf⟩, ?_⟩
  refine ⟨LinearIsometryEquiv.ofSurjective (W hF x) (W_surj hF x), fun f hf => ?_⟩
  refine ⟨iota (specMeasure hF x) f hf, MemLp.coeFn_toLp (memLp_bdd _ hf), ?_⟩
  show ext hF x (iota (specMeasure hF x) f hf) = value (F f) x
  exact ext_iota hF x hf
