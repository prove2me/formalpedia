-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.calculus_coordinate_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:04:05.764989+00:00
-- url     : https://prove2.me/submissions/e25be70f-4c9e-4409-830e-2728df95c61f

import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_first_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_further_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_generating_set

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05.X7U

variable {k : Type*} [RCLike k]
variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]

/-- agreement set of two calculi -/
def Agree (F G : Symbol X k → Relation H) : Set (Symbol X k) := {f | F f = G f}

lemma sym_ext {f g : Symbol X k} (h : ∀ x, f.val x = g.val x) : f = g := Subtype.ext (funext h)

lemma qr_pos' (z : k) : (1 + ‖z‖ ^ 2 : ℝ) ≠ 0 := by positivity

lemma qr_pos (f : Symbol X k) (x : X) : (1 + ‖f.val x‖ ^ 2 : ℝ) ≠ 0 := by positivity

section
variable {F G : Symbol X k → Relation H} (hF : Calculus F) (hG : Calculus G)
include hF hG

lemma ag_const (c : k) : constant c ∈ Agree F G := by
  have e : (constant c : Symbol X k) = scalar c (constant 1) := sym_ext fun x => by simp [constant, scalar]
  have hb : ∀ (F : Symbol X k → Relation H), Calculus F → BoundedOperator (k := k) (F (constant 1)) := by
    intro F hF; rw [hF.2.1.1]
    exact ⟨ContinuousLinearMap.id k H, by ext p; simp [identity, boundedGraph]⟩
  show F _ = G _
  rw [e, (calculus_first_properties F hF).1 c _ (Or.inr (hb F hF)),
    (calculus_first_properties G hG).1 c _ (Or.inr (hb G hG)), hF.2.1.1, hG.2.1.1]

lemma ag_plus {f g : Symbol X k} (hf : f ∈ Agree F G) (hg : g ∈ Agree F G) : plus f g ∈ Agree F G := by
  show F _ = G _
  rw [← ((calculus_further_properties F hF).2.1 f g).1, ← ((calculus_further_properties G hG).2.1 f g).1]
  rw [show F f = G f from hf, show F g = G g from hg]

lemma ag_times {f g : Symbol X k} (hf : f ∈ Agree F G) (hg : g ∈ Agree F G) : times f g ∈ Agree F G := by
  show F _ = G _
  rw [← ((calculus_further_properties F hF).2.1 f g).2, ← ((calculus_further_properties G hG).2.1 f g).2]
  rw [show F f = G f from hf, show F g = G g from hg]

lemma ag_star {f : Symbol X k} (hf : f ∈ Agree F G) : starSymbol f ∈ Agree F G := by
  show F _ = G _
  rw [← (calculus_further_properties F hF).2.2.1 f, ← (calculus_further_properties G hG).2.2.1 f]
  rw [show F f = G f from hf]

lemma ag_recip {f : Symbol X k} (hf : f ∈ Agree F G) (h0 : ∀ x, f.val x ≠ 0) : reciprocal f ∈ Agree F G := by
  show F _ = G _
  rw [← ((calculus_first_properties F hF).2.2.1 f h0).2, ← ((calculus_first_properties G hG).2.2.1 f h0).2]
  rw [show F f = G f from hf]

lemma ag_scalar (c : k) {f : Symbol X k} (hf : f ∈ Agree F G) : scalar c f ∈ Agree F G := by
  have : scalar c f = times (constant c) f := sym_ext fun x => rfl
  rw [this]; exact ag_times hF hG (ag_const hF hG c) hf

lemma ag_congr {f g : Symbol X k} (hf : f ∈ Agree F G) (h : ∀ x, f.val x = g.val x) : g ∈ Agree F G := by
  rw [← sym_ext h]; exact hf

lemma ag_quad_fwd {f : Symbol X k} (hf : f ∈ Agree F G) :
    times f (quadraticRegularizer f) ∈ Agree F G ∧ quadraticRegularizer f ∈ Agree F G := by
  have ht : plus (constant 1) (times (starSymbol f) f) ∈ Agree F G :=
    ag_plus hF hG (ag_const hF hG 1) (ag_times hF hG (ag_star hF hG hf) hf)
  have hv : ∀ x, (plus (constant 1) (times (starSymbol f) f)).val x = ((1 + ‖f.val x‖ ^ 2 : ℝ) : k) := by
    intro x
    simp only [plus, constant, times, starSymbol]
    rw [RCLike.star_def, RCLike.conj_mul]; push_cast; ring
  have h0 : ∀ x, (plus (constant 1) (times (starSymbol f) f)).val x ≠ 0 := by
    intro x; rw [hv]; exact_mod_cast qr_pos f x
  have hq : quadraticRegularizer f ∈ Agree F G := by
    refine ag_congr hF hG (ag_recip hF hG ht h0) fun x => ?_
    simp only [reciprocal, quadraticRegularizer]
    rw [hv]
  exact ⟨ag_times hF hG hf hq, hq⟩

lemma ag_quad_bwd {f : Symbol X k} (h1 : times f (quadraticRegularizer f) ∈ Agree F G)
    (h2 : quadraticRegularizer f ∈ Agree F G) : f ∈ Agree F G := by
  have h0 : ∀ x, (quadraticRegularizer f).val x ≠ 0 := by
    intro x; simp only [quadraticRegularizer]
    have := qr_pos f x
    exact_mod_cast inv_ne_zero this
  refine ag_congr hF hG (ag_times hF hG h1 (ag_recip hF hG h2 h0)) fun x => ?_
  simp only [times, reciprocal]
  rw [mul_assoc, mul_inv_cancel₀ (h0 x), mul_one]

end

lemma value_bg (T : H →L[k] H) (y : H) : value (boundedGraph T) y = T y := by
  have h : ∃ z, (y, z) ∈ boundedGraph T := ⟨T y, rfl⟩
  unfold value; rw [dif_pos h]
  exact Classical.choose_spec h

lemma weak_unique {A : ℕ → Relation H} {B B' : Relation H} (h : Weak (k := k) A B) (h' : Weak (k := k) A B') :
    B = B' := by
  obtain ⟨T, rfl⟩ := h.2.1
  obtain ⟨T', rfl⟩ := h'.2.1
  have : T = T' := by
    ext y
    refine ext_inner_left k fun x => ?_
    have := tendsto_nhds_unique (h.2.2 x y) (h'.2.2 x y)
    rwa [value_bg, value_bg] at this
  rw [this]

lemma qr_cont : Continuous fun z : k => ((1 + ‖z‖ ^ 2 : ℝ)⁻¹ : k) := by
  refine (RCLike.continuous_ofReal.comp (continuous_const.add (continuous_norm.pow 2))).inv₀ fun z => ?_
  simp only [Function.comp]
  exact_mod_cast (qr_pos' z)

lemma qr_le (z : k) : ‖((1 + ‖z‖ ^ 2 : ℝ)⁻¹ : k)‖ ≤ 1 := by
  rw [norm_inv, RCLike.norm_ofReal, abs_of_pos (by positivity)]
  exact inv_le_one_of_one_le₀ (by nlinarith [norm_nonneg z])

lemma zqr_le (z : k) : ‖z * ((1 + ‖z‖ ^ 2 : ℝ)⁻¹ : k)‖ ≤ 1 := by
  rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos (by positivity), ← div_eq_mul_inv,
    div_le_one (by positivity)]
  nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - 1)]

section
variable {F G : Symbol X k → Relation H} (hF : Calculus F) (hG : Calculus G)
include hF hG

lemma ag_bp {fn : ℕ → Symbol X k} {f : Symbol X k} (hn : ∀ n, fn n ∈ Agree F G) (hbp : BP fn f) :
    f ∈ Agree F G := by
  have h1 := hF.2.2.2 fn f hbp
  have h2 := hG.2.2.2 fn f hbp
  have : (fun n => F (fn n)) = (fun n => G (fn n)) := funext hn
  rw [this] at h1
  exact weak_unique h1 h2

lemma ag_pointwise {fn : ℕ → Symbol X k} {f : Symbol X k} (hn : ∀ n, fn n ∈ Agree F G)
    (hp : Pointwise fn f) : f ∈ Agree F G := by
  have hq : ∀ x, Tendsto (fun n => (quadraticRegularizer (fn n)).val x) atTop
      (𝓝 ((quadraticRegularizer f).val x)) := fun x =>
    ((qr_cont).tendsto _).comp (hp x)

  refine ag_quad_bwd hF hG ?_ ?_
  · refine ag_bp hF hG (fun n => (ag_quad_fwd hF hG (hn n)).1) ⟨fun x => (hp x).mul (hq x), 1, fun n x => ?_⟩
    exact zqr_le ((fn n).val x)
  · refine ag_bp hF hG (fun n => (ag_quad_fwd hF hG (hn n)).2) ⟨hq, 1, fun n x => ?_⟩
    exact qr_le ((fn n).val x)

end

/-- Heron iteration for the square root -/
def her (t : ℝ) : ℕ → ℝ
  | 0 => 1 + t
  | n + 1 => (her t n + t / her t n) / 2

lemma her_pos {t : ℝ} (ht : 0 ≤ t) : ∀ n, 0 < her t n
  | 0 => by simp [her]; linarith
  | n + 1 => by
    have := her_pos ht n
    simp only [her]; positivity

lemma her_ge {t : ℝ} (ht : 0 ≤ t) : ∀ n, Real.sqrt t ≤ her t n
  | 0 => by
    simp only [her]
    have h1 := Real.sq_sqrt ht
    nlinarith [sq_nonneg (Real.sqrt t - 1), Real.sqrt_nonneg t]
  | n + 1 => by
    have hp := her_pos ht n
    simp only [her]
    have h1 := Real.sq_sqrt ht
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), ← sub_nonneg]
    have : her t n + t / her t n - Real.sqrt t * 2 = (her t n - Real.sqrt t) ^ 2 / her t n := by
      field_simp; linarith [h1]
    rw [this]; positivity

lemma her_err {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    her t (n + 1) - Real.sqrt t ≤ (her t n - Real.sqrt t) / 2 := by
  have hp := her_pos ht n
  have hg := her_ge ht n
  have h1 := Real.sq_sqrt ht
  have hs := Real.sqrt_nonneg t
  simp only [her]
  have : (her t n + t / her t n) / 2 - Real.sqrt t = (her t n - Real.sqrt t) ^ 2 / (2 * her t n) := by
    field_simp; linarith [h1]
  rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hg) hs]

lemma her_bound {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    her t n - Real.sqrt t ≤ (her t 0 - Real.sqrt t) / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc her t (n + 1) - Real.sqrt t ≤ (her t n - Real.sqrt t) / 2 := her_err ht n
      _ ≤ (her t 0 - Real.sqrt t) / 2 ^ n / 2 := by linarith
      _ = _ := by rw [pow_succ, div_div]

lemma her_tendsto {t : ℝ} (ht : 0 ≤ t) : Tendsto (her t) atTop (𝓝 (Real.sqrt t)) := by
  have h2 : Tendsto (fun n : ℕ => Real.sqrt t + (her t 0 - Real.sqrt t) / 2 ^ n) atTop
      (𝓝 (Real.sqrt t + 0)) := by
    refine tendsto_const_nhds.add ?_
    simp_rw [div_eq_mul_inv, ← inv_pow]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹)
      (by norm_num)).const_mul (her t 0 - Real.sqrt t)
  rw [add_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun n => her_ge ht n)
    (fun n => ?_)
  have := her_bound ht n
  simp only; linarith

lemma real_eq {f : Symbol X k} (hf : RealValued f) (x : X) : f.val x = ((RCLike.re (f.val x) : ℝ) : k) :=
  (RCLike.conj_eq_iff_re.mp (hf x)).symm

/-- Heron symbols -/
def hsym (f : Symbol X k) : ℕ → Symbol X k
  | 0 => plus (constant 1) (times (starSymbol f) f)
  | n + 1 => times (constant (1 / 2)) (plus (hsym f n) (times (times (starSymbol f) f) (reciprocal (hsym f n))))

lemma star_mul_self' (z : k) : star z * z = ((‖z‖ ^ 2 : ℝ) : k) := by
  rw [RCLike.star_def, RCLike.conj_mul]; push_cast; rfl

lemma hsym_val (f : Symbol X k) (x : X) : ∀ n, (hsym f n).val x = ((her (‖f.val x‖ ^ 2) n : ℝ) : k)
  | 0 => by
    simp only [hsym, plus, constant, times, starSymbol, her]
    rw [star_mul_self']; push_cast; ring
  | n + 1 => by
    simp only [hsym, plus, constant, times, starSymbol, reciprocal, her]
    rw [hsym_val f x n, star_mul_self']; push_cast; ring

section
variable {F G : Symbol X k → Relation H} (hF : Calculus F) (hG : Calculus G)
include hF hG

lemma ag_hsym {f : Symbol X k} (hf : f ∈ Agree F G) : ∀ n, hsym f n ∈ Agree F G
  | 0 => ag_plus hF hG (ag_const hF hG 1) (ag_times hF hG (ag_star hF hG hf) hf)
  | n + 1 => by
    have h0 : ∀ x, (hsym f n).val x ≠ 0 := fun x => by
      rw [hsym_val]; exact_mod_cast (her_pos (by positivity) n).ne'
    exact ag_times hF hG (ag_const hF hG _) (ag_plus hF hG (ag_hsym hf n)
      (ag_times hF hG (ag_times hF hG (ag_star hF hG hf) hf) (ag_recip hF hG (ag_hsym hf n) h0)))

lemma ag_abs {f : Symbol X k} (hf : f ∈ Agree F G) : absolute f ∈ Agree F G := by
  refine ag_pointwise hF hG (ag_hsym hF hG hf) fun x => ?_
  simp only [hsym_val, absolute]
  have := her_tendsto (sq_nonneg ‖f.val x‖)
  rw [Real.sqrt_sq (norm_nonneg _)] at this
  exact (RCLike.continuous_ofReal.tendsto _).comp this

lemma ag_max {f g : Symbol X k} (hf : f ∈ Agree F G) (hg : g ∈ Agree F G) (rf : RealValued f)
    (rg : RealValued g) : realMax f g ∈ Agree F G ∧ realMin f g ∈ Agree F G := by
  have hd := ag_abs hF hG (ag_plus hF hG hf (ag_scalar hF hG (-1) hg))
  have hs := ag_plus hF hG hf hg
  constructor
  · refine ag_congr hF hG (ag_times hF hG (ag_const hF hG (1 / 2)) (ag_plus hF hG hs hd)) fun x => ?_
    simp only [times, constant, plus, absolute, scalar, realMax]
    rw [real_eq rf x, real_eq rg x]
    simp only [RCLike.ofReal_re]
    rw [show (RCLike.re (f.val x) : k) + -1 * (RCLike.re (g.val x) : k) =
      ((RCLike.re (f.val x) - RCLike.re (g.val x) : ℝ) : k) by push_cast; ring, RCLike.norm_ofReal]
    rcases le_total (RCLike.re (f.val x)) (RCLike.re (g.val x)) with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]; push_cast; ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]; push_cast; ring
  · refine ag_congr hF hG (ag_times hF hG (ag_const hF hG (1 / 2))
      (ag_plus hF hG hs (ag_scalar hF hG (-1) hd))) fun x => ?_
    simp only [times, constant, plus, absolute, scalar, realMin]
    rw [real_eq rf x, real_eq rg x]
    simp only [RCLike.ofReal_re]
    rw [show (RCLike.re (f.val x) : k) + -1 * (RCLike.re (g.val x) : k) =
      ((RCLike.re (f.val x) - RCLike.re (g.val x) : ℝ) : k) by push_cast; ring, RCLike.norm_ofReal]
    rcases le_total (RCLike.re (f.val x)) (RCLike.re (g.val x)) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; push_cast; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; push_cast; ring

end
end QAlgorithms.Papers.Independent.Claimed50.P05.X7U

namespace QAlgorithms.Papers.Independent.Claimed50.P05.X7U

variable {k : Type*} [RCLike k]
variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]

lemma ind_val (A : Set X) (hA : MeasurableSet A) (x : X) :
    (indicator (k := k) A hA).val x = if x ∈ A then 1 else 0 := by
  simp [indicator, Set.indicator_apply]

/-- partial unions -/
def acc (A : ℕ → Set X) : ℕ → Set X
  | 0 => A 0
  | n + 1 => acc A n ∪ A (n + 1)

lemma acc_meas {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n)) : ∀ n, MeasurableSet (acc A n)
  | 0 => hA 0
  | n + 1 => (acc_meas hA n).union (hA (n + 1))

lemma mem_acc {A : ℕ → Set X} {x : X} : ∀ n, x ∈ acc A n ↔ ∃ i ≤ n, x ∈ A i
  | 0 => by simp [acc]
  | n + 1 => by
    simp only [acc, mem_union, mem_acc n]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n + 1, le_rfl, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_or_ge i (n + 1) with h' | h'
      · exact Or.inl ⟨i, by omega, h⟩
      · have : i = n + 1 := by omega
        subst this; exact Or.inr h

lemma rv_of {f : Symbol X k} (r : X → ℝ) (h : ∀ x, f.val x = (r x : k)) : RealValued f := fun x => by
  rw [h, RCLike.star_def, RCLike.conj_ofReal]

section
variable {F G : Symbol X k → Relation H} (hF : Calculus F) (hG : Calculus G)
include hF hG

lemma ag_ind_congr {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A = B)
    (hm : indicator (k := k) A hA ∈ Agree F G) : indicator (k := k) B hB ∈ Agree F G := by
  subst h; exact hm

lemma ag_ind_empty : indicator (k := k) (∅ : Set X) MeasurableSet.empty ∈ Agree F G :=
  ag_congr hF hG (ag_const hF hG 0) fun x => by rw [ind_val]; simp [constant]

lemma ag_ind_univ : indicator (k := k) (univ : Set X) MeasurableSet.univ ∈ Agree F G :=
  ag_congr hF hG (ag_const hF hG 1) fun x => by rw [ind_val]; simp [constant]

lemma ag_ind_compl {A : Set X} (hA : MeasurableSet A) (h : indicator (k := k) A hA ∈ Agree F G) :
    indicator (k := k) Aᶜ hA.compl ∈ Agree F G := by
  refine ag_congr hF hG (ag_plus hF hG (ag_const hF hG 1) (ag_scalar hF hG (-1) h)) fun x => ?_
  simp only [plus, constant, scalar]
  rw [ind_val, ind_val]
  by_cases hx : x ∈ A <;> simp [hx]

lemma ag_ind_union {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h1 : indicator (k := k) A hA ∈ Agree F G) (h2 : indicator (k := k) B hB ∈ Agree F G) :
    indicator (k := k) (A ∪ B) (hA.union hB) ∈ Agree F G := by
  refine ag_congr hF hG (ag_plus hF hG (ag_plus hF hG h1 h2)
    (ag_scalar hF hG (-1) (ag_times hF hG h1 h2))) fun x => ?_
  simp only [plus, times, scalar]
  rw [ind_val, ind_val, ind_val]
  by_cases hx : x ∈ A <;> by_cases hy : x ∈ B <;> simp [hx, hy]

lemma ag_ind_iUnion (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (h : ∀ n, indicator (k := k) (A n) (hA n) ∈ Agree F G) :
    indicator (k := k) (⋃ n, A n) (MeasurableSet.iUnion hA) ∈ Agree F G := by
  have hacc : ∀ n, indicator (k := k) (acc A n) (acc_meas hA n) ∈ Agree F G := by
    intro n
    induction n with
    | zero => exact h 0
    | succ n ih => exact ag_ind_union hF hG _ _ ih (h (n + 1))
  refine ag_pointwise hF hG hacc fun x => ?_
  rw [ind_val]
  simp_rw [ind_val]
  by_cases hx : x ∈ ⋃ n, A n
  · obtain ⟨m, hm⟩ := mem_iUnion.mp hx
    rw [if_pos hx]
    refine tendsto_atTop_of_eventually_const (i₀ := m) fun n hn => ?_
    rw [if_pos ((mem_acc n).mpr ⟨m, hn, hm⟩)]
  · rw [if_neg hx]
    refine tendsto_atTop_of_eventually_const (i₀ := 0) fun n _ => ?_
    rw [if_neg]
    intro h'
    obtain ⟨i, _, hi⟩ := (mem_acc n).mp h'
    exact hx (mem_iUnion.mpr ⟨i, hi⟩)

/-- preimage of an open ball -/
lemma ag_ball {f : Symbol X k} (hf : f ∈ Agree F G) (c : k) {r : ℝ} (hr : 0 < r) :
    indicator (k := k) (f.val ⁻¹' Metric.ball c r) (measurableSet_ball.preimage f.property) ∈ Agree F G := by
  set g := plus f (constant (-c)) with hg
  have hgE : g ∈ Agree F G := ag_plus hF hG hf (ag_const hF hG _)
  set t := times (starSymbol g) g
  have ht : t ∈ Agree F G := ag_times hF hG (ag_star hF hG hgE) hgE
  have tv : ∀ x, t.val x = ((‖f.val x - c‖ ^ 2 : ℝ) : k) := fun x => by
    show star (g.val x) * g.val x = _
    rw [star_mul_self']
    simp [hg, plus, constant, sub_eq_add_neg]
  let s : ℕ → Symbol X k := fun n => scalar (n : k) (plus (constant ((r ^ 2 : ℝ) : k)) (scalar (-1) t))
  have sv : ∀ n x, (s n).val x = (((n : ℝ) * (r ^ 2 - ‖f.val x - c‖ ^ 2) : ℝ) : k) := fun n x => by
    simp only [s, scalar, plus, constant]; rw [tv]; push_cast; ring
  let φ : ℕ → Symbol X k := fun n => realMin (constant 1) (realMax (constant 0) (s n))
  have hφ : ∀ n, φ n ∈ Agree F G := by
    intro n
    have hs : s n ∈ Agree F G :=
      ag_scalar hF hG _ (ag_plus hF hG (ag_const hF hG _) (ag_scalar hF hG _ ht))
    have r0 : RealValued (constant (0 : k) : Symbol X k) := rv_of (fun _ => 0) fun x => by simp [constant]
    have r1 : RealValued (constant (1 : k) : Symbol X k) := rv_of (fun _ => 1) fun x => by simp [constant]
    have rs : RealValued (s n) := rv_of _ (sv n)
    have hm := (ag_max hF hG (ag_const hF hG 0) hs r0 rs).1
    have rm : RealValued (realMax (constant (0 : k)) (s n)) := rv_of _ fun x => rfl
    exact (ag_max hF hG (ag_const hF hG 1) hm r1 rm).2
  have φv : ∀ n x, (φ n).val x = ((min 1 (max 0 ((n : ℝ) * (r ^ 2 - ‖f.val x - c‖ ^ 2))) : ℝ) : k) := by
    intro n x
    simp only [φ, realMin, realMax, constant, RCLike.one_re, RCLike.zero_re]
    rw [sv]; simp only [RCLike.ofReal_re]
  refine ag_pointwise hF hG hφ fun x => ?_
  simp_rw [φv]
  rw [ind_val]
  by_cases hx : x ∈ f.val ⁻¹' Metric.ball c r
  · rw [if_pos hx]
    have hd : ‖f.val x - c‖ < r := by simpa [dist_eq_norm] using hx
    have hpos : 0 < r ^ 2 - ‖f.val x - c‖ ^ 2 := by nlinarith [norm_nonneg (f.val x - c)]
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / (r ^ 2 - ‖f.val x - c‖ ^ 2))
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
    have : 1 ≤ (n : ℝ) * (r ^ 2 - ‖f.val x - c‖ ^ 2) := by
      have h1 : (N : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_le_iff₀ hpos] at hN
      nlinarith
    rw [max_eq_right (by linarith), min_eq_left this]; simp
  · rw [if_neg hx]
    have hd : r ≤ ‖f.val x - c‖ := by simpa [dist_eq_norm] using hx
    have hneg : r ^ 2 - ‖f.val x - c‖ ^ 2 ≤ 0 := by nlinarith
    refine tendsto_atTop_of_eventually_const (i₀ := 0) fun n _ => ?_
    have : (n : ℝ) * (r ^ 2 - ‖f.val x - c‖ ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hneg
    rw [max_eq_left this, min_eq_right zero_le_one]; simp

end
end QAlgorithms.Papers.Independent.Claimed50.P05.X7U

namespace QAlgorithms.Papers.Independent.Claimed50.P05.X7U

variable {k : Type*} [RCLike k]
variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]

section
variable {F G : Symbol X k → Relation H} (hF : Calculus F) (hG : Calculus G)
include hF hG

lemma ag_open {f : Symbol X k} (hf : f ∈ Agree F G) (U : Set k) (hU : IsOpen U) :
    indicator (k := k) (f.val ⁻¹' U) (hU.measurableSet.preimage f.property) ∈ Agree F G := by
  let S0 : Set (Set k) := {B | ∃ c r, 0 < r ∧ B = Metric.ball c r ∧ B ⊆ U}
  have hS0 : ⋃₀ S0 = U := by
    ext z; constructor
    · rintro ⟨B, ⟨c, r, _, rfl, hB⟩, hz⟩; exact hB hz
    · intro hz
      obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hU z hz
      exact ⟨Metric.ball z ε, ⟨z, ε, hε, rfl, hb⟩, Metric.mem_ball_self hε⟩
  obtain ⟨T, hTc, hTS, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable S0
    (fun s hs => by obtain ⟨c, r, _, rfl, _⟩ := hs; exact Metric.isOpen_ball)
  rcases T.eq_empty_or_nonempty with hT | hT
  · have : U = ∅ := by rw [← hS0, ← hTU, hT, sUnion_empty]
    refine ag_ind_congr hF hG MeasurableSet.empty _ ?_ (ag_ind_empty hF hG)
    rw [this, preimage_empty]
  · obtain ⟨g, hg⟩ := hTc.exists_eq_range hT
    have hgS : ∀ n, ∃ c r, 0 < r ∧ g n = Metric.ball c r := fun n => by
      obtain ⟨c, r, hr, h, _⟩ := hTS (hg ▸ mem_range_self n : g n ∈ T); exact ⟨c, r, hr, h⟩
    have hm : ∀ n, MeasurableSet (f.val ⁻¹' g n) := fun n => by
      obtain ⟨c, r, _, h⟩ := hgS n; rw [h]; exact measurableSet_ball.preimage f.property
    have hi : ∀ n, indicator (k := k) (f.val ⁻¹' g n) (hm n) ∈ Agree F G := fun n => by
      obtain ⟨c, r, hr, h⟩ := hgS n
      exact ag_ind_congr hF hG _ _ (by rw [h]) (ag_ball hF hG hf c hr)
    refine ag_ind_congr hF hG _ _ ?_ (ag_ind_iUnion hF hG _ hm hi)
    rw [← preimage_iUnion, ← sUnion_range, ← hg, hTU, hS0]

/-- σ-algebra of good sets -/
def goodSpace {f : Symbol X k} (hf : f ∈ Agree F G) : MeasurableSpace k where
  MeasurableSet' := fun B => MeasurableSet B ∧
    ∀ h : MeasurableSet (f.val ⁻¹' B), indicator (k := k) (f.val ⁻¹' B) h ∈ Agree F G
  measurableSet_empty := ⟨MeasurableSet.empty, fun h =>
    ag_ind_congr hF hG _ _ (preimage_empty).symm (ag_ind_empty hF hG)⟩
  measurableSet_compl := fun B ⟨hB, hi⟩ => ⟨hB.compl, fun h =>
    ag_ind_congr hF hG _ _ (preimage_compl).symm
      (ag_ind_compl hF hG _ (hi (hB.preimage f.property)))⟩
  measurableSet_iUnion := fun B hB => ⟨MeasurableSet.iUnion fun n => (hB n).1, fun h =>
    ag_ind_congr hF hG _ _ (preimage_iUnion).symm
      (ag_ind_iUnion hF hG _ (fun n => (hB n).1.preimage f.property)
        fun n => (hB n).2 _)⟩

lemma ag_preimage {f : Symbol X k} (hf : f ∈ Agree F G) (B : Set k) (hB : MeasurableSet B) :
    indicator (k := k) (f.val ⁻¹' B) (hB.preimage f.property) ∈ Agree F G := by
  have hle : borel k ≤ goodSpace hF hG hf := MeasurableSpace.generateFrom_le fun U hU =>
    ⟨(show IsOpen U from hU).measurableSet, fun h => ag_open hF hG hf U hU⟩
  have hB' : MeasurableSet[borel k] B := by rw [← BorelSpace.measurable_eq]; exact hB
  exact (hle B hB').2 _

theorem eight : EightProperties (Agree F G) := by
  refine ⟨⟨fun c => ag_const hF hG c, fun f g hf hg => ⟨ag_plus hF hG hf hg, ag_times hF hG hf hg⟩,
    fun f hf => ag_star hF hG hf⟩, fun f hf h0 => ag_recip hF hG hf h0,
    fun f => ⟨fun hf => ag_quad_fwd hF hG hf, fun h => ag_quad_bwd hF hG h.1 h.2⟩,
    fun fn f hn hp => ag_pointwise hF hG hn hp, fun f hf => ag_abs hF hG hf,
    fun f g hf hg rf rg => ag_max hF hG hf hg rf rg,
    ⟨ag_ind_univ hF hG, fun A hA h => ag_ind_compl hF hG hA h, fun A hA h => ag_ind_iUnion hF hG A hA h⟩,
    fun f hf B hB => ag_preimage hF hG hf B hB⟩

end

theorem coord_unique {d : ℕ} (S : Set (Fin d → k))
    (F G : Symbol S k → Relation H) (hF : Calculus F) (hG : Calculus G) :
    ((∀ j, F (restrictedCoordinate S j) = G (restrictedCoordinate S j)) → F = G) ∧
    (((∀ j, F (times (restrictedCoordinate S j) (tupleRegularizer S)) = G (times (restrictedCoordinate S j) (tupleRegularizer S))) ∧
      F (tupleRegularizer S) = G (tupleRegularizer S)) → F = G) ∧
    ((∀ j, F (tupleRootCoordinate S j) = G (tupleRootCoordinate S j)) → F = G) := by
  have h := calculus_generating_set S (Agree F G) (eight hF hG)
  have fin : Agree F G = univ → F = G := fun hu => funext fun f => by
    have : f ∈ Agree F G := hu ▸ mem_univ f
    exact this
  exact ⟨fun hc => fin (h.1.mpr hc), fun hc => fin (h.2.1.mpr hc), fun hc => fin (h.2.2.mpr hc)⟩

end QAlgorithms.Papers.Independent.Claimed50.P05.X7U


universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

open QAlgorithms.Papers.Independent.Claimed50.P05 in
theorem solution {d : ℕ} (S : Set (Fin d → k))
    (F G : QAlgorithms.Papers.Independent.Claimed50.P05.Symbol S k → Relation H) (hF : Calculus F) (hG : Calculus G) :
    ((∀ j, F (restrictedCoordinate S j) = G (restrictedCoordinate S j)) → F = G) ∧
    (((∀ j, F (times (restrictedCoordinate S j) (tupleRegularizer S)) = G (times (restrictedCoordinate S j) (tupleRegularizer S))) ∧
      F (tupleRegularizer S) = G (tupleRegularizer S)) → F = G) ∧
    ((∀ j, F (tupleRootCoordinate S j) = G (tupleRootCoordinate S j)) → F = G) :=
  QAlgorithms.Papers.Independent.Claimed50.P05.X7U.coord_unique S F G hF hG

end
