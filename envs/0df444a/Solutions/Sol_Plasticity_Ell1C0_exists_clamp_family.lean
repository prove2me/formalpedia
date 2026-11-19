-- Prove2me | solution 1 for Plasticity.Ell1C0.exists_clamp_family
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-11-18T19:27:13.328904+00:00
-- url     : https://prove2.me/submissions/e01b99b5-11cf-4b29-a366-a46ddd914ca6

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

namespace Sol_Plasticity_Ell1C0_exists_clamp_family

open Classical

section Scalar
variable {M : Type*} [PseudoMetricSpace M] {J : Type*} (e : J → M) (b : J → ℝ) (S : Set J)

noncomputable def ell (x : M) : Option J → ℝ
  | none => -1
  | some j => if j ∈ S then b j - dist x (e j) else -1

noncomputable def upp (x : M) : Option J → ℝ
  | none => 1
  | some j => if j ∈ S then b j + dist x (e j) else 1

noncomputable def lo (x : M) : ℝ := ⨆ o, ell e b S x o
noncomputable def up (x : M) : ℝ := ⨅ o, upp e b S x o
noncomputable def cl (h : M → ℝ) (x : M) : ℝ := max (lo e b S x) (min (h x) (up e b S x))

variable {e b S}

section
variable (hb1 : ∀ j, |b j| ≤ 1) (hb : ∀ j k, |b j - b k| ≤ dist (e j) (e k))
include hb1

lemma ell_le_one (x : M) (o) : ell e b S x o ≤ 1 := by
  cases o with
  | none => simp [ell]
  | some j =>
    have := hb1 j; have := abs_le.1 this
    simp only [ell]; split_ifs <;> nlinarith [dist_nonneg (x := x) (y := e j)]

lemma neg_one_le_upp (x : M) (o) : -1 ≤ upp e b S x o := by
  cases o with
  | none => simp [upp]
  | some j =>
    have := abs_le.1 (hb1 j)
    simp only [upp]; split_ifs <;> nlinarith [dist_nonneg (x := x) (y := e j)]

include hb

lemma ell_le_upp (x : M) (o o') : ell e b S x o ≤ upp e b S x o' := by
  have h1 := ell_le_one hb1 (e := e) (S := S) x o
  have h2 := neg_one_le_upp hb1 (e := e) (S := S) x o'
  cases o with
  | none => simp only [ell]; linarith
  | some j =>
    cases o' with
    | none => simp only [upp]; linarith
    | some k =>
      by_cases a : j ∈ S <;> by_cases c : k ∈ S <;>
        simp only [ell, upp, a, c, if_true, if_false] at h1 h2 ⊢
      · have := abs_le.1 (hb j k)
        have := dist_triangle_left (e j) (e k) x
        have := dist_comm x (e j)
        linarith [dist_comm x (e j), dist_comm x (e k)]
      all_goals linarith

lemma bddAbove_ell (x : M) : BddAbove (Set.range (ell e b S x)) :=
  ⟨1, by rintro _ ⟨o, rfl⟩; exact ell_le_one hb1 x o⟩

lemma bddBelow_upp (x : M) : BddBelow (Set.range (upp e b S x)) :=
  ⟨-1, by rintro _ ⟨o, rfl⟩; exact neg_one_le_upp hb1 x o⟩

lemma neg_one_le_lo (x : M) : -1 ≤ lo e b S x :=
  le_ciSup_of_le (bddAbove_ell hb1 hb x) none (by simp [ell])

lemma up_le_one (x : M) : up e b S x ≤ 1 :=
  ciInf_le_of_le (bddBelow_upp hb1 hb x) none (by simp [upp])

lemma lo_le_up (x : M) : lo e b S x ≤ up e b S x :=
  ciSup_le fun o => le_ciInf fun o' => ell_le_upp hb1 hb x o o'

lemma ell_le_lo (x : M) (o) : ell e b S x o ≤ lo e b S x :=
  le_ciSup (bddAbove_ell hb1 hb x) o

lemma up_le_upp (x : M) (o) : up e b S x ≤ upp e b S x o :=
  ciInf_le (bddBelow_upp hb1 hb x) o

lemma lo_lip : LipschitzWith 1 (lo e b S) := by
  refine LipschitzWith.of_le_add fun x y => ?_
  refine ciSup_le fun o => ?_
  have : ell e b S x o ≤ ell e b S y o + dist x y := by
    cases o with
    | none => simp only [ell]; linarith [dist_nonneg (x := x) (y := y)]
    | some j =>
      simp only [ell]; split_ifs
      · linarith [dist_triangle y x (e j), dist_comm x y]
      · linarith [dist_nonneg (x := x) (y := y)]
  exact this.trans (add_le_add_left (ell_le_lo hb1 hb y o) _)

lemma up_lip : LipschitzWith 1 (up e b S) := by
  refine LipschitzWith.of_le_add fun x y => ?_
  have key : ∀ o, up e b S x - dist x y ≤ upp e b S y o := by
    intro o
    have : upp e b S x o ≤ upp e b S y o + dist x y := by
      cases o with
      | none => simp only [upp]; linarith [dist_nonneg (x := x) (y := y)]
      | some j =>
        simp only [upp]; split_ifs
        · linarith [dist_triangle x y (e j), dist_comm x y]
        · linarith [dist_nonneg (x := x) (y := y)]
    linarith [up_le_upp hb1 hb (S := S) x o]
  have := le_ciInf key
  show up e b S x ≤ up e b S y + dist x y
  unfold up at this ⊢; linarith

lemma cl_lip {h : M → ℝ} (hh : LipschitzWith 1 h) : LipschitzWith 1 (cl e b S h) := by
  have := (lo_lip (e := e) (b := b) (S := S) hb1 hb).max
    (hh.min (up_lip (e := e) (b := b) (S := S) hb1 hb))
  unfold cl
  simpa only [max_self] using this

omit hb1 hb in
lemma lo_le_cl (h : M → ℝ) (x : M) : lo e b S x ≤ cl e b S h x := le_max_left _ _

lemma cl_le_up (h : M → ℝ) (x : M) : cl e b S h x ≤ up e b S x :=
  max_le (lo_le_up hb1 hb x) (min_le_right _ _)

lemma abs_cl_le (h : M → ℝ) (x : M) : |cl e b S h x| ≤ 1 :=
  abs_le.2 ⟨(neg_one_le_lo hb1 hb x).trans (lo_le_cl h x),
    (cl_le_up hb1 hb h x).trans (up_le_one hb1 hb x)⟩

lemma cl_at (h : M → ℝ) {j : J} (hj : j ∈ S) : cl e b S h (e j) = b j := by
  have h1 : b j ≤ lo e b S (e j) := by
    have := ell_le_lo hb1 hb (S := S) (e j) (some j); simpa [ell, hj] using this
  have h2 : up e b S (e j) ≤ b j := by
    have := up_le_upp hb1 hb (S := S) (e j) (some j); simpa [upp, hj] using this
  have h3 := lo_le_up hb1 hb (S := S) (e j)
  have h4 : lo e b S (e j) = b j := le_antisymm (h3.trans h2) h1
  have h5 : up e b S (e j) = b j := le_antisymm h2 (h1.trans h3)
  unfold cl; rw [h4, h5]; exact max_eq_left (min_le_right _ _)

omit hb1 hb in
lemma cl_eq_h (h : M → ℝ) (x : M) (hx : ∀ j ∈ S, |b j - h x| ≤ dist x (e j))
    (h1 : |h x| ≤ 1) : cl e b S h x = h x := by
  have hl : lo e b S x ≤ h x := by
    refine ciSup_le fun o => ?_
    cases o with
    | none => simp only [ell]; linarith [(abs_le.1 h1).1]
    | some j =>
      simp only [ell]; split_ifs with a
      · linarith [(abs_le.1 (hx j a)).2]
      · linarith [(abs_le.1 h1).1]
  have hu : h x ≤ up e b S x := by
    refine le_ciInf fun o => ?_
    cases o with
    | none => simp only [upp]; linarith [(abs_le.1 h1).2]
    | some j =>
      simp only [upp]; split_ifs with a
      · linarith [(abs_le.1 (hx j a)).1, dist_comm x (e j)]
      · linarith [(abs_le.1 h1).2]
  unfold cl; rw [min_eq_left hu]; exact max_eq_right hl

omit hb1 hb in
lemma real_clamp_eq {LK L U UK h : ℝ} (h1 : LK ≤ L) (h2 : L ≤ U) (h3 : U ≤ UK)
    (h4 : L ≤ max LK h) (h5 : min UK h ≤ U) :
    max L (min h U) = max LK (min h UK) := by
  simp only [max_def, min_def] at *
  split_ifs at * <;> first | rfl | linarith

lemma cl_omit {K : Set J} (hKS : K ⊆ S) (h : M → ℝ) (x : M)
    (hx : ∀ j ∈ S, j ∉ K → |b j - h x| ≤ dist x (e j)) :
    cl e b S h x = cl e b K h x := by
  have h1 : lo e b K x ≤ lo e b S x := by
    refine ciSup_le fun o => ?_
    cases o with
    | none => exact ell_le_lo hb1 hb x none |>.trans' (by simp [ell])
    | some j =>
      by_cases a : j ∈ K
      · have := ell_le_lo hb1 hb (S := S) x (some j)
        simpa [ell, a, hKS a] using this
      · exact (neg_one_le_lo hb1 hb (S := S) x).trans' (by simp [ell, a])
  have h3 : up e b S x ≤ up e b K x := by
    refine le_ciInf fun o => ?_
    cases o with
    | none => exact up_le_one hb1 hb x |>.trans (by simp [upp])
    | some j =>
      by_cases a : j ∈ K
      · have := up_le_upp hb1 hb (S := S) x (some j)
        simpa [upp, a, hKS a] using this
      · exact (up_le_one hb1 hb (S := S) x).trans (by simp [upp, a])
  have h4 : lo e b S x ≤ max (lo e b K x) (h x) := by
    refine ciSup_le fun o => ?_
    cases o with
    | none => exact (neg_one_le_lo hb1 hb (S := K) x).trans (le_max_left _ _) |>.trans' (by simp [ell])
    | some j =>
      by_cases a : j ∈ S
      · by_cases c : j ∈ K
        · have := ell_le_lo hb1 hb (S := K) x (some j)
          simp only [ell, a, c, if_true] at this ⊢
          exact this.trans (le_max_left _ _)
        · simp only [ell, a, if_true]
          exact (by linarith [(abs_le.1 (hx j a c)).2] : b j - dist x (e j) ≤ h x).trans (le_max_right _ _)
      · simp only [ell, a, if_false]
        exact (neg_one_le_lo hb1 hb (S := K) x).trans (le_max_left _ _)
  have h5 : min (up e b K x) (h x) ≤ up e b S x := by
    refine le_ciInf fun o => ?_
    cases o with
    | none => exact (min_le_left _ _).trans (up_le_one hb1 hb x) |>.trans (by simp [upp])
    | some j =>
      by_cases a : j ∈ S
      · by_cases c : j ∈ K
        · have := up_le_upp hb1 hb (S := K) x (some j)
          simp only [upp, a, c, if_true] at this ⊢
          exact (min_le_left _ _).trans this
        · simp only [upp, a, if_true]
          refine (min_le_right _ _).trans ?_
          linarith [(abs_le.1 (hx j a c)).1, dist_comm x (e j)]
      · simp only [upp, a, if_false]
        exact (min_le_left _ _).trans (up_le_one hb1 hb (S := K) x)
  exact real_clamp_eq h1 (lo_le_up hb1 hb x) h3 h4 h5

omit hb1 hb in
lemma cl_congr {K : Set J} {b' : J → ℝ} (hbb : ∀ j ∈ K, b j = b' j) (h : M → ℝ) (x : M) :
    cl e b K h x = cl e b' K h x := by
  have h1 : ell e b K x = ell e b' K x := by
    funext o; cases o with
    | none => rfl
    | some j => by_cases a : j ∈ K <;> simp [ell, a, hbb j]
  have h2 : upp e b K x = upp e b' K x := by
    funext o; cases o with
    | none => rfl
    | some j => by_cases a : j ∈ K <;> simp [upp, a, hbb j]
  simp only [cl, lo, up, h1, h2]

end
end Scalar
section L1
variable {J : Type*} [DecidableEq J]

lemma l1_norm_eq (x : lp (fun _ : J => ℝ) 1) : ‖x‖ = ∑' i, |x i| := by
  have := lp.norm_eq_tsum_rpow (by simp) x
  simpa [Real.rpow_one] using this

lemma l1_summable (x : lp (fun _ : J => ℝ) 1) : Summable fun i => |x i| := by
  have := (lp.memℓp x).summable (by simp)
  simpa [Real.rpow_one] using this

lemma l1_dist_single (x : lp (fun _ : J => ℝ) 1) (j : J) :
    ‖x - lp.single 1 j (1 : ℝ)‖ = ‖x‖ - |x j| + |x j - 1| := by
  have hz := l1_summable (x - lp.single 1 j (1 : ℝ))
  have hx := l1_summable x
  have hz' : ∀ i, (x - lp.single 1 j (1 : ℝ) : lp (fun _ : J => ℝ) 1) i = x i - if i = j then 1 else 0 := by
    intro i
    simp [lp.single_apply, Pi.single_apply]
  rw [l1_norm_eq, l1_norm_eq, hx.tsum_eq_add_tsum_ite j, hz.tsum_eq_add_tsum_ite j]
  have : (∑' i, if i = j then 0 else |(x - lp.single 1 j (1 : ℝ) : lp (fun _ : J => ℝ) 1) i|)
      = ∑' i, if i = j then 0 else |x i| := by
    congr 1; ext i
    by_cases h : i = j <;> simp [h, hz']
  rw [this, hz']
  simp; ring

lemma l1_dist_formula (x : lp (fun _ : J => ℝ) 1) (hx : ‖x‖ ≤ 1) (j : J) :
    ‖x - lp.single 1 j (1 : ℝ)‖ = 1 + ‖x‖ - 2 * max (x j) 0 := by
  rw [l1_dist_single]
  have h1 : |x j| ≤ 1 := (lp.norm_apply_le_norm (by simp) x j).trans hx |>.trans' (by simp)
  rcases le_total (x j) 0 with h | h
  · rw [abs_of_nonpos h, abs_of_nonpos (by linarith), max_eq_right h]; ring
  · rw [abs_of_nonneg h, abs_of_nonpos (by linarith [(abs_le.1 h1).2]), max_eq_left h]; ring

end L1
section Main
open Plasticity Filter Topology
variable {J : Type*} [DecidableEq J]

abbrev L1 (J : Type*) := lp (fun _ : J => ℝ) 1
abbrev Ball (J : Type*) := Metric.closedBall (0 : L1 J) 1

noncomputable def w (k : ℕ) : ℝ := (2 : ℝ) ^ (-((k : ℤ) + 2))

lemma w_eq (k : ℕ) : w k = (1 / 2) ^ k * (1 / 4) := by
  unfold w
  rw [show -((k : ℤ) + 2) = -((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, pow_add]
  have : (2:ℝ)^k * (1/2)^k = 1 := by rw [← mul_pow]; norm_num
  field_simp
  linear_combination (-4) * this

lemma w_pos (k : ℕ) : 0 < w k := by rw [w_eq]; positivity

lemma w_le (k : ℕ) : w k ≤ 1 / 4 := by
  rw [w_eq]
  have : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

lemma w_tendsto : Tendsto w atTop (𝓝 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_const (1 / 4 : ℝ)
  simp only [zero_mul] at this
  exact this.congr fun k => (w_eq k).symm

lemma norm_single_one (j : J) : ‖(lp.single 1 j (1 : ℝ) : L1 J)‖ = 1 := by
  simp [lp.norm_single]

noncomputable def e1 (j : J) : Ball J :=
  ⟨lp.single 1 j (1 : ℝ), by simp [norm_single_one]⟩

lemma dist_e1 (x : Ball J) (j : J) : dist x (e1 j) = ‖(x : L1 J) - lp.single 1 j (1 : ℝ)‖ := by
  rw [Subtype.dist_eq, dist_eq_norm]; rfl

lemma dist_formula (x : Ball J) (j : J) :
    dist x (e1 j) = 1 + ‖(x : L1 J)‖ - 2 * max ((x : L1 J) j) 0 := by
  rw [dist_e1]; exact l1_dist_formula _ (mem_closedBall_zero_iff.1 x.2) j

lemma dist_e1_e1 {j k : J} (h : j ≠ k) : dist (e1 j) (e1 k) = 2 := by
  rw [dist_formula]
  simp [e1, norm_single_one, lp.single_apply, h.symm]
  norm_num

lemma norm_apply_le (x : L1 J) (j : J) : |x j| ≤ ‖x‖ :=
  (lp.norm_apply_le_norm (by simp) x j).trans' (by simp)

noncomputable def bco (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (i : J × ℕ) : J → ℝ :=
  fun j => (((y j : c0 (J × ℕ)) : Linf (J × ℕ)) i)

lemma bco_abs (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (i : J × ℕ) (j : J) :
    |bco y i j| ≤ 1 := by
  have h1 : ‖(y j : c0 (J × ℕ))‖ ≤ 1 := mem_closedBall_zero_iff.1 (y j).2
  have h2 : ‖((y j : c0 (J × ℕ)) : Linf (J × ℕ))‖ ≤ 1 := h1
  exact (lp.norm_apply_le_norm (by simp) _ i).trans' (by simp [bco]) |>.trans h2

lemma bco_pair (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (i : J × ℕ) (j k : J) :
    |bco y i j - bco y i k| ≤ dist (e1 j) (e1 k) := by
  by_cases h : j = k
  · subst h; simp
  · rw [dist_e1_e1 h]
    have := abs_le.1 (bco_abs y i j); have := abs_le.1 (bco_abs y i k)
    rw [abs_le]; constructor <;> linarith

noncomputable def hfun (i : J × ℕ) (x : Ball J) : ℝ := w i.2 * (x : L1 J) i.1

lemma hfun_lip (i : J × ℕ) : LipschitzWith 1 (hfun i) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  simp only [hfun, NNReal.coe_one, one_mul, Real.dist_eq]
  rw [← mul_sub, abs_mul, abs_of_pos (w_pos _)]
  have h1 : |(x : L1 J) i.1 - (x' : L1 J) i.1| ≤ dist x x' := by
    have := norm_apply_le (((x : L1 J) - (x' : L1 J) : L1 J)) i.1
    simpa [Subtype.dist_eq, dist_eq_norm] using this
  have := w_le i.2
  nlinarith [abs_nonneg ((x : L1 J) i.1 - (x' : L1 J) i.1)]

lemma hfun_abs (i : J × ℕ) (x : Ball J) : |hfun i x| ≤ ‖(x : L1 J)‖ / 4 := by
  simp only [hfun, abs_mul, abs_of_pos (w_pos _)]
  have := w_le i.2; have := norm_apply_le (x : L1 J) i.1
  nlinarith [abs_nonneg ((x : L1 J) i.1), w_pos i.2]

lemma l1_finite_ge (x : L1 J) {ε : ℝ} (hε : 0 < ε) : {j | ε ≤ |x j|}.Finite := by
  have := (Metric.tendsto_nhds.1 (l1_summable x).tendsto_cofinite_zero) ε hε
  refine (Filter.eventually_cofinite.1 this).subset ?_
  intro j hj
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_abs, not_lt] at hj ⊢
  exact hj

lemma D_finite (x : L1 J) : {j | ‖x‖ / 4 < x j}.Finite := by
  rcases (norm_nonneg x).eq_or_lt with h | h
  · convert Set.finite_empty
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    rw [← h]; linarith [le_abs_self (x j), norm_apply_le x j]
  · refine (l1_finite_ge x (by linarith : 0 < ‖x‖ / 4)).subset ?_
    intro j hj
    exact (le_of_lt (show ‖x‖ / 4 < x j from hj)).trans (le_abs_self _)

lemma H_tendsto (x : L1 J) : Tendsto (fun i : J × ℕ => w i.2 * x i.1) cofinite (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  rw [Filter.eventually_cofinite]
  have hB : {k : ℕ | ε ≤ ‖x‖ * w k}.Finite := by
    have := (Metric.tendsto_nhds.1 (w_tendsto.const_mul ‖x‖)) ε hε
    rw [mul_zero] at this
    have := Filter.eventually_atTop.1 this
    obtain ⟨N, hN⟩ := this
    refine (Set.finite_lt_nat N).subset ?_
    intro k hk
    by_contra hlt
    have := hN k (not_lt.1 hlt)
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hk this
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (w_pos k).le)] at this
    linarith
  refine ((l1_finite_ge x hε).prod hB).subset ?_
  rintro ⟨j, k⟩ hjk
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, not_lt] at hjk
  rw [abs_mul, abs_of_pos (w_pos k)] at hjk
  have h1 := norm_apply_le x j
  have h2 := w_le k
  have h3 := w_pos k
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_ofPred_eq]
    nlinarith [abs_nonneg (x j)]
  · simp only [Set.mem_ofPred_eq]
    nlinarith [abs_nonneg (x j)]

noncomputable def Fv (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (x : Ball J) (i : J × ℕ) : ℝ :=
  cl e1 (bco y i) Set.univ (hfun i) x

lemma Fv_abs (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (x : Ball J) (i : J × ℕ) : |Fv y x i| ≤ 1 := abs_cl_le (bco_abs y i) (bco_pair y i) _ _

lemma omit_cond (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (x : Ball J) (i : J × ℕ) (j : J)
    (hj : ¬ ‖(x : L1 J)‖ / 4 < (x : L1 J) j) : |bco y i j - hfun i x| ≤ dist x (e1 j) := by
  rw [dist_formula]
  have h0 := norm_nonneg (x : L1 J)
  have hm : max ((x : L1 J) j) 0 ≤ ‖(x : L1 J)‖ / 4 := max_le (not_lt.1 hj) (by linarith)
  have h1 := abs_le.1 (bco_abs y i j)
  have h2 := abs_le.1 (hfun_abs i x)
  rw [abs_le]; constructor <;> linarith

lemma Fv_congr (y y' : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (x : Ball J)
    (h : ∀ j, ‖(x : L1 J)‖ / 4 < (x : L1 J) j → y j = y' j) : Fv y x = Fv y' x := by
  funext i
  set K : Set J := {j | ‖(x : L1 J)‖ / 4 < (x : L1 J) j}
  have hK : K ⊆ Set.univ := Set.subset_univ _
  unfold Fv
  rw [cl_omit (bco_abs y i) (bco_pair y i) hK _ x (fun j _ hjK => omit_cond y x i j hjK),
    cl_omit (bco_abs y' i) (bco_pair y' i) hK _ x (fun j _ hjK => omit_cond y' x i j hjK)]
  exact cl_congr (fun j hj => by simp [bco, h j hj]) _ _

lemma Fv_eq_H (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (x : Ball J)
    (h : ∀ j, (x : L1 J) j ≤ ‖(x : L1 J)‖ / 4) (i : J × ℕ) : Fv y x i = hfun i x := by
  unfold Fv
  rw [cl_omit (bco_abs y i) (bco_pair y i) (Set.empty_subset _) _ x
    (fun j _ _ => omit_cond y x i j (not_lt.2 (h j)))]
  refine cl_eq_h _ x (by simp) ?_
  have := abs_le.1 (hfun_abs i x)
  have h1 := mem_closedBall_zero_iff.1 x.2
  rw [abs_le]; constructor <;> linarith [norm_nonneg (x : L1 J)]

lemma Fv_single (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (x : Ball J) (j : J)
    (h : (x : L1 J) = lp.single 1 j (1 : ℝ)) (i : J × ℕ) : Fv y x i = bco y i j := by
  have : x = e1 j := Subtype.ext h
  subst this
  exact cl_at (bco_abs y i) (bco_pair y i) _ (Set.mem_univ j)

lemma bco_tendsto (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (j : J) :
    Tendsto (fun i : J × ℕ => bco y i j) cofinite (𝓝 0) :=
  (y j : c0 (J × ℕ)).2

lemma Fv_finite (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (x : Ball J)
    (hx : ∀ j, (x : L1 J) ≠ lp.single 1 j (1 : ℝ)) :
    {i | Fv y x i ≠ hfun i x}.Finite := by
  set K : Set J := {j | ‖(x : L1 J)‖ / 4 < (x : L1 J) j} with hKdef
  have hK : K ⊆ Set.univ := Set.subset_univ _
  have hfin : K.Finite := D_finite _
  have hsub : {i | Fv y x i ≠ hfun i x} ⊆
      ⋃ j ∈ K, {i : J × ℕ | dist x (e1 j) ≤ |bco y i j - hfun i x|} := by
    intro i hi
    by_contra hnot
    apply hi
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hnot
    unfold Fv
    rw [cl_omit (bco_abs y i) (bco_pair y i) hK _ x (fun j _ hjK => omit_cond y x i j hjK)]
    refine cl_eq_h _ x (fun j hj => (hnot j hj).le) ?_
    have := abs_le.1 (hfun_abs i x)
    have h1 := mem_closedBall_zero_iff.1 x.2
    rw [abs_le]; constructor <;> linarith [norm_nonneg (x : L1 J)]
  refine (hfin.biUnion fun j _ => ?_).subset hsub
  have hpos : 0 < dist x (e1 j) := dist_pos.2 fun h => hx j (by rw [h]; rfl)
  have ht : Tendsto (fun i : J × ℕ => bco y i j - hfun i x) cofinite (𝓝 0) := by
    have := (bco_tendsto y j).sub (H_tendsto (x : L1 J))
    rw [sub_zero] at this
    exact this
  have := (Metric.tendsto_nhds.1 ht) _ hpos
  refine (Filter.eventually_cofinite.1 this).subset ?_
  intro i hi
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, not_lt] at hi ⊢
  exact hi

lemma Fv_tendsto (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (x : Ball J) :
    Tendsto (Fv y x) cofinite (𝓝 0) := by
  by_cases h : ∃ j, (x : L1 J) = lp.single 1 j (1 : ℝ)
  · obtain ⟨j, hj⟩ := h
    have : Fv y x = fun i => bco y i j := funext (Fv_single y x j hj)
    rw [this]; exact bco_tendsto y j
  · push Not at h
    have hev : ∀ᶠ i in cofinite, hfun i x = Fv y x i :=
      Filter.eventually_cofinite.2 ((Fv_finite y x h).subset fun i hi => Ne.symm hi)
    exact (H_tendsto (x : L1 J)).congr' hev

noncomputable def Gel (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (x : Ball J) :
    c0 (J × ℕ) :=
  ⟨⟨Fv y x, memℓp_infty_iff.2 ⟨1, by
      rintro _ ⟨i, rfl⟩; simpa using Fv_abs y x i⟩⟩, Fv_tendsto y x⟩

lemma Gel_apply (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (x : Ball J) (i : J × ℕ) :
    ((Gel y x : c0 (J × ℕ)) : Linf (J × ℕ)) i = Fv y x i := rfl

lemma Gel_norm (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (x : Ball J) :
    ‖Gel y x‖ ≤ 1 := by
  show ‖((Gel y x : c0 (J × ℕ)) : Linf (J × ℕ))‖ ≤ 1
  refine lp.norm_le_of_forall_le zero_le_one fun i => ?_
  rw [Gel_apply, Real.norm_eq_abs]; exact Fv_abs y x i

noncomputable def Gmap (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) (x : Ball J) :
    Metric.closedBall (0 : c0 (J × ℕ)) 1 :=
  ⟨Gel y x, mem_closedBall_zero_iff.2 (Gel_norm y x)⟩

lemma Gmap_lip (y : J → Metric.closedBall (0 : c0 (J × ℕ)) 1) : LipschitzWith 1 (Gmap y) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  simp only [NNReal.coe_one, one_mul]
  rw [Subtype.dist_eq, dist_eq_norm]
  show ‖((Gel y x - Gel y x' : c0 (J × ℕ)) : Linf (J × ℕ))‖ ≤ dist x x'
  refine lp.norm_le_of_forall_le dist_nonneg fun i => ?_
  have := (cl_lip (S := Set.univ) (bco_abs y i) (bco_pair y i) (hfun_lip i)).dist_le_mul x x'
  rw [Real.dist_eq] at this
  show ‖Fv y x i - Fv y x' i‖ ≤ _
  rw [Real.norm_eq_abs]
  simpa [Fv] using this

end Main
end Sol_Plasticity_Ell1C0_exists_clamp_family

open Plasticity Sol_Plasticity_Ell1C0_exists_clamp_family in
theorem solution (J : Type*) [DecidableEq J] :
    ∃ G : (J → Metric.closedBall (0 : c0 (J × ℕ)) 1) →
        Metric.closedBall (0 : lp (fun _ : J => ℝ) 1) 1 → Metric.closedBall (0 : c0 (J × ℕ)) 1,
      (∀ y, LipschitzWith 1 (G y)) ∧
      (∀ y j (x : Metric.closedBall (0 : lp (fun _ : J => ℝ) 1) 1),
        (x : lp (fun _ : J => ℝ) 1) = lp.single 1 j 1 → G y x = y j) ∧
      (∀ y y' (x : Metric.closedBall (0 : lp (fun _ : J => ℝ) 1) 1),
        (∀ j, ‖(x : lp (fun _ : J => ℝ) 1)‖ / 4 < (x : lp (fun _ : J => ℝ) 1) j → y j = y' j) →
        G y x = G y' x) ∧
      (∀ y (x : Metric.closedBall (0 : lp (fun _ : J => ℝ) 1) 1),
        (∀ j, (x : lp (fun _ : J => ℝ) 1) j ≤ ‖(x : lp (fun _ : J => ℝ) 1)‖ / 4) →
        ∀ i : J × ℕ, ((G y x : c0 (J × ℕ)) : Linf (J × ℕ)) i
            = (2 : ℝ) ^ (-((i.2 : ℤ) + 2)) * (x : lp (fun _ : J => ℝ) 1) i.1) ∧
      (∀ y (x : Metric.closedBall (0 : lp (fun _ : J => ℝ) 1) 1),
        (∀ j, (x : lp (fun _ : J => ℝ) 1) ≠ lp.single 1 j 1) →
        {i : J × ℕ | ((G y x : c0 (J × ℕ)) : Linf (J × ℕ)) i
            ≠ (2 : ℝ) ^ (-((i.2 : ℤ) + 2)) * (x : lp (fun _ : J => ℝ) 1) i.1}.Finite) := by
  refine ⟨Gmap, Gmap_lip, ?_, ?_, ?_, ?_⟩
  · intro y j x hx
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun i => ?_)))
    exact Fv_single y x j hx i
  · intro y y' x h
    have := Fv_congr y y' x h
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun i => ?_)))
    exact congrFun this i
  · intro y x h i
    exact Fv_eq_H y x h i
  · intro y x h
    exact Fv_finite y x h

