-- Prove2me | solution 1 for Plasticity.Ell1C0.exists_tree_clamp_family
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-11-18T20:10:13.682653+00:00
-- url     : https://prove2.me/submissions/5f774fee-ccf7-472e-b8fe-29693e09c90f

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

namespace Sol_Plasticity_Ell1C0_exists_tree_clamp_family

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

lemma ell_le_one (hb1 : ∀ j, |b j| ≤ 1) (x : M) (o) : ell e b S x o ≤ 1 := by
  cases o with
  | none => simp [ell]
  | some j =>
    have := hb1 j; have := abs_le.1 this
    simp only [ell]; split_ifs <;> nlinarith [dist_nonneg (x := x) (y := e j)]

lemma neg_one_le_upp (hb1 : ∀ j, |b j| ≤ 1) (x : M) (o) : -1 ≤ upp e b S x o := by
  cases o with
  | none => simp [upp]
  | some j =>
    have := abs_le.1 (hb1 j)
    simp only [upp]; split_ifs <;> nlinarith [dist_nonneg (x := x) (y := e j)]

lemma ell_le_upp (hb1 : ∀ j, |b j| ≤ 1) (hb : ∀ j ∈ S, ∀ k ∈ S, |b j - b k| ≤ dist (e j) (e k))
    (x : M) (o o') : ell e b S x o ≤ upp e b S x o' := by
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
      · have := abs_le.1 (hb j a k c)
        have := dist_triangle_left (e j) (e k) x
        have := dist_comm x (e j)
        linarith [dist_comm x (e j), dist_comm x (e k)]
      all_goals linarith

lemma bddAbove_ell (hb1 : ∀ j, |b j| ≤ 1) (x : M) : BddAbove (Set.range (ell e b S x)) :=
  ⟨1, by rintro _ ⟨o, rfl⟩; exact ell_le_one hb1 x o⟩

lemma bddBelow_upp (hb1 : ∀ j, |b j| ≤ 1) (x : M) : BddBelow (Set.range (upp e b S x)) :=
  ⟨-1, by rintro _ ⟨o, rfl⟩; exact neg_one_le_upp hb1 x o⟩

lemma neg_one_le_lo (hb1 : ∀ j, |b j| ≤ 1) (x : M) : -1 ≤ lo e b S x :=
  le_ciSup_of_le (bddAbove_ell hb1 x) none (by simp [ell])

lemma lo_le_one (hb1 : ∀ j, |b j| ≤ 1) (x : M) : lo e b S x ≤ 1 :=
  ciSup_le fun o => ell_le_one hb1 x o

lemma up_le_one (hb1 : ∀ j, |b j| ≤ 1) (x : M) : up e b S x ≤ 1 :=
  ciInf_le_of_le (bddBelow_upp hb1 x) none (by simp [upp])

lemma lo_le_up (hb1 : ∀ j, |b j| ≤ 1) (hb : ∀ j ∈ S, ∀ k ∈ S, |b j - b k| ≤ dist (e j) (e k))
    (x : M) : lo e b S x ≤ up e b S x :=
  ciSup_le fun o => le_ciInf fun o' => ell_le_upp hb1 hb x o o'

lemma ell_le_lo (hb1 : ∀ j, |b j| ≤ 1) (x : M) (o) : ell e b S x o ≤ lo e b S x :=
  le_ciSup (bddAbove_ell hb1 x) o

lemma up_le_upp (hb1 : ∀ j, |b j| ≤ 1) (x : M) (o) : up e b S x ≤ upp e b S x o :=
  ciInf_le (bddBelow_upp hb1 x) o

lemma lo_lip (hb1 : ∀ j, |b j| ≤ 1) : LipschitzWith 1 (lo e b S) := by
  refine LipschitzWith.of_le_add fun x y => ?_
  refine ciSup_le fun o => ?_
  have : ell e b S x o ≤ ell e b S y o + dist x y := by
    cases o with
    | none => simp only [ell]; linarith [dist_nonneg (x := x) (y := y)]
    | some j =>
      simp only [ell]; split_ifs
      · linarith [dist_triangle y x (e j), dist_comm x y]
      · linarith [dist_nonneg (x := x) (y := y)]
  exact this.trans (add_le_add_left (ell_le_lo hb1 y o) _)

lemma up_lip (hb1 : ∀ j, |b j| ≤ 1) : LipschitzWith 1 (up e b S) := by
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
    linarith [up_le_upp hb1 (S := S) (e := e) x o]
  have := le_ciInf key
  show up e b S x ≤ up e b S y + dist x y
  unfold up at this ⊢; linarith

lemma cl_lip (hb1 : ∀ j, |b j| ≤ 1) {h : M → ℝ} (hh : LipschitzWith 1 h) :
    LipschitzWith 1 (cl e b S h) := by
  have := (lo_lip (e := e) (b := b) (S := S) hb1).max
    (hh.min (up_lip (e := e) (b := b) (S := S) hb1))
  unfold cl
  simpa only [max_self] using this

lemma lo_le_cl (h : M → ℝ) (x : M) : lo e b S x ≤ cl e b S h x := le_max_left _ _

lemma abs_cl_le (hb1 : ∀ j, |b j| ≤ 1) (h : M → ℝ) (x : M) : |cl e b S h x| ≤ 1 := by
  have h1 := neg_one_le_lo hb1 (e := e) (S := S) x
  have h2 := lo_le_one hb1 (e := e) (S := S) x
  have h3 := up_le_one hb1 (e := e) (S := S) x
  rw [abs_le]; unfold cl
  constructor
  · exact h1.trans (le_max_left _ _)
  · exact max_le h2 ((min_le_right _ _).trans h3)

lemma cl_at (hb1 : ∀ j, |b j| ≤ 1) (hb : ∀ j ∈ S, ∀ k ∈ S, |b j - b k| ≤ dist (e j) (e k))
    (h : M → ℝ) {j : J} (hj : j ∈ S) : cl e b S h (e j) = b j := by
  have h1 : b j ≤ lo e b S (e j) := by
    have := ell_le_lo hb1 (S := S) (e := e) (e j) (some j); simpa [ell, hj] using this
  have h2 : up e b S (e j) ≤ b j := by
    have := up_le_upp hb1 (S := S) (e := e) (e j) (some j); simpa [upp, hj] using this
  have h3 := lo_le_up hb1 hb (e j)
  have h4 : lo e b S (e j) = b j := le_antisymm (h3.trans h2) h1
  have h5 : up e b S (e j) = b j := le_antisymm h2 (h1.trans h3)
  unfold cl; rw [h4, h5]; exact max_eq_left (min_le_right _ _)

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

lemma real_clamp_eq {LK L U UK h : ℝ} (h1 : LK ≤ L) (h2 : L ≤ U) (h3 : U ≤ UK)
    (h4 : L ≤ max LK h) (h5 : min UK h ≤ U) :
    max L (min h U) = max LK (min h UK) := by
  simp only [max_def, min_def] at *
  split_ifs at * <;> first | rfl | linarith

lemma cl_omit (hb1 : ∀ j, |b j| ≤ 1) (hb : ∀ j ∈ S, ∀ k ∈ S, |b j - b k| ≤ dist (e j) (e k))
    {K : Set J} (hKS : K ⊆ S) (h : M → ℝ) (x : M)
    (hx : ∀ j ∈ S, j ∉ K → |b j - h x| ≤ dist x (e j)) :
    cl e b S h x = cl e b K h x := by
  have h1 : lo e b K x ≤ lo e b S x := by
    refine ciSup_le fun o => ?_
    cases o with
    | none => exact ell_le_lo hb1 x none |>.trans' (by simp [ell])
    | some j =>
      by_cases a : j ∈ K
      · have := ell_le_lo hb1 (S := S) (e := e) x (some j)
        simpa [ell, a, hKS a] using this
      · exact (neg_one_le_lo hb1 (S := S) (e := e) x).trans' (by simp [ell, a])
  have h3 : up e b S x ≤ up e b K x := by
    refine le_ciInf fun o => ?_
    cases o with
    | none => exact up_le_one hb1 x |>.trans (by simp [upp])
    | some j =>
      by_cases a : j ∈ K
      · have := up_le_upp hb1 (S := S) (e := e) x (some j)
        simpa [upp, a, hKS a] using this
      · exact (up_le_one hb1 (S := S) (e := e) x).trans (by simp [upp, a])
  have h4 : lo e b S x ≤ max (lo e b K x) (h x) := by
    refine ciSup_le fun o => ?_
    cases o with
    | none => exact (neg_one_le_lo hb1 (S := K) (e := e) x).trans (le_max_left _ _) |>.trans' (by simp [ell])
    | some j =>
      by_cases a : j ∈ S
      · by_cases c : j ∈ K
        · have := ell_le_lo hb1 (S := K) (e := e) x (some j)
          simp only [ell, a, c, if_true] at this ⊢
          exact this.trans (le_max_left _ _)
        · simp only [ell, a, if_true]
          exact (by linarith [(abs_le.1 (hx j a c)).2] : b j - dist x (e j) ≤ h x).trans (le_max_right _ _)
      · simp only [ell, a, if_false]
        exact (neg_one_le_lo hb1 (S := K) (e := e) x).trans (le_max_left _ _)
  have h5 : min (up e b K x) (h x) ≤ up e b S x := by
    refine le_ciInf fun o => ?_
    cases o with
    | none => exact (min_le_left _ _).trans (up_le_one hb1 (S := K) (e := e) x) |>.trans (by simp [upp])
    | some j =>
      by_cases a : j ∈ S
      · by_cases c : j ∈ K
        · have := up_le_upp hb1 (S := K) (e := e) x (some j)
          simp only [upp, a, c, if_true] at this ⊢
          exact (min_le_left _ _).trans this
        · simp only [upp, a, if_true]
          refine (min_le_right _ _).trans ?_
          linarith [(abs_le.1 (hx j a c)).1, dist_comm x (e j)]
      · simp only [upp, a, if_false]
        exact (min_le_left _ _).trans (up_le_one hb1 (S := K) (e := e) x)
  exact real_clamp_eq h1 (lo_le_up hb1 hb x) h3 h4 h5

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

end Scalar

section L1
open Plasticity Filter Topology

abbrev L1 := lp (fun _ : ℕ × ℕ => ℝ) 1
abbrev Ic := (ℕ × ℕ) × ℕ

lemma l1_norm_eq (x : L1) : ‖x‖ = ∑' i, |x i| := by
  have := lp.norm_eq_tsum_rpow (by simp) x
  simpa [Real.rpow_one] using this

lemma l1_summable (x : L1) : Summable fun i => |x i| := by
  have := (lp.memℓp x).summable (by simp)
  simpa [Real.rpow_one] using this

lemma norm_apply_le (x : L1) (j : ℕ × ℕ) : |x j| ≤ ‖x‖ :=
  (lp.norm_apply_le_norm (by simp) x j).trans' (by simp)

lemma norm_sub_eq (x e : L1) : ‖x - e‖ = ∑' j, |x j - e j| := by
  rw [l1_norm_eq]; exact tsum_congr fun j => by simp

lemma sub_summable (x e : L1) : Summable fun j => |x j - e j| := by
  simpa using l1_summable (x - e)

lemma asub (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have := abs_add_le a (-b); simpa [sub_eq_add_neg] using this

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

noncomputable def hfun (i : Ic) (x : L1) : ℝ := w i.2 * x i.1

lemma hfun_lip (i : Ic) : LipschitzWith 1 (hfun i) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  simp only [hfun, NNReal.coe_one, one_mul, Real.dist_eq]
  rw [← mul_sub, abs_mul, abs_of_pos (w_pos _)]
  have h1 : |x i.1 - x' i.1| ≤ dist x x' := by
    have := norm_apply_le (x - x') i.1
    simpa [dist_eq_norm] using this
  have := w_le i.2
  nlinarith [abs_nonneg (x i.1 - x' i.1)]

lemma hfun_abs (i : Ic) (x : L1) : |hfun i x| ≤ ‖x‖ / 4 := by
  simp only [hfun, abs_mul, abs_of_pos (w_pos _)]
  have := w_le i.2; have := norm_apply_le x i.1
  nlinarith [abs_nonneg (x i.1), w_pos i.2]

lemma l1_finite_ge (x : L1) {ε : ℝ} (hε : 0 < ε) : {j | ε ≤ |x j|}.Finite := by
  have := (Metric.tendsto_nhds.1 (l1_summable x).tendsto_cofinite_zero) ε hε
  refine (Filter.eventually_cofinite.1 this).subset ?_
  intro j hj
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, abs_abs, not_lt] at hj ⊢
  exact hj

lemma H_tendsto (x : L1) : Tendsto (fun i : Ic => w i.2 * x i.1) cofinite (𝓝 0) := by
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
    simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hk this
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (w_pos k).le)] at this
    linarith
  refine ((l1_finite_ge x hε).prod hB).subset ?_
  rintro ⟨j, k⟩ hjk
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_lt] at hjk
  rw [abs_mul, abs_of_pos (w_pos k)] at hjk
  have h1 := norm_apply_le x j
  have h2 := w_le k
  have h3 := w_pos k
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_setOf_eq]
    nlinarith [abs_nonneg (x j)]
  · simp only [Set.mem_setOf_eq]
    nlinarith [abs_nonneg (x j)]

def Adm (n : ℕ) (e : L1) : Prop := ‖e‖ = 1 ∧ ∀ j : ℕ × ℕ, 0 ≤ e j ∧ (j.1 ≠ n → e j = 0)

noncomputable def mass (n : ℕ) (x : L1) : ℝ := ∑' m, |x (n, m)|

lemma block_summable (z : L1) (n : ℕ) :
    Summable fun j : ℕ × ℕ => (if j.1 = n then |z j| else 0) :=
  Summable.of_nonneg_of_le (fun j => by split_ifs <;> simp) (fun j => by split_ifs <;> simp)
    (l1_summable z)

lemma block_sum (z : L1) (n : ℕ) :
    ∑' j : ℕ × ℕ, (if j.1 = n then |z j| else 0) = mass n z := by
  rw [(block_summable z n).tsum_prod]
  have : ∀ b : ℕ, (∑' c : ℕ, if (b, c).1 = n then |z (b, c)| else 0)
      = if b = n then mass n z else 0 := by
    intro b; by_cases h : b = n
    · subst h; simp [mass]
    · simp [h]
  simp only [this]; exact tsum_ite_eq n _

lemma mass_le (n : ℕ) (z : L1) : mass n z ≤ ‖z‖ := by
  rw [← block_sum, l1_norm_eq]
  exact Summable.tsum_le_tsum (fun j => by split_ifs <;> simp) (block_summable z n) (l1_summable z)

lemma mass_nonneg (n : ℕ) (z : L1) : 0 ≤ mass n z := tsum_nonneg fun m => abs_nonneg _

lemma mass_eq (n : ℕ) (e : L1) (he : Adm n e) : mass n e = ‖e‖ := by
  rw [← block_sum, l1_norm_eq]
  refine tsum_congr fun j => ?_
  by_cases h : j.1 = n
  · simp [h]
  · simp [h, (he.2 j).2 h]

lemma large_finite (z : L1) : {n | ‖z‖ / 4 < mass n z}.Finite := by
  rcases (norm_nonneg z).eq_or_lt with h | h
  · convert Set.finite_empty
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    linarith [mass_le n z]
  · have hs : Summable fun n => mass n z := (l1_summable z).prod
    have := (Metric.tendsto_nhds.1 hs.tendsto_cofinite_zero) (‖z‖ / 4) (by linarith)
    refine (Filter.eventually_cofinite.1 this).subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_lt] at hn ⊢
    rw [abs_of_nonneg (mass_nonneg n z)]; exact hn.le

lemma dist_lower (n : ℕ) (e x : L1) (he : Adm n e) : 1 + ‖x‖ - 2 * mass n x ≤ ‖x - e‖ := by
  have hex : ∀ j, e j + |x j| - 2 * (if j.1 = n then |x j| else 0) ≤ |x j - e j| := by
    intro j
    obtain ⟨h0, h1⟩ := he.2 j
    by_cases h : j.1 = n
    · simp only [h, if_true]
      have := abs_sub_abs_le_abs_sub (e j) (x j)
      rw [abs_sub_comm (e j), abs_of_nonneg h0] at this
      linarith
    · simp [h, h1 h]
  have hes : Summable fun j => e j := (l1_summable e).congr fun j => abs_of_nonneg (he.2 j).1
  have hte : ∑' j, e j = 1 := by
    rw [← he.1, l1_norm_eq]; exact tsum_congr fun j => (abs_of_nonneg (he.2 j).1).symm
  have hs2 := block_summable x n
  have hsum : ∑' j, (e j + |x j| - 2 * (if j.1 = n then |x j| else 0)) = 1 + ‖x‖ - 2 * mass n x := by
    rw [Summable.tsum_sub (hes.add (l1_summable x)) (hs2.mul_left 2),
      Summable.tsum_add hes (l1_summable x), tsum_mul_left, block_sum, hte, ← l1_norm_eq]
  calc 1 + ‖x‖ - 2 * mass n x = ∑' j, (e j + |x j| - 2 * (if j.1 = n then |x j| else 0)) := hsum.symm
    _ ≤ ∑' j, |x j - e j| :=
        Summable.tsum_le_tsum hex ((hes.add (l1_summable x)).sub (hs2.mul_left 2)) (sub_summable x e)
    _ = ‖x - e‖ := (norm_sub_eq x e).symm

lemma disj_dist {n n' : ℕ} (hn : n ≠ n') {e e' : L1} (he : Adm n e) (he' : Adm n' e') :
    ‖e - e'‖ = 2 := by
  rw [l1_norm_eq]
  have : ∀ j, |(e - e') j| = |e j| + |e' j| := by
    intro j
    by_cases h : j.1 = n
    · have h0 : e' j = 0 := (he'.2 j).2 (by rw [h]; exact hn)
      simp [h0]
    · have h0 : e j = 0 := (he.2 j).2 h
      simp [h0]
  simp_rw [this]
  rw [Summable.tsum_add (l1_summable e) (l1_summable e'), ← l1_norm_eq, ← l1_norm_eq, he.1, he'.1]
  norm_num

end L1

section Core
open Plasticity Filter Topology

noncomputable def ta (F : Finset (ℕ × ℕ)) (u : ℕ × ℕ → ℝ) : ℝ := ∑' j, if j ∈ F then 0 else |u j|

lemma ta_summable (F : Finset (ℕ × ℕ)) {u : ℕ × ℕ → ℝ} (hu : Summable fun j => |u j|) :
    Summable fun j => (if j ∈ F then (0 : ℝ) else |u j|) :=
  Summable.of_nonneg_of_le (fun j => by split_ifs <;> simp) (fun j => by split_ifs <;> simp) hu

lemma split_tail (F : Finset (ℕ × ℕ)) {u : ℕ × ℕ → ℝ} (hu : Summable fun j => |u j|) :
    ∑' j, |u j| = ∑ j ∈ F, |u j| + ta F u := by
  have h1 : ∀ j, |u j| = (if j ∈ F then |u j| else 0) + (if j ∈ F then 0 else |u j|) := by
    intro j; split_ifs <;> simp
  have hs1 : Summable fun j => if j ∈ F then |u j| else 0 :=
    summable_of_ne_finset_zero (s := F) (by intro b hb; simp [hb])
  calc ∑' j, |u j| = ∑' j, ((if j ∈ F then |u j| else 0) + (if j ∈ F then 0 else |u j|)) :=
        tsum_congr h1
    _ = ∑' j, (if j ∈ F then |u j| else 0) + ta F u := Summable.tsum_add hs1 (ta_summable F hu)
    _ = _ := by
        rw [tsum_eq_sum (s := F) (by intro b hb; simp [hb])]
        congr 1
        exact Finset.sum_congr rfl (fun j hj => by simp [hj])

lemma ta_le (F : Finset (ℕ × ℕ)) {u v w : ℕ × ℕ → ℝ} (hu : Summable fun j => |u j|)
    (hv : Summable fun j => |v j|) (hw : Summable fun j => |w j|)
    (hle : ∀ j, |u j| ≤ |v j| + |w j|) : ta F u ≤ ta F v + ta F w := by
  unfold ta
  rw [← Summable.tsum_add (ta_summable F hv) (ta_summable F hw)]
  exact Summable.tsum_le_tsum (fun j => by by_cases h : j ∈ F <;> simp [h, hle j])
    (ta_summable F hu) ((ta_summable F hv).add (ta_summable F hw))

lemma exists_net (K : Set L1) (hK : ∀ e ∈ K, ‖e‖ ≤ 1) (F : Finset (ℕ × ℕ)) {θ : ℝ} (hθ : 0 < θ) :
    ∃ N : Set L1, N.Finite ∧ N ⊆ K ∧ ∀ e ∈ K, ∃ e' ∈ N, ∑ j ∈ F, |e j - e' j| < θ := by
  set π : L1 → (↥F → ℝ) := fun e f => e f.1 with hπ
  have hR : TotallyBounded (π '' K) := by
    refine (isCompact_closedBall (0 : ↥F → ℝ) 1).totallyBounded.subset ?_
    rintro _ ⟨e, he, rfl⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro f; rw [Real.norm_eq_abs]; exact (norm_apply_le e f.1).trans (hK e he)
  set ε : ℝ := θ / (F.card + 1) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨t, htR, htfin, hcov⟩ := Metric.finite_approx_of_totallyBounded hR ε hεpos
  choose! g hgK hgπ using (fun (y : ↥F → ℝ) (hy : y ∈ π '' K) => hy)
  refine ⟨g '' t, htfin.image g, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩; exact hgK y (htR hy)
  · intro e he
    obtain ⟨y, hy, hdist⟩ := Set.mem_iUnion₂.1 (hcov ⟨e, he, rfl⟩)
    refine ⟨g y, ⟨y, hy, rfl⟩, ?_⟩
    have h1 := hgπ y (htR hy)
    have hd : dist (π e) (π (g y)) < ε := by rw [h1]; exact hdist
    rw [dist_pi_lt_iff hεpos] at hd
    calc ∑ j ∈ F, |e j - g y j| = ∑ f : ↥F, |e f.1 - g y f.1| :=
          (Finset.sum_coe_sort F fun j => |e j - g y j|).symm
      _ ≤ ∑ f : ↥F, ε := Finset.sum_le_sum fun f _ => by
          have := hd f; simpa [hπ, Real.dist_eq] using this.le
      _ = F.card * ε := by simp
      _ < θ := by
          rw [hε, ← mul_div_assoc, div_lt_iff₀ (by positivity)]; nlinarith [hθ]

lemma core (K : Set L1) (x : L1) (hs : 0 < ‖x‖) (D : ℝ) (hD : 0 < D)
    (hDK : ∀ e ∈ K, D ≤ ‖x - e‖) (hK : ∀ e ∈ K, ‖e‖ = 1 ∧ ∀ j, 0 ≤ e j)
    {I : Type*} (b : L1 → I → ℝ) (hb1 : ∀ e i, |b e i| ≤ 1)
    (hbt : ∀ e, Tendsto (b e) cofinite (𝓝 0))
    (hq : ∀ e ∈ K, ∀ e' ∈ K, ‖e - e'‖ < 2 → ∀ i, |b e i - b e' i| ≤ ‖e - e'‖ / 4)
    (hh : I → ℝ) (hht : Tendsto hh cofinite (𝓝 0)) :
    ∀ᶠ i in cofinite, ∀ e ∈ K, |b e i - hh i| ≤ ‖x - e‖ := by
  set δ : ℝ := min ‖x‖ D / 20 with hδ
  have hδpos : 0 < δ := by rw [hδ]; have := lt_min hs hD; positivity
  have hδ1 : 20 * δ ≤ ‖x‖ := by rw [hδ]; have := min_le_left ‖x‖ D; linarith
  have hδ2 : 20 * δ ≤ D := by rw [hδ]; have := min_le_right ‖x‖ D; linarith
  obtain ⟨F, hF⟩ : ∃ F : Finset (ℕ × ℕ), ta F x < δ := by
    obtain ⟨F, hF⟩ := ((l1_summable x).hasSum.eventually
      (lt_mem_nhds (by linarith : ∑' j, |x j| - δ < ∑' j, |x j|))).exists
    refine ⟨F, ?_⟩
    have := split_tail F (u := fun j => x j) (l1_summable x)
    simp only at this
    linarith
  obtain ⟨N, hNfin, hNK, hN⟩ := exists_net K (fun e he => (hK e he).1.le) F hδpos
  have h1 : ∀ᶠ i in cofinite, |hh i| < δ := by
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 hht) δ hδpos
  have h2 : ∀ᶠ i in cofinite, ∀ e' ∈ N, |b e' i| < δ :=
    (Filter.eventually_all_finite hNfin).2 fun e' _ => by
      simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 (hbt e')) δ hδpos
  filter_upwards [h1, h2] with i hi1 hi2 e he
  obtain ⟨hne, hnn⟩ := hK e he
  set p := ∑ j ∈ F, e j with hp
  have hte : ta F e = 1 - p := by
    have := split_tail F (u := fun j => e j) (l1_summable e)
    simp only at this
    rw [← l1_norm_eq, hne] at this
    have h' : ∑ j ∈ F, |e j| = p := Finset.sum_congr rfl fun j _ => abs_of_nonneg (hnn j)
    linarith
  have hxs : ‖x‖ = ∑ j ∈ F, |x j| + ta F x := by
    rw [l1_norm_eq]; exact split_tail F (u := fun j => x j) (l1_summable x)
  have hxe : ‖x - e‖ = ∑ j ∈ F, |x j - e j| + ta F (fun j => x j - e j) := by
    rw [norm_sub_eq]; exact split_tail F (u := fun j => x j - e j) (sub_summable x e)
  have h3 : ta F e ≤ ta F (fun j => x j - e j) + ta F x :=
    ta_le F (u := fun j => e j) (l1_summable e) (sub_summable x e) (l1_summable x) (fun j => by
      have a1 := le_abs_self (x j); have a2 := neg_abs_le (x j)
      have a3 := le_abs_self (x j - e j); have a4 := neg_abs_le (x j - e j)
      rw [abs_le]; constructor <;> linarith)
  have h4 : ∑ j ∈ F, |x j| - p ≤ ∑ j ∈ F, |x j - e j| := by
    have := Finset.sum_le_sum (s := F) (f := fun j => |x j| - e j) (g := fun j => |x j - e j|)
      (fun j _ => by
        have := abs_sub_abs_le_abs_sub (x j) (e j)
        rw [abs_of_nonneg (hnn j)] at this; exact this)
    rwa [Finset.sum_sub_distrib] at this
  have h5 : 0 ≤ ∑ j ∈ F, |x j - e j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hlowA : ‖x‖ - 2 * ta F x - 2 * p + 1 ≤ ‖x - e‖ := by linarith
  have hlowC : (1 - p) - ta F x ≤ ‖x - e‖ := by linarith
  have hDe := hDK e he
  by_cases hpd : p ≤ δ
  · have := hb1 e i
    have := asub (b e i) (hh i)
    linarith
  · push Not at hpd
    obtain ⟨e', he'N, hθ⟩ := hN e he
    have he'K := hNK he'N
    obtain ⟨hne', hnn'⟩ := hK e' he'K
    set θ := ∑ j ∈ F, |e j - e' j| with hθdef
    have hp' : p - θ ≤ ∑ j ∈ F, e' j := by
      have := Finset.sum_le_sum (s := F) (f := fun j => e j - e' j) (g := fun j => |e j - e' j|)
        (fun j _ => le_abs_self _)
      rwa [Finset.sum_sub_distrib] at this
      |> fun h => by linarith
    have hte' : ta F e' = 1 - ∑ j ∈ F, e' j := by
      have := split_tail F (u := fun j => e' j) (l1_summable e')
      simp only at this
      rw [← l1_norm_eq, hne'] at this
      have h' : ∑ j ∈ F, |e' j| = ∑ j ∈ F, e' j :=
        Finset.sum_congr rfl fun j _ => abs_of_nonneg (hnn' j)
      linarith
    have hee : ‖e - e'‖ = θ + ta F (fun j => e j - e' j) := by
      rw [norm_sub_eq]; exact split_tail F (u := fun j => e j - e' j) (sub_summable e e')
    have h6 : ta F (fun j => e j - e' j) ≤ ta F e + ta F e' :=
      ta_le F (sub_summable e e') (l1_summable e) (l1_summable e') (fun j => asub (e j) (e' j))
    have hlt : ‖e - e'‖ < 2 := by linarith
    have hqq := hq e he e' he'K hlt i
    have t1 : |b e i - hh i| ≤ |b e i - b e' i| + |b e' i| + |hh i| := by
      calc |b e i - hh i| = |(b e i - b e' i) + (b e' i - hh i)| := by
            rw [show b e i - hh i = (b e i - b e' i) + (b e' i - hh i) by ring]
        _ ≤ |b e i - b e' i| + |b e' i - hh i| := abs_add_le _ _
        _ ≤ _ := by linarith [asub (b e' i) (hh i)]
    have := hi2 e' he'N
    by_cases hpt : 1 - D / 2 ≤ p
    · linarith
    · push Not at hpt
      linarith

end Core

section Main
open Plasticity Filter Topology

abbrev Cb := Metric.closedBall (0 : c0 Ic) 1
abbrev Ball := Metric.closedBall (0 : L1) 1

noncomputable def bco (lab : L1 → Cb) (i : Ic) : L1 → ℝ :=
  fun p => (((lab p : c0 Ic) : Linf Ic) i)

lemma bco_abs (lab : L1 → Cb) (i : Ic) (p : L1) : |bco lab i p| ≤ 1 := by
  have h1 : ‖(lab p : c0 Ic)‖ ≤ 1 := mem_closedBall_zero_iff.1 (lab p).2
  have h2 : ‖((lab p : c0 Ic) : Linf Ic)‖ ≤ 1 := h1
  exact (lp.norm_apply_le_norm (by simp) _ i).trans' (by simp [bco]) |>.trans h2

lemma bco_tendsto (lab : L1 → Cb) (p : L1) :
    Tendsto (fun i : Ic => bco lab i p) cofinite (𝓝 0) := (lab p : c0 Ic).2

lemma coord_dist (a b : Cb) (i : Ic) :
    |((a : c0 Ic) : Linf Ic) i - ((b : c0 Ic) : Linf Ic) i| ≤ dist a b := by
  rw [Subtype.dist_eq, dist_eq_norm]
  have := lp.norm_apply_le_norm (by simp) (((a : c0 Ic) - (b : c0 Ic) : c0 Ic) : Linf Ic) i
  simpa using this

def Kset (E : ℕ → Set L1) (x : L1) : Set L1 :=
  {p | ∃ n, ‖x‖ / 4 < mass n x ∧ p ∈ E n ∧ Adm n p}

def Sset (E : ℕ → Set L1) : Set L1 := {p | ∃ n, p ∈ E n ∧ Adm n p}

lemma Kset_sub (E : ℕ → Set L1) (x : L1) : Kset E x ⊆ Sset E :=
  fun _ ⟨n, _, h1, h2⟩ => ⟨n, h1, h2⟩

noncomputable def Fv (E : ℕ → Set L1) (lab : L1 → Cb) (x : L1) (i : Ic) : ℝ :=
  cl (fun p : L1 => p) (bco lab i) (Kset E x) (hfun i) x

lemma Fv_abs (E : ℕ → Set L1) (lab : L1 → Cb) (x : L1) (i : Ic) : |Fv E lab x i| ≤ 1 :=
  abs_cl_le (bco_abs lab i) _ _

noncomputable def Gel (E : ℕ → Set L1) (lab : L1 → Cb) (x : L1)
    (hT : Tendsto (Fv E lab x) cofinite (𝓝 0)) : c0 Ic :=
  ⟨⟨Fv E lab x, memℓp_infty_iff.2 ⟨1, by
      rintro _ ⟨i, rfl⟩; simpa using Fv_abs E lab x i⟩⟩, hT⟩

lemma Gel_apply (E : ℕ → Set L1) (lab : L1 → Cb) (x : L1)
    (hT : Tendsto (Fv E lab x) cofinite (𝓝 0)) (i : Ic) :
    ((Gel E lab x hT : c0 Ic) : Linf Ic) i = Fv E lab x i := rfl

lemma Gel_norm (E : ℕ → Set L1) (lab : L1 → Cb) (x : L1)
    (hT : Tendsto (Fv E lab x) cofinite (𝓝 0)) : ‖Gel E lab x hT‖ ≤ 1 := by
  show ‖((Gel E lab x hT : c0 Ic) : Linf Ic)‖ ≤ 1
  refine lp.norm_le_of_forall_le zero_le_one fun i => ?_
  rw [Gel_apply, Real.norm_eq_abs]; exact Fv_abs E lab x i

noncomputable def Gdef (E : ℕ → Set L1) (lab : L1 → Cb) (x : Ball) : Cb :=
  if hT : Tendsto (Fv E lab x.1) cofinite (𝓝 0) then
    ⟨Gel E lab x.1 hT, mem_closedBall_zero_iff.2 (Gel_norm E lab x.1 hT)⟩
  else ⟨0, by simp⟩

lemma Gdef_coe (E : ℕ → Set L1) (lab : L1 → Cb) (x : Ball)
    (hT : Tendsto (Fv E lab x.1) cofinite (𝓝 0)) : ((Gdef E lab x : Cb) : c0 Ic) = Gel E lab x.1 hT := by
  unfold Gdef; rw [dif_pos hT]

lemma Gdef_apply (E : ℕ → Set L1) (lab : L1 → Cb) (x : Ball)
    (hT : Tendsto (Fv E lab x.1) cofinite (𝓝 0)) (i : Ic) :
    (((Gdef E lab x : Cb) : c0 Ic) : Linf Ic) i = Fv E lab x.1 i := by
  rw [Gdef_coe E lab x hT]; rfl

lemma Fv_congr' (E E' : ℕ → Set L1) (lab lab' : L1 → Cb) (x : L1)
    (h : ∀ n, ‖x‖ / 4 < mass n x → E' n = E n ∧ ∀ e ∈ E n, lab' e = lab e) :
    Fv E' lab' x = Fv E lab x := by
  funext i
  have hK : Kset E' x = Kset E x := by
    ext p; constructor
    · rintro ⟨n, hn, hp, ha⟩; exact ⟨n, hn, by rw [← (h n hn).1]; exact hp, ha⟩
    · rintro ⟨n, hn, hp, ha⟩; exact ⟨n, hn, by rw [(h n hn).1]; exact hp, ha⟩
  unfold Fv; rw [hK]
  apply cl_congr
  intro p hp
  obtain ⟨n, hn, hpn, _⟩ := hp
  simp only [bco, (h n hn).2 p hpn]

lemma Fv_eq_H (E : ℕ → Set L1) (lab : L1 → Cb) (x : L1) (hx : ‖x‖ ≤ 1)
    (h : ∀ n, mass n x ≤ ‖x‖ / 4) (i : Ic) : Fv E lab x i = hfun i x := by
  have hK : Kset E x = ∅ := by
    ext p; simp only [Kset, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨n, hn, _⟩; linarith [h n]
  unfold Fv; rw [hK]
  refine cl_eq_h _ x (by simp) ?_
  have := hfun_abs i x
  rw [abs_le] at this ⊢; constructor <;> linarith [norm_nonneg x]

section Adm
variable (E : ℕ → Set L1) (lab : L1 → Cb)
  (hadm : ∀ n, ∀ e ∈ E n, Adm n e)
  (hq : ∀ n, ∀ e ∈ E n, ∀ e' ∈ E n, ‖e - e'‖ < 2 → dist (lab e) (lab e') ≤ ‖e - e'‖ / 4)
include hadm hq

lemma bco_close {e e' : L1} (he : e ∈ Sset E) (he' : e' ∈ Sset E) (hlt : ‖e - e'‖ < 2) (i : Ic) :
    |bco lab i e - bco lab i e'| ≤ ‖e - e'‖ / 4 := by
  obtain ⟨n, hn, ha⟩ := he
  obtain ⟨m, hm, ha'⟩ := he'
  have hnm : n = m := by
    by_contra hne
    rw [disj_dist hne ha ha'] at hlt; linarith
  subst hnm
  exact (coord_dist (lab e) (lab e') i).trans (hq n e hn e' hm hlt)

lemma hbS (i : Ic) : ∀ j ∈ Sset E, ∀ k ∈ Sset E,
    |bco lab i j - bco lab i k| ≤ dist ((fun p : L1 => p) j) ((fun p : L1 => p) k) := by
  intro j hj k hk
  show _ ≤ dist j k
  rw [dist_eq_norm]
  rcases lt_or_ge ‖j - k‖ 2 with hlt | hge
  · have := bco_close E lab hadm hq hj hk hlt i
    linarith [norm_nonneg (j - k)]
  · have := asub (bco lab i j) (bco lab i k)
    linarith [bco_abs lab i j, bco_abs lab i k]

end Adm

lemma omit_cond (E : ℕ → Set L1) (lab : L1 → Cb) (x : L1) (i : Ic) (p : L1)
    (hp : p ∈ Sset E) (hpK : p ∉ Kset E x) :
    |bco lab i p - hfun i x| ≤ dist x ((fun q : L1 => q) p) := by
  obtain ⟨n, hpn, ha⟩ := hp
  have hn : ¬ ‖x‖ / 4 < mass n x := fun h => hpK ⟨n, h, hpn, ha⟩
  push Not at hn
  have h1 := dist_lower n p x ha
  show _ ≤ dist x p
  rw [dist_eq_norm]
  have := asub (bco lab i p) (hfun i x)
  linarith [bco_abs lab i p, hfun_abs i x, norm_nonneg x]

section Adm2
variable (E : ℕ → Set L1) (lab : L1 → Cb) (hcl : ∀ n, IsClosed (E n))
  (hadm : ∀ n, ∀ e ∈ E n, Adm n e)
  (hq : ∀ n, ∀ e ∈ E n, ∀ e' ∈ E n, ‖e - e'‖ < 2 → dist (lab e) (lab e') ≤ ‖e - e'‖ / 4)
include hcl hadm hq

lemma Fv_fin (x : L1) (hx1 : ‖x‖ ≤ 1) (hx : ∀ n, x ∉ E n) :
    {i | Fv E lab x i ≠ hfun i x}.Finite := by
  have hev : ∀ᶠ i in cofinite, ∀ e ∈ Kset E x,
      |bco lab i e - hfun i x| ≤ dist x ((fun q : L1 => q) e) := by
    by_cases hne : (Kset E x).Nonempty
    · obtain ⟨p0, n0, hn0, hp0, ha0⟩ := hne
      have hs : 0 < ‖x‖ := by linarith [mass_le n0 x, mass_nonneg n0 x]
      have hLg : {n | ‖x‖ / 4 < mass n x}.Finite := large_finite x
      set K' : Set L1 := ⋃ n ∈ {n | ‖x‖ / 4 < mass n x}, E n with hK'
      have hK'c : IsClosed K' := hLg.isClosed_biUnion fun n _ => hcl n
      have hKK' : Kset E x ⊆ K' := fun p ⟨n, hn, hp, _⟩ => Set.mem_biUnion hn hp
      have hK'ne : K'.Nonempty := ⟨p0, hKK' ⟨n0, hn0, hp0, ha0⟩⟩
      have hxK' : x ∉ K' := by
        simp only [hK', Set.mem_iUnion]; rintro ⟨n, _, h⟩; exact hx n h
      have hD : 0 < Metric.infDist x K' := (hK'c.notMem_iff_infDist_pos hK'ne).1 hxK'
      have := core (Kset E x) x hs _ hD
        (fun e he => by rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem (hKK' he))
        (fun e ⟨n, _, _, ha⟩ => ⟨ha.1, fun j => (ha.2 j).1⟩)
        (fun e i => bco lab i e) (fun e i => bco_abs lab i e) (fun e => bco_tendsto lab e)
        (fun e he e' he' hlt i =>
          bco_close E lab hadm hq (Kset_sub E x he) (Kset_sub E x he') hlt i)
        (fun i => hfun i x) (H_tendsto x)
      filter_upwards [this] with i hi e he
      have := hi e he
      show _ ≤ dist x e
      rwa [dist_eq_norm]
    · exact Filter.Eventually.of_forall fun i e he => absurd ⟨e, he⟩ hne
  refine (Filter.eventually_cofinite.1 hev).subset ?_
  intro i hi hP
  apply hi
  unfold Fv
  exact cl_eq_h _ x hP ((hfun_abs i x).trans (by linarith))

lemma Fv_at (x : L1) (n : ℕ) (hxn : x ∈ E n) (i : Ic) : Fv E lab x i = bco lab i x := by
  have ha := hadm n x hxn
  have hxK : x ∈ Kset E x := ⟨n, by rw [mass_eq n x ha, ha.1]; norm_num, hxn, ha⟩
  have hb : ∀ j ∈ Kset E x, ∀ k ∈ Kset E x, |bco lab i j - bco lab i k| ≤
      dist ((fun p : L1 => p) j) ((fun p : L1 => p) k) := fun j hj k hk =>
    hbS E lab hadm hq i j (Kset_sub E x hj) k (Kset_sub E x hk)
  exact cl_at (e := fun p : L1 => p) (bco_abs lab i) hb (hfun i) hxK

lemma Fv_tendsto (x : L1) (hx1 : ‖x‖ ≤ 1) : Tendsto (Fv E lab x) cofinite (𝓝 0) := by
  by_cases h : ∃ n, x ∈ E n
  · obtain ⟨n, hn⟩ := h
    have : Fv E lab x = fun i => bco lab i x := funext (Fv_at E lab hcl hadm hq x n hn)
    rw [this]; exact bco_tendsto lab x
  · push Not at h
    have hev : ∀ᶠ i in cofinite, hfun i x = Fv E lab x i :=
      Filter.eventually_cofinite.2 ((Fv_fin E lab hcl hadm hq x hx1 h).subset fun i hi => Ne.symm hi)
    exact (H_tendsto x).congr' hev

lemma Fv_eq_clS (x : L1) (i : Ic) :
    Fv E lab x i = cl (fun p : L1 => p) (bco lab i) (Sset E) (hfun i) x :=
  (cl_omit (bco_abs lab i) (hbS E lab hadm hq i) (Kset_sub E x) (hfun i) x
    (fun j hj hjK => omit_cond E lab x i j hj hjK)).symm

lemma Gdef_lip : LipschitzWith 1 (Gdef E lab) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  simp only [NNReal.coe_one, one_mul]
  have hT := Fv_tendsto E lab hcl hadm hq x.1 (mem_closedBall_zero_iff.1 x.2)
  have hT' := Fv_tendsto E lab hcl hadm hq x'.1 (mem_closedBall_zero_iff.1 x'.2)
  rw [Subtype.dist_eq (Gdef E lab x) (Gdef E lab x'), Subtype.dist_eq x x',
    Gdef_coe E lab x hT, Gdef_coe E lab x' hT', dist_eq_norm]
  show ‖((Gel E lab x.1 hT - Gel E lab x'.1 hT' : c0 Ic) : Linf Ic)‖ ≤ dist x.1 x'.1
  refine lp.norm_le_of_forall_le dist_nonneg fun i => ?_
  show ‖Fv E lab x.1 i - Fv E lab x'.1 i‖ ≤ _
  rw [Real.norm_eq_abs, Fv_eq_clS E lab hcl hadm hq x.1 i, Fv_eq_clS E lab hcl hadm hq x'.1 i]
  have := (cl_lip (e := fun p : L1 => p) (S := Sset E) (bco_abs lab i) (hfun_lip i)).dist_le_mul
    x.1 x'.1
  simpa [Real.dist_eq] using this

end Adm2

end Main

end Sol_Plasticity_Ell1C0_exists_tree_clamp_family

open Plasticity Filter Topology Sol_Plasticity_Ell1C0_exists_tree_clamp_family in
theorem solution :
    ∃ G : (ℕ → Set (lp (fun _ : ℕ × ℕ => ℝ) 1)) →
        (lp (fun _ : ℕ × ℕ => ℝ) 1 → Metric.closedBall (0 : c0 ((ℕ × ℕ) × ℕ)) 1) →
        Metric.closedBall (0 : lp (fun _ : ℕ × ℕ => ℝ) 1) 1 →
        Metric.closedBall (0 : c0 ((ℕ × ℕ) × ℕ)) 1,
      ∀ (E : ℕ → Set (lp (fun _ : ℕ × ℕ => ℝ) 1))
        (lab : lp (fun _ : ℕ × ℕ => ℝ) 1 → Metric.closedBall (0 : c0 ((ℕ × ℕ) × ℕ)) 1),
        (∀ n, IsClosed (E n)) →
        (∀ n, ∀ e ∈ E n, ‖e‖ = 1 ∧ ∀ j, 0 ≤ e j ∧ (j.1 ≠ n → e j = 0)) →
        (∀ n, ∀ e ∈ E n, ∀ e' ∈ E n, ‖e - e'‖ < 2 → dist (lab e) (lab e') ≤ ‖e - e'‖ / 4) →
        LipschitzWith 1 (G E lab) ∧
        (∀ n (x : Metric.closedBall (0 : lp (fun _ : ℕ × ℕ => ℝ) 1) 1),
          (x : lp (fun _ : ℕ × ℕ => ℝ) 1) ∈ E n → G E lab x = lab x) ∧
        (∀ (E' : ℕ → Set (lp (fun _ : ℕ × ℕ => ℝ) 1))
          (lab' : lp (fun _ : ℕ × ℕ => ℝ) 1 → Metric.closedBall (0 : c0 ((ℕ × ℕ) × ℕ)) 1)
          (x : Metric.closedBall (0 : lp (fun _ : ℕ × ℕ => ℝ) 1) 1),
          (∀ n, ‖(x : lp (fun _ : ℕ × ℕ => ℝ) 1)‖ / 4 <
              ∑' m, |(x : lp (fun _ : ℕ × ℕ => ℝ) 1) (n, m)| →
            E' n = E n ∧ ∀ e ∈ E n, lab' e = lab e) →
          G E' lab' x = G E lab x) ∧
        (∀ (x : Metric.closedBall (0 : lp (fun _ : ℕ × ℕ => ℝ) 1) 1),
          (∀ n, ∑' m, |(x : lp (fun _ : ℕ × ℕ => ℝ) 1) (n, m)| ≤
              ‖(x : lp (fun _ : ℕ × ℕ => ℝ) 1)‖ / 4) →
          ∀ i : (ℕ × ℕ) × ℕ, ((G E lab x : c0 ((ℕ × ℕ) × ℕ)) : Linf ((ℕ × ℕ) × ℕ)) i
            = (2 : ℝ) ^ (-((i.2 : ℤ) + 2)) * (x : lp (fun _ : ℕ × ℕ => ℝ) 1) i.1) ∧
        (∀ (x : Metric.closedBall (0 : lp (fun _ : ℕ × ℕ => ℝ) 1) 1),
          (∀ n, (x : lp (fun _ : ℕ × ℕ => ℝ) 1) ∉ E n) →
          {i : (ℕ × ℕ) × ℕ | ((G E lab x : c0 ((ℕ × ℕ) × ℕ)) : Linf ((ℕ × ℕ) × ℕ)) i
            ≠ (2 : ℝ) ^ (-((i.2 : ℤ) + 2)) * (x : lp (fun _ : ℕ × ℕ => ℝ) 1) i.1}.Finite) := by
  refine ⟨Gdef, fun E lab hcl hadm hq => ⟨Gdef_lip E lab hcl hadm hq, ?_, ?_, ?_, ?_⟩⟩
  · intro n x hx
    have hT := Fv_tendsto E lab hcl hadm hq x.1 (mem_closedBall_zero_iff.1 x.2)
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun i => ?_)))
    show (((Gdef E lab x : Cb) : c0 Ic) : Linf Ic) i = (((lab x.1 : Cb) : c0 Ic) : Linf Ic) i
    rw [Gdef_apply E lab x hT, Fv_at E lab hcl hadm hq x.1 n hx i]; rfl
  · intro E' lab' x h
    have hF := Fv_congr' E E' lab lab' x.1 h
    by_cases hT : Tendsto (Fv E lab x.1) cofinite (𝓝 0)
    · have hT' : Tendsto (Fv E' lab' x.1) cofinite (𝓝 0) := by rw [hF]; exact hT
      refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun i => ?_)))
      show (((Gdef E' lab' x : Cb) : c0 Ic) : Linf Ic) i = (((Gdef E lab x : Cb) : c0 Ic) : Linf Ic) i
      rw [Gdef_apply E' lab' x hT', Gdef_apply E lab x hT, hF]
    · have hT' : ¬ Tendsto (Fv E' lab' x.1) cofinite (𝓝 0) := by rw [hF]; exact hT
      unfold Gdef; rw [dif_neg hT, dif_neg hT']
  · intro x hx i
    have hx1 := mem_closedBall_zero_iff.1 x.2
    have hfe : Fv E lab x.1 = fun i => hfun i x.1 := funext (Fv_eq_H E lab x.1 hx1 hx)
    have hT : Tendsto (Fv E lab x.1) cofinite (𝓝 0) := by rw [hfe]; exact H_tendsto x.1
    rw [Gdef_apply E lab x hT, hfe]; rfl
  · intro x hx
    have hx1 := mem_closedBall_zero_iff.1 x.2
    have hT := Fv_tendsto E lab hcl hadm hq x.1 hx1
    refine (Fv_fin E lab hcl hadm hq x.1 hx1 hx).subset ?_
    intro i hi
    show Fv E lab x.1 i ≠ hfun i x.1
    rw [← Gdef_apply E lab x hT]; exact hi
