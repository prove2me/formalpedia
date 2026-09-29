-- Prove2me | solution 1 for Problem97.MEC.no_diameter_under_k4
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:53.537176+00:00
-- url     : https://prove2.me/submissions/e2813390-7ea2-4932-9f82-c85562fe9cce

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.NoDiameterUnderK4:32818:48118. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Theorems.Thm_Problem97_MEC_sylvester_dichotomy

section Erdos9796CountingFragment_Erdos9796Proof_P97_NoDiameterUnderK4

open Problem97 Problem97.MEC

/- Fragment from Erdos9796Proof.P97.NoDiameterUnderK4; source SHA-256 6ce8b4da44107edce310a178f612914b094548c6bcfd7d92ba484e7e4b2fb159 -/


/-!
# MEC has at least 3 boundary vertices under `K4` (Lemma 2)

For a nonempty noncollinear convex-independent `A : Finset ℝ²` with the
4-equidistant property, the MEC of `A` cannot land in the Sylvester
*diameter* case: at least three points of `A` must lie on the MEC
boundary.

This is **Lemma 2** of the Erdős Problem 97 general proof (see the
closure plan in `docs/`).

## Argument (Option C — direct convex-hull contradiction)

Suppose for contradiction the diameter case holds: there exist `a, b ∈ A`
on the MEC boundary, with `MEC.center = midpoint a b` and
`MEC.radius = dist a b / 2`.

By the 4-equidistant hypothesis at apex `a ∈ A`, pick `r > 0` such that
`S := A.filter (dist a · = r)` has card ≥ 4.

**Geometric core.**  Each `q ∈ S` lies in the closed MEC disk, which has
`ab` as diameter.  Thales' theorem rephrases this as
`⟨q - a, q - b⟩ ≤ 0`, equivalently `⟨q - a, b - a⟩ ≥ ‖q - a‖² = r²`.

Define `x_q := ⟨q - a, b - a⟩` and `y_q := cross(b - a, q - a)` where
`cross(u, v) := u 0 * v 1 - u 1 * v 0`.  The 2D Lagrange identity gives
`x_q² + y_q² = d² · r²` (so `r ≤ d`, since `x_q² ≥ r⁴`).

For `q ∈ S \ {b}`, we'll show `y_q ≠ 0` (the point is strictly off line
`ab`), so by pigeonhole two of the four equidistant points have same
sign of `y_q`.  Then a convex-combination computation shows the smaller
one is in the convex hull of `{a, larger one, b}`, contradicting
`ConvexIndep A`.

## Main theorem

`Problem97.MEC.no_diameter_under_k4` — the MEC boundary has card ≥ 3,
ruling out the diameter case under K4 + ConvexIndep.
-/

open scoped EuclideanGeometry
open Finset




/- ### Coordinate helpers -/

/-- Signed 2D cross product (oriented twice the triangle area). -/
 noncomputable def Problem97.MEC.cross2 (u v : ℝ²) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- Inner product on `ℝ²` in coordinates. -/
 lemma Problem97.MEC.inner_eq_coords (u v : ℝ²) :
    @inner ℝ _ _ u v = u 0 * v 0 + u 1 * v 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two, mul_comm]

/-- Squared norm in coordinates. -/
 lemma Problem97.MEC.norm_sq_eq_coords (u : ℝ²) :
    ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [← @real_inner_self_eq_norm_sq]
  rw [Problem97.MEC.inner_eq_coords]
  ring

/-- Lagrange identity: `‖u‖² ‖v‖² = ⟨u,v⟩² + cross(u,v)²` in 2D. -/
 lemma Problem97.MEC.cross_sq_plus_inner_sq (u v : ℝ²) :
    (Problem97.MEC.cross2 u v) ^ 2 + (@inner ℝ _ _ u v) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [Problem97.MEC.inner_eq_coords, Problem97.MEC.norm_sq_eq_coords u, Problem97.MEC.norm_sq_eq_coords v]
  unfold Problem97.MEC.cross2
  ring

/-- Antisymmetry of `cross2`. -/
 lemma Problem97.MEC.cross2_anti (u v : ℝ²) : Problem97.MEC.cross2 u v = -Problem97.MEC.cross2 v u := by
  unfold Problem97.MEC.cross2; ring

/-- Pythagorean form: `‖u‖² ‖v‖² = ⟨u,v⟩² + cross(v,u)²` (since cross is antisym). -/
 lemma Problem97.MEC.norm_sq_mul_eq_inner_sq_plus_cross_sq (u v : ℝ²) :
    ‖u‖ ^ 2 * ‖v‖ ^ 2 = (@inner ℝ _ _ u v) ^ 2 + (Problem97.MEC.cross2 v u) ^ 2 := by
  have h := Problem97.MEC.cross_sq_plus_inner_sq u v
  rw [Problem97.MEC.cross2_anti u v] at h
  linarith [h, sq_nonneg (Problem97.MEC.cross2 v u)]

/- ### Thales / midpoint identities -/

/-- A point in the closed disk of diameter `ab` (the midpoint MEC disk)
satisfies `⟨p - a, p - b⟩ ≤ 0`. -/
 lemma Problem97.MEC.thales_of_in_diameter_disk
    {a b p : ℝ²} (hp : dist p (midpoint ℝ a b) ≤ dist a b / 2) :
    @inner ℝ _ _ (p - a) (p - b) ≤ 0 := by
  set m := midpoint ℝ a b with hm_def
  -- `m - a = (1/2) • (b - a)`, `m - b = -(1/2) • (b - a)`.
  have hm_a : m - a = (1 / 2 : ℝ) • (b - a) := by
    rw [hm_def, midpoint_eq_smul_add]
    have h : (⅟2 : ℝ) = 1/2 := by simp [invOf_eq_inv]
    rw [h]; module
  have hm_b : m - b = (-(1 / 2 : ℝ)) • (b - a) := by
    rw [hm_def, midpoint_eq_smul_add]
    have h : (⅟2 : ℝ) = 1/2 := by simp [invOf_eq_inv]
    rw [h]; module
  -- p - a = (p - m) + (m - a), p - b = (p - m) + (m - b).
  have h1 : p - a = (p - m) + (1 / 2 : ℝ) • (b - a) := by
    have heq : p - a = (p - m) + (m - a) := by abel
    rw [heq, hm_a]
  have h2 : p - b = (p - m) - (1 / 2 : ℝ) • (b - a) := by
    have heq : p - b = (p - m) + (m - b) := by abel
    rw [heq, hm_b]
    rw [show (-(1 / 2 : ℝ)) • (b - a) = -((1 / 2 : ℝ) • (b - a)) from by simp]
    abel
  -- ⟨(p - m) + s•(b - a), (p - m) - s•(b - a)⟩ = ‖p - m‖² - s² ‖b - a‖²
  -- with s = 1/2.
  have hkey : @inner ℝ _ _ (p - a) (p - b) =
      ‖p - m‖ ^ 2 - (1 / 4 : ℝ) * ‖b - a‖ ^ 2 := by
    rw [h1, h2, inner_sub_right, inner_add_left, inner_add_left]
    rw [real_inner_self_eq_norm_sq]
    rw [real_inner_smul_right, real_inner_smul_left, real_inner_smul_left]
    rw [show @inner ℝ _ _ (b - a) ((1 / 2 : ℝ) • (b - a)) =
        (1 / 2 : ℝ) * @inner ℝ _ _ (b - a) (b - a) from by
      rw [real_inner_smul_right]]
    rw [real_inner_self_eq_norm_sq (b - a)]
    rw [← real_inner_comm (p - m) (b - a)]
    ring
  rw [hkey]
  have hdist_sq : ‖p - m‖ ^ 2 ≤ (dist a b / 2) ^ 2 := by
    have hpm_eq : dist p m = ‖p - m‖ := dist_eq_norm _ _
    have h_nn : (0 : ℝ) ≤ dist p m := dist_nonneg
    nlinarith [hp, h_nn, hpm_eq]
  have hba : ‖b - a‖ = dist a b := by
    rw [dist_eq_norm]
    rw [show a - b = -(b - a) from by abel, norm_neg]
  rw [hba]
  nlinarith [hdist_sq, sq_nonneg (dist a b)]

/-- `⟨p - a, b - a⟩ ≥ ‖p - a‖²` for `p` in the closed MEC disk diameter
`ab`. -/
 lemma Problem97.MEC.inner_proj_ge_norm_sq_of_in_disk
    {a b p : ℝ²} (hp : dist p (midpoint ℝ a b) ≤ dist a b / 2) :
    ‖p - a‖ ^ 2 ≤ @inner ℝ _ _ (p - a) (b - a) := by
  have h := Problem97.MEC.thales_of_in_diameter_disk hp
  -- ⟨p - a, p - b⟩ = ‖p - a‖² + ⟨p - a, a - b⟩ = ‖p - a‖² - ⟨p - a, b - a⟩.
  have hexp : @inner ℝ _ _ (p - a) (p - b) =
      ‖p - a‖ ^ 2 - @inner ℝ _ _ (p - a) (b - a) := by
    have h1 : p - b = (p - a) + (a - b) := by abel
    rw [h1, inner_add_right]
    rw [real_inner_self_eq_norm_sq]
    rw [show a - b = -(b - a) from by abel]
    rw [inner_neg_right]
    ring
  linarith [hexp ▸ h]

/- ### Auxiliary: points in disk on line `ab` are in segment `[a, b]`. -/

/-- If `p` is in the closed disk diameter `ab` AND collinear with `a, b`, then
`p ∈ segment ℝ a b` (i.e., `p = (1-t) a + t b` for some `t ∈ [0, 1]`). -/
 lemma Problem97.MEC.in_segment_of_in_disk_and_collinear
    {a b p : ℝ²} (hab : a ≠ b)
    (hdisk : dist p (midpoint ℝ a b) ≤ dist a b / 2)
    (hcoll : Problem97.MEC.cross2 (b - a) (p - a) = 0) :
    p ∈ segment ℝ a b := by
  -- From cross = 0, p - a is a scalar multiple of b - a.
  -- p - a = t • (b - a), where t = ⟨p - a, b - a⟩ / ‖b - a‖².
  set t := @inner ℝ _ _ (p - a) (b - a) / ‖b - a‖ ^ 2 with ht_def
  have hba_ne : (b - a) ≠ 0 := sub_ne_zero.mpr hab.symm
  have hba_norm_pos : 0 < ‖b - a‖ := norm_pos_iff.mpr hba_ne
  have hba_sq_pos : 0 < ‖b - a‖ ^ 2 := by positivity
  -- Claim: p - a = t • (b - a).
  have hp_eq : p - a = t • (b - a) := by
    -- Show ‖(p - a) - t • (b - a)‖² = 0 via Lagrange (cross + inner both = 0).
    set w := (p - a) - t • (b - a) with hw_def
    have h_inner_w_ba : @inner ℝ _ _ w (b - a) = 0 := by
      rw [hw_def, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      rw [ht_def]
      field_simp
      ring
    have h_cross_ba_w : Problem97.MEC.cross2 (b - a) w = 0 := by
      rw [hw_def, Problem97.MEC.cross2_anti (b - a) (p - a - t • (b - a))]
      rw [show p - a - t • (b - a) = (p - a) + (-(t • (b - a))) from by abel]
      have hc1 : Problem97.MEC.cross2 ((p - a) + (-(t • (b - a)))) (b - a) =
        Problem97.MEC.cross2 (p - a) (b - a) + Problem97.MEC.cross2 (-(t • (b - a))) (b - a) := by
        unfold Problem97.MEC.cross2; simp; ring
      rw [hc1]
      rw [show Problem97.MEC.cross2 (p - a) (b - a) = -Problem97.MEC.cross2 (b - a) (p - a) from Problem97.MEC.cross2_anti _ _]
      rw [hcoll]
      have hc2 : Problem97.MEC.cross2 (-(t • (b - a))) (b - a) = -t * Problem97.MEC.cross2 (b - a) (b - a) := by
        unfold Problem97.MEC.cross2; simp; ring
      rw [hc2]
      have : Problem97.MEC.cross2 (b - a) (b - a) = 0 := by unfold Problem97.MEC.cross2; ring
      rw [this]
      ring
    -- Lagrange: ‖w‖² ‖b - a‖² = ⟨w, b-a⟩² + cross(b-a, w)² = 0.
    have hLag : ‖w‖ ^ 2 * ‖b - a‖ ^ 2 =
        (@inner ℝ _ _ w (b - a)) ^ 2 + (Problem97.MEC.cross2 (b - a) w) ^ 2 :=
      Problem97.MEC.norm_sq_mul_eq_inner_sq_plus_cross_sq w (b - a)
    rw [h_inner_w_ba, h_cross_ba_w] at hLag
    have hsq_zero : ‖w‖ ^ 2 * ‖b - a‖ ^ 2 = 0 := by linarith
    have hw_sq_zero : ‖w‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hsq_zero with h | h
      · exact h
      · linarith
    have hw_norm_zero : ‖w‖ = 0 := by
      have hnn : 0 ≤ ‖w‖ := norm_nonneg _
      nlinarith
    have hw_zero : w = 0 := norm_eq_zero.mp hw_norm_zero
    have heq := sub_eq_zero.mp hw_zero
    exact heq
  -- p = a + t • (b - a), and Thales constrains t ∈ [0, 1].
  -- ⟨p - a, b - a⟩ = t • ⟨b - a, b - a⟩ = t ‖b - a‖² = t · d² where d = ‖b - a‖.
  -- Thales: ⟨p - a, b - a⟩ ≥ ‖p - a‖² = t² ‖b - a‖².
  -- So t ‖b - a‖² ≥ t² ‖b - a‖², i.e., t(1 - t) ‖b - a‖² ≥ 0.
  -- Since ‖b - a‖² > 0, t(1 - t) ≥ 0, so t ∈ [0, 1].
  have h_inner_pa_ba : @inner ℝ _ _ (p - a) (b - a) = t * ‖b - a‖ ^ 2 := by
    rw [hp_eq, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have h_pa_norm_sq : ‖p - a‖ ^ 2 = t ^ 2 * ‖b - a‖ ^ 2 := by
    rw [hp_eq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h_thales := Problem97.MEC.inner_proj_ge_norm_sq_of_in_disk (a := a) (b := b) (p := p) hdisk
  rw [h_inner_pa_ba, h_pa_norm_sq] at h_thales
  -- t² ‖b - a‖² ≤ t ‖b - a‖², so t (1 - t) ‖b - a‖² ≥ 0.
  have ht_bdd : 0 ≤ t * (1 - t) := by
    have h1 : t ^ 2 * ‖b - a‖ ^ 2 ≤ t * ‖b - a‖ ^ 2 := h_thales
    have h2 : (t - t ^ 2) * ‖b - a‖ ^ 2 ≥ 0 := by linarith
    have h3 : t * (1 - t) * ‖b - a‖ ^ 2 ≥ 0 := by ring_nf; linarith [h2]
    have h4 : 0 ≤ t * (1 - t) := by
      by_contra h_neg
      push_neg at h_neg
      have : t * (1 - t) * ‖b - a‖ ^ 2 < 0 :=
        mul_neg_of_neg_of_pos h_neg hba_sq_pos
      linarith
    exact h4
  -- t ∈ [0, 1].
  have ht_nn : 0 ≤ t := by
    by_contra h_neg
    push_neg at h_neg
    -- t < 0, then 1 - t > 0, so t * (1 - t) < 0.
    have : 1 - t > 0 := by linarith
    have : t * (1 - t) < 0 := mul_neg_of_neg_of_pos h_neg this
    linarith
  have ht_le_one : t ≤ 1 := by
    by_contra h_gt
    push_neg at h_gt
    have : 1 - t < 0 := by linarith
    have : t * (1 - t) < 0 := mul_neg_of_pos_of_neg (by linarith) this
    linarith
  -- p = a + t • (b - a) = (1 - t) • a + t • b.
  rw [segment_eq_image]
  refine ⟨t, ⟨ht_nn, ht_le_one⟩, ?_⟩
  have heq : p = a + t • (b - a) := by rw [← hp_eq]; abel
  rw [heq]; module

/- ### Pair-in-half-plane contradiction.

The technical heart: given `0 < y₁ < y₂`, `x_i² + y_i² = r²`,
`x_i d ≥ r²` (i.e. `q_i` in closed disk diameter `[a, b]` projected),
and `d ≥ r > 0`, the point `q₁ = (x₁, y₁) + a` lies in the convex hull
of `{a, q₂ + a + …, b}` where `q_2 = (x₂, y₂)`.

Concretely we prove `q₁ ∈ convexHull ℝ {a, q₂, b}` via the explicit
convex combination weights `α, β, γ`. -/

/-- Key algebraic inequality: with `x_i² + y_i² = r²`, `0 < y_1 < y_2`,
`x_i d > r²` (strict, from being strictly inside the disk), and
`d > r > 0`: `d (y₂ - y₁) > x₁ y₂ - x₂ y₁`. -/
 lemma Problem97.MEC.key_trig_inequality
    {x₁ y₁ x₂ y₂ r d : ℝ}
    (hr_pos : 0 < r) (_hd_pos : 0 < d) (hrd_lt : r < d)
    (hy_lt : y₁ < y₂) (hy1_pos : 0 < y₁)
    (h_sq1 : x₁ ^ 2 + y₁ ^ 2 = r ^ 2)
    (h_sq2 : x₂ ^ 2 + y₂ ^ 2 = r ^ 2)
    (hx1_pos : 0 < x₁) (hx2_pos : 0 < x₂)
    (hx1d : r ^ 2 < x₁ * d) (hx2d : r ^ 2 < x₂ * d) :
    x₁ * y₂ - x₂ * y₁ < d * (y₂ - y₁) := by
  -- Bounds: x_i ≤ r < d, so d - x_i > 0.
  have hy2_pos : 0 < y₂ := by linarith
  have hx1_le : x₁ ≤ r := by nlinarith [sq_nonneg y₁]
  have hx2_le : x₂ ≤ r := by nlinarith [sq_nonneg y₂]
  have hdx1 : 0 < d - x₁ := by linarith
  have hdx2 : 0 < d - x₂ := by linarith
  -- y_1 < y_2 (both positive) ⇒ y_1² < y_2² ⇒ x_2² < x_1² ⇒ x_2 < x_1.
  have hy1_sq_lt_y2 : y₁ ^ 2 < y₂ ^ 2 := by nlinarith
  have hx2_sq_lt_x1 : x₂ ^ 2 < x₁ ^ 2 := by linarith
  have hx2_lt_x1 : x₂ < x₁ := by
    nlinarith [sq_nonneg (x₁ + x₂), sq_nonneg (x₁ - x₂)]
  -- Algebraic identity: factor `y₂² (d-x₁)² - y₁² (d-x₂)² > 0`.
  have h_pos_target : 0 ≤ y₂ * (d - x₁) := mul_nonneg hy2_pos.le hdx1.le
  have h_pos_rhs : 0 ≤ y₁ * (d - x₂) := mul_nonneg hy1_pos.le hdx2.le
  have h_factor : y₂ ^ 2 * (d - x₁) ^ 2 - y₁ ^ 2 * (d - x₂) ^ 2 =
      (x₁ - x₂) * ((d - x₁) * (d * x₂ - r ^ 2) + (d - x₂) * (d * x₁ - r ^ 2)) := by
    have h1 : y₂ ^ 2 = r ^ 2 - x₂ ^ 2 := by linarith
    have h2 : y₁ ^ 2 = r ^ 2 - x₁ ^ 2 := by linarith
    rw [h1, h2]; ring
  have h_rhs_pos : 0 < (x₁ - x₂) * ((d - x₁) * (d * x₂ - r ^ 2) + (d - x₂) * (d * x₁ - r ^ 2)) := by
    have h1 : 0 < x₁ - x₂ := by linarith
    have h2 : 0 < (d - x₁) * (d * x₂ - r ^ 2) := mul_pos hdx1 (by linarith)
    have h3 : 0 < (d - x₂) * (d * x₁ - r ^ 2) := mul_pos hdx2 (by linarith)
    exact mul_pos h1 (by linarith)
  -- So `(y₁ (d - x₂))² < (y₂ (d - x₁))²`.
  have h_sq_ineq : (y₁ * (d - x₂)) ^ 2 < (y₂ * (d - x₁)) ^ 2 := by
    have hA : (y₁ * (d - x₂)) ^ 2 = y₁ ^ 2 * (d - x₂) ^ 2 := by ring
    have hB : (y₂ * (d - x₁)) ^ 2 = y₂ ^ 2 * (d - x₁) ^ 2 := by ring
    linarith [h_factor.symm ▸ h_rhs_pos]
  -- Take "square roots" via sq_nonneg.
  have h_strict : y₁ * (d - x₂) < y₂ * (d - x₁) := by
    nlinarith [sq_nonneg (y₁ * (d - x₂) - y₂ * (d - x₁)),
               sq_nonneg (y₁ * (d - x₂) + y₂ * (d - x₁))]
  linarith

/-- Triangle convex hull: convex combination of three points lies in `convexHull`. -/
 lemma Problem97.MEC.mem_convexHull_triangle
    (a b c q : ℝ²) (α β γ : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hsum : α + β + γ = 1)
    (hq : α • a + β • b + γ • c = q) :
    q ∈ convexHull ℝ ({a, b, c} : Set ℝ²) := by
  rw [mem_convexHull_iff_exists_fintype]
  refine ⟨Fin 3, inferInstance, fun i => ![α, β, γ] i, fun i => ![a, b, c] i,
    ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp <;> assumption
  · simp [Fin.sum_univ_three]; linarith
  · intro i; fin_cases i
    · simp
    · simp
    · simp
  · simp [Fin.sum_univ_three]
    exact hq

/- ### Helper: ordered-pair contradiction (the inner core).

This is the core of the same-sign argument: assuming `|y_a| < |y_b|`,
construct the convex combination expressing `q_a` as `α • a + β • q_b + γ • b`
with all weights positive, then apply `ConvexIndep A`. -/
set_option maxHeartbeats 600000 in
 lemma Problem97.MEC.same_sign_ordered_pair_contradiction
    {A : Finset ℝ²} (hConv : Problem97.ConvexIndep A)
    {a b qa qb : ℝ²} {r d : ℝ}
    (ha_mem : a ∈ A) (hb_mem : b ∈ A)
    (hqa_A : qa ∈ A) (hqb_A : qb ∈ A)
    (hab_ne : a ≠ b)
    (hqa_a : qa ≠ a) (hqa_b : qa ≠ b)
    (hqb_a : qb ≠ a) (hqb_b : qb ≠ b)
    (hqab : qa ≠ qb)
    (hba_norm_sq : ‖b - a‖ ^ 2 = d ^ 2)
    (hd_pos : 0 < d) (hr_pos : 0 < r) (hrd_lt : r < d)
    (hxa : r ^ 2 < @inner ℝ _ _ (qa - a) (b - a))
    (hxb : r ^ 2 < @inner ℝ _ _ (qb - a) (b - a))
    (hLagA :
      @inner ℝ _ _ (qa - a) (b - a) ^ 2 + Problem97.MEC.cross2 (b - a) (qa - a) ^ 2 =
        r ^ 2 * d ^ 2)
    (hLagB :
      @inner ℝ _ _ (qb - a) (b - a) ^ 2 + Problem97.MEC.cross2 (b - a) (qb - a) ^ 2 =
        r ^ 2 * d ^ 2)
    (hyab_sign :
      0 < Problem97.MEC.cross2 (b - a) (qa - a) * Problem97.MEC.cross2 (b - a) (qb - a))
    (hY_lt :
      |Problem97.MEC.cross2 (b - a) (qa - a)| < |Problem97.MEC.cross2 (b - a) (qb - a)|) :
    False := by
  classical
  set xa := @inner ℝ _ _ (qa - a) (b - a) with hxa_def
  set xb := @inner ℝ _ _ (qb - a) (b - a) with hxb_def
  set ya := Problem97.MEC.cross2 (b - a) (qa - a) with hya_def
  set yb := Problem97.MEC.cross2 (b - a) (qb - a) with hyb_def
  set Ya := |ya| with hYa_def
  set Yb := |yb| with hYb_def
  have hd_sq_pos : (0 : ℝ) < d ^ 2 := by positivity
  have hr_sq_pos : 0 < r ^ 2 := by positivity
  have hxa_pos : 0 < xa := by linarith
  have hxb_pos : 0 < xb := by linarith
  have hya_ne : ya ≠ 0 := by
    intro h; rw [h, zero_mul] at hyab_sign; linarith
  have hyb_ne : yb ≠ 0 := by
    intro h; rw [h, mul_zero] at hyab_sign; linarith
  have hYa_pos : 0 < Ya := abs_pos.mpr hya_ne
  have hYb_pos : 0 < Yb := abs_pos.mpr hyb_ne
  have hYa_sq : Ya ^ 2 = ya ^ 2 := sq_abs ya
  have hYb_sq : Yb ^ 2 = yb ^ 2 := sq_abs yb
  -- Convert hypotheses for rescaling.
  -- Rescale to apply key_trig_inequality.
  set Xa := xa / d with hXa_def
  set Xb := xb / d with hXb_def
  set Ya' := Ya / d with hYa'_def
  set Yb' := Yb / d with hYb'_def
  have hX_Ya'_sq : Xa ^ 2 + Ya' ^ 2 = r ^ 2 := by
    rw [hXa_def, hYa'_def]
    have h_div : (xa / d) ^ 2 + (Ya / d) ^ 2 = (xa ^ 2 + Ya ^ 2) / d ^ 2 := by
      field_simp
    rw [h_div, hYa_sq]
    -- xa² + ya² = r²d², from hLagA.
    have h : xa ^ 2 + ya ^ 2 = r ^ 2 * d ^ 2 := hLagA
    rw [h]; field_simp
  have hX_Yb'_sq : Xb ^ 2 + Yb' ^ 2 = r ^ 2 := by
    rw [hXb_def, hYb'_def]
    have h_div : (xb / d) ^ 2 + (Yb / d) ^ 2 = (xb ^ 2 + Yb ^ 2) / d ^ 2 := by
      field_simp
    rw [h_div, hYb_sq]
    have h : xb ^ 2 + yb ^ 2 = r ^ 2 * d ^ 2 := hLagB
    rw [h]; field_simp
  have hY'_lt : Ya' < Yb' := by
    rw [hYa'_def, hYb'_def]
    exact div_lt_div_of_pos_right hY_lt hd_pos
  have hYa'_pos : 0 < Ya' := div_pos hYa_pos hd_pos
  have hYb'_pos : 0 < Yb' := div_pos hYb_pos hd_pos
  have hXa_pos' : 0 < Xa := div_pos hxa_pos hd_pos
  have hXb_pos' : 0 < Xb := div_pos hxb_pos hd_pos
  have hXa_d : r ^ 2 < Xa * d := by
    rw [hXa_def, div_mul_cancel₀ _ hd_pos.ne']; exact hxa
  have hXb_d : r ^ 2 < Xb * d := by
    rw [hXb_def, div_mul_cancel₀ _ hd_pos.ne']; exact hxb
  have hkey :=
    Problem97.MEC.key_trig_inequality (x₁ := Xa) (y₁ := Ya') (x₂ := Xb) (y₂ := Yb') (r := r) (d := d)
      hr_pos hd_pos hrd_lt hY'_lt hYa'_pos hX_Ya'_sq hX_Yb'_sq
      hXa_pos' hXb_pos' hXa_d hXb_d
  -- Translating back: xa * Yb - xb * Ya < d² * (Yb - Ya).
  have hkey_orig : xa * Yb - xb * Ya < d ^ 2 * (Yb - Ya) := by
    have h_eq1 : Xa * Yb' - Xb * Ya' = (xa * Yb - xb * Ya) / d ^ 2 := by
      rw [hXa_def, hXb_def, hYa'_def, hYb'_def]
      field_simp
    have h_eq2 : d * (Yb' - Ya') = (Yb - Ya) := by
      rw [hYa'_def, hYb'_def]
      field_simp
    rw [h_eq1, h_eq2] at hkey
    have := (div_lt_iff₀ hd_sq_pos).mp hkey
    linarith
  -- Convex combo: β = ya/yb, γ = (xa yb - xb ya)/(d² yb), α = 1 - β - γ.
  set β := ya / yb with hβ_def
  set γ := (xa * yb - xb * ya) / (d ^ 2 * yb) with hγ_def
  set α := 1 - β - γ with hα_def
  -- β = Ya/Yb (sign normalization).
  have hβ_eq_Y : β = Ya / Yb := by
    rw [hβ_def, hYa_def, hYb_def]
    rcases lt_trichotomy yb 0 with hyb_neg | hyb_zero | hyb_pos
    · have hya_neg : ya < 0 := by
        by_contra h; push_neg at h
        rcases eq_or_lt_of_le h with hya_zero | hya_pos
        · rw [← hya_zero, zero_mul] at hyab_sign; linarith
        · have : ya * yb < 0 := mul_neg_of_pos_of_neg hya_pos hyb_neg
          linarith
      rw [abs_of_neg hya_neg, abs_of_neg hyb_neg]
      field_simp
    · exfalso; rw [hyb_zero, mul_zero] at hyab_sign; linarith
    · have hya_pos : 0 < ya := by
        by_contra h; push_neg at h
        rcases eq_or_lt_of_le h with hya_zero | hya_neg
        · rw [hya_zero, zero_mul] at hyab_sign; linarith
        · have : ya * yb < 0 := mul_neg_of_neg_of_pos hya_neg hyb_pos
          linarith
      rw [abs_of_pos hya_pos, abs_of_pos hyb_pos]
  -- γ = (xa Yb - xb Ya)/(d² Yb).
  have hγ_eq_Y : γ = (xa * Yb - xb * Ya) / (d ^ 2 * Yb) := by
    rw [hγ_def, hYa_def, hYb_def]
    rcases lt_trichotomy yb 0 with hyb_neg | hyb_zero | hyb_pos
    · have hya_neg : ya < 0 := by
        by_contra h; push_neg at h
        rcases eq_or_lt_of_le h with hya_zero | hya_pos
        · rw [← hya_zero, zero_mul] at hyab_sign; linarith
        · have : ya * yb < 0 := mul_neg_of_pos_of_neg hya_pos hyb_neg
          linarith
      rw [abs_of_neg hya_neg, abs_of_neg hyb_neg]
      field_simp
      ring
    · exfalso; rw [hyb_zero, mul_zero] at hyab_sign; linarith
    · have hya_pos : 0 < ya := by
        by_contra h; push_neg at h
        rcases eq_or_lt_of_le h with hya_zero | hya_neg
        · rw [hya_zero, zero_mul] at hyab_sign; linarith
        · have : ya * yb < 0 := mul_neg_of_neg_of_pos hya_neg hyb_pos
          linarith
      rw [abs_of_pos hya_pos, abs_of_pos hyb_pos]
  -- Positivity.
  have hβ_pos : 0 < β := by rw [hβ_eq_Y]; exact div_pos hYa_pos hYb_pos
  have hβ_lt_one : β < 1 := by rw [hβ_eq_Y]; exact (div_lt_one hYb_pos).mpr hY_lt
  have hY_sq_lt : Ya ^ 2 < Yb ^ 2 := by
    rw [sq, sq]; exact mul_self_lt_mul_self hYa_pos.le hY_lt
  have hxa_sq_eq : xa ^ 2 = r ^ 2 * d ^ 2 - Ya ^ 2 := by linarith [hYa_sq, hLagA]
  have hxb_sq_eq : xb ^ 2 = r ^ 2 * d ^ 2 - Yb ^ 2 := by linarith [hYb_sq, hLagB]
  have hxa_sq_gt : xb ^ 2 < xa ^ 2 := by linarith
  have hxa_gt_xb : xb < xa := (sq_lt_sq₀ hxb_pos.le hxa_pos.le).mp hxa_sq_gt
  have hγ_num_pos : 0 < xa * Yb - xb * Ya := by
    have h1 : xb * Yb < xa * Yb := mul_lt_mul_of_pos_right hxa_gt_xb hYb_pos
    have h2 : xb * Ya < xb * Yb := mul_lt_mul_of_pos_left hY_lt hxb_pos
    linarith
  have hγ_pos : 0 < γ := by
    rw [hγ_eq_Y]; exact div_pos hγ_num_pos (mul_pos hd_sq_pos hYb_pos)
  have hα_pos : 0 < α := by
    rw [hα_def, hβ_eq_Y, hγ_eq_Y]
    have hYb_d_pos : 0 < d ^ 2 * Yb := mul_pos hd_sq_pos hYb_pos
    rw [sub_pos]
    rw [show (1 : ℝ) - Ya / Yb = (Yb - Ya) / Yb from by field_simp]
    rw [div_lt_div_iff₀ hYb_d_pos hYb_pos]
    have h_lhs : (xa * Yb - xb * Ya) * Yb = Yb * (xa * Yb - xb * Ya) := by ring
    have h_rhs : (Yb - Ya) * (d ^ 2 * Yb) = Yb * (d ^ 2 * (Yb - Ya)) := by ring
    rw [h_lhs, h_rhs]
    exact mul_lt_mul_of_pos_left hkey_orig hYb_pos
  have hsum : α + β + γ = 1 := by rw [hα_def]; ring
  -- Convex combo identity: q_a = α • a + γ • b + β • q_b.
  have hq_combo : α • a + γ • b + β • qb = qa := by
    set w := (qa - a) - β • (qb - a) - γ • (b - a) with hw_def
    have hw_zero : w = 0 := by
      have h_inner_w : @inner ℝ _ _ w (b - a) = 0 := by
        rw [hw_def]
        rw [inner_sub_left, inner_sub_left,
          real_inner_smul_left, real_inner_smul_left]
        rw [show @inner ℝ _ _ (b - a) (b - a) = ‖b - a‖ ^ 2
            from real_inner_self_eq_norm_sq _]
        rw [hba_norm_sq]
        rw [← hxa_def, ← hxb_def]
        rw [hγ_eq_Y, hβ_eq_Y]
        field_simp
        ring
      have h_cross_w : Problem97.MEC.cross2 (b - a) w = 0 := by
        rw [hw_def]
        have hc1 : Problem97.MEC.cross2 (b - a) ((qa - a) - β • (qb - a) - γ • (b - a)) =
            Problem97.MEC.cross2 (b - a) (qa - a) - β * Problem97.MEC.cross2 (b - a) (qb - a) -
              γ * Problem97.MEC.cross2 (b - a) (b - a) := by
          unfold Problem97.MEC.cross2
          simp [PiLp.sub_apply, PiLp.smul_apply]
          ring
        rw [hc1]
        have h_bb : Problem97.MEC.cross2 (b - a) (b - a) = 0 := by unfold Problem97.MEC.cross2; ring
        rw [h_bb]
        rw [← hya_def, ← hyb_def]
        rw [hβ_def]
        field_simp
        ring
      have hLag := Problem97.MEC.norm_sq_mul_eq_inner_sq_plus_cross_sq w (b - a)
      rw [h_inner_w, h_cross_w] at hLag
      have h_zero : ‖w‖ ^ 2 * ‖b - a‖ ^ 2 = 0 := by linarith
      have hba_norm_sq_pos : 0 < ‖b - a‖ ^ 2 := by rw [hba_norm_sq]; exact hd_sq_pos
      have hw_sq : ‖w‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h_zero with h | h
        · exact h
        · linarith
      have hw_norm : ‖w‖ = 0 :=
        pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hw_sq
      exact norm_eq_zero.mp hw_norm
    have h_rearr : qa - a = β • (qb - a) + γ • (b - a) := by
      have hwq : (qa - a) - (β • (qb - a) + γ • (b - a)) = 0 := by
        have h1 : (qa - a) - β • (qb - a) - γ • (b - a) = 0 := hw_zero
        have h2 : (qa - a) - β • (qb - a) - γ • (b - a) =
            (qa - a) - (β • (qb - a) + γ • (b - a)) := by abel
        rw [h2] at h1; exact h1
      exact sub_eq_zero.mp hwq
    -- α • a + γ • b + β • qb = a + (qa - a) = qa
    rw [hα_def]
    have h_target : (1 - β - γ) • a + γ • b + β • qb =
        a + (β • (qb - a) + γ • (b - a)) := by
      module
    rw [h_target, ← h_rearr]
    abel
  -- hq_combo : α • a + γ • b + β • qb = qa
  -- We use {a, qb, b} (instead of {a, b, qb}) so that the order matches.
  have hqa_in_hull : qa ∈ convexHull ℝ ({a, qb, b} : Set ℝ²) := by
    have hq_combo' : α • a + β • qb + γ • b = qa := by
      rw [← hq_combo]; abel
    exact Problem97.MEC.mem_convexHull_triangle a qb b qa α β γ hα_pos.le hβ_pos.le hγ_pos.le hsum hq_combo'
  apply hConv qa (Finset.mem_coe.mpr hqa_A)
  apply convexHull_mono ?_ hqa_in_hull
  intro x hx
  -- {a, qb, b} ⊆ A \ {qa}
  rcases hx with rfl | hx
  · refine ⟨Finset.mem_coe.mpr ha_mem, ?_⟩
    exact fun h => hqa_a (Set.mem_singleton_iff.mp h).symm
  · rcases hx with rfl | rfl
    · refine ⟨Finset.mem_coe.mpr hqb_A, ?_⟩
      exact fun h => hqab (Set.mem_singleton_iff.mp h).symm
    · refine ⟨Finset.mem_coe.mpr hb_mem, ?_⟩
      exact fun h => hqa_b (Set.mem_singleton_iff.mp h).symm

/- ### Helper: same-sign-pair contradiction.

Given two distinct points `q1, q2 ∈ A` both on circle `(a, r)`, strictly
inside the disk on diameter `[a, b]`, and lying on the *same side* of
line `ab` (positive product of cross products), we derive a contradiction
with `ConvexIndep A`: by Lagrange and `key_trig_inequality`, the point
with smaller `|cross|` lies in `convexHull {a, b, q (other)}`. -/
set_option maxHeartbeats 400000 in
 lemma Problem97.MEC.same_sign_pair_contradiction
    {A : Finset ℝ²} (hConv : Problem97.ConvexIndep A)
    {a b q1 q2 : ℝ²} {r d : ℝ}
    (ha_mem : a ∈ A) (hb_mem : b ∈ A)
    (hq1_A : q1 ∈ A) (hq2_A : q2 ∈ A)
    (hab_ne : a ≠ b)
    (hq1_ne_a : q1 ≠ a) (hq1_ne_b : q1 ≠ b)
    (hq2_ne_a : q2 ≠ a) (hq2_ne_b : q2 ≠ b)
    (hq12_ne : q1 ≠ q2)
    (hd_def : d = dist a b) (hd_pos : 0 < d)
    (hr_pos : 0 < r) (hrd_lt : r < d)
    (hq1_dist : dist a q1 = r) (hq2_dist : dist a q2 = r)
    (hx1 : r ^ 2 < @inner ℝ _ _ (q1 - a) (b - a))
    (hx2 : r ^ 2 < @inner ℝ _ _ (q2 - a) (b - a))
    (hsame_sign :
      0 < Problem97.MEC.cross2 (b - a) (q1 - a) * Problem97.MEC.cross2 (b - a) (q2 - a)) :
    False := by
  classical
  -- Abbreviate `x_i, y_i`.
  set x1 := @inner ℝ _ _ (q1 - a) (b - a) with hx1_def
  set x2 := @inner ℝ _ _ (q2 - a) (b - a) with hx2_def
  set y1 := Problem97.MEC.cross2 (b - a) (q1 - a) with hy1_def
  set y2 := Problem97.MEC.cross2 (b - a) (q2 - a) with hy2_def
  -- `b - a ≠ 0`, `‖b - a‖ = d`.
  have hba_ne : (b - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm hab_ne)
  have hba_norm : ‖b - a‖ = d := by
    rw [hd_def, dist_eq_norm]
    rw [show a - b = -(b - a) from by abel, norm_neg]
  have hba_norm_sq : ‖b - a‖ ^ 2 = d ^ 2 := by rw [hba_norm]
  have hd_sq_pos : (0 : ℝ) < d ^ 2 := by positivity
  -- `‖q_i - a‖ = r`, `‖q_i - a‖² = r²`.
  have hqia_norm_i : ∀ q : ℝ², dist a q = r → ‖q - a‖ = r := fun q hd => by
    rw [show ‖q - a‖ = dist q a from (dist_eq_norm _ _).symm, dist_comm]
    exact hd
  have hq1_norm : ‖q1 - a‖ = r := hqia_norm_i q1 hq1_dist
  have hq2_norm : ‖q2 - a‖ = r := hqia_norm_i q2 hq2_dist
  have hq1_norm_sq : ‖q1 - a‖ ^ 2 = r ^ 2 := by rw [hq1_norm]
  have hq2_norm_sq : ‖q2 - a‖ ^ 2 = r ^ 2 := by rw [hq2_norm]
  -- `x_i > 0`.
  have hr_sq_pos : 0 < r ^ 2 := by positivity
  have hx1_pos : 0 < x1 := by linarith
  have hx2_pos : 0 < x2 := by linarith
  -- Lagrange: `x_i² + y_i² = r² d²`. (Use `norm_sq_mul_eq_inner_sq_plus_cross_sq`.)
  have hLag1 : x1 ^ 2 + y1 ^ 2 = r ^ 2 * d ^ 2 := by
    have h := Problem97.MEC.norm_sq_mul_eq_inner_sq_plus_cross_sq (q1 - a) (b - a)
    rw [hq1_norm_sq, hba_norm_sq] at h
    linarith
  have hLag2 : x2 ^ 2 + y2 ^ 2 = r ^ 2 * d ^ 2 := by
    have h := Problem97.MEC.norm_sq_mul_eq_inner_sq_plus_cross_sq (q2 - a) (b - a)
    rw [hq2_norm_sq, hba_norm_sq] at h
    linarith
  -- `y_i ≠ 0` (from `hsame_sign : y_1 * y_2 > 0`).
  have hy1_ne : y1 ≠ 0 := by
    intro h; rw [h, zero_mul] at hsame_sign; linarith
  have hy2_ne : y2 ≠ 0 := by
    intro h; rw [h, mul_zero] at hsame_sign; linarith
  -- Define `Y_i := |y_i|`. Both positive.
  set Y1 := |y1| with hY1_def
  set Y2 := |y2| with hY2_def
  have hY1_pos : 0 < Y1 := abs_pos.mpr hy1_ne
  have hY2_pos : 0 < Y2 := abs_pos.mpr hy2_ne
  -- `Y_i² = y_i²`.
  have hY1_sq : Y1 ^ 2 = y1 ^ 2 := sq_abs y1
  have hY2_sq : Y2 ^ 2 = y2 ^ 2 := sq_abs y2
  -- Distinctness of q_1 and q_2 implies (x_1, y_1) ≠ (x_2, y_2).
  have hxy_ne : (x1, y1) ≠ (x2, y2) := by
    intro h
    obtain ⟨hx_eq, hy_eq⟩ := Prod.mk.inj h
    apply hq12_ne
    -- If x_1 = x_2 and y_1 = y_2, then q_1 - a = q_2 - a as vectors.
    set w := (q1 - a) - (q2 - a) with hw_def
    have h_inner_w : @inner ℝ _ _ w (b - a) = 0 := by
      rw [hw_def, inner_sub_left, ← hx1_def, ← hx2_def, hx_eq, sub_self]
    have h_cross_w : Problem97.MEC.cross2 (b - a) w = 0 := by
      rw [hw_def]
      have h1 : Problem97.MEC.cross2 (b - a) ((q1 - a) - (q2 - a)) =
          Problem97.MEC.cross2 (b - a) (q1 - a) - Problem97.MEC.cross2 (b - a) (q2 - a) := by
        simp [Problem97.MEC.cross2, PiLp.sub_apply]; ring
      rw [h1, ← hy1_def, ← hy2_def, hy_eq, sub_self]
    have hLag := Problem97.MEC.norm_sq_mul_eq_inner_sq_plus_cross_sq w (b - a)
    rw [h_inner_w, h_cross_w] at hLag
    have h_zero : ‖w‖ ^ 2 * ‖b - a‖ ^ 2 = 0 := by linarith
    have hba_norm_sq_pos : 0 < ‖b - a‖ ^ 2 := by rw [hba_norm_sq]; exact hd_sq_pos
    have hw_sq : ‖w‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h_zero with h | h
      · exact h
      · linarith
    have hw_norm : ‖w‖ = 0 := by
      have hnn : 0 ≤ ‖w‖ := norm_nonneg _
      nlinarith
    have hw_zero : w = 0 := norm_eq_zero.mp hw_norm
    have hsub_zero : q1 - q2 = 0 := by
      have hwq : (q1 - a) - (q2 - a) = q1 - q2 := by abel
      rw [← hwq]; exact hw_zero
    exact sub_eq_zero.mp hsub_zero
  -- WLOG on the order of Y_1 vs Y_2; the equality case yields q1 = q2.
  rcases lt_trichotomy Y1 Y2 with hY12 | hY12 | hY12
  · exact Problem97.MEC.same_sign_ordered_pair_contradiction hConv ha_mem hb_mem hq1_A hq2_A
      hab_ne hq1_ne_a hq1_ne_b hq2_ne_a hq2_ne_b hq12_ne hba_norm_sq hd_pos
      hr_pos hrd_lt hx1 hx2 (by rw [← hx1_def, ← hy1_def]; exact hLag1)
      (by rw [← hx2_def, ← hy2_def]; exact hLag2)
      (by rw [← hy1_def, ← hy2_def]; exact hsame_sign)
      (by rw [← hy1_def, ← hy2_def, ← hY1_def, ← hY2_def]; exact hY12)
  · -- Y1 = Y2 ⇒ q1 = q2, contradiction.
    exfalso
    have hY_sq : Y1 ^ 2 = Y2 ^ 2 := by rw [hY12]
    have hy_sq_eq : y1 ^ 2 = y2 ^ 2 := by
      rw [← hY1_sq, ← hY2_sq]; exact hY_sq
    have hx_sq_eq : x1 ^ 2 = x2 ^ 2 := by linarith [hLag1, hLag2, hy_sq_eq]
    have hx_eq : x1 = x2 := (sq_eq_sq₀ hx1_pos.le hx2_pos.le).mp hx_sq_eq
    have hy_eq : y1 = y2 := by
      rcases lt_or_gt_of_ne hy1_ne with h1_neg | h1_pos
      · have hy2_neg : y2 < 0 := by
          by_contra h
          push_neg at h
          rcases eq_or_lt_of_le h with hy2_zero | hy2_pos
          · rw [← hy2_zero, mul_zero] at hsame_sign; linarith
          · have : y1 * y2 < 0 := mul_neg_of_neg_of_pos h1_neg hy2_pos
            linarith
        have hY1_eq : Y1 = -y1 := by rw [hY1_def, abs_of_neg h1_neg]
        have hY2_eq : Y2 = -y2 := by rw [hY2_def, abs_of_neg hy2_neg]
        have : -y1 = -y2 := by rw [← hY1_eq, ← hY2_eq]; exact hY12
        linarith
      · have hy2_pos : 0 < y2 := by
          by_contra h
          push_neg at h
          rcases eq_or_lt_of_le h with hy2_zero | hy2_neg
          · rw [hy2_zero, mul_zero] at hsame_sign; linarith
          · have : y1 * y2 < 0 := mul_neg_of_pos_of_neg h1_pos hy2_neg
            linarith
        have hY1_eq : Y1 = y1 := by rw [hY1_def, abs_of_pos h1_pos]
        have hY2_eq : Y2 = y2 := by rw [hY2_def, abs_of_pos hy2_pos]
        have : y1 = y2 := by rw [← hY1_eq, ← hY2_eq]; exact hY12
        exact this
    exact hxy_ne (Prod.ext hx_eq hy_eq)
  · -- Y2 < Y1: swap roles.
    exact Problem97.MEC.same_sign_ordered_pair_contradiction hConv ha_mem hb_mem hq2_A hq1_A
      hab_ne hq2_ne_a hq2_ne_b hq1_ne_a hq1_ne_b (Ne.symm hq12_ne) hba_norm_sq hd_pos
      hr_pos hrd_lt hx2 hx1 (by rw [← hx2_def, ← hy2_def]; exact hLag2)
      (by rw [← hx1_def, ← hy1_def]; exact hLag1)
      (by rw [← hy1_def, ← hy2_def]; rw [mul_comm]; exact hsame_sign)
      (by rw [← hy1_def, ← hy2_def, ← hY1_def, ← hY2_def]; exact hY12)

/- ### The main proof: derive contradiction from the diameter case. -/


theorem solution
    {A : Finset ℝ²} (hA : A.Nonempty)
    (hncol : ¬ Collinear ℝ (A : Set ℝ²))
    (hConv : Problem97.ConvexIndep A)
    (hK4 : Problem97.HasNEquidistantProperty 4 A) :
    3 ≤ (A.filter (fun p => dist p (Problem97.MEC.mec A hA).center
                            = (Problem97.MEC.mec A hA).radius)).card := by
  classical
  -- Case-split on whether the MEC boundary has ≥ 3 points (the goal).
  by_contra h_lt_three
  push_neg at h_lt_three
  -- From Sylvester, either diameter case or boundary card ≥ 3. So we're in diameter.
  rcases sylvester_dichotomy hA hncol with hdiam | hcirc
  swap
  · exact absurd hcirc h_lt_three.not_ge
  -- Diameter case: derive a contradiction with K4 + ConvexIndep.
  obtain ⟨a, ha_mem, b, hb_mem, hab_ne, ha_bdry, hb_bdry, hc_eq, hr_eq⟩ := hdiam
  -- K4 at apex `a`: there's `r > 0` and `S := {q ∈ A | dist a q = r}` with `|S| ≥ 4`.
  obtain ⟨r, hr_pos, hr_card⟩ := hK4 a ha_mem
  set S := A.filter (fun q => dist a q = r) with hS_def
  have hS_data : ∀ q ∈ S, q ∈ A ∧ dist a q = r := fun q hq => by
    rw [hS_def, Finset.mem_filter] at hq; exact hq
  -- `d := dist a b > 0`.
  set d := dist a b with hd_def
  have hd_pos : 0 < d := by rw [hd_def, dist_pos]; exact hab_ne
  -- For `q ∈ S`, `q` is in the closed MEC disk centered at `(a+b)/2` of radius `d/2`.
  have hq_in_disk : ∀ q ∈ S, dist q (midpoint ℝ a b) ≤ d / 2 := by
    intro q hq
    have ⟨hq_A, _⟩ := hS_data q hq
    have h1 := (mec A hA).enclosing q hq_A
    rw [hc_eq, hr_eq] at h1; exact h1
  -- `a ∉ S` (distance 0 ≠ r > 0).
  have ha_not_S : a ∉ S := by
    rw [hS_def, Finset.mem_filter]
    intro ⟨_, h⟩; rw [dist_self] at h; linarith
  -- `b ∈ S ↔ r = d`.
  have hb_in_S_iff : b ∈ S ↔ r = d := by
    rw [hS_def, Finset.mem_filter]
    refine ⟨fun ⟨_, h⟩ => h.symm, fun heq => ⟨hb_mem, ?_⟩⟩
    exact heq.symm
  -- Distance bound for `q ∈ S`: `dist a q = r ≤ d` (in disk).
  have hr_le_d : r ≤ d := by
    have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hq⟩ := hS_ne
    have ⟨hq_A, hq_dist⟩ := hS_data q hq
    have hdisk := hq_in_disk q hq
    have h1 : dist q a ≤ dist q (midpoint ℝ a b) + dist (midpoint ℝ a b) a :=
      dist_triangle _ _ _
    have h2 : dist (midpoint ℝ a b) a = d / 2 := by
      rw [dist_comm, dist_left_midpoint, Real.norm_two, hd_def]
      ring
    linarith [hq_dist ▸ (dist_comm q a ▸ h1), h2]
  -- Show `r < d`. (Otherwise `r = d` and `S = {b}`, but `|S| ≥ 4`.)
  have hr_lt_d : r < d := by
    by_contra h_not_lt
    push_neg at h_not_lt
    have hr_eq_d : r = d := le_antisymm hr_le_d h_not_lt
    -- Then every q ∈ S has dist a q = d, so q = b.
    have hSb : ∀ q ∈ S, q = b := by
      intro q hq
      have ⟨hq_A, hq_dist⟩ := hS_data q hq
      have hq_d : dist q a = d := by rw [dist_comm]; rw [hq_dist, hr_eq_d]
      have hdisk := hq_in_disk q hq
      have h_inner : @inner ℝ _ _ (q - a) (b - a) = d ^ 2 := by
        have ht := Problem97.MEC.thales_of_in_diameter_disk (a := a) (b := b) (p := q) hdisk
        have heq : @inner ℝ _ _ (q - a) (q - b) =
            ‖q - a‖ ^ 2 - @inner ℝ _ _ (q - a) (b - a) := by
          have h1 : q - b = (q - a) + (a - b) := by abel
          rw [h1, inner_add_right, real_inner_self_eq_norm_sq]
          rw [show a - b = -(b - a) from by abel, inner_neg_right]; ring
        have hqa : ‖q - a‖ ^ 2 = d ^ 2 := by
          rw [show ‖q - a‖ = dist q a from (dist_eq_norm _ _).symm, hq_d]
        have hCS : @inner ℝ _ _ (q - a) (b - a) ≤ ‖q - a‖ * ‖b - a‖ :=
          real_inner_le_norm _ _
        have hba_norm : ‖b - a‖ = d := by
          rw [hd_def, dist_eq_norm]
          rw [show a - b = -(b - a) from by abel, norm_neg]
        rw [hba_norm] at hCS
        rw [show ‖q - a‖ = dist q a from (dist_eq_norm _ _).symm, hq_d] at hCS
        have h_ge : d ^ 2 ≤ @inner ℝ _ _ (q - a) (b - a) := by
          linarith [heq, hqa, ht]
        have h_le : @inner ℝ _ _ (q - a) (b - a) ≤ d ^ 2 := by
          nlinarith [hCS]
        linarith
      have hba_norm_sq : ‖b - a‖ ^ 2 = d ^ 2 := by
        have h_norm : ‖b - a‖ = d := by
          rw [hd_def, dist_eq_norm]
          rw [show a - b = -(b - a) from by abel, norm_neg]
        rw [h_norm]
      have hqa_norm_sq : ‖q - a‖ ^ 2 = d ^ 2 := by
        rw [show ‖q - a‖ = dist q a from (dist_eq_norm _ _).symm, hq_d]
      have hLag := Problem97.MEC.norm_sq_mul_eq_inner_sq_plus_cross_sq (q - a) (b - a)
      rw [hba_norm_sq, hqa_norm_sq, h_inner] at hLag
      have hcross_sq_zero : Problem97.MEC.cross2 (b - a) (q - a) ^ 2 = 0 := by linarith
      have hcross_zero : Problem97.MEC.cross2 (b - a) (q - a) = 0 := by
        exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hcross_sq_zero
      have hq_seg : q ∈ segment ℝ a b :=
        Problem97.MEC.in_segment_of_in_disk_and_collinear hab_ne hdisk hcross_zero
      rcases hq_seg with ⟨s, t, hs_nn, ht_nn, hst, hq_eq⟩
      have hq_sub : q - a = t • (b - a) := by
        rw [← hq_eq]
        have : s = 1 - t := by linarith
        rw [this]
        module
      have hdist_q_a : dist q a = t * d := by
        rw [show dist q a = ‖q - a‖ from dist_eq_norm _ _]
        rw [hq_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nn]
        rw [show ‖b - a‖ = d from by
          rw [hd_def, dist_eq_norm]
          rw [show a - b = -(b - a) from by abel, norm_neg]]
      have ht_eq_one : t = 1 := by
        have htd : t * d = d := by rw [← hdist_q_a, hq_d]
        have : t * d = 1 * d := by rw [one_mul]; exact htd
        exact (mul_right_cancel₀ hd_pos.ne' this)
      have hs_eq_zero : s = 0 := by linarith
      rw [hs_eq_zero, ht_eq_one] at hq_eq
      simp at hq_eq
      exact hq_eq.symm
    have hSeq : S = {b} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨(hb_in_S_iff).mpr hr_eq_d, ?_⟩
      intro x hx; exact hSb x hx
    have : S.card = 1 := by rw [hSeq]; rfl
    omega
  -- Now r < d, so b ∉ S.
  have hb_not_S : b ∉ S := by
    rw [hb_in_S_iff]; exact ne_of_lt hr_lt_d
  -- Every q ∈ S satisfies q ∈ A, q ≠ a, q ≠ b.
  have hS_sub_AAB : ∀ q ∈ S, q ∈ A ∧ q ≠ a ∧ q ≠ b := by
    intro q hq
    have ⟨hq_A, _⟩ := hS_data q hq
    refine ⟨hq_A, ?_, ?_⟩
    · intro h; rw [h] at hq; exact ha_not_S hq
    · intro h; rw [h] at hq; exact hb_not_S hq
  -- Every q ∈ A \ {a, b} is strictly inside the MEC disk.
  have h_strict_interior : ∀ q ∈ A, q ≠ a → q ≠ b →
      dist q (midpoint ℝ a b) < d / 2 := by
    intro q hq_A hq_a hq_b
    have h_le : dist q (midpoint ℝ a b) ≤ d / 2 := by
      have h := (mec A hA).enclosing q hq_A
      rw [hc_eq, hr_eq] at h; exact h
    rcases lt_or_eq_of_le h_le with h_lt | h_eq
    · exact h_lt
    exfalso
    set boundary := A.filter (fun p => dist p (mec A hA).center = (mec A hA).radius)
      with hbdry_def
    have ha_in : a ∈ boundary := Finset.mem_filter.mpr ⟨ha_mem, ha_bdry⟩
    have hb_in : b ∈ boundary := Finset.mem_filter.mpr ⟨hb_mem, hb_bdry⟩
    have hq_bdry : dist q (mec A hA).center = (mec A hA).radius := by
      rw [hc_eq, hr_eq]; exact h_eq
    have hq_in : q ∈ boundary := Finset.mem_filter.mpr ⟨hq_A, hq_bdry⟩
    have h_three_sub : ({a, b, q} : Finset ℝ²) ⊆ boundary := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha_in
      · exact hb_in
      · exact hq_in
    have h_three_card : ({a, b, q} : Finset ℝ²).card = 3 := by
      rw [show ({a, b, q} : Finset ℝ²) = insert a (insert b {q}) from rfl]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp; exact hq_b.symm
      · simp; constructor
        · exact hab_ne
        · exact hq_a.symm
    have h_bdry_ge_three : 3 ≤ boundary.card := by
      have := Finset.card_le_card h_three_sub
      omega
    exact absurd h_bdry_ge_three h_lt_three.not_ge
  have h_strict_interior_S : ∀ q ∈ S, dist q (midpoint ℝ a b) < d / 2 := fun q hq => by
    have ⟨hq_A, hq_a, hq_b⟩ := hS_sub_AAB q hq
    exact h_strict_interior q hq_A hq_a hq_b
  -- Strict Thales: ⟨q - a, b - a⟩ > ‖q - a‖² = r² for each q ∈ S.
  have h_inner_strict : ∀ q ∈ S, r ^ 2 < @inner ℝ _ _ (q - a) (b - a) := by
    intro q hq
    have ⟨_, hq_dist⟩ := hS_data q hq
    have h_disk_lt := h_strict_interior_S q hq
    have ht : @inner ℝ _ _ (q - a) (q - b) < 0 := by
      set m := midpoint ℝ a b with hm_def
      have hm_a : m - a = (1 / 2 : ℝ) • (b - a) := by
        rw [hm_def, midpoint_eq_smul_add]
        have h : (⅟2 : ℝ) = 1/2 := by simp [invOf_eq_inv]
        rw [h]; module
      have hm_b : m - b = (-(1 / 2 : ℝ)) • (b - a) := by
        rw [hm_def, midpoint_eq_smul_add]
        have h : (⅟2 : ℝ) = 1/2 := by simp [invOf_eq_inv]
        rw [h]; module
      have h1 : q - a = (q - m) + (1 / 2 : ℝ) • (b - a) := by
        have heq : q - a = (q - m) + (m - a) := by abel
        rw [heq, hm_a]
      have h2 : q - b = (q - m) - (1 / 2 : ℝ) • (b - a) := by
        have heq : q - b = (q - m) + (m - b) := by abel
        rw [heq, hm_b]
        rw [show (-(1 / 2 : ℝ)) • (b - a) = -((1 / 2 : ℝ) • (b - a)) from by simp]
        abel
      have hkey : @inner ℝ _ _ (q - a) (q - b) =
          ‖q - m‖ ^ 2 - (1 / 4 : ℝ) * ‖b - a‖ ^ 2 := by
        rw [h1, h2, inner_sub_right, inner_add_left, inner_add_left]
        rw [real_inner_self_eq_norm_sq]
        rw [real_inner_smul_right, real_inner_smul_left, real_inner_smul_left]
        rw [show @inner ℝ _ _ (b - a) ((1 / 2 : ℝ) • (b - a)) =
            (1 / 2 : ℝ) * @inner ℝ _ _ (b - a) (b - a) from by
          rw [real_inner_smul_right]]
        rw [real_inner_self_eq_norm_sq (b - a)]
        rw [← real_inner_comm (q - m) (b - a)]
        ring
      rw [hkey]
      have hba : ‖b - a‖ = d := by
        rw [hd_def, dist_eq_norm]
        rw [show a - b = -(b - a) from by abel, norm_neg]
      rw [hba]
      have hdist_sq : ‖q - m‖ ^ 2 < (d / 2) ^ 2 := by
        have hqm_eq : dist q m = ‖q - m‖ := dist_eq_norm _ _
        have h_nn : (0 : ℝ) ≤ dist q m := dist_nonneg
        nlinarith [h_disk_lt, h_nn, hqm_eq]
      nlinarith [hdist_sq]
    have hexp : @inner ℝ _ _ (q - a) (q - b) =
        ‖q - a‖ ^ 2 - @inner ℝ _ _ (q - a) (b - a) := by
      have h1 : q - b = (q - a) + (a - b) := by abel
      rw [h1, inner_add_right, real_inner_self_eq_norm_sq]
      rw [show a - b = -(b - a) from by abel, inner_neg_right]; ring
    have hqa_norm_sq : ‖q - a‖ ^ 2 = r ^ 2 := by
      rw [show ‖q - a‖ = dist q a from (dist_eq_norm _ _).symm, dist_comm, hq_dist]
    linarith [hexp ▸ ht, hqa_norm_sq]
  -- For each q ∈ S, Y_q ≠ 0 (q ≠ a, b, in disk, so not on line ab).
  have h_Y_ne : ∀ q ∈ S, Problem97.MEC.cross2 (b - a) (q - a) ≠ 0 := by
    intro q hq h_zero
    have ⟨hq_A, hq_a, hq_b⟩ := hS_sub_AAB q hq
    have hdisk_le : dist q (midpoint ℝ a b) ≤ d / 2 := by
      have h := (mec A hA).enclosing q hq_A
      rw [hc_eq, hr_eq] at h; exact h
    have hq_seg : q ∈ segment ℝ a b :=
      Problem97.MEC.in_segment_of_in_disk_and_collinear hab_ne hdisk_le h_zero
    apply hConv q (Finset.mem_coe.mpr hq_A)
    rw [← convexHull_pair] at hq_seg
    apply convexHull_mono ?_ hq_seg
    intro x hx
    rcases hx with rfl | rfl
    · refine ⟨?_, ?_⟩
      · exact Finset.mem_coe.mpr ha_mem
      · exact fun h => hq_a (Set.mem_singleton_iff.mp h).symm
    · refine ⟨?_, ?_⟩
      · exact Finset.mem_coe.mpr hb_mem
      · exact fun h => hq_b (Set.mem_singleton_iff.mp h).symm
  -- Pigeonhole on sign of Y_q: at least 4 points in S, each with Y_q ≠ 0.
  set S_pos := S.filter (fun q => 0 < Problem97.MEC.cross2 (b - a) (q - a)) with hS_pos_def
  set S_neg := S.filter (fun q => Problem97.MEC.cross2 (b - a) (q - a) < 0) with hS_neg_def
  have hS_partition : S_pos ∪ S_neg = S := by
    ext q
    simp only [Finset.mem_union, hS_pos_def, hS_neg_def, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hq
      have h_ne := h_Y_ne q hq
      rcases lt_trichotomy (Problem97.MEC.cross2 (b - a) (q - a)) 0 with h | h | h
      · right; exact ⟨hq, h⟩
      · exact absurd h h_ne
      · left; exact ⟨hq, h⟩
  have hS_disjoint : Disjoint S_pos S_neg := by
    rw [Finset.disjoint_left]
    intro q hq_pos hq_neg
    rw [hS_pos_def, Finset.mem_filter] at hq_pos
    rw [hS_neg_def, Finset.mem_filter] at hq_neg
    linarith [hq_pos.2, hq_neg.2]
  have hS_card : S_pos.card + S_neg.card = S.card := by
    rw [← Finset.card_union_of_disjoint hS_disjoint, hS_partition]
  -- S.card ≥ 4, so S_pos.card ≥ 2 or S_neg.card ≥ 2.
  have h_pigeon : 2 ≤ S_pos.card ∨ 2 ≤ S_neg.card := by
    by_contra h
    push_neg at h
    obtain ⟨h1, h2⟩ := h
    omega
  rcases h_pigeon with h_pos | h_neg
  · -- S_pos has 2 points; extract them and apply the helper.
    obtain ⟨q1, hq1_pos, q2, hq2_pos, hq12_ne⟩ := Finset.one_lt_card.mp h_pos
    have hq1_S : q1 ∈ S := (Finset.mem_filter.mp hq1_pos).1
    have hq2_S : q2 ∈ S := (Finset.mem_filter.mp hq2_pos).1
    have hq1_cross : 0 < Problem97.MEC.cross2 (b - a) (q1 - a) := (Finset.mem_filter.mp hq1_pos).2
    have hq2_cross : 0 < Problem97.MEC.cross2 (b - a) (q2 - a) := (Finset.mem_filter.mp hq2_pos).2
    have ⟨hq1_A, hq1_dist⟩ := hS_data q1 hq1_S
    have ⟨hq2_A, hq2_dist⟩ := hS_data q2 hq2_S
    have ⟨_, hq1_ne_a, hq1_ne_b⟩ := hS_sub_AAB q1 hq1_S
    have ⟨_, hq2_ne_a, hq2_ne_b⟩ := hS_sub_AAB q2 hq2_S
    have hsame_sign : 0 < Problem97.MEC.cross2 (b - a) (q1 - a) * Problem97.MEC.cross2 (b - a) (q2 - a) :=
      mul_pos hq1_cross hq2_cross
    exact Problem97.MEC.same_sign_pair_contradiction hConv ha_mem hb_mem hq1_A hq2_A hab_ne
      hq1_ne_a hq1_ne_b hq2_ne_a hq2_ne_b hq12_ne hd_def hd_pos hr_pos hr_lt_d
      hq1_dist hq2_dist (h_inner_strict q1 hq1_S) (h_inner_strict q2 hq2_S)
      hsame_sign
  · -- S_neg has 2 points; extract them and apply the helper (cross products both negative,
    -- product is positive).
    obtain ⟨q1, hq1_neg, q2, hq2_neg, hq12_ne⟩ := Finset.one_lt_card.mp h_neg
    have hq1_S : q1 ∈ S := (Finset.mem_filter.mp hq1_neg).1
    have hq2_S : q2 ∈ S := (Finset.mem_filter.mp hq2_neg).1
    have hq1_cross : Problem97.MEC.cross2 (b - a) (q1 - a) < 0 := (Finset.mem_filter.mp hq1_neg).2
    have hq2_cross : Problem97.MEC.cross2 (b - a) (q2 - a) < 0 := (Finset.mem_filter.mp hq2_neg).2
    have ⟨hq1_A, hq1_dist⟩ := hS_data q1 hq1_S
    have ⟨hq2_A, hq2_dist⟩ := hS_data q2 hq2_S
    have ⟨_, hq1_ne_a, hq1_ne_b⟩ := hS_sub_AAB q1 hq1_S
    have ⟨_, hq2_ne_a, hq2_ne_b⟩ := hS_sub_AAB q2 hq2_S
    have hsame_sign : 0 < Problem97.MEC.cross2 (b - a) (q1 - a) * Problem97.MEC.cross2 (b - a) (q2 - a) :=
      mul_pos_of_neg_of_neg hq1_cross hq2_cross
    exact Problem97.MEC.same_sign_pair_contradiction hConv ha_mem hb_mem hq1_A hq2_A hab_ne
      hq1_ne_a hq1_ne_b hq2_ne_a hq2_ne_b hq12_ne hd_def hd_pos hr_pos hr_lt_d
      hq1_dist hq2_dist (h_inner_strict q1 hq1_S) (h_inner_strict q2 hq2_S)
      hsame_sign

end Erdos9796CountingFragment_Erdos9796Proof_P97_NoDiameterUnderK4
