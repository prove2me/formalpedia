-- Prove2me | solution 1 for Problem97.MEC.sylvester_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:22.972692+00:00
-- url     : https://prove2.me/submissions/04fba056-9240-4ddf-bc60-ba4b1c578bda

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.MEC.Boundary:24744:27366. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_MEC_Boundary

section Erdos9796CountingFragment_Erdos9796Proof_P97_MEC_Boundary

open Problem97 Problem97.MEC

/- Fragment from Erdos9796Proof.P97.MEC.Boundary; source SHA-256 e7d16b0637be4dd967cade4cfb9db7d4ba52c8fdb229ece7b87498ff207e21a7 -/


/-!
# MEC boundary structure — Sylvester (1857) dichotomy

For any nonempty noncollinear finite point set `A ⊆ ℝ²` we prove the
classical Sylvester dichotomy on the minimum enclosing circle (MEC) of
`A`:

* **Diameter case** — two points of `A` lie diametrically opposite on
  the MEC boundary, pinning the centre to their midpoint, OR
* **Circumscribed case** — at least three points of `A` lie on the MEC
  boundary.

The naive "≥3 boundary points" statement is **false** in general:
obtuse triangles realise the diameter case (the two acute-angle vertices
form an antipodal pair on the MEC, the obtuse vertex sits strictly
inside).  The disjunction below is the correct formulation, due to
Sylvester (1857).

The argument is variational.  Define
`B(A) := { p ∈ A | dist p M.center = M.radius }`, the set of points
realising the maximum distance from the MEC centre.  Then:

* `B.card = 0` is impossible: by continuity of `radF`, every point sits
  strictly inside, so we can shrink `M.radius` keeping the centre fixed
  — contradicting minimality.
* `B.card = 1` is impossible for noncollinear `A`: perturb the centre
  toward the lone boundary point.  Strict interior distance to other
  points is preserved by continuity, so we obtain a smaller enclosing
  radius — contradicting minimality.
* `B.card = 2` forces the diameter case: the two boundary points
  `p, q` pin the centre to their midpoint (otherwise we could shift
  along the perpendicular bisector toward `midpoint p q` to shrink the
  radius — same contradiction).
* `B.card ≥ 3` is the circumscribed case by definition.

The core perturbation uses an algebraic identity: along the segment
from `c := M.center` toward a target `q*` chosen so that
`⟨p - c, q* - c⟩ = ‖q* - c‖²` for every boundary point `p ∈ B`,
the squared distance `‖p - c'(t)‖²` equals
`M.radius² + (t² - 2t) ‖q* - c‖²`, which is strictly less than
`M.radius²` for `t ∈ (0, 2)` (and `q* ≠ c`).  For interior points the
distance change is bounded by `t · ‖q* - c‖`, so picking `t` small
enough keeps them inside as well.

## Main theorem

* `Problem97.MEC.sylvester_dichotomy` — the Sylvester (1857) dichotomy
  in disjunctive form, suitable for downstream consumers branching on
  the two cases.
-/

open scoped EuclideanGeometry
open Finset




/- ### Boundary set of the MEC -/



/-- Membership in the MEC boundary is membership in `A` together with
equality to the radius from the MEC centre. -/
lemma Problem97.MEC.mem_boundary_iff {A : Finset ℝ²} (hA : A.Nonempty) {p : ℝ²} :
    p ∈ boundary A hA ↔ p ∈ A ∧ dist p (mec A hA).center = (mec A hA).radius := by
  classical
  simp [boundary]



/- ### Auxiliary helpers -/

/-- For nonempty `A`, the MEC radius is the max distance from the centre. -/
 lemma Problem97.MEC.mec_radius_eq_sup'
    (A : Finset ℝ²) (hA : A.Nonempty) :
    (mec A hA).radius =
      A.sup' hA (fun p => dist p (mec A hA).center) := by
  classical
  set M := mec A hA with hM_def
  -- M.radius ≤ sup' (use minimality with c = M.center, r = sup').
  have hsup_encl : ∀ p ∈ A,
      dist p M.center ≤ A.sup' hA (fun p => dist p M.center) := by
    intro p hp; exact Finset.le_sup' (fun p => dist p M.center) hp
  have hsup_min : M.radius ≤ A.sup' hA (fun p => dist p M.center) :=
    M.minimal M.center _ hsup_encl
  -- sup' ≤ M.radius (each distance is ≤ M.radius).
  have hsup_le : A.sup' hA (fun p => dist p M.center) ≤ M.radius :=
    (Finset.sup'_le_iff hA _).mpr (fun p hp => M.enclosing p hp)
  linarith

/-- For a nonempty finite set, some point attains the MEC radius and hence
lies on the boundary. -/
lemma Problem97.MEC.boundary_nonempty
    (A : Finset ℝ²) (hA : A.Nonempty) :
    (boundary A hA).Nonempty := by
  classical
  set M := mec A hA with hM_def
  -- Sup of `dist · M.center` over `A` is attained at some `p`.
  obtain ⟨p, hp_mem, hp_eq⟩ :=
    Finset.exists_mem_eq_sup' hA (fun p => dist p M.center)
  refine ⟨p, ?_⟩
  rw [mem_boundary_iff]
  refine ⟨hp_mem, ?_⟩
  -- dist p M.center = sup' = M.radius
  rw [← hp_eq, ← Problem97.MEC.mec_radius_eq_sup' A hA]

/-- Noncollinear ⇒ `A` is not a singleton. -/
 lemma Problem97.MEC.not_singleton_of_noncollinear
    {A : Finset ℝ²} (hncol : ¬ Collinear ℝ (A : Set ℝ²)) :
    ∀ a, A ≠ {a} := by
  intro a hA_eq
  apply hncol
  -- Singleton is collinear.
  have : (A : Set ℝ²) = {a} := by rw [hA_eq]; simp
  rw [this]
  exact collinear_singleton ℝ a



/- ### Boundary card lower bound: ≥ 1 -/

 lemma Problem97.MEC.boundary_card_pos
    (A : Finset ℝ²) (hA : A.Nonempty) :
    1 ≤ (boundary A hA).card :=
  Finset.card_pos.mpr (boundary_nonempty A hA)

/- ### Sentinel computation: distance along a "shrink-toward-target" line.

We isolate the algebraic identity that underlies both the card-1 and card-2
variational arguments.  If `p, c, q* : ℝ²` satisfy
`⟨p - c, q* - c⟩ = ‖q* - c‖²`, then
`‖p - (c + t • (q* - c))‖² = ‖p - c‖² - (2t - t²) ‖q* - c‖²`.

For `card = 1` with single boundary point `p₀`, take `q* := p₀`; then
`⟨p₀ - c, p₀ - c⟩ = ‖p₀ - c‖² = M.radius² = ‖q* - c‖²` (uses `q* - c = p₀ - c`).

For `card = 2` with boundary `{p, q}`, take `q* := midpoint p q = m`; then
on the perpendicular bisector, `⟨p - c, m - c⟩ = ‖m - c‖²`.
-/

/-- The core shrink identity at `t = 1` and along the segment to `q*`:
if `⟨p - c, q* - c⟩ = ‖q* - c‖²`, then moving `t` of the way from `c` to `q*`
reduces `‖p - · ‖²` by `(2t - t²) ‖q* - c‖²`. -/
 lemma Problem97.MEC.sq_dist_shrink_along_line
    (p c q : ℝ²) (t : ℝ)
    (hpin : inner ℝ (p - c) (q - c) = ‖q - c‖ ^ 2) :
    ‖p - (c + t • (q - c))‖ ^ 2 = ‖p - c‖ ^ 2 - (2 * t - t ^ 2) * ‖q - c‖ ^ 2 := by
  have h1 : p - (c + t • (q - c)) = (p - c) - t • (q - c) := by abel_nf
  rw [h1, norm_sub_pow_two_real, real_inner_smul_right]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hpin]
  ring

/-- An ordinary triangle-inequality bound on the distance under the same
perturbation: `‖p - (c + t • v)‖ ≤ ‖p - c‖ + |t| · ‖v‖`. -/
 lemma Problem97.MEC.norm_perturb_le
    (p c v : ℝ²) (t : ℝ) :
    ‖p - (c + t • v)‖ ≤ ‖p - c‖ + |t| * ‖v‖ := by
  have h : p - (c + t • v) = (p - c) - t • v := by abel_nf
  rw [h]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]

/- ### Card 1 case — impossible for noncollinear A -/

/-- If the boundary has exactly one point `p₀`, the MEC centre can be
perturbed toward `p₀` to obtain a strictly smaller enclosing radius —
contradicting minimality. -/
 lemma Problem97.MEC.not_card_boundary_eq_one
    {A : Finset ℝ²} (hA : A.Nonempty)
    (hncol : ¬ Collinear ℝ (A : Set ℝ²)) :
    (boundary A hA).card ≠ 1 := by
  classical
  intro hcard
  set M := mec A hA with hM_def
  have hr_pos : 0 < M.radius := mec_radius_pos hA hncol
  -- Extract the unique boundary point.
  rw [Finset.card_eq_one] at hcard
  obtain ⟨p₀, hp₀_def⟩ := hcard
  have hp₀_in_b : p₀ ∈ boundary A hA := by rw [hp₀_def]; exact Finset.mem_singleton_self _
  have hp₀_data := (mem_boundary_iff hA).1 hp₀_in_b
  have hp₀_mem : p₀ ∈ A := hp₀_data.1
  have hp₀_bdry : dist p₀ M.center = M.radius := hp₀_data.2
  -- p₀ ≠ M.center (since M.radius > 0).
  have hp₀_ne_c : p₀ ≠ M.center := by
    intro hpc; rw [hpc] at hp₀_bdry
    rw [dist_self] at hp₀_bdry; linarith
  -- All other points of `A` are strictly inside.
  have hinterior : ∀ q ∈ A, q ≠ p₀ → dist q M.center < M.radius := by
    intro q hq hne
    have hq_not_bdry : q ∉ boundary A hA := by
      intro h; rw [hp₀_def, Finset.mem_singleton] at h; exact hne h
    have hq_le : dist q M.center ≤ M.radius := M.enclosing q hq
    rw [mem_boundary_iff] at hq_not_bdry; push_neg at hq_not_bdry
    exact lt_of_le_of_ne hq_le (hq_not_bdry hq)
  -- A is not the singleton {p₀} (else collinear).
  have hex_other : ∃ q ∈ A, q ≠ p₀ := by
    by_contra hno
    push_neg at hno
    apply Problem97.MEC.not_singleton_of_noncollinear hncol p₀
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hp₀_mem, hno⟩
  -- Set of interior points (A.erase p₀), all strictly inside.
  set I := A.erase p₀ with hI_def
  have hI_subset : I ⊆ A := Finset.erase_subset _ _
  obtain ⟨qSample, hqSample_mem, hqSample_ne⟩ := hex_other
  have hI_ne : I.Nonempty :=
    ⟨qSample, Finset.mem_erase.mpr ⟨hqSample_ne, hqSample_mem⟩⟩
  have hI_strict : ∀ q ∈ I, dist q M.center < M.radius := by
    intro q hq
    have ⟨hq_ne, hq_mem⟩ := Finset.mem_erase.mp hq
    exact hinterior q hq_mem hq_ne
  -- Imax := max over I of dist q M.center; this is < M.radius.
  set Imax := I.sup' hI_ne (fun q => dist q M.center) with hImax_def
  have hImax_lt : Imax < M.radius :=
    (Finset.sup'_lt_iff hI_ne).mpr hI_strict
  set δ := M.radius - Imax with hδ_def
  have hδ_pos : 0 < δ := by simp [hδ_def]; linarith
  -- Pick perturbation parameter t with 0 < t < 1 and t · M.radius < δ.
  set t := min (1/2) (δ / (2 * M.radius)) with ht_def
  have ht_pos : 0 < t := lt_min (by norm_num) (by positivity)
  have ht_le_half : t ≤ 1/2 := min_le_left _ _
  have ht_le_dM : t ≤ δ / (2 * M.radius) := min_le_right _ _
  have ht_lt_one : t < 1 := lt_of_le_of_lt ht_le_half (by norm_num)
  have ht_M_lt_δ : t * M.radius < δ := by
    have h1 : t * M.radius ≤ (δ / (2 * M.radius)) * M.radius :=
      mul_le_mul_of_nonneg_right ht_le_dM (le_of_lt hr_pos)
    have h2 : (δ / (2 * M.radius)) * M.radius = δ / 2 := by
      field_simp
    rw [h2] at h1
    linarith
  -- The perturbed centre.
  set c' := M.center + t • (p₀ - M.center) with hc'_def
  -- dist p₀ c' = (1 - t) * M.radius.
  have hdist_p₀ : dist p₀ c' = (1 - t) * M.radius := by
    have hsub : p₀ - c' = (1 - t) • (p₀ - M.center) := by
      simp [hc'_def, sub_smul, one_smul, smul_sub]
      module
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    have h1t : 0 ≤ 1 - t := by linarith
    rw [abs_of_nonneg h1t]
    rw [show dist p₀ M.center = ‖p₀ - M.center‖ from dist_eq_norm _ _] at hp₀_bdry
    rw [hp₀_bdry]
  -- For q ∈ I, dist q c' < M.radius.
  have hdist_I : ∀ q ∈ I, dist q c' < M.radius := by
    intro q hq
    have hbnd : dist q c' ≤ dist q M.center + t * M.radius := by
      -- ‖q - (M.center + t • (p₀ - M.center))‖ ≤ ‖q - M.center‖ + t * ‖p₀ - M.center‖
      have h := Problem97.MEC.norm_perturb_le q M.center (p₀ - M.center) t
      rw [show |t| = t from abs_of_pos ht_pos] at h
      rw [show ‖p₀ - M.center‖ = M.radius from by
        rw [← dist_eq_norm]; exact hp₀_bdry] at h
      rw [show dist q M.center = ‖q - M.center‖ from dist_eq_norm _ _]
      rw [show dist q c' = ‖q - c'‖ from dist_eq_norm _ _]
      exact h
    have hq_strict : dist q M.center < M.radius := hI_strict q hq
    have h_dist_q : dist q M.center ≤ Imax :=
      Finset.le_sup' (f := fun q => dist q M.center) hq
    -- dist q c' ≤ Imax + t * M.radius < (M.radius - δ) + δ = M.radius
    have : dist q M.center + t * M.radius ≤ Imax + t * M.radius := by linarith
    have : dist q c' ≤ Imax + t * M.radius := hbnd.trans this
    linarith
  -- Also, dist p₀ c' < M.radius (since 0 < t).
  have hdist_p₀_lt : dist p₀ c' < M.radius := by
    rw [hdist_p₀]
    nlinarith [hr_pos]
  -- Combine: A.sup' hA (dist · c') < M.radius, contradicting minimality.
  have h_all_lt : ∀ q ∈ A, dist q c' < M.radius := by
    intro q hq
    by_cases hqp : q = p₀
    · rw [hqp]; exact hdist_p₀_lt
    · have hqI : q ∈ I := Finset.mem_erase.mpr ⟨hqp, hq⟩
      exact hdist_I q hqI
  -- Let r' = sup' < M.radius, then (c', r') is enclosing.
  set r' := A.sup' hA (fun q => dist q c') with hr'_def
  have hr'_lt : r' < M.radius := (Finset.sup'_lt_iff hA).mpr h_all_lt
  have hr'_encl : ∀ q ∈ A, dist q c' ≤ r' :=
    fun q hq => Finset.le_sup' (f := fun q => dist q c') hq
  have hmin : M.radius ≤ r' := M.minimal c' r' hr'_encl
  linarith

/- ### Card 2 case — diameter case -/

/-- Key fact: if two points `p, q ∈ A` are MEC-boundary points (`dist = radius`),
then `c := M.center` lies on the perpendicular bisector of `p, q`. -/
 lemma Problem97.MEC.center_on_perpBisector_of_boundary
    {A : Finset ℝ²} (hA : A.Nonempty)
    {p q : ℝ²} (hp : p ∈ boundary A hA) (hq : q ∈ boundary A hA) :
    (mec A hA).center ∈ AffineSubspace.perpBisector p q := by
  classical
  set M := mec A hA with hM_def
  rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
  -- dist M.center p = dist M.center q (both equal M.radius, with dist_comm)
  have hp_data := (mem_boundary_iff hA).1 hp
  have hq_data := (mem_boundary_iff hA).1 hq
  rw [dist_comm, hp_data.2, dist_comm, hq_data.2]

/-- **Algebraic core of card-2 diameter argument**:
if `c` is equidistant from `p, q` (i.e., on perp bisector), then
`⟨p - c, m - c⟩ = ‖m - c‖²` where `m = midpoint p q`. -/
 lemma Problem97.MEC.inner_p_sub_c_m_sub_c
    (p q c : ℝ²)
    (hc : c ∈ AffineSubspace.perpBisector p q) :
    inner ℝ (p - c) (midpoint ℝ p q - c) = ‖midpoint ℝ p q - c‖^2 := by
  -- m - c = (1/2) • ((p - c) + (q - c))
  have hm_eq : midpoint ℝ p q - c = (1/2 : ℝ) • ((p - c) + (q - c)) := by
    rw [midpoint_eq_smul_add]
    have h : (⅟2 : ℝ) = 1/2 := by simp [invOf_eq_inv]
    rw [h]
    module
  rw [hm_eq, real_inner_smul_right, inner_add_right]
  rw [norm_smul, Real.norm_eq_abs, mul_pow]
  have habs : |(1/2 : ℝ)| = 1/2 := by norm_num
  rw [habs]
  rw [norm_add_pow_two_real]
  rw [show inner ℝ (p - c) (p - c) = ‖p - c‖^2 from real_inner_self_eq_norm_sq _]
  have h_pc_qc : ‖p - c‖ = ‖q - c‖ := by
    have hdist : dist c p = dist c q :=
      (AffineSubspace.mem_perpBisector_iff_dist_eq).1 hc
    rw [show ‖p - c‖ = dist p c from (dist_eq_norm _ _).symm]
    rw [show ‖q - c‖ = dist q c from (dist_eq_norm _ _).symm]
    rw [dist_comm p c, dist_comm q c]
    exact hdist
  rw [h_pc_qc]
  ring

/-- For `B = {p, q}` (card-2 case), the diameter case holds: `M.center = midpoint p q`
and `M.radius = dist p q / 2`. -/
 lemma Problem97.MEC.diameter_case_of_card_boundary_eq_two
    {A : Finset ℝ²} (hA : A.Nonempty)
    (hncol : ¬ Collinear ℝ (A : Set ℝ²))
    {p q : ℝ²}
    (hp_bdry : p ∈ boundary A hA) (hq_bdry : q ∈ boundary A hA)
    (_hpq_ne : p ≠ q)
    (h_only_pq : ∀ x ∈ boundary A hA, x = p ∨ x = q) :
    (mec A hA).center = midpoint ℝ p q := by
  classical
  set M := mec A hA with hM_def
  have hr_pos : 0 < M.radius := mec_radius_pos hA hncol
  -- M.center on perp bisector of {p, q}.
  have hc_perp := Problem97.MEC.center_on_perpBisector_of_boundary hA hp_bdry hq_bdry
  -- Inner product identity: ⟨p - c, m - c⟩ = ‖m - c‖².
  set m := midpoint ℝ p q with hm_def
  have hpc_data := (mem_boundary_iff hA).1 hp_bdry
  have hqc_data := (mem_boundary_iff hA).1 hq_bdry
  have hp_mem : p ∈ A := hpc_data.1
  have hq_mem : q ∈ A := hqc_data.1
  have hp_bdry_eq : dist p M.center = M.radius := hpc_data.2
  have hq_bdry_eq : dist q M.center = M.radius := hqc_data.2
  -- Other points strictly inside.
  have hinterior : ∀ x ∈ A, x ≠ p → x ≠ q → dist x M.center < M.radius := by
    intro x hxA hxp hxq
    by_contra h
    push_neg at h
    have hx_le : dist x M.center ≤ M.radius := M.enclosing x hxA
    have hx_eq : dist x M.center = M.radius := le_antisymm hx_le h
    have hx_bdry : x ∈ boundary A hA := (mem_boundary_iff hA).2 ⟨hxA, hx_eq⟩
    rcases h_only_pq x hx_bdry with hxp' | hxq'
    · exact hxp hxp'
    · exact hxq hxq'
  -- Suppose M.center ≠ midpoint — derive contradiction by perturbation toward m.
  by_contra hne
  have hmc_pos : 0 < ‖m - M.center‖ := by
    rw [norm_pos_iff]; intro h
    have : m = M.center := sub_eq_zero.mp h
    exact hne this.symm
  -- Shrink identity: along c'(t) = M.center + t • (m - M.center), for both p and q,
  -- ‖p - c'(t)‖² = M.radius² - (2t - t²) ‖m - M.center‖².
  -- Hence for t ∈ (0, 1], this is < M.radius².
  -- For interior points x, ‖x - c'(t)‖ ≤ ‖x - M.center‖ + t * ‖m - M.center‖,
  -- which is < M.radius for small t.
  -- Choose t = min(1/2, δ / (2 ‖m - M.center‖)) where δ > 0 controls interior gap.
  -- ===
  -- For p: inner (p - M.center) (m - M.center) = ‖m - M.center‖² (by lemma).
  -- For q: similarly via perp bisector. But we need same identity for q.
  -- Verify for q: ⟨q - c, m - c⟩ = ?  Note m = (p+q)/2, so q - c = 2(m - c) - (p - c).
  -- ⟨q - c, m - c⟩ = 2 ‖m - c‖² - ⟨p - c, m - c⟩ = 2 ‖m - c‖² - ‖m - c‖² = ‖m - c‖².  Good.
  -- ===
  have hinner_p : inner ℝ (p - M.center) (m - M.center) = ‖m - M.center‖^2 :=
    Problem97.MEC.inner_p_sub_c_m_sub_c p q M.center hc_perp
  -- For q, use that q - c = 2 (m - c) - (p - c) (since m = (p+q)/2).
  have hq_decomp : q - M.center = (2 : ℝ) • (m - M.center) - (p - M.center) := by
    rw [hm_def, midpoint_eq_smul_add]
    have h : (⅟2 : ℝ) = 1/2 := by simp [invOf_eq_inv]
    rw [h]; module
  have hinner_q : inner ℝ (q - M.center) (m - M.center) = ‖m - M.center‖^2 := by
    rw [hq_decomp, inner_sub_left, real_inner_smul_left, hinner_p]
    rw [show inner ℝ (m - M.center) (m - M.center) = ‖m - M.center‖^2 from
      real_inner_self_eq_norm_sq _]
    ring
  -- Setup interior gap.
  set Iset := A.filter (fun x => x ≠ p ∧ x ≠ q) with hIset_def
  -- Compute the perturbation parameter t.
  -- Case A: Iset is empty. Then A = {p, q}, two points, collinear.  Contradiction.
  by_cases hIset_empty : Iset = ∅
  · -- All of A is in {p, q}; A.card ≤ 2; A is collinear (2 points are collinear).
    have hA_sub : (A : Set ℝ²) ⊆ {p, q} := by
      intro x hx
      have hxA : x ∈ A := hx
      by_cases hxp : x = p
      · left; exact hxp
      by_cases hxq : x = q
      · right; rw [hxq]; rfl
      exfalso
      have hxIset : x ∈ Iset := Finset.mem_filter.mpr ⟨hxA, hxp, hxq⟩
      rw [hIset_empty] at hxIset
      exact Finset.notMem_empty _ hxIset
    apply hncol
    refine Collinear.subset hA_sub ?_
    exact collinear_pair ℝ p q
  rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at hIset_empty
  have hIset_ne := hIset_empty
  -- Iset is nonempty; each element strictly inside.
  have hIset_strict : ∀ x ∈ Iset, dist x M.center < M.radius := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact hinterior x hx.1 hx.2.1 hx.2.2
  set Imax := Iset.sup' hIset_ne (fun x => dist x M.center) with hImax_def
  have hImax_lt : Imax < M.radius :=
    (Finset.sup'_lt_iff hIset_ne).mpr hIset_strict
  set δ := M.radius - Imax with hδ_def
  have hδ_pos : 0 < δ := by simp [hδ_def]; linarith
  -- Choose t = min(1/2, δ / (2 ‖m - M.center‖)).
  set s := ‖m - M.center‖ with hs_def
  set t := min (1/2) (δ / (2 * s)) with ht_def
  have hs_pos : 0 < s := hmc_pos
  have ht_pos : 0 < t := lt_min (by norm_num) (by positivity)
  have ht_le_half : t ≤ 1/2 := min_le_left _ _
  have ht_le_δs : t ≤ δ / (2 * s) := min_le_right _ _
  have ht_lt_one : t < 1 := lt_of_le_of_lt ht_le_half (by norm_num)
  have ht_s_lt_δ : t * s < δ := by
    have h1 : t * s ≤ (δ / (2 * s)) * s :=
      mul_le_mul_of_nonneg_right ht_le_δs (le_of_lt hs_pos)
    have h2 : (δ / (2 * s)) * s = δ / 2 := by
      field_simp
    rw [h2] at h1; linarith
  -- Perturbed centre.
  set c' := M.center + t • (m - M.center) with hc'_def
  -- Show all distances strictly < M.radius.
  -- For p (use shrink identity).
  have h_psq : ‖p - c'‖^2 = M.radius^2 - (2 * t - t^2) * s^2 := by
    have h := Problem97.MEC.sq_dist_shrink_along_line p M.center m t hinner_p
    rw [hc'_def]
    rw [show ‖p - M.center‖ = M.radius from by
      rw [← dist_eq_norm]; exact hp_bdry_eq] at h
    rw [show ‖m - M.center‖ = s from rfl] at h
    exact h
  have h_qsq : ‖q - c'‖^2 = M.radius^2 - (2 * t - t^2) * s^2 := by
    have h := Problem97.MEC.sq_dist_shrink_along_line q M.center m t hinner_q
    rw [hc'_def]
    rw [show ‖q - M.center‖ = M.radius from by
      rw [← dist_eq_norm]; exact hq_bdry_eq] at h
    rw [show ‖m - M.center‖ = s from rfl] at h
    exact h
  -- Numerical bound: (2 t - t²) s² > 0 since 0 < t < 2 and s > 0.
  have h_ts_pos : 0 < (2 * t - t^2) * s^2 := by
    have h1 : 0 < 2 * t - t^2 := by nlinarith
    have h2 : 0 < s^2 := by positivity
    exact mul_pos h1 h2
  have h_psq_lt : ‖p - c'‖^2 < M.radius^2 := by
    rw [h_psq]; linarith
  have h_qsq_lt : ‖q - c'‖^2 < M.radius^2 := by
    rw [h_qsq]; linarith
  have hp_dist_lt : dist p c' < M.radius := by
    rw [dist_eq_norm]
    have h_nn1 : (0 : ℝ) ≤ ‖p - c'‖ := norm_nonneg _
    have h_nn2 : (0 : ℝ) ≤ M.radius := M.radius_nn
    nlinarith [sq_nonneg (‖p - c'‖ - M.radius), sq_nonneg (‖p - c'‖ + M.radius)]
  have hq_dist_lt : dist q c' < M.radius := by
    rw [dist_eq_norm]
    have h_nn1 : (0 : ℝ) ≤ ‖q - c'‖ := norm_nonneg _
    have h_nn2 : (0 : ℝ) ≤ M.radius := M.radius_nn
    nlinarith [sq_nonneg (‖q - c'‖ - M.radius), sq_nonneg (‖q - c'‖ + M.radius)]
  -- For x ∈ Iset: dist x c' < M.radius.
  have hx_dist_lt : ∀ x ∈ Iset, dist x c' < M.radius := by
    intro x hx
    have hx_strict : dist x M.center < M.radius := hIset_strict x hx
    have hx_data : dist x M.center ≤ Imax :=
      Finset.le_sup' (f := fun x => dist x M.center) hx
    -- norm_perturb_le: ‖x - c'‖ ≤ ‖x - M.center‖ + t * s.
    have h := Problem97.MEC.norm_perturb_le x M.center (m - M.center) t
    rw [show |t| = t from abs_of_pos ht_pos] at h
    rw [show ‖m - M.center‖ = s from rfl] at h
    rw [show dist x c' = ‖x - c'‖ from dist_eq_norm _ _]
    have hx_M_eq : ‖x - M.center‖ = dist x M.center := by rw [dist_eq_norm]
    rw [hx_M_eq] at h
    linarith
  -- Combine all points.
  have h_all_lt : ∀ x ∈ A, dist x c' < M.radius := by
    intro x hx
    by_cases hxp : x = p
    · rw [hxp]; exact hp_dist_lt
    by_cases hxq : x = q
    · rw [hxq]; exact hq_dist_lt
    have hxIset : x ∈ Iset := Finset.mem_filter.mpr ⟨hx, hxp, hxq⟩
    exact hx_dist_lt x hxIset
  -- Sup is < M.radius; contradicts minimality.
  set r' := A.sup' hA (fun x => dist x c') with hr'_def
  have hr'_lt : r' < M.radius := (Finset.sup'_lt_iff hA).mpr h_all_lt
  have hr'_encl : ∀ x ∈ A, dist x c' ≤ r' :=
    fun x hx => Finset.le_sup' (f := fun x => dist x c') hx
  have hmin : M.radius ≤ r' := M.minimal c' r' hr'_encl
  linarith

/-- For `B = {p, q}` (card-2 case), the MEC radius equals `dist p q / 2`. -/
 lemma Problem97.MEC.radius_eq_half_dist_of_card_boundary_eq_two
    {A : Finset ℝ²} (hA : A.Nonempty)
    (hncol : ¬ Collinear ℝ (A : Set ℝ²))
    {p q : ℝ²}
    (hp_bdry : p ∈ boundary A hA)
    (hq_bdry : q ∈ boundary A hA)
    (hpq_ne : p ≠ q)
    (h_only_pq : ∀ x ∈ boundary A hA, x = p ∨ x = q) :
    (mec A hA).radius = dist p q / 2 := by
  have hc_eq := Problem97.MEC.diameter_case_of_card_boundary_eq_two hA hncol hp_bdry hq_bdry hpq_ne h_only_pq
  -- (mec A hA).radius = dist p (mec A hA).center = dist p (midpoint p q) = dist p q / 2
  have hp_data := (mem_boundary_iff hA).1 hp_bdry
  have h1 : (mec A hA).radius = dist p (mec A hA).center := hp_data.2.symm
  rw [h1, hc_eq, dist_left_midpoint, Real.norm_two]
  ring

/- ### Main theorem -/


theorem solution
    {A : Finset ℝ²} (hA : A.Nonempty)
    (hncol : ¬ Collinear ℝ (A : Set ℝ²)) :
    (∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧
        dist p (mec A hA).center = (mec A hA).radius ∧
        dist q (mec A hA).center = (mec A hA).radius ∧
        (mec A hA).center = midpoint ℝ p q ∧
        (mec A hA).radius = dist p q / 2)
      ∨ 3 ≤ (A.filter (fun p => dist p (mec A hA).center = (mec A hA).radius)).card := by
  classical
  set M := mec A hA with hM_def
  set B := boundary A hA with hB_def
  -- Note B = A.filter (...), same as the right-disjunct.
  have hB_unfold : B = A.filter (fun p => dist p M.center = M.radius) := rfl
  -- Case split on B.card.
  by_cases h_card_ge_three : 3 ≤ B.card
  · right; rw [← hB_unfold]; exact h_card_ge_three
  -- B.card ≤ 2.  card ≥ 1 (always), card ≠ 1 (variational).
  left
  push_neg at h_card_ge_three
  have h_card_lt_three : B.card < 3 := h_card_ge_three
  have h_card_pos : 1 ≤ B.card := Problem97.MEC.boundary_card_pos A hA
  have h_card_ne_one : B.card ≠ 1 := Problem97.MEC.not_card_boundary_eq_one hA hncol
  -- So B.card = 2.
  have h_card_eq_two : B.card = 2 := by omega
  rw [Finset.card_eq_two] at h_card_eq_two
  obtain ⟨p, q, hpq_ne, hB_eq⟩ := h_card_eq_two
  -- B = {p, q}.  p, q ∈ boundary.
  have hp_bdry : p ∈ B := by rw [hB_eq]; exact Finset.mem_insert_self _ _
  have hq_bdry : q ∈ B := by
    rw [hB_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h_only_pq : ∀ x ∈ B, x = p ∨ x = q := by
    intro x hx
    rw [hB_eq, Finset.mem_insert, Finset.mem_singleton] at hx
    exact hx
  -- p, q in A.
  have hp_mem : p ∈ A := ((mem_boundary_iff hA).1 hp_bdry).1
  have hq_mem : q ∈ A := ((mem_boundary_iff hA).1 hq_bdry).1
  have hp_dist : dist p M.center = M.radius := ((mem_boundary_iff hA).1 hp_bdry).2
  have hq_dist : dist q M.center = M.radius := ((mem_boundary_iff hA).1 hq_bdry).2
  -- Apply diameter-case lemma.
  have hc_eq :=
    Problem97.MEC.diameter_case_of_card_boundary_eq_two hA hncol hp_bdry hq_bdry hpq_ne h_only_pq
  have hr_eq :=
    Problem97.MEC.radius_eq_half_dist_of_card_boundary_eq_two hA hncol hp_bdry hq_bdry hpq_ne h_only_pq
  exact ⟨p, hp_mem, q, hq_mem, hpq_ne, hp_dist, hq_dist, hc_eq, hr_eq⟩

end Erdos9796CountingFragment_Erdos9796Proof_P97_MEC_Boundary
