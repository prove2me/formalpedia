-- Prove2me | solution 1 for Problem97.MEC.arc_partition_count_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:55.198778+00:00
-- url     : https://prove2.me/submissions/81033cab-eaa5-45e5-9da6-76ec3e4df0a9

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.ArcPartitionCount:17995:32990. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_Moser_Triangle
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Hull
import Theorems.Thm_Problem97_collinear_of_signedArea2_eq_zero

section Erdos9796CountingFragment_Erdos9796Proof_P97_ArcPartitionCount

open Problem97 Problem97.MEC

/- Fragment from Erdos9796Proof.P97.ArcPartitionCount; source SHA-256 572f8bf0c2c29f5db2afe9ef8dfa5a179cea8a5fabea8a5ecd5dcd76c653030d -/


/-!
# Arc-partition count for the MEC cap partition (Problem 97)

`Problem97.MEC.arc_partition_count_eq_one` discharges the
`hAGenericCapCount` hypothesis of
`Problem97.MEC.cap_partition_from_moser_circumscribed`.

For a convex-independent finite point set `A ⊆ ℝ²` and a Moser triangle
`{v1, v2, v3}` produced by the Sylvester dichotomy on its
circumscribed branch (the three Moser vertices are pairwise distinct
and on the MEC boundary), every non-Moser `A`-vertex lies on *exactly
one* of the three closed caps `Ci`, where each `Ci` is defined by
the `OnArcOpposite` chord-separation predicate.

## Proof outline

For each non-Moser `v ∈ A`, we use the barycentric decomposition with
base point `v3`:
`v - v3 = a (v1 - v3) + b (v2 - v3)`.
Then by an affine ring identity:
* `signedArea2 v v2 v3 = a · Δ`
* `signedArea2 v v3 v1 = b · Δ`
* `signedArea2 v v1 v2 = (1 - a - b) · Δ`
where `Δ = signedArea2 v1 v2 v3`.

Hence the three `OnArcOpposite` indicators reduce to:
* `i₁ = 1 ↔ a · Δ² ≤ 0 ↔ a ≤ 0`
* `i₂ = 1 ↔ b · Δ² ≤ 0 ↔ b ≤ 0`
* `i₃ = 1 ↔ (1 - a - b) · Δ² ≤ 0 ↔ a + b ≥ 1`

**Step 1**: Show `Δ ≠ 0` (non-degenerate triangle). If `Δ = 0`, the
three Moser vertices are collinear; the Wbtw-trichotomy + ConvexIndep
gives a contradiction.

**Step 2**: For non-Moser `v ∈ A`, show `a, b, 1-a-b` are all
non-zero (i.e., `v` is not on any chord). If, e.g., `a = 0`, then
`signedArea2 v v2 v3 = 0`, so `v, v2, v3` are collinear. Combined
with `v ∈ A`, MEC enclosing, `v2, v3` on MEC boundary, we deduce
`v ∈ segment v2 v3`. By ConvexIndep, contradiction.

**Step 3**: Rule out `a < 0 ∧ b < 0` (two-negative corner at `v3`).
Use the supporting-hyperplane argument: `v3` on the MEC boundary
means the tangent at `v3` separates the closed disk from the
"outside-the-tangent" half-plane. The corner region {a, b < 0} lies
strictly outside the tangent. So `v` in the disk cannot have both
`a, b < 0`. Symmetric arguments at `v1, v2` rule out the other two
two-negative cases.

**Step 4**: Rule out `a, b, 1-a-b` all having the same sign as `−Δ²`
— impossible since they sum to 1.

**Step 5**: Therefore exactly one indicator is 1.

## Main declarations

* `Problem97.MEC.arc_partition_count_eq_one` — the cap-count
  identity, dispatched to `hAGenericCapCount` downstream.
-/

open scoped EuclideanGeometry
open Finset Classical




/- ### Barycentric/area algebraic identities -/

/-- **Affine decomposition lemma**: if `v - v3 = a • (v1 - v3) + b • (v2 - v3)`
then `signedArea2 v v2 v3 = a · signedArea2 v1 v2 v3`. -/
 lemma Problem97.MEC.signedArea2_bary_v2v3
    (v v1 v2 v3 : ℝ²) (a b : ℝ)
    (hv : v - v3 = a • (v1 - v3) + b • (v2 - v3)) :
    signedArea2 v v2 v3 = a * signedArea2 v1 v2 v3 := by
  -- Coordinate expansion.
  -- v 0 = v3 0 + a (v1 0 - v3 0) + b (v2 0 - v3 0)
  -- v 1 = v3 1 + a (v1 1 - v3 1) + b (v2 1 - v3 1)
  have hv0 : v 0 = v3 0 + a * (v1 0 - v3 0) + b * (v2 0 - v3 0) := by
    have h : (v - v3) 0 = (a • (v1 - v3) + b • (v2 - v3)) 0 := by rw [hv]
    simp [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
    linarith
  have hv1 : v 1 = v3 1 + a * (v1 1 - v3 1) + b * (v2 1 - v3 1) := by
    have h : (v - v3) 1 = (a • (v1 - v3) + b • (v2 - v3)) 1 := by rw [hv]
    simp [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
    linarith
  unfold signedArea2
  rw [hv0, hv1]
  ring

/-- **Affine decomposition lemma**: if `v - v3 = a • (v1 - v3) + b • (v2 - v3)`
then `signedArea2 v v3 v1 = b · signedArea2 v1 v2 v3`. -/
 lemma Problem97.MEC.signedArea2_bary_v3v1
    (v v1 v2 v3 : ℝ²) (a b : ℝ)
    (hv : v - v3 = a • (v1 - v3) + b • (v2 - v3)) :
    signedArea2 v v3 v1 = b * signedArea2 v1 v2 v3 := by
  have hv0 : v 0 = v3 0 + a * (v1 0 - v3 0) + b * (v2 0 - v3 0) := by
    have h : (v - v3) 0 = (a • (v1 - v3) + b • (v2 - v3)) 0 := by rw [hv]
    simp [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
    linarith
  have hv1 : v 1 = v3 1 + a * (v1 1 - v3 1) + b * (v2 1 - v3 1) := by
    have h : (v - v3) 1 = (a • (v1 - v3) + b • (v2 - v3)) 1 := by rw [hv]
    simp [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
    linarith
  unfold signedArea2
  rw [hv0, hv1]
  ring

/-- **Affine decomposition lemma**: if `v - v3 = a • (v1 - v3) + b • (v2 - v3)`
then `signedArea2 v v1 v2 = (1 - a - b) · signedArea2 v1 v2 v3`. -/
 lemma Problem97.MEC.signedArea2_bary_v1v2
    (v v1 v2 v3 : ℝ²) (a b : ℝ)
    (hv : v - v3 = a • (v1 - v3) + b • (v2 - v3)) :
    signedArea2 v v1 v2 = (1 - a - b) * signedArea2 v1 v2 v3 := by
  have hv0 : v 0 = v3 0 + a * (v1 0 - v3 0) + b * (v2 0 - v3 0) := by
    have h : (v - v3) 0 = (a • (v1 - v3) + b • (v2 - v3)) 0 := by rw [hv]
    simp [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
    linarith
  have hv1 : v 1 = v3 1 + a * (v1 1 - v3 1) + b * (v2 1 - v3 1) := by
    have h : (v - v3) 1 = (a • (v1 - v3) + b • (v2 - v3)) 1 := by rw [hv]
    simp [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
    linarith
  unfold signedArea2
  rw [hv0, hv1]
  ring

/-- **Existence of barycentric decomposition** (in ℝ²): if
`signedArea2 v1 v2 v3 ≠ 0`, then any `v ∈ ℝ²` admits a decomposition
`v - v3 = a • (v1 - v3) + b • (v2 - v3)`. -/
 lemma Problem97.MEC.exists_bary_decomp
    (v v1 v2 v3 : ℝ²) (hΔ : signedArea2 v1 v2 v3 ≠ 0) :
    ∃ a b : ℝ, v - v3 = a • (v1 - v3) + b • (v2 - v3) := by
  -- Work entirely in the cross-product form. The 2x2 system
  --   a*(v1 0 - v3 0) + b*(v2 0 - v3 0) = v 0 - v3 0
  --   a*(v1 1 - v3 1) + b*(v2 1 - v3 1) = v 1 - v3 1
  -- has determinant D = (v1 0 - v3 0)*(v2 1 - v3 1) - (v2 0 - v3 0)*(v1 1 - v3 1).
  -- Cramer:
  --   a = ((v 0 - v3 0)*(v2 1 - v3 1) - (v2 0 - v3 0)*(v 1 - v3 1)) / D
  --   b = ((v1 0 - v3 0)*(v 1 - v3 1) - (v 0 - v3 0)*(v1 1 - v3 1)) / D
  -- To make `field_simp` work, we package the relevant nonzero hypothesis
  -- in the exact unfolded form, AND avoid `set` of D (so the indices in
  -- the goal don't get out of sync with the hypothesis).
  set D := (v1 0 - v3 0) * (v2 1 - v3 1) - (v2 0 - v3 0) * (v1 1 - v3 1) with hD_def
  have hD_ne : D ≠ 0 := by
    intro h
    apply hΔ
    unfold signedArea2
    change (v2 0 - v1 0) * (v3 1 - v1 1) - (v3 0 - v1 0) * (v2 1 - v1 1) = 0
    have : D = (v1 0 - v3 0) * (v2 1 - v3 1) - (v2 0 - v3 0) * (v1 1 - v3 1) := hD_def
    nlinarith [h, this]
  refine ⟨((v 0 - v3 0) * (v2 1 - v3 1) - (v2 0 - v3 0) * (v 1 - v3 1)) / D,
         ((v1 0 - v3 0) * (v 1 - v3 1) - (v 0 - v3 0) * (v1 1 - v3 1)) / D, ?_⟩
  apply PiLp.ext
  intro i
  match i with
  | 0 =>
    change v 0 - v3 0 = _
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    change v 0 - v3 0 = _
    field_simp
    ring
  | 1 =>
    change v 1 - v3 1 = _
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    change v 1 - v3 1 = _
    field_simp
    ring

/- ### Inner-product / sphere identities -/

/-- **Sphere identity**: if `vi` and `vk` lie on a sphere of squared
radius `r²` centered at `O`, then `⟨vi - vk, vk - O⟩ = -‖vi - vk‖² / 2`. -/
 lemma Problem97.MEC.inner_sub_eq_of_sphere
    (vi vk O : ℝ²) (h_eq : ‖vi - O‖ = ‖vk - O‖) :
    inner ℝ (vi - vk) (vk - O) = - ‖vi - vk‖^2 / 2 := by
  -- ‖vi - vk‖² = ‖(vi - O) - (vk - O)‖² = ‖vi - O‖² + ‖vk - O‖² - 2⟨vi - O, vk - O⟩
  -- 2⟨vi - O, vk - O⟩ = 2‖vk - O‖² - ‖vi - vk‖² (using ‖vi-O‖ = ‖vk-O‖)
  -- ⟨vi - vk, vk - O⟩ = ⟨vi - O, vk - O⟩ - ⟨vk - O, vk - O⟩
  --                    = ⟨vi - O, vk - O⟩ - ‖vk - O‖²
  --                    = ‖vk - O‖² - ‖vi - vk‖²/2 - ‖vk - O‖² = -‖vi - vk‖²/2
  have h_subst : vi - vk = (vi - O) - (vk - O) := by abel
  rw [h_subst, inner_sub_left]
  have hself : inner ℝ (vk - O) (vk - O) = ‖vk - O‖^2 :=
    real_inner_self_eq_norm_sq _
  rw [hself]
  -- Now: inner (vi - O) (vk - O) = (‖vi - O‖² + ‖vk - O‖² - ‖(vi - O) - (vk - O)‖²) / 2
  -- using ‖a - b‖² = ‖a‖² + ‖b‖² - 2⟨a, b⟩.
  have hkey : ‖(vi - O) - (vk - O)‖^2 = ‖vi - O‖^2 + ‖vk - O‖^2
      - 2 * inner ℝ (vi - O) (vk - O) := by
    rw [@norm_sub_pow_two_real ℝ² _ _ (vi - O) (vk - O)]
    ring
  -- After `rw [h_subst]` at top, the goal's `‖vi - vk‖²` already became
  -- `‖(vi - O) - (vk - O)‖²`, so we don't need to rewrite again.
  rw [hkey, h_eq]
  ring

/-- **Disk inequality** at boundary point `vk`: if `‖v - O‖ ≤ ‖vk - O‖`,
then `⟨v - vk, vk - O⟩ ≤ -‖v - vk‖² / 2 ≤ 0`. -/
 lemma Problem97.MEC.inner_disk_at_boundary
    (v vk O : ℝ²) (h_disk : ‖v - O‖ ≤ ‖vk - O‖) :
    inner ℝ (v - vk) (vk - O) ≤ - ‖v - vk‖^2 / 2 := by
  -- ‖v - O‖² = ‖(v - vk) + (vk - O)‖² = ‖v - vk‖² + 2⟨v - vk, vk - O⟩ + ‖vk - O‖²
  -- ‖v - O‖² ≤ ‖vk - O‖² ⟹ ‖v - vk‖² + 2⟨v - vk, vk - O⟩ ≤ 0
  -- ⟹ ⟨v - vk, vk - O⟩ ≤ -‖v - vk‖²/2.
  have hv_O_sq : ‖v - O‖^2 ≤ ‖vk - O‖^2 := by
    have h1 : (0 : ℝ) ≤ ‖v - O‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ ‖vk - O‖ := norm_nonneg _
    nlinarith
  have h_subst : v - O = (v - vk) + (vk - O) := by abel
  have hkey : ‖(v - vk) + (vk - O)‖^2 = ‖v - vk‖^2 + ‖vk - O‖^2
      + 2 * inner ℝ (v - vk) (vk - O) := by
    rw [@norm_add_pow_two_real ℝ² _ _ (v - vk) (vk - O)]
    ring
  have hvO_sq : ‖v - O‖^2 = ‖(v - vk) + (vk - O)‖^2 := by rw [← h_subst]
  rw [hvO_sq] at hv_O_sq
  linarith

/- ### Corner exclusion -/

/-- **Corner exclusion at `vk`**: if `v1, v2, vk` lie on a sphere centered
at `O`, `v` is in the closed disk, and `v - vk = a • (v1 - vk) + b • (v2 - vk)`
with `a < 0` and `b < 0` (strict), then we reach a contradiction.

Geometrically, the "corner past `vk`" region opens away from the disk,
and the tangent line at `vk` separates it from the closed disk. -/
 lemma Problem97.MEC.corner_exclusion
    (v1 v2 vk v O : ℝ²) (a b : ℝ)
    (h1_sph : ‖v1 - O‖ = ‖vk - O‖)
    (h2_sph : ‖v2 - O‖ = ‖vk - O‖)
    (h_disk : ‖v - O‖ ≤ ‖vk - O‖)
    (h_decomp : v - vk = a • (v1 - vk) + b • (v2 - vk))
    (h_v_ne_vk : v ≠ vk)
    (ha_neg : a < 0) (hb_neg : b < 0) : False := by
  -- ⟨v - vk, vk - O⟩ ≤ -‖v - vk‖²/2 < 0 (disk constraint, v ≠ vk).
  have h_disk_inner : inner ℝ (v - vk) (vk - O) ≤ - ‖v - vk‖^2 / 2 :=
    Problem97.MEC.inner_disk_at_boundary v vk O h_disk
  have h_v_vk_ne : ‖v - vk‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; intro h
    exact h_v_ne_vk (sub_eq_zero.mp h)
  have h_vvk_sq_pos : 0 < ‖v - vk‖^2 := by
    have hnn : 0 ≤ ‖v - vk‖ := norm_nonneg _
    have hne : ‖v - vk‖ ≠ 0 := h_v_vk_ne
    positivity
  -- ⟨v - vk, vk - O⟩ from decomposition = a · ⟨v1 - vk, vk - O⟩ + b · ⟨v2 - vk, vk - O⟩.
  have h_inner_decomp :
      inner ℝ (v - vk) (vk - O) =
        a * inner ℝ (v1 - vk) (vk - O) + b * inner ℝ (v2 - vk) (vk - O) := by
    rw [h_decomp, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  -- Each ⟨vi - vk, vk - O⟩ = -‖vi - vk‖²/2 (sphere identity).
  have h_inner_1 : inner ℝ (v1 - vk) (vk - O) = - ‖v1 - vk‖^2 / 2 :=
    Problem97.MEC.inner_sub_eq_of_sphere v1 vk O h1_sph
  have h_inner_2 : inner ℝ (v2 - vk) (vk - O) = - ‖v2 - vk‖^2 / 2 :=
    Problem97.MEC.inner_sub_eq_of_sphere v2 vk O h2_sph
  -- Substitute.
  have h_inner_eq :
      inner ℝ (v - vk) (vk - O) =
        - a * ‖v1 - vk‖^2 / 2 + - b * ‖v2 - vk‖^2 / 2 := by
    rw [h_inner_decomp, h_inner_1, h_inner_2]; ring
  -- Since a < 0 and b < 0, both -a and -b are positive, so the RHS is ≥ 0.
  -- Actually it could be 0 only if both norms are 0 (v1 = vk and v2 = vk).
  -- In general, since at least one of a, b is nonzero and the corresponding norm is positive
  -- (assuming v1 ≠ vk and v2 ≠ vk), the RHS is > 0.
  -- But we have a < 0 and b < 0 BOTH strict.
  -- If ‖v1 - vk‖ = 0 then v1 = vk; then a • 0 = 0, so v - vk = b • (v2 - vk).
  -- Combined with v ≠ vk and b < 0, this means v2 ≠ vk and ⟨v - vk, vk - O⟩ = -b ‖v2 - vk‖²/2 > 0.
  -- Similarly if v2 = vk.
  -- General argument: in the worst case both v1 = vk and v2 = vk, but then v - vk = 0, so v = vk.
  -- Let's handle it case by case.
  by_cases hv1eq : v1 = vk
  · -- v1 = vk: v1 - vk = 0, so the a-term vanishes.
    have h1_zero : v1 - vk = 0 := sub_eq_zero.mpr hv1eq
    have h_eff : v - vk = b • (v2 - vk) := by
      rw [h_decomp, h1_zero, smul_zero, zero_add]
    -- v ≠ vk implies v - vk ≠ 0 implies b • (v2 - vk) ≠ 0 implies v2 ≠ vk.
    have hv2_ne : v2 ≠ vk := by
      intro h
      apply h_v_ne_vk
      have h2_zero : v2 - vk = 0 := sub_eq_zero.mpr h
      have : v - vk = 0 := by rw [h_eff, h2_zero, smul_zero]
      exact sub_eq_zero.mp this
    have h2_norm_pos : 0 < ‖v2 - vk‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv2_ne)
    have h2_norm_sq_pos : 0 < ‖v2 - vk‖^2 := by positivity
    -- ⟨v - vk, vk - O⟩ = b · ⟨v2 - vk, vk - O⟩ = b · (-‖v2 - vk‖²/2) = -b‖v2-vk‖²/2 > 0
    have h_inner_pos : inner ℝ (v - vk) (vk - O) > 0 := by
      rw [h_inner_eq]
      rw [show v1 - vk = (0 : ℝ²) from h1_zero, norm_zero]
      have : -b > 0 := by linarith
      nlinarith
    linarith
  · -- v1 ≠ vk: v1 - vk ≠ 0.
    have h1_norm_pos : 0 < ‖v1 - vk‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv1eq)
    have h1_norm_sq_pos : 0 < ‖v1 - vk‖^2 := by positivity
    -- ⟨v - vk, vk - O⟩ = -a‖v1-vk‖²/2 + -b‖v2-vk‖²/2. Both terms ≥ 0; first > 0.
    have h_inner_pos : inner ℝ (v - vk) (vk - O) > 0 := by
      rw [h_inner_eq]
      have h2_norm_sq_nn : 0 ≤ ‖v2 - vk‖^2 := sq_nonneg _
      have hna_pos : 0 < -a := by linarith
      have hnb_pos : 0 < -b := by linarith
      nlinarith
    linarith

/- ### Non-degeneracy of the Moser triangle under ConvexIndep -/

/-- **Moser nondegeneracy**: pairwise-distinct vertices in a
convex-independent set have nonzero signed area. Reuses
`Problem97.collinear_of_signedArea2_eq_zero` from MoserNonDeg, then
applies Wbtw-trichotomy + ConvexIndep. -/
 lemma Problem97.MEC.signedArea2_ne_zero_of_convexIndep
    {A : Finset ℝ²} (hA : ConvexIndep A)
    {v1 v2 v3 : ℝ²} (h1A : v1 ∈ A) (h2A : v2 ∈ A) (h3A : v3 ∈ A)
    (h12 : v1 ≠ v2) (h23 : v2 ≠ v3) (h13 : v1 ≠ v3) :
    signedArea2 v1 v2 v3 ≠ 0 := by
  intro hΔ
  -- signedArea2 = 0 ⟹ Collinear {v1, v2, v3} via existing lemma.
  have hcol : Collinear ℝ ({v1, v2, v3} : Set ℝ²) :=
    Problem97.collinear_of_signedArea2_eq_zero v1 v2 v3 hΔ
  -- Now use Wbtw trichotomy.
  rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
  · -- Wbtw v1 v2 v3: v2 ∈ segment v1 v3 ⊆ convexHull (A \ {v2}).
    apply hA v2 h2A
    have hseg : v2 ∈ segment ℝ v1 v3 := hw.mem_segment
    rw [← convexHull_pair] at hseg
    have hsub : ({v1, v3} : Set ℝ²) ⊆ ((A : Set ℝ²) \ {v2}) := by
      intro x hx
      rcases hx with rfl | hx
      · -- x = v1, need v1 ∉ {v2}, i.e., ¬ (v1 = v2). Use h12 : v1 ≠ v2.
        refine ⟨h1A, ?_⟩
        simp only [Set.mem_singleton_iff]
        exact h12
      rcases hx with rfl
      -- x = v3, need v3 ∉ {v2}, i.e., ¬ (v3 = v2). Use h23.symm : v3 ≠ v2.
      refine ⟨h3A, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact h23.symm
    exact convexHull_mono hsub hseg
  · -- Wbtw v2 v3 v1: v3 ∈ segment v2 v1 ⊆ convexHull (A \ {v3}).
    apply hA v3 h3A
    have hseg : v3 ∈ segment ℝ v2 v1 := hw.mem_segment
    rw [← convexHull_pair] at hseg
    have hsub : ({v2, v1} : Set ℝ²) ⊆ ((A : Set ℝ²) \ {v3}) := by
      intro x hx
      rcases hx with rfl | hx
      · -- x = v2, need v2 ∉ {v3}, i.e., ¬ (v2 = v3). Use h23 : v2 ≠ v3.
        refine ⟨h2A, ?_⟩
        simp only [Set.mem_singleton_iff]
        exact h23
      rcases hx with rfl
      -- x = v1, need v1 ∉ {v3}, i.e., ¬ (v1 = v3). Use h13 : v1 ≠ v3.
      refine ⟨h1A, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact h13
    exact convexHull_mono hsub hseg
  · -- Wbtw v3 v1 v2: v1 ∈ segment v3 v2 ⊆ convexHull (A \ {v1}).
    apply hA v1 h1A
    have hseg : v1 ∈ segment ℝ v3 v2 := hw.mem_segment
    rw [← convexHull_pair] at hseg
    have hsub : ({v3, v2} : Set ℝ²) ⊆ ((A : Set ℝ²) \ {v1}) := by
      intro x hx
      rcases hx with rfl | hx
      · -- x = v3, need v3 ∉ {v1}, i.e., ¬ (v3 = v1). Use h13.symm : v3 ≠ v1.
        refine ⟨h3A, ?_⟩
        simp only [Set.mem_singleton_iff]
        exact h13.symm
      rcases hx with rfl
      -- x = v2, need v2 ∉ {v1}, i.e., ¬ (v2 = v1). Use h12.symm.
      refine ⟨h2A, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact h12.symm
    exact convexHull_mono hsub hseg

/- ### Chord exclusion: non-Moser A-vertex not on any chord -/

/-- **Chord exclusion at edge (v_j, v_k)**: under ConvexIndep, a
non-Moser A-vertex `v` cannot have `signedArea2 v vj vk = 0` (i.e.,
cannot be collinear with two distinct Moser vertices `vj, vk`).

The proof: if `signedArea2 v vj vk = 0`, then `{v, vj, vk}` is
collinear. By Wbtw-trichotomy, one of the three is between the others;
in any case, the betweenness contradicts ConvexIndep (the in-between
point lies in convexHull of the other two, which are in `A \ {it}`). -/
 lemma Problem97.MEC.not_on_chord
    {A : Finset ℝ²} (hA : ConvexIndep A)
    {v vj vk : ℝ²} (hvA : v ∈ A) (hjA : vj ∈ A) (hkA : vk ∈ A)
    (hjk : vj ≠ vk) (hvj : v ≠ vj) (hvk : v ≠ vk)
    (h_area : signedArea2 v vj vk = 0) : False :=
  Problem97.MEC.signedArea2_ne_zero_of_convexIndep hA hvA hjA hkA hvj hjk hvk h_area

/- ### Main theorem -/

open Classical in

theorem solution
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    (hConv : Problem97.ConvexIndep A)
    (MT : Problem97.MEC.MoserTriangle A hA hncol)
    (hCircumscribed : ∃ h12 h23 h13,
      MT.case_split = Or.inl ⟨h12, h23, h13⟩) :
    ∀ v ∈ A, v ≠ MT.v1 → v ≠ MT.v2 → v ≠ MT.v3 →
      (if Problem97.OnArcOpposite MT.v1 MT.v2 MT.v3 v then 1 else 0)
        + (if Problem97.OnArcOpposite MT.v2 MT.v3 MT.v1 v then 1 else 0)
        + (if Problem97.OnArcOpposite MT.v3 MT.v1 MT.v2 v then 1 else 0)
        = 1 := by
  intro v hvA hv1 hv2 hv3
  -- Unpack the circumscribed case: v1, v2, v3 pairwise distinct.
  obtain ⟨h12_ne, h23_ne, h13_ne, _⟩ := hCircumscribed
  -- Renaming for clarity.
  set V1 := MT.v1 with hV1
  set V2 := MT.v2 with hV2
  set V3 := MT.v3 with hV3
  set Δ := signedArea2 V1 V2 V3 with hΔ
  -- Step 1: Δ ≠ 0 (Moser nondegeneracy).
  have hΔ_ne : Δ ≠ 0 := Problem97.MEC.signedArea2_ne_zero_of_convexIndep hConv
    MT.v1_mem MT.v2_mem MT.v3_mem h12_ne h23_ne h13_ne
  -- Step 2: barycentric decomposition v - V3 = a • (V1 - V3) + b • (V2 - V3).
  obtain ⟨a, b, h_decomp⟩ := Problem97.MEC.exists_bary_decomp v V1 V2 V3 hΔ_ne
  -- Step 3: translate the three signed areas.
  have h_α : signedArea2 v V2 V3 = a * Δ := Problem97.MEC.signedArea2_bary_v2v3 v V1 V2 V3 a b h_decomp
  have h_β : signedArea2 v V3 V1 = b * Δ := Problem97.MEC.signedArea2_bary_v3v1 v V1 V2 V3 a b h_decomp
  have h_γ : signedArea2 v V1 V2 = (1 - a - b) * Δ := Problem97.MEC.signedArea2_bary_v1v2 v V1 V2 V3 a b h_decomp
  -- Step 4: cyclic identities. Use `change` to expose `Δ` definitionally.
  have hcyc1 : signedArea2 V2 V3 V1 = Δ := by
    change signedArea2 V2 V3 V1 = signedArea2 V1 V2 V3
    unfold signedArea2; ring
  have hcyc2 : signedArea2 V3 V1 V2 = Δ := by
    change signedArea2 V3 V1 V2 = signedArea2 V1 V2 V3
    unfold signedArea2; ring
  -- Step 5: translate the OnArcOpposite predicates.
  -- After unfold + rw, the goal closes directly (no `constructor` needed).
  have h_i1 : Problem97.OnArcOpposite V1 V2 V3 v ↔ a * Δ * Δ ≤ 0 := by
    unfold Problem97.OnArcOpposite
    rw [h_α]
  have h_i2 : Problem97.OnArcOpposite V2 V3 V1 v ↔ b * Δ * Δ ≤ 0 := by
    unfold Problem97.OnArcOpposite
    rw [h_β, hcyc1]
  have h_i3 : Problem97.OnArcOpposite V3 V1 V2 v ↔ (1 - a - b) * Δ * Δ ≤ 0 := by
    unfold Problem97.OnArcOpposite
    rw [h_γ, hcyc2]
  -- Step 6: Δ² > 0.
  have hΔsq_pos : 0 < Δ * Δ := by
    have : Δ * Δ = Δ^2 := by ring
    rw [this]
    have : Δ ≠ 0 := hΔ_ne
    positivity
  -- Step 7: indicators become sign tests.
  -- a · Δ² ≤ 0 ↔ a ≤ 0.
  have h_a_iff : a * Δ * Δ ≤ 0 ↔ a ≤ 0 := by
    rw [mul_assoc]
    constructor
    · intro h
      rcases le_or_gt a 0 with h' | h'
      · exact h'
      · exfalso
        have : 0 < a * (Δ * Δ) := mul_pos h' hΔsq_pos
        linarith
    · intro h
      have h' : a * (Δ * Δ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (le_of_lt hΔsq_pos)
      linarith
  have h_b_iff : b * Δ * Δ ≤ 0 ↔ b ≤ 0 := by
    rw [mul_assoc]
    constructor
    · intro h
      rcases le_or_gt b 0 with h' | h'
      · exact h'
      · exfalso
        have : 0 < b * (Δ * Δ) := mul_pos h' hΔsq_pos
        linarith
    · intro h
      have h' : b * (Δ * Δ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (le_of_lt hΔsq_pos)
      linarith
  have h_c_iff : (1 - a - b) * Δ * Δ ≤ 0 ↔ (1 - a - b) ≤ 0 := by
    rw [mul_assoc]
    constructor
    · intro h
      rcases le_or_gt (1 - a - b) 0 with h' | h'
      · exact h'
      · exfalso
        have : 0 < (1 - a - b) * (Δ * Δ) := mul_pos h' hΔsq_pos
        linarith
    · intro h
      have h' : (1 - a - b) * (Δ * Δ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (le_of_lt hΔsq_pos)
      linarith
  -- Step 8: Chord exclusion. Each indicator is actually a strict inequality (chord exclusion).
  -- We need to know a ≠ 0, b ≠ 0, 1 - a - b ≠ 0.
  have h_a_ne : a ≠ 0 := by
    intro ha
    -- a = 0 ⟹ α = signedArea2 v V2 V3 = 0 ⟹ chord exclusion.
    have : signedArea2 v V2 V3 = 0 := by rw [h_α, ha]; ring
    exact Problem97.MEC.not_on_chord hConv hvA MT.v2_mem MT.v3_mem h23_ne hv2 hv3 this
  have h_b_ne : b ≠ 0 := by
    intro hb
    have h_area_β : signedArea2 v V3 V1 = 0 := by rw [h_β, hb]; ring
    -- signedArea2 v V3 V1 = 0 ⟹ collinear v, V3, V1.
    exact Problem97.MEC.not_on_chord hConv hvA MT.v3_mem MT.v1_mem (Ne.symm h13_ne) hv3 hv1 h_area_β
  have h_c_ne : (1 - a - b) ≠ 0 := by
    intro hc
    have h_area_γ : signedArea2 v V1 V2 = 0 := by rw [h_γ, hc]; ring
    exact Problem97.MEC.not_on_chord hConv hvA MT.v1_mem MT.v2_mem h12_ne hv1 hv2 h_area_γ
  -- Step 9: Disk constraint and corner exclusion.
  -- v in closed disk: ‖v - O‖ ≤ r where O = MEC center, r = MEC radius.
  set O := (mec A hA).center with hO
  set r := (mec A hA).radius with hr
  have hv_disk : dist v O ≤ r := (mec A hA).enclosing v hvA
  have h_v1_bdry : dist V1 O = r := MT.v1_boundary
  have h_v2_bdry : dist V2 O = r := MT.v2_boundary
  have h_v3_bdry : dist V3 O = r := MT.v3_boundary
  -- Convert distance to norm for the corner_exclusion lemma.
  have h_V1_norm_r : ‖V1 - O‖ = r := by
    rw [show ‖V1 - O‖ = dist V1 O from (dist_eq_norm _ _).symm]; exact h_v1_bdry
  have h_V2_norm_r : ‖V2 - O‖ = r := by
    rw [show ‖V2 - O‖ = dist V2 O from (dist_eq_norm _ _).symm]; exact h_v2_bdry
  have h_V3_norm_r : ‖V3 - O‖ = r := by
    rw [show ‖V3 - O‖ = dist V3 O from (dist_eq_norm _ _).symm]; exact h_v3_bdry
  have hv_norm_r : ‖v - O‖ ≤ r := by
    rw [show ‖v - O‖ = dist v O from (dist_eq_norm _ _).symm]; exact hv_disk
  -- Pairwise sphere equalities and disk inequalities for each base vertex.
  have h_V12_eq_V3 : ‖V1 - O‖ = ‖V3 - O‖ := by rw [h_V1_norm_r, h_V3_norm_r]
  have h_V22_eq_V3 : ‖V2 - O‖ = ‖V3 - O‖ := by rw [h_V2_norm_r, h_V3_norm_r]
  have hv_le_V3 : ‖v - O‖ ≤ ‖V3 - O‖ := by rw [h_V3_norm_r]; exact hv_norm_r
  have h_V23_eq_V1 : ‖V2 - O‖ = ‖V1 - O‖ := by rw [h_V2_norm_r, h_V1_norm_r]
  have h_V33_eq_V1 : ‖V3 - O‖ = ‖V1 - O‖ := by rw [h_V3_norm_r, h_V1_norm_r]
  have hv_le_V1 : ‖v - O‖ ≤ ‖V1 - O‖ := by rw [h_V1_norm_r]; exact hv_norm_r
  have h_V31_eq_V2 : ‖V3 - O‖ = ‖V2 - O‖ := by rw [h_V3_norm_r, h_V2_norm_r]
  have h_V11_eq_V2 : ‖V1 - O‖ = ‖V2 - O‖ := by rw [h_V1_norm_r, h_V2_norm_r]
  have hv_le_V2 : ‖v - O‖ ≤ ‖V2 - O‖ := by rw [h_V2_norm_r]; exact hv_norm_r
  -- Corner at V3: NOT (a < 0 ∧ b < 0).
  have h_corner_v3 : ¬ (a < 0 ∧ b < 0) := by
    intro ⟨ha_neg, hb_neg⟩
    exact Problem97.MEC.corner_exclusion V1 V2 V3 v O a b h_V12_eq_V3 h_V22_eq_V3 hv_le_V3
      h_decomp hv3 ha_neg hb_neg
  -- For corner at V1 and V2, derive new decompositions.
  -- V1-base: v - V1 = a' (V2 - V1) + b' (V3 - V1).
  obtain ⟨a', b', h_decomp_V1⟩ := Problem97.MEC.exists_bary_decomp v V2 V3 V1
    (by rw [show signedArea2 V2 V3 V1 = Δ from hcyc1]; exact hΔ_ne)
  have h_α_V1 : signedArea2 v V3 V1 = a' * signedArea2 V2 V3 V1 :=
    Problem97.MEC.signedArea2_bary_v2v3 v V2 V3 V1 a' b' h_decomp_V1
  have h_β_V1 : signedArea2 v V1 V2 = b' * signedArea2 V2 V3 V1 :=
    Problem97.MEC.signedArea2_bary_v3v1 v V2 V3 V1 a' b' h_decomp_V1
  rw [hcyc1] at h_α_V1 h_β_V1
  have ha'_eq : a' = b := by
    have : a' * Δ = b * Δ := h_α_V1.symm.trans h_β
    exact mul_right_cancel₀ hΔ_ne this
  have hb'_eq : b' = 1 - a - b := by
    have : b' * Δ = (1 - a - b) * Δ := h_β_V1.symm.trans h_γ
    exact mul_right_cancel₀ hΔ_ne this
  have h_corner_v1 : ¬ (b < 0 ∧ (1 - a - b) < 0) := by
    intro ⟨hb_neg, hc_neg⟩
    have ha'_neg : a' < 0 := by rw [ha'_eq]; exact hb_neg
    have hb'_neg : b' < 0 := by rw [hb'_eq]; exact hc_neg
    exact Problem97.MEC.corner_exclusion V2 V3 V1 v O a' b' h_V23_eq_V1 h_V33_eq_V1 hv_le_V1
      h_decomp_V1 hv1 ha'_neg hb'_neg
  -- V2-base: v - V2 = a'' (V3 - V2) + b'' (V1 - V2).
  obtain ⟨a'', b'', h_decomp_V2⟩ := Problem97.MEC.exists_bary_decomp v V3 V1 V2
    (by rw [show signedArea2 V3 V1 V2 = Δ from hcyc2]; exact hΔ_ne)
  have h_α_V2 : signedArea2 v V1 V2 = a'' * signedArea2 V3 V1 V2 :=
    Problem97.MEC.signedArea2_bary_v2v3 v V3 V1 V2 a'' b'' h_decomp_V2
  have h_β_V2 : signedArea2 v V2 V3 = b'' * signedArea2 V3 V1 V2 :=
    Problem97.MEC.signedArea2_bary_v3v1 v V3 V1 V2 a'' b'' h_decomp_V2
  rw [hcyc2] at h_α_V2 h_β_V2
  have ha''_eq : a'' = 1 - a - b := by
    have : a'' * Δ = (1 - a - b) * Δ := h_α_V2.symm.trans h_γ
    exact mul_right_cancel₀ hΔ_ne this
  have hb''_eq : b'' = a := by
    have : b'' * Δ = a * Δ := h_β_V2.symm.trans h_α
    exact mul_right_cancel₀ hΔ_ne this
  have h_corner_v2 : ¬ (a < 0 ∧ (1 - a - b) < 0) := by
    intro ⟨ha_neg, hc_neg⟩
    have ha''_neg : a'' < 0 := by rw [ha''_eq]; exact hc_neg
    have hb''_neg : b'' < 0 := by rw [hb''_eq]; exact ha_neg
    exact Problem97.MEC.corner_exclusion V3 V1 V2 v O a'' b'' h_V31_eq_V2 h_V11_eq_V2 hv_le_V2
      h_decomp_V2 hv2 ha''_neg hb''_neg
  -- Step 10: ConvexIndep ⟹ v ∉ convexHull {V1, V2, V3}, ruling out "all positive" case.
  -- This is the Case A elimination.
  have h_not_inside : ¬ (0 < a ∧ 0 < b ∧ 0 < (1 - a - b)) := by
    intro ⟨ha_pos, hb_pos, hc_pos⟩
    -- v = a V1 + b V2 + (1 - a - b) V3, convex combination of vertices in A \ {v}.
    apply hConv v hvA
    -- Show v ∈ convexHull ({V1, V2, V3} : Set ℝ²) ⊆ convexHull (A \ {v}).
    have hv_in_hull : v ∈ convexHull ℝ ({V1, V2, V3} : Set ℝ²) := by
      -- Use mem_convexHull_of_exists_fintype with a 3-element index.
      refine mem_convexHull_of_exists_fintype (ι := Fin 3)
        (fun i => match i with | 0 => a | 1 => b | 2 => 1 - a - b)
        (fun i => match i with | 0 => V1 | 1 => V2 | 2 => V3)
        ?_ ?_ ?_ ?_
      · intro i; fin_cases i
        · exact le_of_lt ha_pos
        · exact le_of_lt hb_pos
        · exact le_of_lt hc_pos
      · -- simp closes this entirely (a + b + (1 - a - b) = 1)
        simp [Fin.sum_univ_three]
      · intro i; fin_cases i
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · -- Sum of weighted points equals v.
        simp [Fin.sum_univ_three]
        -- a • V1 + b • V2 + (1 - a - b) • V3 = v.
        -- From h_decomp: v - V3 = a • (V1 - V3) + b • (V2 - V3).
        -- So v = a • V1 + b • V2 + (1 - a - b) • V3.
        have h_decomp' : v = a • V1 + b • V2 + (1 - a - b) • V3 := by
          have : v - V3 = a • (V1 - V3) + b • (V2 - V3) := h_decomp
          have : v = a • (V1 - V3) + b • (V2 - V3) + V3 := by
            rw [← this]; abel
          rw [this]
          rw [show (1 - a - b) • V3 = V3 - a • V3 - b • V3 from by
            rw [sub_smul, sub_smul, one_smul]]
          rw [smul_sub, smul_sub]
          abel
        rw [h_decomp']
    -- Now extend to convexHull (A \ {v}).
    have hsub : ({V1, V2, V3} : Set ℝ²) ⊆ ((A : Set ℝ²) \ {v}) := by
      intro x hx
      rcases hx with rfl | hx
      · refine ⟨MT.v1_mem, ?_⟩
        simp only [Set.mem_singleton_iff]; exact (Ne.symm hv1)
      rcases hx with rfl | hx
      · refine ⟨MT.v2_mem, ?_⟩
        simp only [Set.mem_singleton_iff]; exact (Ne.symm hv2)
      rcases hx with rfl
      refine ⟨MT.v3_mem, ?_⟩
      simp only [Set.mem_singleton_iff]; exact (Ne.symm hv3)
    exact convexHull_mono hsub hv_in_hull
  -- Step 11: Determine the sign pattern of (a, b, c=1-a-b).
  -- a + b + c = 1.
  -- By chord exclusion, a, b, c ≠ 0.
  -- By corner exclusions, no two are simultaneously negative.
  -- By "not_inside", they are not all positive.
  -- Combined with chord exclusion (each nonzero), exactly one must be < 0.
  -- Determine which.
  have h_one_neg : (a < 0 ∧ 0 < b ∧ 0 < (1 - a - b))
      ∨ (0 < a ∧ b < 0 ∧ 0 < (1 - a - b))
      ∨ (0 < a ∧ 0 < b ∧ (1 - a - b) < 0) := by
    rcases lt_or_gt_of_ne h_a_ne with ha_neg | ha_pos
    · -- a < 0.
      have hb_pos : 0 < b := by
        rcases lt_or_gt_of_ne h_b_ne with hb_neg | hb_pos
        · exact absurd ⟨ha_neg, hb_neg⟩ h_corner_v3
        · exact hb_pos
      have hc_pos : 0 < (1 - a - b) := by
        rcases lt_or_gt_of_ne h_c_ne with hc_neg | hc_pos
        · exact absurd ⟨ha_neg, hc_neg⟩ h_corner_v2
        · exact hc_pos
      exact Or.inl ⟨ha_neg, hb_pos, hc_pos⟩
    · -- a > 0.
      rcases lt_or_gt_of_ne h_b_ne with hb_neg | hb_pos
      · -- b < 0.
        have hc_pos : 0 < (1 - a - b) := by
          rcases lt_or_gt_of_ne h_c_ne with hc_neg | hc_pos
          · exact absurd ⟨hb_neg, hc_neg⟩ h_corner_v1
          · exact hc_pos
        exact Or.inr (Or.inl ⟨ha_pos, hb_neg, hc_pos⟩)
      · -- b > 0.
        rcases lt_or_gt_of_ne h_c_ne with hc_neg | hc_pos
        · -- c < 0.
          exact Or.inr (Or.inr ⟨ha_pos, hb_pos, hc_neg⟩)
        · -- c > 0: all positive ⟹ inside triangle ⟹ contradicts h_not_inside.
          exact absurd ⟨ha_pos, hb_pos, hc_pos⟩ h_not_inside
  -- Step 12: Compute the sum of indicators in each case.
  -- Indicators evaluate via h_i1, h_i2, h_i3, then to sign tests via h_a_iff/h_b_iff/h_c_iff.
  rcases h_one_neg with ⟨ha_neg, hb_pos, hc_pos⟩ | ⟨ha_pos, hb_neg, hc_pos⟩
    | ⟨ha_pos, hb_pos, hc_neg⟩
  · -- a < 0: i1 = 1, i2 = 0, i3 = 0.
    have hi1 : Problem97.OnArcOpposite V1 V2 V3 v :=
      h_i1.mpr (h_a_iff.mpr (le_of_lt ha_neg))
    have hi2_neg : ¬ Problem97.OnArcOpposite V2 V3 V1 v := by
      intro h; exact absurd (h_b_iff.mp (h_i2.mp h)) (not_le_of_gt hb_pos)
    have hi3_neg : ¬ Problem97.OnArcOpposite V3 V1 V2 v := by
      intro h; exact absurd (h_c_iff.mp (h_i3.mp h)) (not_le_of_gt hc_pos)
    rw [if_pos hi1, if_neg hi2_neg, if_neg hi3_neg]
  · -- b < 0: i1 = 0, i2 = 1, i3 = 0.
    have hi1_neg : ¬ Problem97.OnArcOpposite V1 V2 V3 v := by
      intro h; exact absurd (h_a_iff.mp (h_i1.mp h)) (not_le_of_gt ha_pos)
    have hi2 : Problem97.OnArcOpposite V2 V3 V1 v :=
      h_i2.mpr (h_b_iff.mpr (le_of_lt hb_neg))
    have hi3_neg : ¬ Problem97.OnArcOpposite V3 V1 V2 v := by
      intro h; exact absurd (h_c_iff.mp (h_i3.mp h)) (not_le_of_gt hc_pos)
    rw [if_neg hi1_neg, if_pos hi2, if_neg hi3_neg]
  · -- c < 0: i1 = 0, i2 = 0, i3 = 1.
    have hi1_neg : ¬ Problem97.OnArcOpposite V1 V2 V3 v := by
      intro h; exact absurd (h_a_iff.mp (h_i1.mp h)) (not_le_of_gt ha_pos)
    have hi2_neg : ¬ Problem97.OnArcOpposite V2 V3 V1 v := by
      intro h; exact absurd (h_b_iff.mp (h_i2.mp h)) (not_le_of_gt hb_pos)
    have hi3 : Problem97.OnArcOpposite V3 V1 V2 v :=
      h_i3.mpr (h_c_iff.mpr (le_of_lt hc_neg))
    rw [if_neg hi1_neg, if_neg hi2_neg, if_pos hi3]

end Erdos9796CountingFragment_Erdos9796Proof_P97_ArcPartitionCount
