-- Prove2me | solution 1 for SP4Mission.sphere_simplyConnected
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T06:01:58.54485+00:00
-- url     : https://prove2.me/submissions/375223ec-8d97-49de-8e13-826c93649dc0

import Definitions.Def_SP4Sphere

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open SP4Mission Set unitInterval Metric

/-!
# `π₁(S^{n-1}) = 0` for `n ≥ 3`

The unit sphere of `EuclideanSpace ℝ (Fin n)`, `n ≥ 3`, is simply connected.

Strategy (a piecewise-geodesic approximation argument; compare Hatcher, Proposition 1.14):

1. The punctured sphere `S ∖ {q}` is homeomorphic to a real vector space via stereographic
   projection, hence contractible, hence simply connected.
2. Any path `γ` in `S` is homotopic (rel end points) to a path `γ'` missing some point `q`.
   Uniform continuity gives a mesh `m` with `dist (γ a) (γ b) < 1/2` whenever `|a - b| ≤ 1/m`.
   The piecewise-linear interpolant `L t = ∑ₖ hatₖ(t) • γ(k/m)` of the grid values (hat functions
   of the grid) satisfies `⟪L t, γ t⟫ > 0`, so the straight-line homotopy from `γ t` to `L t`
   avoids the origin and normalizes to a path homotopy from `γ` to `γ' := L / ‖L‖`. Each `L t`
   lies in the plane spanned by two consecutive grid values, so `γ'` lies in a finite union of
   `≤ 2`-dimensional subspaces, which cannot cover `ℝⁿ` for `n ≥ 3`; a unit vector outside them is
   the point `q`.
3. A loop missing `q` contracts in `S ∖ {q}`, hence in `S`.
-/

namespace SphereSimplyConnected

variable {n : ℕ}


/-! ### Part 1: the punctured sphere is simply connected (stereographic projection) -/

private theorem sphere_compl_singleton_simplyConnected (q : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    SimplyConnectedSpace (({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1))) := by
  have hq : ‖(q : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.mp q.2
  let e := stereographic hq
  have hsrc : e.source = ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
    rw [stereographic_source]
  let h1 : ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) ≃ₜ e.source := Homeomorph.setCongr hsrc.symm
  let h2 : e.source ≃ₜ e.target := e.toHomeomorphSourceTarget
  let h3 : e.target ≃ₜ (Set.univ : Set (ℝ ∙ (q : EuclideanSpace ℝ (Fin n)))ᗮ) := Homeomorph.setCongr (stereographic_target hq)
  let h4 : (Set.univ : Set (ℝ ∙ (q : EuclideanSpace ℝ (Fin n)))ᗮ) ≃ₜ (ℝ ∙ (q : EuclideanSpace ℝ (Fin n)))ᗮ := Homeomorph.Set.univ _
  have : ContractibleSpace ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    (((h1.trans h2).trans h3).trans h4).contractibleSpace
  infer_instance

/-! ### Part 2: normalization -/

/-- Normalization `v ↦ v / ‖v‖`. -/
private noncomputable def nz (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := ‖v‖⁻¹ • v

private theorem norm_nz {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) : ‖nz v‖ = 1 := by
  unfold nz
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

private theorem nz_of_norm_one {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ = 1) : nz v = v := by
  unfold nz
  rw [hv, inv_one, one_smul]

private theorem nz_mem_sphere {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) : nz v ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  mem_sphere_zero_iff_norm.mpr (norm_nz hv)

private theorem continuous_nz_of {X : Type*} [TopologicalSpace X] {f : X → EuclideanSpace ℝ (Fin n)} (hf : Continuous f)
    (h0 : ∀ x, f x ≠ 0) : Continuous fun x => nz (f x) := by
  unfold nz
  exact (hf.norm.inv₀ fun x => norm_ne_zero_iff.mpr (h0 x)).smul hf

private theorem inner_pos_of_dist_lt (a b : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (h : dist a b < 1 / 2) :
    0 < inner ℝ (a : EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n)) := by
  have ha : ‖(a : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.mp a.2
  have hb : ‖(b : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.mp b.2
  have hd : ‖(a : EuclideanSpace ℝ (Fin n)) - b‖ < 1 / 2 := by rwa [Subtype.dist_eq, dist_eq_norm] at h
  have hsq := norm_sub_sq_real (a : EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n))
  rw [ha, hb] at hsq
  have h0 : 0 ≤ ‖(a : EuclideanSpace ℝ (Fin n)) - b‖ := norm_nonneg _
  nlinarith


/-! ### Part 3: piecewise-geodesic approximation -/

section Approx

variable {x y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1} (γ : Path x y) (m : ℕ)

/-- Grid point `k / m` of the unit interval (clamped into `[0,1]`). -/
private noncomputable def gp (m k : ℕ) : I := Set.projIcc 0 1 zero_le_one ((k : ℝ) / m)

private theorem gp_coe {m k : ℕ} (hm : 0 < m) (hk : k ≤ m) : ((gp m k : I) : ℝ) = k / m := by
  unfold gp
  rw [Set.projIcc_of_mem]
  constructor
  · positivity
  · rw [div_le_one (by exact_mod_cast hm)]
    exact_mod_cast hk

private theorem gp_zero (m : ℕ) : gp m 0 = 0 := by
  apply Subtype.ext
  simp [gp, Set.projIcc]

private theorem gp_self {m : ℕ} (hm : 0 < m) : gp m m = 1 := by
  apply Subtype.ext
  have : (m : ℝ) / m = 1 := div_self (by exact_mod_cast hm.ne')
  simp [gp, Set.projIcc, this]

/-- Hat function centred at the grid point `k / m`, with support `(k-1)/m < t < (k+1)/m`. -/
private noncomputable def hat (m k : ℕ) (t : I) : ℝ := max 0 (1 - |(t : ℝ) * m - k|)

private theorem continuous_hat (m k : ℕ) : Continuous (hat m k) := by
  unfold hat
  fun_prop

private theorem hat_nonneg (m k : ℕ) (t : I) : 0 ≤ hat m k t := le_max_left _ _

private theorem hat_pos_iff (m k : ℕ) (t : I) : 0 < hat m k t ↔ |(t : ℝ) * m - k| < 1 := by
  unfold hat
  rw [lt_max_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (lt_irrefl 0)
    · linarith
  · intro h
    right
    linarith

private theorem hat_zero_left (m k : ℕ) : hat m k 0 = if k = 0 then 1 else 0 := by
  unfold hat
  simp only [Set.Icc.coe_zero, zero_mul, zero_sub, abs_neg, Nat.abs_cast]
  split_ifs with h
  · subst h
    simp
  · have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    exact max_eq_left (by linarith)

private theorem hat_one_left (m k : ℕ) : hat m k 1 = if k = m then 1 else 0 := by
  unfold hat
  simp only [Set.Icc.coe_one, one_mul]
  split_ifs with h
  · subst h
    simp
  · have hz : ((m : ℤ) - k) ≠ 0 := by omega
    have h1 := Int.one_le_abs hz
    have h2 : (1 : ℝ) ≤ |(m : ℝ) - k| := by exact_mod_cast h1
    exact max_eq_left (by linarith)


/-- Piecewise-linear interpolation of the grid values of `γ` (as a curve in `EuclideanSpace ℝ (Fin n)`). -/
private noncomputable def L (t : I) : EuclideanSpace ℝ (Fin n) :=
  ∑ k ∈ Finset.range (m + 1), hat m k t • (γ (gp m k) : EuclideanSpace ℝ (Fin n))

private theorem continuous_L : Continuous (L γ m) := by
  unfold L
  exact continuous_finsetSum _ fun k _ => (continuous_hat m k).smul continuous_const

private theorem L_zero : L γ m 0 = x := by
  unfold L
  rw [Finset.sum_eq_single 0]
  · rw [hat_zero_left, if_pos rfl, one_smul, gp_zero, γ.source]
  · intro k _ hk
    rw [hat_zero_left, if_neg hk, zero_smul]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h

private theorem L_one (hm : 0 < m) : L γ m 1 = y := by
  unfold L
  rw [Finset.sum_eq_single m]
  · rw [hat_one_left, if_pos rfl, one_smul, gp_self hm, γ.target]
  · intro k _ hk
    rw [hat_one_left, if_neg hk, zero_smul]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) h

private theorem tm_le (t : I) : (t : ℝ) * m ≤ m := by
  have h1 : (t : ℝ) ≤ 1 := t.2.2
  have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

private theorem exists_hat_pos (t : I) : ∃ k ∈ Finset.range (m + 1), 0 < hat m k t := by
  refine ⟨⌊(t : ℝ) * m⌋₊, ?_, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    have : ⌊(t : ℝ) * m⌋₊ ≤ ⌊(m : ℝ)⌋₊ := Nat.floor_le_floor (tm_le m t)
    simpa using this
  · rw [hat_pos_iff, abs_sub_lt_iff]
    have hu0 : (0 : ℝ) ≤ (t : ℝ) * m := mul_nonneg t.2.1 (Nat.cast_nonneg m)
    constructor
    · linarith [Nat.lt_floor_add_one ((t : ℝ) * m)]
    · linarith [Nat.floor_le hu0]

/-- If the hat function at `k` is positive at `t`, the grid point `k / m` is within `1 / m` of `t`. -/
private theorem dist_gp_lt (hm : 0 < m) {k : ℕ} (hk : k ∈ Finset.range (m + 1)) {t : I}
    (h : 0 < hat m k t) : dist (gp m k) t < 1 / m := by
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [hat_pos_iff] at h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Subtype.dist_eq, Real.dist_eq, gp_coe hm hk]
  have : (k : ℝ) / m - t = ((k : ℝ) - t * m) / m := by
    field_simp
  rw [this, abs_div, abs_of_pos hm', div_lt_div_iff_of_pos_right hm', abs_sub_comm]
  exact h

private theorem hat_index (hm : 0 < m) {k : ℕ} (hk : k ∈ Finset.range (m + 1)) {t : I}
    (h : 0 < hat m k t) :
    k = min ⌊(t : ℝ) * m⌋₊ (m - 1) ∨ k = min ⌊(t : ℝ) * m⌋₊ (m - 1) + 1 := by
  rw [Finset.mem_range] at hk
  rw [hat_pos_iff, abs_sub_lt_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hu0 : (0 : ℝ) ≤ (t : ℝ) * m := mul_nonneg t.2.1 (Nat.cast_nonneg m)
  have hfl : (⌊(t : ℝ) * m⌋₊ : ℝ) ≤ (t : ℝ) * m := Nat.floor_le hu0
  have hfu : (t : ℝ) * m < ⌊(t : ℝ) * m⌋₊ + 1 := Nat.lt_floor_add_one _
  have hum : (t : ℝ) * m ≤ m := tm_le m t
  have hfk : ⌊(t : ℝ) * m⌋₊ ≤ k := by
    have : (⌊(t : ℝ) * m⌋₊ : ℝ) < k + 1 := by linarith
    have : ⌊(t : ℝ) * m⌋₊ < k + 1 := by exact_mod_cast this
    omega
  have hkf : k ≤ ⌊(t : ℝ) * m⌋₊ + 1 := by
    have : (k : ℝ) < ⌊(t : ℝ) * m⌋₊ + 2 := by linarith
    have : k < ⌊(t : ℝ) * m⌋₊ + 2 := by exact_mod_cast this
    omega
  have hfm : ⌊(t : ℝ) * m⌋₊ ≤ m := by
    have : (⌊(t : ℝ) * m⌋₊ : ℝ) ≤ m := hfl.trans hum
    exact_mod_cast this
  omega

/-- The two-dimensional subspace spanned by two consecutive grid values. -/
private noncomputable def W (j : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range ![(γ (gp m j) : EuclideanSpace ℝ (Fin n)), (γ (gp m (j + 1)) : EuclideanSpace ℝ (Fin n))])

private theorem L_mem_W (hm : 0 < m) (t : I) : L γ m t ∈ W γ m (min ⌊(t : ℝ) * m⌋₊ (m - 1)) := by
  unfold L
  apply Submodule.sum_mem
  intro k hk
  rcases (hat_nonneg m k t).lt_or_eq with h | h
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    rcases hat_index m hm hk h with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rw [← h, zero_smul]
    exact Submodule.zero_mem _

private theorem W_ne_top (hn : 3 ≤ n) (j : ℕ) : W γ m j ≠ ⊤ := by
  have h1 : Module.finrank ℝ (W γ m j) ≤ 2 := by
    have := finrank_range_le_card (R := ℝ) ![(γ (gp m j) : EuclideanSpace ℝ (Fin n)), (γ (gp m (j + 1)) : EuclideanSpace ℝ (Fin n))]
    rw [Fintype.card_fin] at this
    exact this
  have h2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  exact (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne


/-- Under the mesh condition `1 / m < δ` with `δ` a modulus for `dist < 1/2`, the interpolant
`L t` has positive inner product with `γ t`. -/
private theorem inner_L_pos (hm : 0 < m) {δ : ℝ}
    (hδ : ∀ a b : I, dist a b < δ → dist (γ a) (γ b) < 1 / 2) (hmδ : 1 / (m : ℝ) < δ) (t : I) :
    0 < inner ℝ (L γ m t) (γ t : EuclideanSpace ℝ (Fin n)) := by
  have key : ∀ k ∈ Finset.range (m + 1), 0 < hat m k t →
      0 < inner ℝ (γ (gp m k) : EuclideanSpace ℝ (Fin n)) (γ t : EuclideanSpace ℝ (Fin n)) := by
    intro k hk h
    apply inner_pos_of_dist_lt
    apply hδ
    exact (dist_gp_lt m hm hk h).trans hmδ
  unfold L
  rw [sum_inner]
  simp_rw [real_inner_smul_left]
  apply Finset.sum_pos'
  · intro k hk
    rcases (hat_nonneg m k t).lt_or_eq with h | h
    · exact (mul_pos h (key k hk h)).le
    · rw [← h, zero_mul]
  · obtain ⟨k, hk, hpos⟩ := exists_hat_pos m t
    exact ⟨k, hk, mul_pos hpos (key k hk hpos)⟩

private theorem L_ne_zero (hm : 0 < m) {δ : ℝ}
    (hδ : ∀ a b : I, dist a b < δ → dist (γ a) (γ b) < 1 / 2) (hmδ : 1 / (m : ℝ) < δ) (t : I) :
    L γ m t ≠ 0 := by
  intro h
  have := inner_L_pos γ m hm hδ hmδ t
  rw [h, inner_zero_left] at this
  exact lt_irrefl _ this

/-- The normalized interpolant, as a path in the sphere from `x` to `y`. -/
private noncomputable def approx (hm : 0 < m) (hLne : ∀ t, L γ m t ≠ 0) : Path x y where
  toFun t := ⟨nz (L γ m t), nz_mem_sphere (hLne t)⟩
  continuous_toFun := (continuous_nz_of (continuous_L γ m) hLne).subtype_mk _
  source' := by
    apply Subtype.ext
    show nz (L γ m 0) = x
    rw [L_zero]
    exact nz_of_norm_one (mem_sphere_zero_iff_norm.mp x.2)
  target' := by
    apply Subtype.ext
    show nz (L γ m 1) = y
    rw [L_one γ m hm]
    exact nz_of_norm_one (mem_sphere_zero_iff_norm.mp y.2)

private theorem approx_apply (hm : 0 < m) (hLne : ∀ t, L γ m t ≠ 0) (t : I) :
    (approx γ m hm hLne t : EuclideanSpace ℝ (Fin n)) = nz (L γ m t) := rfl

/-- The straight-line-then-normalize homotopy from `γ` to its normalized interpolant. -/
private theorem homotopic_approx (hm : 0 < m) {δ : ℝ}
    (hδ : ∀ a b : I, dist a b < δ → dist (γ a) (γ b) < 1 / 2) (hmδ : 1 / (m : ℝ) < δ) :
    γ.Homotopic (approx γ m hm (L_ne_zero γ m hm hδ hmδ)) := by
  have hLne := L_ne_zero γ m hm hδ hmδ
  have hpos := inner_L_pos γ m hm hδ hmδ
  -- the segment from `γ t` to `nz (L t)` avoids the origin
  have hne : ∀ (s t : I),
      (1 - (s : ℝ)) • (γ t : EuclideanSpace ℝ (Fin n)) + (s : ℝ) • nz (L γ m t) ≠ 0 := by
    intro s t hzero
    have hγt : ‖(γ t : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.mp (γ t).2
    have hs0 : (0 : ℝ) ≤ s := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hp : 0 < ‖L γ m t‖⁻¹ * inner ℝ (L γ m t) (γ t : EuclideanSpace ℝ (Fin n)) :=
      mul_pos (inv_pos.mpr (norm_pos_iff.mpr (hLne t))) (hpos t)
    have h : 0 < inner ℝ ((1 - (s : ℝ)) • (γ t : EuclideanSpace ℝ (Fin n)) + (s : ℝ) • nz (L γ m t))
        (γ t : EuclideanSpace ℝ (Fin n)) := by
      unfold nz
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hγt]
      rcases eq_or_lt_of_le hs1 with h | h
      · rw [h]
        simpa using hp
      · have h1 : 0 < (1 - (s : ℝ)) * 1 ^ 2 := by nlinarith
        have h2 : 0 ≤ (s : ℝ) * (‖L γ m t‖⁻¹ * inner ℝ (L γ m t) (γ t : EuclideanSpace ℝ (Fin n))) :=
          mul_nonneg hs0 hp.le
        linarith
    rw [hzero, inner_zero_left] at h
    exact lt_irrefl _ h
  refine ⟨{ toFun := fun p => ⟨nz ((1 - (p.1 : ℝ)) • (γ p.2 : EuclideanSpace ℝ (Fin n)) +
              (p.1 : ℝ) • nz (L γ m p.2)), nz_mem_sphere (hne p.1 p.2)⟩
            continuous_toFun := ?_
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · have hγ : Continuous fun p : I × I => (γ p.2 : EuclideanSpace ℝ (Fin n)) :=
      continuous_subtype_val.comp (γ.continuous.comp continuous_snd)
    have hnzL : Continuous fun p : I × I => nz (L γ m p.2) :=
      (continuous_nz_of (continuous_L γ m) hLne).comp continuous_snd
    have hs : Continuous fun p : I × I => (p.1 : ℝ) := continuous_subtype_val.comp continuous_fst
    have hf : Continuous fun p : I × I =>
        (1 - (p.1 : ℝ)) • (γ p.2 : EuclideanSpace ℝ (Fin n)) + (p.1 : ℝ) • nz (L γ m p.2) :=
      ((continuous_const.sub hs).smul hγ).add (hs.smul hnzL)
    exact (continuous_nz_of hf (fun p => hne p.1 p.2)).subtype_mk _
  · intro t
    apply Subtype.ext
    show nz ((1 - ((0 : I) : ℝ)) • (γ t : EuclideanSpace ℝ (Fin n)) + ((0 : I) : ℝ) • nz (L γ m t))
      = (γ t : EuclideanSpace ℝ (Fin n))
    simp [nz_of_norm_one (mem_sphere_zero_iff_norm.mp (γ t).2)]
  · intro t
    apply Subtype.ext
    show nz ((1 - ((1 : I) : ℝ)) • (γ t : EuclideanSpace ℝ (Fin n)) + ((1 : I) : ℝ) • nz (L γ m t))
      = nz (L γ m t)
    simp [nz_of_norm_one (norm_nz (hLne t))]
  · intro s t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    apply Subtype.ext
    rcases ht with rfl | rfl
    · show nz ((1 - (s : ℝ)) • (γ 0 : EuclideanSpace ℝ (Fin n)) + (s : ℝ) • nz (L γ m 0))
        = (γ 0 : EuclideanSpace ℝ (Fin n))
      have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
      rw [L_zero, γ.source, nz_of_norm_one hx, ← add_smul, sub_add_cancel, one_smul,
        nz_of_norm_one hx]
    · show nz ((1 - (s : ℝ)) • (γ 1 : EuclideanSpace ℝ (Fin n)) + (s : ℝ) • nz (L γ m 1))
        = (γ 1 : EuclideanSpace ℝ (Fin n))
      have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
      rw [L_one γ m hm, γ.target, nz_of_norm_one hy, ← add_smul, sub_add_cancel, one_smul,
        nz_of_norm_one hy]

/-- The normalized interpolant misses some point of the sphere (`n ≥ 3`). -/
private theorem exists_avoided_point (hn : 3 ≤ n) (hm : 0 < m) (hLne : ∀ t, L γ m t ≠ 0) :
    ∃ q : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ∀ t, approx γ m hm hLne t ≠ q := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun j : Fin m => W γ m j) (fun j => W_ne_top γ m hn j)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv ⟨0, hm⟩ (Submodule.zero_mem _)
  refine ⟨⟨nz v, nz_mem_sphere hv0⟩, ?_⟩
  intro t ht
  have hmem : L γ m t ∈ W γ m (min ⌊(t : ℝ) * m⌋₊ (m - 1)) := L_mem_W γ m hm t
  have hj : min ⌊(t : ℝ) * m⌋₊ (m - 1) < m := by omega
  have h1 : nz (L γ m t) ∈ W γ m (min ⌊(t : ℝ) * m⌋₊ (m - 1)) := Submodule.smul_mem _ _ hmem
  have h2 : nz v ∈ W γ m (min ⌊(t : ℝ) * m⌋₊ (m - 1)) := by
    have hval : nz (L γ m t) = nz v := congrArg Subtype.val ht
    rw [← hval]
    exact h1
  have h3 : v ∈ W γ m (min ⌊(t : ℝ) * m⌋₊ (m - 1)) := by
    have : v = ‖v‖ • nz v := by
      unfold nz
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ h2
  exact hv ⟨_, hj⟩ h3

end Approx

/-! ### Part 4: assembly -/

/-- Any path in the sphere `S^{n-1}`, `n ≥ 3`, is homotopic to a path missing some point. -/
private theorem exists_homotopic_avoiding (hn : 3 ≤ n) {x y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1}
    (γ : Path x y) :
    ∃ γ' : Path x y, γ.Homotopic γ' ∧ ∃ q, ∀ t, γ' t ≠ q := by
  have hγu : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp hγu (1 / 2) (by norm_num)
  obtain ⟨m₀, hm₀⟩ := exists_nat_one_div_lt hδpos
  set m : ℕ := m₀ + 1 with hm_def
  have hm : 0 < m := Nat.succ_pos m₀
  have hmδ : 1 / (m : ℝ) < δ := by
    rw [hm_def]
    push_cast
    exact hm₀
  have hδ' : ∀ a b : I, dist a b < δ → dist (γ a) (γ b) < 1 / 2 := fun a b h => hδ h
  refine ⟨approx γ m hm (L_ne_zero γ m hm hδ' hmδ), homotopic_approx γ m hm hδ' hmδ, ?_⟩
  exact exists_avoided_point γ m hn hm _

/-- **The unit sphere in `ℝⁿ`, `n ≥ 3`, is simply connected** (`π₁(S^{n-1}) = 0`). -/
private theorem sphere_simplyConnected (hn : 3 ≤ n) :
    SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨?_, ?_⟩
  · rw [← isPathConnected_iff_pathConnectedSpace]
    refine isPathConnected_sphere ?_ 0 zero_le_one
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < n)
  · intro x γ
    obtain ⟨γ', hγγ', q, hq⟩ := exists_homotopic_avoiding hn γ
    have hxq : x ∈ ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
      have := hq 0
      rw [γ'.source] at this
      simpa using this
    have := sphere_compl_singleton_simplyConnected q
    have hmem : ∀ t, γ' t ∈ ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) := fun t => by
      simpa using hq t
    -- lift `γ'` to the punctured sphere
    let γ'' : Path (⟨x, hxq⟩ : ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1))) ⟨x, hxq⟩ :=
      { toFun := fun t => ⟨γ' t, hmem t⟩
        continuous_toFun := γ'.continuous.subtype_mk hmem
        source' := Subtype.ext γ'.source
        target' := Subtype.ext γ'.target }
    have h1 : γ''.Homotopic (Path.refl _) := SimplyConnectedSpace.paths_homotopic _ _
    have h2 := h1.map ⟨Subtype.val, continuous_subtype_val⟩
    have hL : γ''.map continuous_subtype_val = γ' := by
      ext t
      rfl
    have hR : (Path.refl (⟨x, hxq⟩ : ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))).map
        continuous_subtype_val = Path.refl x := by
      ext t
      rfl
    rw [hL, hR] at h2
    exact hγγ'.trans h2


end SphereSimplyConnected

theorem solution (n : ℕ) (hn : 3 ≤ n) :
    SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  SphereSimplyConnected.sphere_simplyConnected hn
