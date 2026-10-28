-- Prove2me | solution 1 for RovelliLQG.minkowski_spin_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T19:25:36.285228+00:00
-- url     : https://prove2.me/submissions/e937c98b-1864-466c-b261-c1ed77620c4a

import Mathlib
import Definitions.Def_RovelliLQG_Defs
import Theorems.Thm_OAI_PettyProjection_brunnMinkowski_euclidean
import Theorems.Thm_OAI_PettyProjection_brunnMinkowski_equality_euclidean

set_option autoImplicit false

open scoped InnerProductSpace Pointwise
open RovelliLQG MeasureTheory Set Module

namespace FfbMink

lemma norm_unitDir {n : E3} (hn : n ≠ 0) : ‖unitDir n‖ = 1 := by
  unfold unitDir
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]

lemma inner_unitDir (n x : E3) : ⟪unitDir n, x⟫_ℝ = ‖n‖⁻¹ * ⟪n, x⟫_ℝ := by
  unfold unitDir; rw [real_inner_smul_left]

lemma norm_smul_unitDir {n : E3} (hn : n ≠ 0) : ‖n‖ • unitDir n = n := by
  unfold unitDir; rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hn), one_smul]

lemma isClosed_poly {ι : Type*} (u : ι → E3) (h : ι → ℝ) :
    IsClosed (halfspacePolyhedron u h) := by
  have : halfspacePolyhedron u h = ⋂ l, {x : E3 | ⟪u l, x⟫_ℝ ≤ h l} := by
    ext x; simp [halfspacePolyhedron]
  rw [this]
  exact isClosed_iInter fun l => isClosed_le (continuous_const.inner continuous_id) continuous_const

lemma convex_poly {ι : Type*} (u : ι → E3) (h : ι → ℝ) :
    Convex ℝ (halfspacePolyhedron u h) := by
  have : halfspacePolyhedron u h = ⋂ l, {x : E3 | ⟪u l, x⟫_ℝ ≤ h l} := by
    ext x; simp [halfspacePolyhedron]
  rw [this]
  refine convex_iInter fun l => convex_halfSpace_le ?_ (h l)
  exact ⟨fun x y => inner_add_right _ _ _, fun c x => real_inner_smul_right _ _ _⟩

set_option maxHeartbeats 1000000 in
/-- Every polyhedron with the closure normals is bounded. -/
lemma bounded_poly {v : ℕ} (n : Fin v → E3) (hne : ∀ l, n l ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) (hclosure : ∑ l, n l = 0) (h : Fin v → ℝ) :
    Bornology.IsBounded (halfspacePolyhedron (fun l => unitDir (n l)) h) := by
  set C : ℝ := ∑ k, ‖n k‖ * |h k| with hC
  have hc0 : ∀ k, 0 ≤ ‖n k‖ * |h k| := fun k => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  -- upper bounds
  have hup : ∀ x ∈ halfspacePolyhedron (fun l => unitDir (n l)) h, ∀ l,
      ⟪n l, x⟫_ℝ ≤ ‖n l‖ * |h l| := by
    intro x hx l
    have h1 := hx l
    simp only [inner_unitDir] at h1
    have hpos : 0 < ‖n l‖ := norm_pos_iff.mpr (hne l)
    have : ⟪n l, x⟫_ℝ ≤ ‖n l‖ * h l := by
      have := mul_le_mul_of_nonneg_left h1 hpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
    exact this.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hpos.le)
  have hsum : ∀ x : E3, ∑ k, ⟪n k, x⟫_ℝ = 0 := by
    intro x; rw [← sum_inner, hclosure, inner_zero_left]
  have hbd : ∀ x ∈ halfspacePolyhedron (fun l => unitDir (n l)) h, ∀ l, |⟪n l, x⟫_ℝ| ≤ C := by
    intro x hx l
    rw [abs_le]; constructor
    · have e := hsum x
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)] at e
      have : ∑ k ∈ Finset.univ.erase l, ⟪n k, x⟫_ℝ ≤ C := by
        calc ∑ k ∈ Finset.univ.erase l, ⟪n k, x⟫_ℝ ≤ ∑ k ∈ Finset.univ.erase l, ‖n k‖ * |h k| :=
              Finset.sum_le_sum fun k _ => hup x hx k
          _ ≤ C := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun k _ _ => hc0 k)
      linarith
    · exact (hup x hx l).trans (Finset.single_le_sum (fun k _ => hc0 k) (Finset.mem_univ l))
  -- the evaluation map is injective
  let L : E3 →ₗ[ℝ] (Fin v → ℝ) :=
    { toFun := fun x l => ⟪n l, x⟫_ℝ
      map_add' := fun x y => by ext l; simp [inner_add_right]
      map_smul' := fun c x => by ext l; simp [real_inner_smul_right] }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hle : Submodule.span ℝ (Set.range n) ≤ LinearMap.ker (innerₛₗ ℝ x) := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      have := congrFun hx l
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, L] at this
      simp only [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply]
      rw [real_inner_comm]; exact this
    rw [hspan] at hle
    have hx' : x ∈ LinearMap.ker (innerₛₗ ℝ x) := hle Submodule.mem_top
    simpa [innerₛₗ_apply_apply] using hx'
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  refine (hK.isBounded_preimage (Metric.isBounded_closedBall (x := (0 : Fin v → ℝ)) (r := C))).subset ?_
  intro x hx
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun k _ => hc0 k
  refine (pi_norm_le_iff_of_nonneg hC0).mpr fun l => ?_
  simpa [L, Real.norm_eq_abs] using hbd x hx l

lemma isCompact_poly {v : ℕ} (n : Fin v → E3) (hne : ∀ l, n l ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) (hclosure : ∑ l, n l = 0) (h : Fin v → ℝ) :
    IsCompact (halfspacePolyhedron (fun l => unitDir (n l)) h) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_poly _ _) (bounded_poly n hne hspan hclosure h)

/-- A face of positive area is nonempty. -/
lemma face_nonempty_of_area {ι : Type*} (u : ι → E3) (h : ι → ℝ) (l : ι) (w : E3)
    (hA : planarArea w (polyhedronFace u h l) ≠ 0) : (polyhedronFace u h l).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  apply hA
  simp [planarArea, hcon]

/-- Scaling the support numbers by `c > 0` scales the polyhedron. -/
lemma poly_smul {ι : Type*} (u : ι → E3) (h : ι → ℝ) {c : ℝ} (hc : 0 < c) :
    halfspacePolyhedron u (c • h) = c • halfspacePolyhedron u h := by
  ext x
  constructor
  · intro hx
    refine ⟨c⁻¹ • x, fun l => ?_, by
      show c • (c⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]⟩
    have := hx l
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [real_inner_smul_right]
    rw [inv_mul_le_iff₀ hc]; exact this
  · rintro ⟨y, hy, rfl⟩ l
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (hy l) hc.le

/-- Translating the support numbers by a linear functional translates the polyhedron. -/
lemma poly_translate {ι : Type*} (u : ι → E3) (h : ι → ℝ) (z : E3) :
    halfspacePolyhedron u (fun l => h l + ⟪u l, z⟫_ℝ) = (fun x => x + z) '' halfspacePolyhedron u h := by
  ext x
  constructor
  · intro hx
    refine ⟨x - z, fun l => ?_, by simp⟩
    have := hx l
    rw [inner_sub_right]; linarith
  · rintro ⟨y, hy, rfl⟩ l
    have := hy l
    simp only
    rw [inner_add_right]; linarith

/-- A set lying on a line `⟪w,x⟫ = c, ⟪m,x⟫ = d` (with `w` not parallel to `m`) has zero planar area. -/
lemma area_eq_zero_of_line (m w : E3) (hw : w ∉ (ℝ ∙ m)) (S : Set E3) (c d : ℝ)
    (hS : ∀ x ∈ S, ⟪w, x⟫_ℝ = c ∧ ⟪m, x⟫_ℝ = d) : planarArea m S = 0 := by
  rcases S.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
  · simp [planarArea, hE]
  set K : Submodule ℝ E3 := (ℝ ∙ m)ᗮ with hK
  set w' : K := K.orthogonalProjection w with hw'
  have hw'0 : w' ≠ 0 := by
    intro h0
    apply hw
    have : w ∈ Kᗮ := (Submodule.orthogonalProjection_eq_zero_iff).mp h0
    rwa [hK, Submodule.orthogonal_orthogonal] at this
  let A : AffineSubspace ℝ K :=
    AffineSubspace.mk' (K.orthogonalProjection x0) (LinearMap.ker (innerₛₗ ℝ w'))
  have hA : A ≠ ⊤ := by
    intro hA
    have hdir : A.direction = ⊤ := by rw [hA]; exact AffineSubspace.direction_top ℝ K K
    rw [AffineSubspace.direction_mk'] at hdir
    have : w' ∈ LinearMap.ker (innerₛₗ ℝ w') := by rw [hdir]; exact Submodule.mem_top
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero] at this
    exact hw'0 this
  have hsub : K.orthogonalProjection '' S ⊆ (A : Set K) := by
    rintro _ ⟨x, hx, rfl⟩
    show _ ∈ A
    rw [AffineSubspace.mem_mk', vsub_eq_sub, ← map_sub, LinearMap.mem_ker, innerₛₗ_apply_apply]
    have hmem : x - x0 ∈ K := by
      rw [hK, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
        (hS x hx).2, (hS x0 hx0).2, sub_self]
    rw [Submodule.orthogonalProjection_mem_subspace_eq_self (⟨x - x0, hmem⟩ : K)]
    rw [Submodule.coe_inner, hw', Submodule.coe_orthogonalProjection_apply]
    have h1 := Submodule.starProjection_inner_eq_zero (K := K) w (x - x0) hmem
    rw [inner_sub_left] at h1
    have h2 : ⟪w, x - x0⟫_ℝ = 0 := by
      rw [inner_sub_right, (hS x hx).1, (hS x0 hx0).1, sub_self]
    simp only at h1 ⊢
    linarith
  unfold planarArea
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace _ A hA)

set_option maxHeartbeats 1000000 in
/-- Positive face areas force a nonempty interior. -/
lemma interior_nonempty_of_areas {v : ℕ} (n : Fin v → E3) (hne : ∀ l, n l ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) (h : Fin v → ℝ)
    (hA : ∀ l, planarArea (n l) (polyhedronFace (fun l => unitDir (n l)) h l) ≠ 0) :
    (interior (halfspacePolyhedron (fun l => unitDir (n l)) h)).Nonempty := by
  set P := halfspacePolyhedron (fun l => unitDir (n l)) h with hPdef
  have hfin : finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  -- some index exists
  obtain ⟨l0⟩ : Nonempty (Fin v) := by
    by_contra hv
    have : IsEmpty (Fin v) := not_nonempty_iff.mp hv
    have hr : Set.range n = ∅ := Set.range_eq_empty n
    rw [hr, Submodule.span_empty] at hspan
    have := congrArg (fun S : Submodule ℝ E3 => finrank ℝ S) hspan
    simp [finrank_top, hfin] at this
  obtain ⟨x0, hx0⟩ := face_nonempty_of_area _ h l0 (n l0) (hA l0)
  have hx0P : x0 ∈ P := hx0.1
  by_contra hI
  have hspanA : affineSpan ℝ P ≠ ⊤ := fun h' =>
    hI (((convex_poly _ h).interior_nonempty_iff_affineSpan_eq_top).mpr h')
  set D := (affineSpan ℝ P).direction with hD
  have hDtop : D ≠ ⊤ := by
    intro h'
    apply hspanA
    exact (AffineSubspace.direction_eq_top_iff_of_nonempty
      ⟨x0, mem_affineSpan ℝ hx0P⟩).mp h'
  have hDo : Dᗮ ≠ ⊥ := fun h' => hDtop (Submodule.orthogonal_eq_bot_iff.mp h')
  obtain ⟨w, hwD, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hDo
  have hflat : ∀ x ∈ P, ⟪w, x⟫_ℝ = ⟪w, x0⟫_ℝ := by
    intro x hx
    have hmem : x -ᵥ x0 ∈ D :=
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hx) (mem_affineSpan ℝ hx0P)
    have := Submodule.inner_right_of_mem_orthogonal hmem hwD
    rw [vsub_eq_sub, real_inner_comm, inner_sub_right] at this
    linarith
  -- a normal not parallel to `w`
  obtain ⟨l, hl⟩ : ∃ l, w ∉ (ℝ ∙ n l) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hle : Submodule.span ℝ (Set.range n) ≤ ℝ ∙ w := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hall l)
      have ha0 : a ≠ 0 := by rintro rfl; rw [zero_smul] at ha; exact hw0 ha.symm
      have : n l = a⁻¹ • w := by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    rw [hspan, top_le_iff] at hle
    have := finrank_span_singleton (K := ℝ) hw0
    rw [hle, finrank_top, hfin] at this
    exact absurd this (by norm_num)
  apply hA l
  refine area_eq_zero_of_line (n l) w hl _ (⟪w, x0⟫_ℝ) (‖n l‖ * h l) ?_
  intro x hx
  refine ⟨hflat x hx.1, ?_⟩
  have h2 : ⟪unitDir (n l), x⟫_ℝ = h l := hx.2
  rw [inner_unitDir] at h2
  have hpos : ‖n l‖ ≠ 0 := norm_ne_zero_iff.mpr (hne l)
  rw [← h2, ← mul_assoc, mul_inv_cancel₀ hpos, one_mul]

/-- One-sided derivative comparison. -/
lemma deriv_le_of_le {f g : ℝ → ℝ} {a b : ℝ} (hf : HasDerivWithinAt f a (Ici 0) 0)
    (hg : HasDerivWithinAt g b (Ici 0) 0) (h0 : f 0 = g 0)
    (hle : ∀ s ∈ Icc (0:ℝ) 1, g s ≤ f s) : b ≤ a := by
  have hD := hf.sub hg
  rw [hasDerivWithinAt_iff_tendsto_slope] at hD
  have hset : Ici (0:ℝ) \ {0} = Ioi 0 := by
    ext s; simp [lt_iff_le_and_ne, eq_comm]
  rw [hset] at hD
  have hev : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0), 0 ≤ slope (fun x => f x - g x) 0 s := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with s hs
    rw [slope_def_field]
    apply div_nonneg _ (by linarith [hs.1])
    have := hle s ⟨hs.1.le, hs.2.le⟩
    simp only [h0, sub_self, sub_zero]
    linarith
  have := ge_of_tendsto hD hev
  linarith

lemma vol_poly_smul {ι : Type*} (u : ι → E3) (h : ι → ℝ) {c : ℝ} (hc : 0 < c) :
    volume.real (halfspacePolyhedron u (c • h)) = c ^ 3 * volume.real (halfspacePolyhedron u h) := by
  rw [poly_smul u h hc, measureReal_def, Measure.addHaar_smul_of_nonneg _ hc.le,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    measureReal_def]

/-- Convex combinations of polyhedra lie in the polyhedron of the combined support numbers. -/
lemma combo_subset {ι : Type*} (u : ι → E3) (g g' : ι → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • halfspacePolyhedron u g + b • halfspacePolyhedron u g' ⊆
      halfspacePolyhedron u (a • g + b • g') := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩ l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  exact add_le_add (mul_le_mul_of_nonneg_left (hy l) ha) (mul_le_mul_of_nonneg_left (hz l) hb)

lemma interior_combo_nonempty {K M : Set E3} (hK : (interior K).Nonempty) (hM : M.Nonempty)
    {a b : ℝ} (ha : 0 < a) :
    (interior (a • K + b • M)).Nonempty := by
  obtain ⟨x, hx⟩ := hK
  obtain ⟨m, hm⟩ := hM
  have hopen : IsOpen (a • interior K + b • M) :=
    IsOpen.add_right ((isOpen_interior).smul₀ ha.ne')
  refine ⟨a • x + b • m, interior_maximal ?_ hopen ?_⟩
  · exact Set.add_subset_add (Set.smul_set_mono interior_subset) le_rfl
  · exact Set.add_mem_add (Set.smul_mem_smul_set hx) (Set.smul_mem_smul_set hm)

lemma planarArea_unitDir {n : E3} (hn : n ≠ 0) (S : Set E3) :
    planarArea (unitDir n) S = planarArea n S := by
  have hsp : (ℝ ∙ unitDir n) = (ℝ ∙ n) := by
    unfold unitDir
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero (norm_ne_zero_iff.mpr hn))) n
  have hgen : ∀ K : Submodule ℝ E3, K = (ℝ ∙ n) →
      MeasureTheory.volume (Kᗮ.orthogonalProjection '' S) = planarArea n S := by
    rintro K rfl; rfl
  exact hgen _ hsp

lemma cube_rpow {X : ℝ} (hX : 0 ≤ X) : (X ^ (((3:ℕ):ℝ)⁻¹)) ^ 3 = X := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
  norm_num

set_option maxHeartbeats 1000000 in
/-- Uniqueness half of the parent, assuming the first-variation child `hC` and Brunn-Minkowski. -/
theorem uniqueness_of {v : ℕ} (n : Fin v → E3) (hne : ∀ l, n l ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) (hclosure : ∑ l, n l = 0)
    (hC : ∀ (g k : Fin v → ℝ), Bornology.IsBounded (halfspacePolyhedron (fun l => unitDir (n l)) g) →
      (interior (halfspacePolyhedron (fun l => unitDir (n l)) g)).Nonempty →
      HasDerivWithinAt
        (fun t : ℝ => volume.real (halfspacePolyhedron (fun l => unitDir (n l)) (g + t • k)))
        (∑ l, k l * (planarArea (unitDir (n l)) (polyhedronFace (fun l => unitDir (n l)) g l)).toReal)
        (Ici 0) 0)
    (hBM : ∀ K M : Set E3, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      IsCompact M → Convex ℝ M → (interior M).Nonempty → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a * volume.real K ^ (((3:ℕ):ℝ)⁻¹) + b * volume.real M ^ (((3:ℕ):ℝ)⁻¹) ≤
        volume.real (a • K + b • M) ^ (((3:ℕ):ℝ)⁻¹))
    (hBMeq : ∀ K M : Set E3, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      IsCompact M → Convex ℝ M → (interior M).Nonempty →
      volume.real (K + M) ^ (((3:ℕ):ℝ)⁻¹) =
        volume.real K ^ (((3:ℕ):ℝ)⁻¹) + volume.real M ^ (((3:ℕ):ℝ)⁻¹) →
      ∃ z : E3, ∃ c : ℝ, 0 < c ∧ K = (fun x => z + c • x) '' M)
    (h h' : Fin v → ℝ)
    (hA : ∀ l, planarArea (n l) (polyhedronFace (fun l => unitDir (n l)) h l) = ENNReal.ofReal ‖n l‖)
    (hA' : ∀ l, planarArea (n l) (polyhedronFace (fun l => unitDir (n l)) h' l) = ENNReal.ofReal ‖n l‖) :
    ∃ t : E3, halfspacePolyhedron (fun l => unitDir (n l)) h' =
        (fun x => x + t) '' halfspacePolyhedron (fun l => unitDir (n l)) h := by
  set u : Fin v → E3 := fun l => unitDir (n l) with hu
  set r : ℝ := ((3:ℕ):ℝ)⁻¹ with hr
  have hcpt : ∀ g, IsCompact (halfspacePolyhedron u g) := isCompact_poly n hne hspan hclosure
  have hbdd : ∀ g, Bornology.IsBounded (halfspacePolyhedron u g) := bounded_poly n hne hspan hclosure
  have hcvx : ∀ g, Convex ℝ (halfspacePolyhedron u g) := convex_poly u
  have hfin : ∀ g, volume (halfspacePolyhedron u g) ≠ ⊤ := fun g => (hcpt g).measure_lt_top.ne
  have hint : ∀ g, (∀ l, planarArea (n l) (polyhedronFace u g l) = ENNReal.ofReal ‖n l‖) →
      (interior (halfspacePolyhedron u g)).Nonempty := by
    intro g hg
    refine interior_nonempty_of_areas n hne hspan g fun l => ?_
    rw [hg l]
    exact (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (hne l))).ne'
  have hVpos : ∀ g, (interior (halfspacePolyhedron u g)).Nonempty →
      0 < volume.real (halfspacePolyhedron u g) := by
    intro g hg
    have : 0 < volume (halfspacePolyhedron u g) :=
      (isOpen_interior.measure_pos volume hg).trans_le (measure_mono interior_subset)
    exact ENNReal.toReal_pos this.ne' (hfin g)
  have hreal : ∀ g, (∀ l, planarArea (n l) (polyhedronFace u g l) = ENNReal.ofReal ‖n l‖) →
      ∀ l, (planarArea (u l) (polyhedronFace u g l)).toReal = ‖n l‖ := by
    intro g hg l
    rw [hu, planarArea_unitDir (hne l), hg l, ENNReal.toReal_ofReal (norm_nonneg _)]
  have hderiv : ∀ g k, (∀ l, planarArea (n l) (polyhedronFace u g l) = ENNReal.ofReal ‖n l‖) →
      HasDerivWithinAt (fun t : ℝ => volume.real (halfspacePolyhedron u (g + t • k)))
        (∑ l, k l * ‖n l‖) (Ici 0) 0 := by
    intro g k hg
    have := hC g k (hbdd g) (hint g hg)
    rwa [Finset.sum_congr rfl fun l _ => by rw [hreal g hg l]] at this
  -- volume formula
  have hvol : ∀ g, (∀ l, planarArea (n l) (polyhedronFace u g l) = ENNReal.ofReal ‖n l‖) →
      ∑ l, g l * ‖n l‖ = 3 * volume.real (halfspacePolyhedron u g) := by
    intro g hg
    have d1 := hderiv g g hg
    have d2 : HasDerivWithinAt (fun t : ℝ => volume.real (halfspacePolyhedron u (g + t • g)))
        (3 * volume.real (halfspacePolyhedron u g)) (Ici 0) 0 := by
      have hp : HasDerivAt (fun t : ℝ => (1 + t) ^ 3 * volume.real (halfspacePolyhedron u g))
          (3 * volume.real (halfspacePolyhedron u g)) 0 := by
        have := (((hasDerivAt_id (0:ℝ)).const_add 1).pow 3).mul_const
          (volume.real (halfspacePolyhedron u g))
        exact this.congr_deriv (by simp)
      refine hp.hasDerivWithinAt.congr (fun t ht => ?_) (by simp)
      have ht' : 0 < 1 + t := by have := mem_Ici.mp ht; linarith
      have : g + t • g = (1 + t) • g := by ext l; simp; ring
      rw [this, vol_poly_smul u g ht']
    exact (uniqueDiffOn_Ici 0 0 (Set.mem_Ici.mpr le_rfl)).eq_deriv _ d1 d2
  -- the key one-sided inequality
  have key : ∀ g1 g2, (∀ l, planarArea (n l) (polyhedronFace u g1 l) = ENNReal.ofReal ‖n l‖) →
      (∀ l, planarArea (n l) (polyhedronFace u g2 l) = ENNReal.ofReal ‖n l‖) →
      3 * ((volume.real (halfspacePolyhedron u g1) ^ r) ^ 2 *
        (volume.real (halfspacePolyhedron u g2) ^ r - volume.real (halfspacePolyhedron u g1) ^ r))
        ≤ 3 * volume.real (halfspacePolyhedron u g2) - 3 * volume.real (halfspacePolyhedron u g1) := by
    intro g1 g2 hg1 hg2
    set x1 := volume.real (halfspacePolyhedron u g1) ^ r
    set x2 := volume.real (halfspacePolyhedron u g2) ^ r
    have d := hderiv g1 (g2 - g1) hg1
    have hval : ∑ l, (g2 - g1) l * ‖n l‖ =
        3 * volume.real (halfspacePolyhedron u g2) - 3 * volume.real (halfspacePolyhedron u g1) := by
      rw [← hvol g2 hg2, ← hvol g1 hg1, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by simp [sub_mul]
    rw [hval] at d
    have dG : HasDerivWithinAt (fun s : ℝ => ((1 - s) * x1 + s * x2) ^ 3)
        (3 * (x1 ^ 2 * (x2 - x1))) (Ici 0) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => (1 - s) * x1 + s * x2) (x2 - x1) 0 := by
        have := (((hasDerivAt_id (0:ℝ)).const_sub 1).mul_const x1).add ((hasDerivAt_id (0:ℝ)).mul_const x2)
        exact this.congr_deriv (by ring)
      have := (h1.pow 3).hasDerivWithinAt (s := Ici 0)
      exact this.congr_deriv (by simp only [Nat.cast_ofNat, sub_zero, one_mul, zero_mul, add_zero]; ring)
    refine deriv_le_of_le d dG ?_ ?_
    · simp only [zero_smul, add_zero, sub_zero, one_mul, zero_mul]
      exact (cube_rpow measureReal_nonneg).symm
    · intro s hs
      have hs0 : 0 ≤ s := hs.1
      have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
      have hsub : (1 - s) • halfspacePolyhedron u g1 + s • halfspacePolyhedron u g2 ⊆
          halfspacePolyhedron u (g1 + s • (g2 - g1)) := by
        have := combo_subset u g1 g2 hs1 hs0
        have he : (1 - s) • g1 + s • g2 = g1 + s • (g2 - g1) := by ext l; simp; ring
        rwa [he] at this
      have hbm := hBM _ _ (hcpt g1) (hcvx g1) (hint g1 hg1) (hcpt g2) (hcvx g2) (hint g2 hg2)
        (1 - s) s hs1 hs0 (by ring)
      have hmono : volume.real ((1 - s) • halfspacePolyhedron u g1 + s • halfspacePolyhedron u g2) ^ r ≤
          volume.real (halfspacePolyhedron u (g1 + s • (g2 - g1))) ^ r :=
        Real.rpow_le_rpow measureReal_nonneg (measureReal_mono hsub (hfin _)) (by rw [hr]; positivity)
      have hle := hbm.trans hmono
      have hx1 : 0 ≤ x1 := Real.rpow_nonneg measureReal_nonneg _
      have hx2 : 0 ≤ x2 := Real.rpow_nonneg measureReal_nonneg _
      have h0 : 0 ≤ (1 - s) * x1 + s * x2 := by positivity
      calc ((1 - s) * x1 + s * x2) ^ 3
          ≤ (volume.real (halfspacePolyhedron u (g1 + s • (g2 - g1))) ^ r) ^ 3 :=
            pow_le_pow_left₀ h0 hle 3
        _ = volume.real (halfspacePolyhedron u (g1 + s • (g2 - g1))) := cube_rpow measureReal_nonneg
  have hX := hVpos h (hint h hA)
  have hY := hVpos h' (hint h' hA')
  have hx0 : 0 < volume.real (halfspacePolyhedron u h) ^ r := Real.rpow_pos_of_pos hX _
  have hy0 : 0 < volume.real (halfspacePolyhedron u h') ^ r := Real.rpow_pos_of_pos hY _
  have hx3 := cube_rpow hX.le
  have hy3 := cube_rpow hY.le
  have k1 := key h h' hA hA'
  have k2 := key h' h hA' hA
  set X := volume.real (halfspacePolyhedron u h) with hXd
  set Y := volume.real (halfspacePolyhedron u h') with hYd
  set x := X ^ r with hxd
  set y := Y ^ r with hyd
  have hxy : x = y := by
    rw [← hx3, ← hy3] at k1 k2
    have e1 : x ^ 2 * y ≤ y ^ 2 * y := by nlinarith
    have e2 : y ^ 2 * x ≤ x ^ 2 * x := by nlinarith
    have f1 : x ^ 2 ≤ y ^ 2 := le_of_mul_le_mul_right e1 hy0
    have f2 : y ^ 2 ≤ x ^ 2 := le_of_mul_le_mul_right e2 hx0
    nlinarith
  have hXY : X = Y := by rw [← hx3, ← hy3, hxy]
  -- the midpoint polyhedron
  set k2v : Fin v → ℝ := (1/2 : ℝ) • (h' - h) with hk2v
  have hsubN : (1/2:ℝ) • halfspacePolyhedron u h + (1/2:ℝ) • halfspacePolyhedron u h' ⊆
      halfspacePolyhedron u (h + k2v) := by
    have := combo_subset u h h' (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    have he : (1/2:ℝ) • h + (1/2:ℝ) • h' = h + k2v := by ext l; simp [hk2v]; ring
    rwa [he] at this
  have hMne : (halfspacePolyhedron u h').Nonempty := (hint h' hA').mono interior_subset
  have hNint : (interior (halfspacePolyhedron u (h + k2v))).Nonempty :=
    (interior_combo_nonempty (hint h hA) hMne (by norm_num : (0:ℝ) < 1/2)).mono (interior_mono hsubN)
  have hd0 : HasDerivWithinAt (fun t : ℝ => volume.real (halfspacePolyhedron u (h + t • k2v)))
      0 (Ici 0) 0 := by
    have := hderiv h k2v hA
    have hz : ∑ l, k2v l * ‖n l‖ = 0 := by
      have e : ∑ l, k2v l * ‖n l‖ = (1/2) * (∑ l, h' l * ‖n l‖ - ∑ l, h l * ‖n l‖) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by simp [hk2v]; ring
      rw [e, hvol h' hA', hvol h hA, ← hXd, ← hYd, hXY]; ring
    rwa [hz] at this
  set nn := volume.real (halfspacePolyhedron u (h + k2v)) ^ r with hnnd
  have hnn0 : 0 ≤ nn := Real.rpow_nonneg measureReal_nonneg _
  have hnn : nn ≤ x := by
    have dG : HasDerivWithinAt (fun s : ℝ => ((1 - s) * x + s * nn) ^ 3)
        (3 * (x ^ 2 * (nn - x))) (Ici 0) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => (1 - s) * x + s * nn) (nn - x) 0 := by
        have := (((hasDerivAt_id (0:ℝ)).const_sub 1).mul_const x).add ((hasDerivAt_id (0:ℝ)).mul_const nn)
        exact this.congr_deriv (by ring)
      have := (h1.pow 3).hasDerivWithinAt (s := Ici 0)
      exact this.congr_deriv (by simp only [Nat.cast_ofNat, sub_zero, one_mul, zero_mul, add_zero]; ring)
    have hle := deriv_le_of_le hd0 dG (by
        simp only [zero_smul, add_zero, sub_zero, one_mul, zero_mul]
        exact hx3.symm) (by
        intro s hs
        have hs0 : 0 ≤ s := hs.1
        have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
        have hsub : (1 - s) • halfspacePolyhedron u h + s • halfspacePolyhedron u (h + k2v) ⊆
            halfspacePolyhedron u (h + s • k2v) := by
          have := combo_subset u h (h + k2v) hs1 hs0
          have he : (1 - s) • h + s • (h + k2v) = h + s • k2v := by ext l; simp; ring
          rwa [he] at this
        have hbm := hBM _ _ (hcpt h) (hcvx h) (hint h hA) (hcpt _) (hcvx _) hNint
          (1 - s) s hs1 hs0 (by ring)
        have hmono : volume.real ((1 - s) • halfspacePolyhedron u h +
              s • halfspacePolyhedron u (h + k2v)) ^ r ≤
            volume.real (halfspacePolyhedron u (h + s • k2v)) ^ r :=
          Real.rpow_le_rpow measureReal_nonneg (measureReal_mono hsub (hfin _)) (by rw [hr]; positivity)
        have hle := hbm.trans hmono
        have h0 : 0 ≤ (1 - s) * x + s * nn := by positivity
        calc ((1 - s) * x + s * nn) ^ 3
            ≤ (volume.real (halfspacePolyhedron u (h + s • k2v)) ^ r) ^ 3 :=
              pow_le_pow_left₀ h0 hle 3
          _ = volume.real (halfspacePolyhedron u (h + s • k2v)) := cube_rpow measureReal_nonneg)
    have hx2 : 0 < x ^ 2 := by positivity
    nlinarith
  set W := volume.real ((1/2:ℝ) • halfspacePolyhedron u h + (1/2:ℝ) • halfspacePolyhedron u h') with hWd
  have hW0 : 0 ≤ W := measureReal_nonneg
  have hhalf : W ^ r = x := by
    apply le_antisymm
    · exact (Real.rpow_le_rpow hW0 (measureReal_mono hsubN (hfin _)) (by rw [hr]; positivity)).trans hnn
    · have := hBM _ _ (hcpt h) (hcvx h) (hint h hA) (hcpt h') (hcvx h') (hint h' hA')
        (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
      simp only [← hXd, ← hYd, ← hxd, ← hyd, ← hWd] at this
      rw [← hxy] at this
      have e : (1/2:ℝ) * x + 1/2 * x = x := by ring
      rw [e] at this
      exact this
  have hKM : halfspacePolyhedron u h + halfspacePolyhedron u h' =
      (2:ℝ) • ((1/2:ℝ) • halfspacePolyhedron u h + (1/2:ℝ) • halfspacePolyhedron u h') := by
    rw [smul_add, smul_smul, smul_smul]; norm_num
  have hvolKM : volume.real (halfspacePolyhedron u h + halfspacePolyhedron u h') ^ r = x + y := by
    have e : volume.real (halfspacePolyhedron u h + halfspacePolyhedron u h') = 2 ^ 3 * W := by
      rw [hKM, measureReal_def, Measure.addHaar_smul_of_nonneg _ (by norm_num : (0:ℝ) ≤ 2),
        finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
        ← measureReal_def]
    rw [e, Real.mul_rpow (by positivity) hW0, hhalf, ← hxy]
    have h8 : ((2:ℝ) ^ 3) ^ r = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hr]; norm_num
    rw [h8]; ring
  obtain ⟨z, c, hc, hKeq⟩ := hBMeq _ _ (hcpt h) (hcvx h) (hint h hA) (hcpt h') (hcvx h') (hint h' hA')
    hvolKM
  have himg : (fun w => z + c • w) '' halfspacePolyhedron u h' = z +ᵥ (c • halfspacePolyhedron u h') := by
    rw [← Set.image_smul, ← Set.image_vadd, Set.image_image]; rfl
  have hc1 : c = 1 := by
    have e : X = c ^ 3 * Y := by
      rw [hXd, hKeq, himg, measureReal_def, measure_vadd, Measure.addHaar_smul_of_nonneg _ hc.le,
        finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
        ← measureReal_def]
    rw [← hXY] at e
    have : c ^ 3 = 1 := by
      have := mul_right_cancel₀ hX.ne' (e.symm.trans (one_mul X).symm)
      exact this
    exact (pow_eq_one_iff_of_nonneg hc.le (by norm_num)).mp this
  subst hc1
  refine ⟨-z, ?_⟩
  rw [hKeq, Set.image_image]
  simp

end FfbMink


namespace FfbC

/-! ## Part 1: Cavalieri along a unit direction -/

lemma inner_W {u : E3} (y : (ℝ ∙ u)ᗮ) : ⟪u, (y : E3)⟫_ℝ = 0 :=
  Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self u) y.2

/-- `(y, τ) ↦ y + τ u` on `WithLp 2 (uᗮ × ℝ)`. -/
noncomputable def psiL (u : E3) : WithLp 2 ((ℝ ∙ u)ᗮ × ℝ) →ₗ[ℝ] E3 :=
  ((ℝ ∙ u)ᗮ.subtype.coprod (LinearMap.toSpanSingleton ℝ E3 u)) ∘ₗ
    (WithLp.linearEquiv 2 ℝ ((ℝ ∙ u)ᗮ × ℝ)).toLinearMap

lemma psiL_apply (u : E3) (p : WithLp 2 ((ℝ ∙ u)ᗮ × ℝ)) :
    psiL u p = ((p.fst : (ℝ ∙ u)ᗮ) : E3) + p.snd • u := rfl

lemma psiL_norm {u : E3} (hu : ‖u‖ = 1) (p : WithLp 2 ((ℝ ∙ u)ᗮ × ℝ)) :
    ‖psiL u p‖ = ‖p‖ := by
  have h0 : ⟪((p.fst : (ℝ ∙ u)ᗮ) : E3), p.snd • u⟫_ℝ = 0 := by
    rw [real_inner_smul_right, real_inner_comm, inner_W, mul_zero]
  have h1 : ‖psiL u p‖ ^ 2 = ‖p‖ ^ 2 := by
    rw [psiL_apply, norm_add_sq_real, h0, WithLp.prod_norm_sq_eq_of_L2,
      norm_smul, hu, mul_one]
    simp
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

noncomputable def psiI {u : E3} (hu : ‖u‖ = 1) : WithLp 2 ((ℝ ∙ u)ᗮ × ℝ) →ₗᵢ[ℝ] E3 :=
  ⟨psiL u, psiL_norm hu⟩

lemma proj_add {u : E3} (hu : ‖u‖ = 1) (x : E3) :
    (((ℝ ∙ u)ᗮ.orthogonalProjectionOnto x : (ℝ ∙ u)ᗮ) : E3) + ⟪u, x⟫_ℝ • u = x := by
  have h1 : (((ℝ ∙ u)ᗮ.orthogonalProjectionOnto x : (ℝ ∙ u)ᗮ) : E3) = (ℝ ∙ u)ᗮ.starProjection x := rfl
  rw [h1, Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton, hu]
  simp

lemma psiI_surj {u : E3} (hu : ‖u‖ = 1) : Function.Surjective (psiI hu) := by
  intro x
  refine ⟨WithLp.toLp 2 ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto x, ⟪u, x⟫_ℝ), ?_⟩
  show psiL u _ = x
  rw [psiL_apply]
  exact proj_add hu x

noncomputable def psiE {u : E3} (hu : ‖u‖ = 1) : WithLp 2 ((ℝ ∙ u)ᗮ × ℝ) ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.ofSurjective (psiI hu) (psiI_surj hu)

lemma psiE_apply {u : E3} (hu : ‖u‖ = 1) (y : (ℝ ∙ u)ᗮ) (τ : ℝ) :
    psiE hu (WithLp.toLp 2 (y, τ)) = (y : E3) + τ • u := rfl

lemma mp_split {u : E3} (hu : ‖u‖ = 1) :
    MeasurePreserving (fun q : (ℝ ∙ u)ᗮ × ℝ => (q.1 : E3) + (q.2 : ℝ) • u) := by
  have := (psiE hu).measurePreserving.comp (WithLp.volume_preserving_toLp ((ℝ ∙ u)ᗮ) ℝ)
  exact this

/-- Cavalieri: volume = integral of the sections' areas along a unit direction. -/
lemma cavalieri {u : E3} (hu : ‖u‖ = 1) {S : Set E3} (hS : MeasurableSet S) :
    volume S = ∫⁻ τ : ℝ, volume {y : (ℝ ∙ u)ᗮ | (y : E3) + τ • u ∈ S} := by
  have hmp := mp_split hu
  rw [← hmp.measure_preimage hS.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply_symm (hmp.measurable hS)]
  rfl

/-! ## Part 2: sections of polyhedra and slabs -/

section Part2
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → E3)

/-- The projected section constraints (all constraints except `l`). -/
def Rset (l : ι) (d : ι → ℝ) : Set (ℝ ∙ u l)ᗮ :=
  {y | ∀ m, m ≠ l → ⟪u m, (y : E3)⟫_ℝ ≤ d m}

/-- Support numbers of the section at height `τ`. -/
noncomputable def secd (l : ι) (g : ι → ℝ) (τ : ℝ) : ι → ℝ := fun m => g m - τ * ⟪u m, u l⟫_ℝ

lemma isClosed_P (g : ι → ℝ) : IsClosed (halfspacePolyhedron u g) := by
  have : halfspacePolyhedron u g = ⋂ l, {x : E3 | ⟪u l, x⟫_ℝ ≤ g l} := by
    ext x; simp [halfspacePolyhedron]
  rw [this]
  exact isClosed_iInter fun l => isClosed_le (by fun_prop) continuous_const

lemma inner_shift {l : ι} (hu : ‖u l‖ = 1) (y : (ℝ ∙ u l)ᗮ) (τ : ℝ) (m : ι) :
    ⟪u m, (y : E3) + τ • u l⟫_ℝ = ⟪u m, (y : E3)⟫_ℝ + τ * ⟪u m, u l⟫_ℝ := by
  rw [inner_add_right, real_inner_smul_right]

lemma inner_shift_self {l : ι} (hu : ‖u l‖ = 1) (y : (ℝ ∙ u l)ᗮ) (τ : ℝ) :
    ⟪u l, (y : E3) + τ • u l⟫_ℝ = τ := by
  rw [inner_shift u hu, inner_W, real_inner_self_eq_norm_sq, hu]; ring

lemma mem_P_shift_iff {l : ι} (hu : ‖u l‖ = 1) (g : ι → ℝ) (y : (ℝ ∙ u l)ᗮ) (τ : ℝ) :
    (y : E3) + τ • u l ∈ halfspacePolyhedron u g ↔ y ∈ Rset u l (secd u l g τ) ∧ τ ≤ g l := by
  constructor
  · intro hx
    refine ⟨fun m _ => ?_, ?_⟩
    · have := hx m
      rw [inner_shift u hu] at this
      simp only [secd]; linarith
    · have := hx l
      rwa [inner_shift_self u hu] at this
  · rintro ⟨hR, hτ⟩ m
    by_cases hm : m = l
    · subst hm; rw [inner_shift_self u hu]; exact hτ
    · have := hR m hm
      rw [inner_shift u hu]
      simp only [secd] at this; linarith

lemma sec_eq {l : ι} (hu : ‖u l‖ = 1) (g : ι → ℝ) {τ : ℝ} (hτ : τ ≤ g l) :
    {y : (ℝ ∙ u l)ᗮ | (y : E3) + τ • u l ∈ halfspacePolyhedron u g} = Rset u l (secd u l g τ) := by
  ext y
  simp only [mem_setOf_eq, mem_P_shift_iff u hu, and_iff_left hτ]

lemma Rset_update (l : ι) (g : ι → ℝ) (b τ : ℝ) :
    Rset u l (secd u l (Function.update g l b) τ) = Rset u l (secd u l g τ) := by
  ext y
  simp only [Rset, secd, mem_setOf_eq]
  refine forall_congr' fun m => imp_congr_right fun hm => ?_
  rw [Function.update_of_ne hm]

/-- Volume of a slab, as a lower integral of section areas. -/
lemma slab_lintegral {l : ι} (hu : ‖u l‖ = 1) (g : ι → ℝ) (a : ℝ) :
    volume (halfspacePolyhedron u g \ halfspacePolyhedron u (Function.update g l a)) =
      ∫⁻ τ in Ioc a (g l), volume (Rset u l (secd u l g τ)) := by
  rw [cavalieri hu ((isClosed_P u g).measurableSet.diff (isClosed_P u _).measurableSet),
    ← lintegral_indicator measurableSet_Ioc]
  congr 1
  funext τ
  by_cases hτ : τ ∈ Ioc a (g l)
  · rw [indicator_of_mem hτ]
    congr 1
    ext y
    simp only [mem_setOf_eq, mem_diff, mem_P_shift_iff u hu, Function.update_self,
      Rset_update]
    constructor
    · rintro ⟨⟨h1, _⟩, _⟩; exact h1
    · intro h1; exact ⟨⟨h1, hτ.2⟩, fun h2 => absurd h2.2 (not_le.2 hτ.1)⟩
  · rw [indicator_of_notMem hτ]
    convert measure_empty (μ := (volume : Measure (ℝ ∙ u l)ᗮ))
    ext y
    simp only [mem_setOf_eq, mem_diff, mem_P_shift_iff u hu, Function.update_self,
      Rset_update, mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    exact hτ ⟨lt_of_not_ge (h2 h1.1), h1.2⟩

/-- Two-sided bounds on the volume increment of a one-coordinate change. -/
lemma slab_bounds {l : ι} (hu : ‖u l‖ = 1) (g : ι → ℝ) {a : ℝ} (hab : a ≤ g l)
    (hfin : volume (halfspacePolyhedron u g) ≠ ⊤) {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hb : ∀ τ ∈ Ioc a (g l), ENNReal.ofReal lo ≤ volume (Rset u l (secd u l g τ)) ∧
      volume (Rset u l (secd u l g τ)) ≤ ENNReal.ofReal hi) :
    (g l - a) * lo ≤ volume.real (halfspacePolyhedron u g) -
        volume.real (halfspacePolyhedron u (Function.update g l a)) ∧
      volume.real (halfspacePolyhedron u g) -
        volume.real (halfspacePolyhedron u (Function.update g l a)) ≤ (g l - a) * hi := by
  have hsub : halfspacePolyhedron u (Function.update g l a) ⊆ halfspacePolyhedron u g := by
    intro x hx m
    have := hx m
    by_cases hm : m = l
    · subst hm; rw [Function.update_self] at this; linarith
    · rwa [Function.update_of_ne hm] at this
  have hdiff : volume.real (halfspacePolyhedron u g) -
      volume.real (halfspacePolyhedron u (Function.update g l a)) =
      (volume (halfspacePolyhedron u g \ halfspacePolyhedron u (Function.update g l a))).toReal := by
    rw [measure_diff hsub (isClosed_P u _).measurableSet.nullMeasurableSet
      (ne_top_of_le_ne_top hfin (measure_mono hsub)),
      ENNReal.toReal_sub_of_le (measure_mono hsub) hfin]
    rfl
  rw [hdiff, slab_lintegral u hu]
  have hae : ∀ᵐ τ ∂(volume.restrict (Ioc a (g l))), ENNReal.ofReal lo ≤
      volume (Rset u l (secd u l g τ)) ∧ volume (Rset u l (secd u l g τ)) ≤ ENNReal.ofReal hi :=
    (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hb)
  have hL : ∫⁻ τ in Ioc a (g l), ENNReal.ofReal lo ≤
      ∫⁻ τ in Ioc a (g l), volume (Rset u l (secd u l g τ)) := lintegral_mono_ae (hae.mono fun _ h => h.1)
  have hU : ∫⁻ τ in Ioc a (g l), volume (Rset u l (secd u l g τ)) ≤
      ∫⁻ τ in Ioc a (g l), ENNReal.ofReal hi := lintegral_mono_ae (hae.mono fun _ h => h.2)
  rw [setLIntegral_const, Real.volume_Ioc] at hL hU
  have hfinI : ∫⁻ τ in Ioc a (g l), volume (Rset u l (secd u l g τ)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hU
  constructor
  · have := ENNReal.toReal_mono hfinI hL
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hlo, ENNReal.toReal_ofReal (sub_nonneg.2 hab),
      mul_comm] at this
  · have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hU
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hhi, ENNReal.toReal_ofReal (sub_nonneg.2 hab),
      mul_comm] at this

end Part2

/-! ## Part 3: continuity of the volume of a polyhedral region in its support numbers -/

section Part3
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {ι : Type*} [Fintype ι] (p : ι → Prop) (φ : ι → E →L[ℝ] ℝ)

def Rg (d : ι → ℝ) : Set E := {y | ∀ m, p m → φ m y ≤ d m}

lemma Rg_mono {d d' : ι → ℝ} (h : ∀ m, p m → d m ≤ d' m) : Rg p φ d ⊆ Rg p φ d' :=
  fun _ hy m hm => (hy m hm).trans (h m hm)

lemma isClosed_Rg (d : ι → ℝ) : IsClosed (Rg p φ d) := by
  have : Rg p φ d = ⋂ m, ⋂ (_ : p m), {y | φ m y ≤ d m} := by ext y; simp [Rg]
  rw [this]
  exact isClosed_iInter fun m => isClosed_iInter fun _ =>
    isClosed_le (φ m).continuous continuous_const

lemma convex_Rg (d : ι → ℝ) : Convex ℝ (Rg p φ d) := by
  intro x hx y hy a b ha hb hab m hm
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  calc a * φ m x + b * φ m y ≤ a * d m + b * d m :=
        add_le_add (mul_le_mul_of_nonneg_left (hx m hm) ha) (mul_le_mul_of_nonneg_left (hy m hm) hb)
    _ = d m := by rw [← add_mul, hab, one_mul]

lemma Rg_homothety (y0 : E) {r : ℝ} (hr : 0 < r) (d : ι → ℝ) :
    Rg p φ (fun m => φ m y0 + r * (d m - φ m y0)) = AffineMap.homothety y0 r '' Rg p φ d := by
  ext z
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, mem_image]
  constructor
  · intro hz
    refine ⟨y0 + r⁻¹ • (z - y0), fun m hm => ?_, ?_⟩
    · have := hz m hm
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
      have h2 : r⁻¹ * (φ m z - φ m y0) ≤ d m - φ m y0 := by
        rw [inv_mul_le_iff₀ hr]; linarith
      linarith
    · rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, sub_add_cancel]
  · rintro ⟨y, hy, rfl⟩ m hm
    have := hy m hm
    simp only [map_add, map_smul, map_sub, smul_eq_mul]
    nlinarith

lemma interior_nonempty_of_pos {S : Set E} (hc : Convex ℝ S) (hS : IsClosed S) (hpos : μ S ≠ 0) :
    (interior S).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  apply hpos
  have : S ⊆ frontier S := by rw [frontier, hS.closure_eq, h, diff_empty]
  exact measure_mono_null this (hc.addHaar_frontier μ)

lemma strict_of_interior {d : ι → ℝ} {y0 : E} (hy0 : y0 ∈ interior (Rg p φ d))
    (hz : ∀ m, p m → φ m = 0 → 0 < d m) : ∀ m, p m → φ m y0 < d m := by
  intro m hm
  by_cases h0 : φ m = 0
  · rw [h0]; simpa using hz m hm h0
  · obtain ⟨z, hz'⟩ : ∃ z, 0 < φ m z := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      apply h0
      ext z
      have h1 := hcon z
      have h2 := hcon (-z)
      rw [map_neg] at h2
      simp only [ContinuousLinearMap.zero_apply]
      linarith
    have hT : Filter.Tendsto (fun t : ℝ => y0 + t • z) (nhds 0) (nhds y0) := by
      have : Continuous (fun t : ℝ => y0 + t • z) := by fun_prop
      simpa using this.tendsto 0
    have hev := (hT.eventually (mem_interior_iff_mem_nhds.1 hy0))
    obtain ⟨t, ht, htpos⟩ :=
      ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (0:ℝ)))).exists
    have := ht m hm
    rw [map_add, map_smul, smul_eq_mul] at this
    have : 0 < t * φ m z := mul_pos htpos hz'
    linarith

set_option maxHeartbeats 1000000 in
/-- Continuity (in `ε`-form) of `d ↦ μ (Rg d)` at `d0`. -/
lemma rcont {d0 : ι → ℝ} (hz : ∀ m, p m → φ m = 0 → 0 < d0 m) {ε0 : ℝ} (hε0 : 0 < ε0)
    (hfin : μ (Rg p φ (fun m => d0 m + ε0)) ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d in nhds d0, ENNReal.ofReal ((μ (Rg p φ d0)).toReal - ε) ≤ μ (Rg p φ d) ∧
      μ (Rg p φ d) ≤ ENNReal.ofReal ((μ (Rg p φ d0)).toReal + ε) := by
  have hA : μ (Rg p φ d0) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono (Rg_mono p φ (fun m _ => by linarith)))
  have hcoord : ∀ m, Filter.Tendsto (fun d : ι → ℝ => d m) (nhds d0) (nhds (d0 m)) :=
    fun m => (continuous_apply m).tendsto d0
  refine Filter.Eventually.and ?_ ?_
  -- lower bound
  · by_cases hA0 : μ (Rg p φ d0) = 0
    · refine Filter.Eventually.of_forall fun d => ?_
      rw [hA0, ENNReal.toReal_zero, zero_sub, ENNReal.ofReal_of_nonpos (by linarith)]
      exact zero_le
    obtain ⟨y0, hy0⟩ := interior_nonempty_of_pos μ (convex_Rg p φ d0) (isClosed_Rg p φ d0) hA0
    have hδ := strict_of_interior p φ hy0 hz
    set a0 := (μ (Rg p φ d0)).toReal with ha0
    set n := finrank ℝ E
    have ha0nn : 0 ≤ a0 := ENNReal.toReal_nonneg
    have hden : 0 < (n : ℝ) * a0 + 1 := by positivity
    set θ := min (1 / 2 : ℝ) (ε / ((n : ℝ) * a0 + 1)) with hθ
    have hθpos : 0 < θ := lt_min (by norm_num) (div_pos hε hden)
    have hθ1 : θ ≤ 1 / 2 := min_le_left _ _
    have hθ2 : θ * ((n : ℝ) * a0 + 1) ≤ ε := (le_div_iff₀ hden).1 (min_le_right _ _)
    have hev : ∀ᶠ d in nhds d0, ∀ m, p m → d0 m - θ * (d0 m - φ m y0) < d m := by
      rw [Filter.eventually_all]
      intro m
      by_cases hm : p m
      · have : d0 m - θ * (d0 m - φ m y0) < d0 m := by
          have := hδ m hm; nlinarith
        exact ((hcoord m).eventually (lt_mem_nhds this)).mono fun d hd _ => hd
      · exact Filter.Eventually.of_forall fun d h => absurd h hm
    refine hev.mono fun d hd => ?_
    have hsub : Rg p φ (fun m => φ m y0 + (1 - θ) * (d0 m - φ m y0)) ⊆ Rg p φ d :=
      Rg_mono p φ fun m hm => by have := hd m hm; linarith
    have hmeas : μ (Rg p φ (fun m => φ m y0 + (1 - θ) * (d0 m - φ m y0))) =
        ENNReal.ofReal ((1 - θ) ^ n * a0) := by
      rw [Rg_homothety p φ y0 (by linarith) d0, Measure.addHaar_image_homothety,
        abs_of_nonneg (pow_nonneg (by linarith) _), ENNReal.ofReal_mul (pow_nonneg (by linarith) _),
        ha0, ENNReal.ofReal_toReal hA]
    refine le_trans ?_ (hmeas ▸ measure_mono hsub)
    apply ENNReal.ofReal_le_ofReal
    have hb : 1 + (n : ℝ) * (-θ) ≤ (1 + -θ) ^ n := one_add_le_pow_of_two_add_nonneg (by linarith) n
    have : (1 - (n : ℝ) * θ) * a0 ≤ (1 - θ) ^ n * a0 :=
      mul_le_mul_of_nonneg_right (by rw [sub_eq_add_neg, sub_eq_add_neg]; linarith) ha0nn
    nlinarith
  -- upper bound
  · set s : ℕ → Set E := fun k => Rg p φ (fun m => d0 m + ε0 / ((k : ℝ) + 1)) with hs
    have hanti : Antitone s := by
      intro i j hij
      refine Rg_mono p φ fun m _ => ?_
      have : ((i : ℝ) + 1) ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hij
      have := div_le_div_of_nonneg_left hε0.le (by positivity) this
      linarith
    have hinter : (⋂ k, s k) = Rg p φ d0 := by
      ext y
      simp only [hs, mem_iInter, Rg, mem_setOf_eq]
      constructor
      · intro hy m hm
        have hT : Filter.Tendsto (fun k : ℕ => d0 m + ε0 / ((k : ℝ) + 1)) Filter.atTop
            (nhds (d0 m + 0)) :=
          tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat ε0 |>.comp
            (Filter.tendsto_add_atTop_nat 1) |>.congr fun k => by simp)
        rw [add_zero] at hT
        exact ge_of_tendsto' hT fun k => hy k m hm
      · intro hy k m hm
        have := hy m hm
        have : 0 ≤ ε0 / ((k : ℝ) + 1) := by positivity
        linarith
    have hT : Filter.Tendsto (μ ∘ s) Filter.atTop (nhds (μ (Rg p φ d0))) := by
      rw [← hinter]
      exact tendsto_measure_iInter_atTop
        (fun k => (isClosed_Rg p φ _).measurableSet.nullMeasurableSet) hanti
        ⟨0, by simpa [hs] using hfin⟩
    have hlt : μ (Rg p φ d0) < ENNReal.ofReal ((μ (Rg p φ d0)).toReal + ε) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hA]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    obtain ⟨N, hN⟩ := (hT.eventually (gt_mem_nhds hlt)).exists
    have hev : ∀ᶠ d in nhds d0, ∀ m, d m < d0 m + ε0 / ((N : ℝ) + 1) := by
      rw [Filter.eventually_all]
      intro m
      have h1 : 0 < ε0 / ((N : ℝ) + 1) := by positivity
      have h2 : d0 m < d0 m + ε0 / ((N : ℝ) + 1) := by linarith
      exact (hcoord m).eventually (gt_mem_nhds h2)
    refine hev.mono fun d hd => ?_
    exact le_trans (measure_mono (Rg_mono p φ fun m _ => (hd m).le)) hN.le

end Part3

/-! ## Part 4: the polyhedral setting -/

section Part4
set_option linter.unusedSectionVars false
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → E3)

lemma P_eq_Rg (g : ι → ℝ) :
    halfspacePolyhedron u g = Rg (fun _ => True) (fun m => innerSL ℝ (u m)) g := by
  ext x; simp [halfspacePolyhedron, Rg]

lemma strict_of_mem_interior (hu : ∀ l, ‖u l‖ = 1) {g : ι → ℝ} {x0 : E3}
    (hx0 : x0 ∈ interior (halfspacePolyhedron u g)) : ∀ m, ⟪u m, x0⟫_ℝ < g m := by
  rw [P_eq_Rg] at hx0
  intro m
  have hz : ∀ m, (fun _ => True) m → (fun m => innerSL ℝ (u m)) m = 0 → 0 < g m := by
    intro m _ h0
    exfalso
    have := congrArg (fun f : E3 →L[ℝ] ℝ => f (u m)) h0
    simp [hu m] at this
  have := strict_of_interior (fun _ => True) (fun m => innerSL ℝ (u m)) hx0 hz m trivial
  simpa using this

lemma bounded_all (hu : ∀ l, ‖u l‖ = 1) {h : ι → ℝ}
    (hb : Bornology.IsBounded (halfspacePolyhedron u h))
    (hi : (interior (halfspacePolyhedron u h)).Nonempty) (g : ι → ℝ) :
    Bornology.IsBounded (halfspacePolyhedron u g) := by
  obtain ⟨x0, hx0⟩ := hi
  have hs := strict_of_mem_interior u hu hx0
  have hpos : ∀ m, 0 < h m - ⟪u m, x0⟫_ℝ := fun m => sub_pos.2 (hs m)
  set r : ℝ := 1 + ∑ m, |g m - ⟪u m, x0⟫_ℝ| / (h m - ⟪u m, x0⟫_ℝ) with hr
  have hsum : 0 ≤ ∑ m, |g m - ⟪u m, x0⟫_ℝ| / (h m - ⟪u m, x0⟫_ℝ) :=
    Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (hpos i).le
  have hr0 : 0 < r := by linarith
  have hsub : halfspacePolyhedron u g ⊆ AffineMap.homothety x0 r '' halfspacePolyhedron u h := by
    rw [P_eq_Rg u h, ← Rg_homothety _ _ x0 hr0 h, P_eq_Rg u g]
    refine Rg_mono _ _ fun m _ => ?_
    simp only [innerSL_apply_apply]
    have h1 : |g m - ⟪u m, x0⟫_ℝ| / (h m - ⟪u m, x0⟫_ℝ) ≤ r := by
      have := Finset.single_le_sum (f := fun m => |g m - ⟪u m, x0⟫_ℝ| / (h m - ⟪u m, x0⟫_ℝ))
        (fun i _ => div_nonneg (abs_nonneg _) (hpos i).le) (Finset.mem_univ m)
      linarith
    rw [div_le_iff₀ (hpos m)] at h1
    linarith [le_abs_self (g m - ⟪u m, x0⟫_ℝ)]
  have hc : IsCompact (halfspacePolyhedron u h) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_P u h) hb
  exact ((hc.image (AffineMap.homothety_continuous x0 r)).isBounded).subset hsub

lemma proj_shift {l : ι} (hu : ‖u l‖ = 1) (y : (ℝ ∙ u l)ᗮ) (c : ℝ) :
    (ℝ ∙ u l)ᗮ.orthogonalProjectionOnto ((y : E3) + c • u l) = y := by
  apply Subtype.ext
  have := proj_add hu ((y : E3) + c • u l)
  rw [inner_shift_self u hu] at this
  exact add_right_cancel this

lemma face_area (hu : ∀ l, ‖u l‖ = 1) (h : ι → ℝ) (l : ι) :
    planarArea (u l) (polyhedronFace u h l) = volume (Rset u l (secd u l h (h l))) := by
  show volume ((ℝ ∙ u l)ᗮ.orthogonalProjectionOnto '' _) = _
  rw [← sec_eq u (hu l) h le_rfl]
  congr 1
  ext y
  simp only [mem_image, mem_setOf_eq, polyhedronFace, mem_inter_iff]
  constructor
  · rintro ⟨x, ⟨hxP, hxl⟩, rfl⟩
    have := proj_add (hu l) x
    rw [hxl] at this
    rw [this]; exact hxP
  · intro hy
    exact ⟨(y : E3) + h l • u l, ⟨hy, inner_shift_self u (hu l) y _⟩, proj_shift u (hu l) y _⟩

lemma hz_face (hu : ∀ l, ‖u l‖ = 1) (hinj : Function.Injective u) {h : ι → ℝ} {x0 : E3}
    (hs : ∀ m, ⟪u m, x0⟫_ℝ < h m) (l m : ι) (hm : m ≠ l)
    (h0 : (innerSL ℝ (u m)).comp (ℝ ∙ u l)ᗮ.subtypeL = 0) : 0 < secd u l h (h l) m := by
  set w : (ℝ ∙ u l)ᗮ := (ℝ ∙ u l)ᗮ.orthogonalProjectionOnto (u m) with hwdef
  have hdec : (w : E3) + ⟪u l, u m⟫_ℝ • u l = u m := proj_add (hu l) (u m)
  have h1 : ⟪u m, (w : E3)⟫_ℝ = 0 := by
    have := congrArg (fun f : (ℝ ∙ u l)ᗮ →L[ℝ] ℝ => f w) h0
    simpa using this
  have h2 : ⟪u m, (w : E3)⟫_ℝ = ⟪(w : E3), (w : E3)⟫_ℝ := by
    conv_lhs => rw [← hdec]
    rw [inner_add_left, real_inner_smul_left, inner_W, mul_zero, add_zero]
  have hw : (w : E3) = 0 := by
    rw [h1] at h2
    exact inner_self_eq_zero.1 h2.symm
  rw [hw, zero_add] at hdec
  set c := ⟪u l, u m⟫_ℝ with hc
  have habs : |c| = 1 := by
    have := hu m
    rw [← hdec, norm_smul, hu l, mul_one, Real.norm_eq_abs] at this
    exact this
  rcases (abs_eq (zero_le_one)).1 habs with h3 | h3
  · exfalso; apply hm; apply hinj; rw [← hdec, h3, one_smul]
  · have hUml : ⟪u m, u l⟫_ℝ = -1 := by rw [real_inner_comm, ← hc, h3]
    have hsm := hs m
    have hsl := hs l
    rw [← hdec, real_inner_smul_left, h3] at hsm
    simp only [secd, hUml]
    linarith

lemma hfin_face (hu : ∀ l, ‖u l‖ = 1) {h : ι → ℝ}
    (hb : ∀ g, Bornology.IsBounded (halfspacePolyhedron u g)) (l : ι) :
    volume (Rset u l (fun m => secd u l h (h l) m + 1)) ≠ ⊤ := by
  have hsub : Rset u l (fun m => secd u l h (h l) m + 1) ⊆
      {y : (ℝ ∙ u l)ᗮ | (y : E3) + h l • u l ∈ halfspacePolyhedron u (fun m => h m + 1)} := by
    intro y hy
    rw [mem_setOf_eq, mem_P_shift_iff u (hu l)]
    refine ⟨fun m hm => ?_, by linarith⟩
    have := hy m hm
    simp only [secd] at this ⊢
    linarith
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  refine (Bornology.IsBounded.measure_lt_top ?_).ne
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 (hb (fun m => h m + 1))
  refine Metric.isBounded_iff.2 ⟨C, fun y1 hy1 y2 hy2 => ?_⟩
  have := hC hy1 hy2
  rwa [dist_add_right, ← Subtype.dist_eq] at this

lemma Rset_eq_Rg (l : ι) (d : ι → ℝ) :
    Rset u l d = Rg (fun m => m ≠ l) (fun m => (innerSL ℝ (u m)).comp (ℝ ∙ u l)ᗮ.subtypeL) d := by
  ext y; simp [Rset, Rg]

/-- Section areas near the face converge to the face area. -/
lemma face_cont (hu : ∀ l, ‖u l‖ = 1) (hinj : Function.Injective u) {h : ι → ℝ}
    (hb : Bornology.IsBounded (halfspacePolyhedron u h))
    (hi : (interior (halfspacePolyhedron u h)).Nonempty) (l : ι) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : (ι → ℝ) × ℝ in nhds (h, h l),
      ENNReal.ofReal ((planarArea (u l) (polyhedronFace u h l)).toReal - ε) ≤
        volume (Rset u l (secd u l q.1 q.2)) ∧
      volume (Rset u l (secd u l q.1 q.2)) ≤
        ENNReal.ofReal ((planarArea (u l) (polyhedronFace u h l)).toReal + ε) := by
  obtain ⟨x0, hx0⟩ := hi
  have hs := strict_of_mem_interior u hu hx0
  have key := rcont volume (fun m => m ≠ l)
    (fun m => (innerSL ℝ (u m)).comp (ℝ ∙ u l)ᗮ.subtypeL) (d0 := secd u l h (h l))
    (fun m hm h0 => hz_face u hu hinj hs l m hm h0) one_pos
    (by rw [← Rset_eq_Rg]; exact hfin_face u hu (bounded_all u hu hb ⟨x0, hx0⟩) l) hε
  have hcont : Continuous (fun q : (ι → ℝ) × ℝ => secd u l q.1 q.2) := by
    unfold secd; fun_prop
  have := (hcont.tendsto (h, h l)).eventually key
  rw [face_area u hu h l]
  refine this.mono fun q hq => ?_
  simp only [Rset_eq_Rg] at hq ⊢
  exact hq

end Part4

/-! ## Part 5: one-coordinate estimate and telescoping -/

section Part5
set_option linter.unusedSectionVars false
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → E3)

lemma ofReal_max0 (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hx]
  · rw [max_eq_left hx]

lemma term_est (hu : ∀ l, ‖u l‖ = 1) (hinj : Function.Injective u) {h : ι → ℝ}
    (hb : Bornology.IsBounded (halfspacePolyhedron u h))
    (hi : (interior (halfspacePolyhedron u h)).Nonempty) (l : ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ c : ι → ℝ, ∀ s : ℝ, (∀ m, |c m - h m| < η) → |s| < η → c l = h l →
      |volume.real (halfspacePolyhedron u (Function.update c l (h l + s))) -
        volume.real (halfspacePolyhedron u c) -
        s * (planarArea (u l) (polyhedronFace u h l)).toReal| ≤ ε * |s| := by
  set a := (planarArea (u l) (polyhedronFace u h l)).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 (face_cont u hu hinj hb hi l hε)
  refine ⟨η, hη, fun c s hc hs hcl => ?_⟩
  have hfin : ∀ g, volume (halfspacePolyhedron u g) ≠ ⊤ := fun g =>
    (Bornology.IsBounded.measure_lt_top (bounded_all u hu hb hi g)).ne
  -- the section bounds on the relevant range
  have hsec : ∀ g : ι → ℝ, (∀ m, |g m - h m| < η) → ∀ τ, |τ - h l| < η →
      ENNReal.ofReal (max (a - ε) 0) ≤ volume (Rset u l (secd u l g τ)) ∧
      volume (Rset u l (secd u l g τ)) ≤ ENNReal.ofReal (a + ε) := by
    intro g hg τ hτ
    rw [ofReal_max0]
    have hd : dist (g, τ) (h, h l) < η := by
      rw [Prod.dist_eq, max_lt_iff, dist_pi_lt_iff hη]
      exact ⟨fun m => by rw [Real.dist_eq]; exact hg m, by rw [Real.dist_eq]; exact hτ⟩
    exact hball hd
  have hlo : 0 ≤ max (a - ε) 0 := le_max_right _ _
  have hhi : 0 ≤ a + ε := by linarith
  have hlo' : a - ε ≤ max (a - ε) 0 := le_max_left _ _
  have hlo'' : max (a - ε) 0 ≤ a + ε := max_le (by linarith) hhi
  rcases le_total 0 s with hs0 | hs0
  · -- increase coordinate `l`
    set g := Function.update c l (h l + s) with hg
    have hgl : g l = h l + s := by rw [hg, Function.update_self]
    have hgc : Function.update g l (h l) = c := by
      rw [hg, Function.update_idem, ← hcl, Function.update_eq_self]
    have hgb : ∀ m, |g m - h m| < η := by
      intro m
      by_cases hm : m = l
      · subst hm; rw [hgl, add_sub_cancel_left]; exact hs
      · rw [hg, Function.update_of_ne hm]; exact hc m
    have := slab_bounds u (hu l) g (a := h l) (by rw [hgl]; linarith) (hfin g) hlo hhi
      (fun τ hτ => hsec g hgb τ (by
        rw [hgl] at hτ
        rw [abs_lt]; constructor <;> [linarith [hτ.1]; linarith [hτ.2, (abs_lt.1 hs).2]]))
    rw [hgc, hgl, add_sub_cancel_left] at this
    rw [abs_of_nonneg hs0, abs_le]
    constructor <;> nlinarith [this.1, this.2]
  · -- decrease coordinate `l`
    have hca : Function.update c l (h l + s) = Function.update c l (h l + s) := rfl
    have := slab_bounds u (hu l) c (a := h l + s) (by rw [hcl]; linarith) (hfin c) hlo hhi
      (fun τ hτ => hsec c hc τ (by
        rw [hcl] at hτ
        rw [abs_lt]; constructor <;> [linarith [hτ.1, (abs_lt.1 hs).1]; linarith [hτ.2]]))
    rw [hcl] at this
    rw [abs_of_nonpos hs0, abs_le]
    constructor <;> nlinarith [this.1, this.2]

end Part5

/-- Coordinates `< j` moved by `t k`, the rest kept at `h`. -/
noncomputable def Fj {v : ℕ} (h k : Fin v → ℝ) (t : ℝ) (j : ℕ) : Fin v → ℝ :=
  fun m => h m + if (m : ℕ) < j then t * k m else 0

lemma Fj_succ {v : ℕ} (h k : Fin v → ℝ) (t : ℝ) (l : Fin v) :
    Fj h k t ((l : ℕ) + 1) = Function.update (Fj h k t l) l (h l + t * k l) := by
  funext m
  by_cases hm : m = l
  · subst hm; simp [Fj]
  · rw [Function.update_of_ne hm]
    have : ((m : ℕ) < (l : ℕ) + 1) ↔ ((m : ℕ) < l) := by
      have : (m : ℕ) ≠ l := fun h => hm (Fin.ext h)
      omega
    simp only [Fj, this]

set_option maxHeartbeats 1000000 in
theorem first_variation {v : ℕ} (u : Fin v → E3) (hu : ∀ l, ‖u l‖ = 1)
    (hinj : Function.Injective u) (h k : Fin v → ℝ)
    (hb : Bornology.IsBounded (halfspacePolyhedron u h))
    (hi : (interior (halfspacePolyhedron u h)).Nonempty) :
    HasDerivAt (fun t : ℝ => MeasureTheory.volume.real (halfspacePolyhedron u (h + t • k)))
      (∑ l, k l * (planarArea (u l) (polyhedronFace u h l)).toReal) 0 := by
  set a : Fin v → ℝ := fun l => (planarArea (u l) (polyhedronFace u h l)).toReal with ha
  set V : (Fin v → ℝ) → ℝ := fun g => volume.real (halfspacePolyhedron u g) with hV
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  set K : ℝ := ∑ l, |k l| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun l _ => abs_nonneg _
  have hε' : 0 < ε / (K + 1) := div_pos hε (by linarith)
  have hest := fun l => term_est u hu hinj hb hi l hε'
  choose η hη hηest using hest
  have hev : ∀ᶠ t : ℝ in nhds 0, ∀ l, |t| * (K + 1) < η l := by
    rw [Filter.eventually_all]
    intro l
    have hc : Continuous (fun t : ℝ => |t| * (K + 1)) := by fun_prop
    have := hc.tendsto 0
    simp only [abs_zero, zero_mul] at this
    exact this.eventually (gt_mem_nhds (hη l))
  refine hev.mono fun t ht => ?_
  have hkle : ∀ m, |k m| ≤ K := fun m =>
    Finset.single_le_sum (f := fun m => |k m|) (fun i _ => abs_nonneg _) (Finset.mem_univ m)
  have hFb : ∀ (j : ℕ) (l : Fin v) (m : Fin v), |Fj h k t j m - h m| < η l := by
    intro j l m
    simp only [Fj, add_sub_cancel_left]
    have h1 : |t| * |k m| < η l := by
      have := ht l
      have : |t| * |k m| ≤ |t| * (K + 1) := mul_le_mul_of_nonneg_left (by linarith [hkle m]) (abs_nonneg t)
      linarith
    split_ifs
    · rw [abs_mul]; exact h1
    · rw [abs_zero]; exact (hη l)
  have hs : ∀ l, |t * k l| < η l := by
    intro l
    rw [abs_mul]
    have : |t| * |k l| ≤ |t| * (K + 1) := mul_le_mul_of_nonneg_left (by linarith [hkle l]) (abs_nonneg t)
    linarith [ht l]
  -- telescoping
  have hF0 : Fj h k t 0 = h := by funext m; simp [Fj]
  have hFv : Fj h k t v = h + t • k := by funext m; simp [Fj, m.2]
  have htel : V (h + t • k) - V h = ∑ l : Fin v, (V (Fj h k t ((l : ℕ) + 1)) - V (Fj h k t l)) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => V (Fj h k t (j + 1)) - V (Fj h k t j)) v,
      Finset.sum_range_sub (fun j => V (Fj h k t j)) v, hF0, hFv]
  have hterm : ∀ l : Fin v, |V (Fj h k t ((l : ℕ) + 1)) - V (Fj h k t l) - t * k l * a l| ≤
      ε / (K + 1) * |t * k l| := by
    intro l
    rw [Fj_succ]
    have hl : Fj h k t l l = h l := by simp [Fj]
    have := hηest l (Fj h k t l) (t * k l) (hFb l l) (hs l) hl
    simpa [hV, ha, mul_assoc] using this
  simp only [sub_zero, zero_smul, add_zero, smul_eq_mul, Real.norm_eq_abs]
  show |V (h + t • k) - V h - t * ∑ l, k l * a l| ≤ ε * |t|
  rw [htel, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ l : Fin v, (V (Fj h k t ((l : ℕ) + 1)) - V (Fj h k t l) - t * (k l * a l))|
      ≤ ∑ l : Fin v, |V (Fj h k t ((l : ℕ) + 1)) - V (Fj h k t l) - t * (k l * a l)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Fin v, ε / (K + 1) * |t * k l| := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [← mul_assoc]; exact hterm l
    _ = ε / (K + 1) * (|t| * K) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [hK, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => abs_mul t (k l)
    _ ≤ ε * |t| := by
        have h1 : ε / (K + 1) * (|t| * K) = ε * |t| * (K / (K + 1)) := by ring
        have h2 : K / (K + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
        rw [h1]
        exact mul_le_of_le_one_right (by positivity) h2

theorem polytope_volume_hasDerivWithinAt_support {v : ℕ} (u : Fin v → E3) (hu : ∀ l, ‖u l‖ = 1)
    (hinj : Function.Injective u) (h k : Fin v → ℝ)
    (hb : Bornology.IsBounded (halfspacePolyhedron u h))
    (hi : (interior (halfspacePolyhedron u h)).Nonempty) :
    HasDerivWithinAt (fun t : ℝ => MeasureTheory.volume.real (halfspacePolyhedron u (h + t • k)))
      (∑ l, k l * (planarArea (u l) (polyhedronFace u h l)).toReal) (Set.Ici 0) 0 :=
  (first_variation u hu hinj h k hb hi).hasDerivWithinAt

end FfbC


/-! ## Existence (Minkowski): variational argument -/

namespace FfbB

lemma unit_of {v : ℕ} (n : Fin v → E3) (hne : ∀ l, n l ≠ 0) :
    ∀ l, ‖(fun l => unitDir (n l)) l‖ = 1 := fun l => FfbMink.norm_unitDir (hne l)

lemma inj_of {v : ℕ} (n : Fin v → E3)
    (hdir : ∀ l l', l ≠ l' → unitDir (n l) ≠ unitDir (n l')) :
    Function.Injective (fun l => unitDir (n l)) := by
  intro l l' h
  by_contra hne
  exact hdir l l' hne h

lemma phi_translate {v : ℕ} (n : Fin v → E3) (hne : ∀ l, n l ≠ 0) (hclosure : ∑ l, n l = 0)
    (z : E3) : ∑ l, ‖n l‖ * ⟪unitDir (n l), z⟫_ℝ = 0 := by
  have : ∀ l, ‖n l‖ * ⟪unitDir (n l), z⟫_ℝ = ⟪n l, z⟫_ℝ := by
    intro l
    rw [← real_inner_smul_left, FfbMink.norm_smul_unitDir (hne l)]
  simp only [this]
  rw [← sum_inner, hclosure, inner_zero_left]

lemma vol_ne_top {v : ℕ} (n : Fin v → E3) (hne : ∀ l, n l ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) (hclosure : ∑ l, n l = 0) (g : Fin v → ℝ) :
    volume (halfspacePolyhedron (fun l => unitDir (n l)) g) ≠ ⊤ :=
  (Bornology.IsBounded.measure_lt_top (FfbMink.bounded_poly n hne hspan hclosure g)).ne

lemma V_cont {v : ℕ} (n : Fin v → E3) (hne : ∀ l, n l ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) (hclosure : ∑ l, n l = 0) :
    Continuous (fun g : Fin v → ℝ => volume.real (halfspacePolyhedron (fun l => unitDir (n l)) g)) := by
  set u : Fin v → E3 := fun l => unitDir (n l) with hu_def
  have hu := unit_of n hne
  rw [continuous_iff_continuousAt]
  intro g
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hz : ∀ m, (fun _ => True) m → (fun m => innerSL ℝ (u m)) m = 0 → 0 < g m := by
    intro m _ h0
    exfalso
    have := congrArg (fun f : E3 →L[ℝ] ℝ => f (u m)) h0
    simp at this
    have h2 : ‖u m‖ = 1 := hu m
    rw [this, norm_zero] at h2
    exact zero_ne_one h2
  have hfin : volume (FfbC.Rg (fun _ => True) (fun m => innerSL ℝ (u m)) (fun m => g m + 1)) ≠ ⊤ := by
    rw [← FfbC.P_eq_Rg]; exact vol_ne_top n hne hspan hclosure _
  have key := FfbC.rcont volume (fun _ => True) (fun m => innerSL ℝ (u m)) (d0 := g) hz one_pos
    hfin (half_pos hε)
  simp only [← FfbC.P_eq_Rg] at key
  refine key.mono fun g' hg' => ?_
  have hf' := vol_ne_top n hne hspan hclosure g'
  have h1 := ENNReal.toReal_mono hf' hg'.1
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg'.2
  rw [ENNReal.toReal_ofReal'] at h1 h2
  rw [Real.dist_eq, abs_lt]
  simp only [measureReal_def] at *
  constructor
  · linarith [le_max_left ((volume (halfspacePolyhedron u g)).toReal - ε / 2) 0]
  · have : max ((volume (halfspacePolyhedron u g)).toReal + ε / 2) 0 =
        (volume (halfspacePolyhedron u g)).toReal + ε / 2 :=
      max_eq_left (by have := ENNReal.toReal_nonneg (a := volume (halfspacePolyhedron u g)); linarith)
    linarith

lemma face_smul {ι : Type*} (u : ι → E3) (h : ι → ℝ) {c : ℝ} (hc : 0 < c) (l : ι) :
    polyhedronFace u (c • h) l = c • polyhedronFace u h l := by
  unfold polyhedronFace
  rw [Set.smul_set_inter₀ hc.ne', FfbMink.poly_smul u h hc]
  congr 1
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
  simp only [mem_setOf_eq, Pi.smul_apply, smul_eq_mul, real_inner_smul_right]
  constructor
  · intro hx; rw [hx, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  · intro hx; rw [← hx, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

lemma area_smul (w : E3) (hw : w ≠ 0) (S : Set E3) {c : ℝ} (hc : 0 < c) :
    planarArea w (c • S) = ENNReal.ofReal (c ^ 2) * planarArea w S := by
  have hfr : finrank ℝ (ℝ ∙ w)ᗮ = 2 := by
    haveI : Fact (finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
    exact Submodule.finrank_orthogonal_span_singleton hw
  unfold planarArea
  have himg : (ℝ ∙ w)ᗮ.orthogonalProjectionOnto '' (c • S) =
      c • ((ℝ ∙ w)ᗮ.orthogonalProjectionOnto '' S) :=
    image_smul_set ((ℝ ∙ w)ᗮ.orthogonalProjectionOnto) c S
  have himg' : (ℝ ∙ w)ᗮ.orthogonalProjection '' (c • S) =
      c • ((ℝ ∙ w)ᗮ.orthogonalProjection '' S) := himg
  rw [himg', Measure.addHaar_smul, hfr,
    abs_of_nonneg (by positivity)]

set_option maxHeartbeats 1000000 in
/-- Existence half of Minkowski's theorem. -/
theorem existence {v : ℕ} (n : Fin v → E3)
    (hne : ∀ l, n l ≠ 0)
    (hdir : ∀ l l', l ≠ l' → unitDir (n l) ≠ unitDir (n l'))
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (hclosure : ∑ l, n l = 0) :
    ∃ h : Fin v → ℝ,
      Bornology.IsBounded (halfspacePolyhedron (fun l => unitDir (n l)) h) ∧
      (interior (halfspacePolyhedron (fun l => unitDir (n l)) h)).Nonempty ∧
      ∀ l, planarArea (n l) (polyhedronFace (fun l => unitDir (n l)) h l) =
        ENNReal.ofReal ‖n l‖ := by
  set u : Fin v → E3 := fun l => unitDir (n l) with hu_def
  have hu := unit_of n hne
  have hinj := inj_of n hdir
  set α : Fin v → ℝ := fun l => ‖n l‖ with hα
  have hαpos : ∀ l, 0 < α l := fun l => norm_pos_iff.2 (hne l)
  set V : (Fin v → ℝ) → ℝ := fun g => volume.real (halfspacePolyhedron u g) with hV
  have hVc : Continuous V := V_cont n hne hspan hclosure
  have hbdd := FfbMink.bounded_poly n hne hspan hclosure
  -- v ≠ 0
  have hv : 0 < v := by
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · exfalso
      subst h0
      have : Set.range n = ∅ := Set.range_eq_empty n
      rw [this, Submodule.span_empty] at hspan
      have h1 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E3) ∈ (⊥ : Submodule ℝ E3) := by
        rw [hspan]; exact Submodule.mem_top
      rw [Submodule.mem_bot] at h1
      have := congrArg (fun x : E3 => x 0) h1
      simp at this
    · exact h0
  let l0 : Fin v := ⟨0, hv⟩
  -- the constraint set
  set D : Set (Fin v → ℝ) := {g | (∀ l, 0 ≤ g l) ∧ ∑ l, α l * g l = 1} with hD
  have hDsub : D ⊆ Set.univ.pi (fun l => Set.Icc (0 : ℝ) (1 / α l)) := by
    intro g hg l _
    refine ⟨hg.1 l, ?_⟩
    have := Finset.single_le_sum (f := fun l => α l * g l)
      (fun i _ => mul_nonneg (hαpos i).le (hg.1 i)) (Finset.mem_univ l)
    rw [hg.2] at this
    rw [le_div_iff₀ (hαpos l)]; linarith
  have hDclosed : IsClosed D := by
    have : D = (⋂ l, {g : Fin v → ℝ | 0 ≤ g l}) ∩ {g | ∑ l, α l * g l = 1} := by
      ext g; simp [hD]
    rw [this]
    exact (isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  have hDc : IsCompact D :=
    (isCompact_univ_pi fun l => isCompact_Icc).of_isClosed_subset hDclosed hDsub
  set S : ℝ := ∑ l, α l with hS
  have hSpos : 0 < S := Finset.sum_pos (fun l _ => hαpos l) ⟨l0, Finset.mem_univ _⟩
  set g0 : Fin v → ℝ := fun _ => 1 / S with hg0
  have hg0D : g0 ∈ D := by
    refine ⟨fun l => by positivity, ?_⟩
    simp only [hg0]
    rw [← Finset.sum_mul, ← hS, mul_one_div_cancel hSpos.ne']
  obtain ⟨hs, hsD, hmax⟩ := hDc.exists_isMaxOn ⟨g0, hg0D⟩ hVc.continuousOn
  -- positivity of the maximal volume
  have hVg0 : 0 < V g0 := by
    have hball : Metric.ball (0 : E3) (1 / S) ⊆ halfspacePolyhedron u g0 := by
      intro x hx l
      rw [Metric.mem_ball, dist_zero_right] at hx
      have := real_inner_le_norm (u l) x
      rw [hu l, one_mul] at this
      simp only [hg0]; linarith
    have hpos : 0 < volume (halfspacePolyhedron u g0) :=
      lt_of_lt_of_le (Metric.measure_ball_pos volume 0 (by positivity)) (measure_mono hball)
    exact ENNReal.toReal_pos hpos.ne' (vol_ne_top n hne hspan hclosure g0)
  have hVs : 0 < V hs := lt_of_lt_of_le hVg0 (hmax hg0D)
  have hpos_int : ∀ g, 0 < V g → (interior (halfspacePolyhedron u g)).Nonempty := by
    intro g hg
    refine FfbC.interior_nonempty_of_pos volume (FfbMink.convex_poly u g) (FfbC.isClosed_P u g) ?_
    intro h0
    simp only [hV, measureReal_def, h0, ENNReal.toReal_zero] at hg
    exact lt_irrefl _ hg
  obtain ⟨x0, hx0⟩ := hpos_int hs hVs
  have hstrict := FfbC.strict_of_mem_interior u hu hx0
  -- translate to strictly positive support numbers
  set h' : Fin v → ℝ := fun l => hs l + ⟪u l, -x0⟫_ℝ with hh'
  have hh'pos : ∀ l, 0 < h' l := by
    intro l; simp only [hh', inner_neg_right]; linarith [hstrict l]
  have hPh' : halfspacePolyhedron u h' = (fun x => x + -x0) '' halfspacePolyhedron u hs :=
    FfbMink.poly_translate u hs (-x0)
  have hVh' : V h' = V hs := by
    simp only [hV, measureReal_def]
    rw [hPh', Set.image_add_right, measure_preimage_add_right]
  have hh'D : h' ∈ D := by
    refine ⟨fun l => (hh'pos l).le, ?_⟩
    simp only [hh', mul_add, Finset.sum_add_distrib]
    rw [hsD.2]
    have := phi_translate n hne hclosure (-x0)
    simp only [hα, hu_def] at this ⊢
    linarith
  have hVh'pos : 0 < V h' := hVh' ▸ hVs
  have hint' := hpos_int h' hVh'pos
  set a : Fin v → ℝ := fun l => (planarArea (u l) (polyhedronFace u h' l)).toReal with ha
  have hFV : ∀ k : Fin v → ℝ, HasDerivAt (fun t : ℝ => V (h' + t • k)) (∑ l, k l * a l) 0 :=
    fun k => FfbC.first_variation u hu hinj h' k (hbdd h') hint'
  -- first-order condition
  have hfoc : ∀ k : Fin v → ℝ, ∑ l, α l * k l = 0 → ∑ l, k l * a l = 0 := by
    intro k hk
    have hlm : IsLocalMax (fun t : ℝ => V (h' + t • k)) 0 := by
      have hev : ∀ᶠ t : ℝ in nhds 0, ∀ l, 0 < h' l + t * k l := by
        rw [Filter.eventually_all]
        intro l
        have hc : Continuous (fun t : ℝ => h' l + t * k l) := by fun_prop
        have := hc.tendsto 0
        simp only [zero_mul, add_zero] at this
        exact this.eventually (lt_mem_nhds (hh'pos l))
      refine hev.mono fun t ht => ?_
      have hmem : h' + t • k ∈ D := by
        refine ⟨fun l => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact (ht l).le, ?_⟩
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
        rw [hh'D.2]
        have : ∑ l, α l * (t * k l) = t * ∑ l, α l * k l := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, hk, mul_zero, add_zero]
      simp only [zero_smul, add_zero]
      rw [hVh']
      exact hmax hmem
    exact hlm.hasDerivAt_eq_zero (hFV k)
  -- proportionality a = λ α
  have hprop : ∀ l m, a l * α m = a m * α l := by
    intro l m
    set k : Fin v → ℝ := fun j => (if j = l then α m else 0) - (if j = m then α l else 0) with hk
    have hk0 : ∑ j, α j * k j = 0 := by
      simp only [hk, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring
    have := hfoc k hk0
    simp only [hk, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at this
    linarith
  set lam : ℝ := a l0 / α l0 with hlam
  have hal : ∀ l, a l = lam * α l := by
    intro l
    have := hprop l l0
    rw [hlam, div_mul_eq_mul_div, eq_div_iff (hαpos l0).ne']
    linarith
  -- volume formula: ∑ h'_l a_l = 3 V(h')
  have hvolf : ∑ l, h' l * a l = 3 * V h' := by
    have h1 := hFV h'
    have h2 : HasDerivAt (fun t : ℝ => (1 + t) ^ 3 * V h') (3 * V h') 0 := by
      have := ((hasDerivAt_id (0:ℝ)).const_add 1).pow 3 |>.mul_const (V h')
      simpa using this
    have heq : (fun t : ℝ => V (h' + t • h')) =ᶠ[nhds 0] (fun t : ℝ => (1 + t) ^ 3 * V h') := by
      have : ∀ᶠ t : ℝ in nhds 0, 0 < 1 + t := by
        have hc : Continuous (fun t : ℝ => 1 + t) := by fun_prop
        have := hc.tendsto 0
        simp only [add_zero] at this
        exact this.eventually (lt_mem_nhds one_pos)
      refine this.mono fun t ht => ?_
      have : h' + t • h' = (1 + t) • h' := by rw [add_smul, one_smul]
      simp only [hV, this]
      exact FfbMink.vol_poly_smul u h' ht
    exact h1.unique (h2.congr_of_eventuallyEq heq)
  have hlam_eq : lam = 3 * V h' := by
    rw [← hvolf]
    simp only [hal]
    have : ∑ l, h' l * (lam * α l) = lam * ∑ l, α l * h' l := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [this, hh'D.2, mul_one]
  have hlampos : 0 < lam := by rw [hlam_eq]; linarith
  -- rescale
  set c : ℝ := (Real.sqrt lam)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.2 (Real.sqrt_pos.2 hlampos)
  have hc2 : c ^ 2 * lam = 1 := by
    rw [hc, inv_pow, Real.sq_sqrt hlampos.le, inv_mul_cancel₀ hlampos.ne']
  have hfinA : ∀ l, planarArea (u l) (polyhedronFace u h' l) ≠ ⊤ := by
    intro l
    rw [FfbC.face_area u hu h' l]
    refine ne_top_of_le_ne_top (FfbC.hfin_face u hu (h := h') hbdd l) (measure_mono ?_)
    intro y hy m hm
    have := hy m hm
    linarith
  have hareas : ∀ l, planarArea (n l) (polyhedronFace u (c • h') l) = ENNReal.ofReal ‖n l‖ := by
    intro l
    rw [← FfbMink.planarArea_unitDir (hne l), face_smul u h' hcpos l,
      area_smul (u l) (by have : ‖u l‖ = 1 := hu l; intro h0; rw [h0, norm_zero] at this; exact zero_ne_one this)
        _ hcpos]
    rw [← ENNReal.ofReal_toReal (hfinA l), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have := hal l
    simp only [ha] at this
    rw [this]
    have : ‖n l‖ = α l := rfl
    rw [this, ← mul_assoc, hc2, one_mul]
  refine ⟨c • h', hbdd _, ?_, hareas⟩
  exact FfbMink.interior_nonempty_of_areas n hne hspan (c • h') fun l => by
    rw [hareas l]
    exact (ENNReal.ofReal_pos.2 (norm_pos_iff.2 (hne l))).ne'

end FfbB


open RovelliLQG in
theorem solution {v : ℕ} (n : Fin v → E3)
    (hne : ∀ l, n l ≠ 0)
    (hdir : ∀ l l', l ≠ l' → unitDir (n l) ≠ unitDir (n l'))
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (hclosure : ∑ l, n l = 0) :
    (∃ h : Fin v → ℝ,
      Bornology.IsBounded (halfspacePolyhedron (fun l => unitDir (n l)) h) ∧
      (interior (halfspacePolyhedron (fun l => unitDir (n l)) h)).Nonempty ∧
      ∀ l, planarArea (n l) (polyhedronFace (fun l => unitDir (n l)) h l) =
        ENNReal.ofReal ‖n l‖) ∧
    (∀ h h' : Fin v → ℝ,
      (∀ l, planarArea (n l) (polyhedronFace (fun l => unitDir (n l)) h l) =
        ENNReal.ofReal ‖n l‖) →
      (∀ l, planarArea (n l) (polyhedronFace (fun l => unitDir (n l)) h' l) =
        ENNReal.ofReal ‖n l‖) →
      ∃ t : E3, halfspacePolyhedron (fun l => unitDir (n l)) h' =
        (fun x => x + t) '' halfspacePolyhedron (fun l => unitDir (n l)) h) := by
  refine ⟨FfbB.existence n hne hdir hspan hclosure, fun h h' hA hA' => ?_⟩
  exact FfbMink.uniqueness_of n hne hspan hclosure
    (fun g k hg hi => FfbC.polytope_volume_hasDerivWithinAt_support (fun l => unitDir (n l))
      (FfbB.unit_of n hne) (FfbB.inj_of n hdir) g k hg hi)
    (fun K M hK hcK hiK hM hcM hiM a b ha hb hab =>
      OAI.PettyProjection.brunnMinkowski_euclidean (n := 3) (by norm_num) K M hK hcK hiK hM hcM hiM
        a b ha hb hab)
    (fun K M hK hcK hiK hM hcM hiM hv =>
      OAI.PettyProjection.brunnMinkowski_equality_euclidean (n := 3) (by norm_num) hK hcK hiK hM hcM
        hiM hv)
    h h' hA hA'
