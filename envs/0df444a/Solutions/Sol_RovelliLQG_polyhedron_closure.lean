-- Prove2me | solution 1 for RovelliLQG.polyhedron_closure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:16:34.154977+00:00
-- url     : https://prove2.me/submissions/f737461c-e64d-4a9e-a356-9313d930cdab

import Mathlib
import Definitions.Def_RovelliLQG_Defs


open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace RLQAux
open RovelliLQG

noncomputable abbrev Kp (u : E3) : Submodule ℝ E3 := (ℝ ∙ u)ᗮ

noncomputable abbrev prj (u : E3) : E3 →L[ℝ] Kp u := (Kp u).orthogonalProjection

lemma prj_eq (u : E3) (hu : ‖u‖ = 1) (x : E3) : (prj u x : E3) = x - ⟪u, x⟫ • u := by
  rw [← Submodule.starProjection_apply]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hu]; ring
  · intro w hw
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hw
    rw [sub_sub_cancel, inner_smul_left, hw]; simp

lemma decomp (u : E3) (hu : ‖u‖ = 1) (x : E3) : x = (prj u x : E3) + ⟪u, x⟫ • u := by
  rw [prj_eq u hu]; abel

lemma norm_sq_decomp (u : E3) (hu : ‖u‖ = 1) (x : E3) :
    ‖x‖ ^ 2 = ‖prj u x‖ ^ 2 + ⟪u, x⟫ ^ 2 := by
  have h := congrArg (fun y => ‖y‖ ^ 2) (decomp u hu x)
  rw [h, norm_add_sq_real, inner_smul_right, norm_smul, hu, Real.norm_eq_abs]
  have : ⟪(prj u x : E3), u⟫ = 0 := by
    have := (prj u x).2
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at this
    exact this
  rw [this]; simp [sq_abs]

noncomputable def frameLI (u : E3) (hu : ‖u‖ = 1) : E3 →ₗᵢ[ℝ] WithLp 2 (Kp u × ℝ) where
  toFun x := WithLp.toLp 2 (prj u x, ⟪u, x⟫)
  map_add' x y := by
    simp only [map_add, inner_add_right]; rfl
  map_smul' c x := by
    simp only [map_smul, inner_smul_right, RingHom.id_apply]; rfl
  norm_map' x := by
    have h1 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (prj u x, ⟪u, x⟫))
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs] at h1
    rw [← norm_sq_decomp u hu x] at h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

lemma finrank_Kp (u : E3) (hu : ‖u‖ = 1) : Module.finrank ℝ (Kp u) = 2 := by
  have : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  exact Submodule.finrank_orthogonal_span_singleton (by rintro rfl; simp at hu)

noncomputable def frame (u : E3) (hu : ‖u‖ = 1) : E3 ≃ₗᵢ[ℝ] WithLp 2 (Kp u × ℝ) :=
  (frameLI u hu).toLinearIsometryEquiv (by
    rw [finrank_euclideanSpace_fin, LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (Kp u × ℝ)),
      Module.finrank_prod, finrank_Kp u hu, Module.finrank_self])

lemma frame_mp (u : E3) (hu : ‖u‖ = 1) :
    MeasurePreserving (fun x : E3 => (prj u x, ⟪u, x⟫)) volume ((volume : Measure (Kp u)).prod volume) := by
  have h := (WithLp.volume_preserving_ofLp (Kp u) ℝ).comp (frame u hu).measurePreserving
  exact h

end RLQAux


open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace RLQAux
open RovelliLQG

lemma vol_slices (u : E3) (hu : ‖u‖ = 1) (S : Set E3) (hS : MeasurableSet S) :
    volume S = ∫⁻ s : ℝ, volume {z : Kp u | (z : E3) + s • u ∈ S} := by
  set T : Set (Kp u × ℝ) := {p | (p.1 : E3) + p.2 • u ∈ S} with hT
  have hTm : MeasurableSet T := by
    have : Measurable (fun p : Kp u × ℝ => (p.1 : E3) + p.2 • u) := by fun_prop
    exact this hS
  have hpre : (fun x : E3 => (prj u x, ⟪u, x⟫)) ⁻¹' T = S := by
    ext x; simp only [hT, mem_preimage, mem_setOf_eq]; rw [← decomp u hu x]
  conv_lhs => rw [← hpre]
  rw [(frame_mp u hu).measure_preimage hTm.nullMeasurableSet, Measure.prod_apply_symm hTm]
  rfl

def cone (x0 : E3) (F : Set E3) : Set E3 :=
  {x | ∃ y ∈ F, ∃ t ∈ Icc (0:ℝ) 1, x = x0 + t • (y - x0)}

lemma cone_slice (u : E3) (hu : ‖u‖ = 1) (x0 : E3) (F : Set E3) (h : ℝ)
    (hF : ∀ y ∈ F, ⟪u, y⟫ = h) (hd : ⟪u, x0⟫ < h) (s : ℝ) :
    {z : Kp u | (z : E3) + s • u ∈ cone x0 F} =
      if (s - ⟪u, x0⟫) / (h - ⟪u, x0⟫) ∈ Icc (0:ℝ) 1 then
        AffineMap.homothety (prj u x0) ((s - ⟪u, x0⟫) / (h - ⟪u, x0⟫)) '' (prj u '' F)
      else ∅ := by
  have hd' : 0 < h - ⟪u, x0⟫ := by linarith
  set t0 := (s - ⟪u, x0⟫) / (h - ⟪u, x0⟫) with ht0
  ext z
  simp only [mem_setOf_eq, cone]
  constructor
  · rintro ⟨y, hy, t, ht, hx⟩
    have hinner := congrArg (fun v => ⟪u, v⟫) hx
    simp only [inner_add_right, inner_smul_right, inner_sub_right, hF y hy] at hinner
    have hz : ⟪u, (z : E3)⟫ = 0 := by
      have := z.2
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
      exact this
    rw [real_inner_self_eq_norm_sq, hu, hz] at hinner
    have htt : t = t0 := by
      rw [ht0, eq_div_iff hd'.ne']; linarith
    rw [if_pos (htt ▸ ht)]
    refine ⟨prj u y, ⟨y, hy, rfl⟩, ?_⟩
    rw [AffineMap.homothety_apply, ← htt]
    apply Subtype.ext
    have := congrArg (fun v => (prj u v : E3)) hx
    simp only [map_add, map_smul, map_sub, Submodule.coe_add, Submodule.coe_smul,
      Submodule.coe_sub] at this
    have e3 : prj u (z : E3) = z := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self z
    have e4 : prj u u = 0 := Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero u
    rw [e3, e4] at this
    simp only [ZeroMemClass.coe_zero, smul_zero, add_zero] at this
    simp only [vsub_eq_sub, vadd_eq_add, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub]
    rw [this]; abel
  · intro hz
    split_ifs at hz with ht
    · obtain ⟨_, ⟨y, hy, rfl⟩, hzy⟩ := hz
      refine ⟨y, hy, t0, ht, ?_⟩
      have e1 := decomp u hu y
      have e2 := decomp u hu x0
      rw [hF y hy] at e1
      have hzv : (z : E3) = t0 • ((prj u y : E3) - prj u x0) + prj u x0 := by
        rw [← hzy, AffineMap.homothety_apply]; simp
      rw [hzv]
      conv_rhs => rw [e1, e2]
      have : s = ⟪u, x0⟫ + t0 * (h - ⟪u, x0⟫) := by rw [ht0]; field_simp; ring
      rw [this]
      simp only [smul_sub, smul_add, add_smul, smul_smul]
      abel_nf
      module
    · exact absurd hz (Set.notMem_empty z)

end RLQAux


open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace RLQAux
open RovelliLQG

lemma cone_compact (x0 : E3) (F : Set E3) (hF : IsCompact F) : IsCompact (cone x0 F) := by
  have : cone x0 F = (fun p : E3 × ℝ => x0 + p.2 • (p.1 - x0)) '' (F ×ˢ Icc (0:ℝ) 1) := by
    ext x; simp only [cone, mem_setOf_eq, mem_image, mem_prod, Prod.exists]
    constructor
    · rintro ⟨y, hy, t, ht, rfl⟩; exact ⟨y, t, ⟨hy, ht⟩, rfl⟩
    · rintro ⟨y, t, ⟨hy, ht⟩, rfl⟩; exact ⟨y, hy, t, ht, rfl⟩
  rw [this]
  exact (hF.prod isCompact_Icc).image (by fun_prop)

lemma lint_sq (a d : ℝ) (hd : 0 < d) :
    ∫⁻ s in Icc a (a + d), ENNReal.ofReal (((s - a) / d) ^ 2) = ENNReal.ofReal (d / 3) := by
  have hc : Continuous (fun s : ℝ => ((s - a) / d) ^ 2) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc)
    (Filter.Eventually.of_forall fun _ => by positivity)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_right (fun x => (x / d) ^ 2)]
  simp only [sub_self, add_sub_cancel_left]
  simp_rw [div_pow]
  rw [intervalIntegral.integral_div, integral_pow]
  field_simp
  ring

lemma cone_vol (u : E3) (hu : ‖u‖ = 1) (x0 : E3) (F : Set E3) (hFc : IsCompact F) (h : ℝ)
    (hF : ∀ y ∈ F, ⟪u, y⟫ = h) (hd : ⟪u, x0⟫ < h) :
    volume (cone x0 F) = ENNReal.ofReal ((h - ⟪u, x0⟫) / 3) * volume (prj u '' F) := by
  have hd' : 0 < h - ⟪u, x0⟫ := by linarith
  set d := h - ⟪u, x0⟫ with hdd
  set a := ⟪u, x0⟫ with ha
  rw [vol_slices u hu _ (cone_compact x0 F hFc).isClosed.measurableSet]
  rw [show (fun s : ℝ => volume {z : Kp u | (z : E3) + s • u ∈ cone x0 F}) = _ from funext fun s => congrArg volume (cone_slice u hu x0 F h hF hd s)]
  have hfun : ∀ s : ℝ, volume (if (s - a) / d ∈ Icc (0:ℝ) 1 then
        ⇑(AffineMap.homothety (prj u x0) ((s - a) / d)) '' (prj u '' F) else ∅) =
      (Icc a (a + d)).indicator (fun s => ENNReal.ofReal (((s - a) / d) ^ 2) * volume (prj u '' F)) s := by
    intro s
    have hiff : (s - a) / d ∈ Icc (0:ℝ) 1 ↔ s ∈ Icc a (a + d) := by
      constructor
      · rintro ⟨h1, h2⟩
        rw [le_div_iff₀ hd'] at h1; rw [div_le_iff₀ hd'] at h2
        constructor <;> linarith
      · rintro ⟨h1, h2⟩
        constructor
        · apply div_nonneg <;> linarith
        · rw [div_le_iff₀ hd']; linarith
    split_ifs with h1
    · rw [indicator_of_mem (hiff.mp h1), Measure.addHaar_image_homothety, finrank_Kp u hu]
      congr 2
      exact abs_of_nonneg (by positivity)
    · rw [indicator_of_notMem (fun h2 => h1 (hiff.mpr h2)), measure_empty]
  rw [← hdd, ← ha]
  simp_rw [hfun]
  rw [lintegral_indicator measurableSet_Icc, lintegral_mul_const _ (by fun_prop), lint_sq a d hd']

end RLQAux


open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace RLQAux
open RovelliLQG

variable {v : ℕ} (u : Fin v → E3) (h : Fin v → ℝ)

lemma P_closed : IsClosed (halfspacePolyhedron u h) := by
  have : halfspacePolyhedron u h = ⋂ l, {x | ⟪u l, x⟫ ≤ h l} := by
    ext x; simp [halfspacePolyhedron]
  rw [this]
  exact isClosed_iInter fun l => isClosed_le (by fun_prop) continuous_const

lemma P_convex : Convex ℝ (halfspacePolyhedron u h) := by
  intro x hx y hy a b ha hb hab l
  have h1 := hx l; have h2 := hy l
  show ⟪u l, a • x + b • y⟫ ≤ h l
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have e : a * h l + b * h l = h l := by rw [← add_mul, hab, one_mul]
  linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma int_strict (x0 : E3) (hx0 : x0 ∈ interior (halfspacePolyhedron u h)) (hu : ∀ l, ‖u l‖ = 1)
    (l : Fin v) : ⟪u l, x0⟫ < h l := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx0
  obtain ⟨ε, hε, hball⟩ := hx0
  have hm : x0 + (ε / 2) • u l ∈ Metric.ball x0 ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu l, Real.norm_eq_abs,
      abs_of_pos (by linarith)]; linarith
  have := hball hm l
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hu l] at this
  linarith

lemma face_compact (hb : Bornology.IsBounded (halfspacePolyhedron u h)) (l : Fin v) :
    IsCompact (polyhedronFace u h l) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (P_closed u h).inter (isClosed_eq (by fun_prop) continuous_const)
  · exact hb.subset inter_subset_left

lemma cone_subset (x0 : E3) (hx0 : x0 ∈ halfspacePolyhedron u h) (l : Fin v) :
    cone x0 (polyhedronFace u h l) ⊆ halfspacePolyhedron u h := by
  rintro x ⟨y, hy, t, ht, rfl⟩
  have hy' : y ∈ halfspacePolyhedron u h := hy.1
  have := (P_convex u h).add_smul_sub_mem hx0 hy' ht
  exact this

end RLQAux


open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace RLQAux
open RovelliLQG

variable {v : ℕ} (u : Fin v → E3) (h : Fin v → ℝ)

lemma exit_point (hb : Bornology.IsBounded (halfspacePolyhedron u h)) (x0 : E3)
    (hx0 : x0 ∈ interior (halfspacePolyhedron u h)) (x : E3) (hx : x ∈ halfspacePolyhedron u h) :
    ∃ l, x ∈ cone x0 (polyhedronFace u h l) := by
  set P := halfspacePolyhedron u h with hP
  have hx0P : x0 ∈ P := interior_subset hx0
  set w : E3 := if x = x0 then EuclideanSpace.single 0 1 else x - x0 with hw
  have hw0 : w ≠ 0 := by
    rw [hw]; split_ifs with hxx
    · intro h0; have := congrArg (fun z : E3 => z 0) h0; simp at this
    · exact sub_ne_zero.mpr hxx
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set T : Set ℝ := {μ | 0 ≤ μ ∧ x0 + μ • w ∈ P} with hT
  have h0T : (0:ℝ) ∈ T := ⟨le_rfl, by simpa using hx0P⟩
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hbdd : BddAbove T := by
    refine ⟨(R + ‖x0‖) / ‖w‖, fun μ hμ => ?_⟩
    rw [le_div_iff₀ hwn]
    have h1 := hR hμ.2
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : ‖μ • w‖ ≤ ‖x0 + μ • w‖ + ‖x0‖ := by
      have := norm_sub_le (x0 + μ • w) x0
      simp only [add_sub_cancel_left] at this
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ.1] at h2
    linarith
  have hTc : IsClosed T := by
    apply IsClosed.inter isClosed_Ici
    exact (P_closed u h).preimage (by fun_prop)
  set μs := sSup T with hμs
  have hμT : μs ∈ T := hTc.csSup_mem ⟨0, h0T⟩ hbdd
  -- μs > 0
  have hμpos : 0 < μs := by
    have hx0' := hx0
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx0'
    obtain ⟨ε, hε, hball⟩ := hx0'
    have hm : ε / (2 * ‖w‖) ∈ T := by
      refine ⟨by positivity, hball ?_⟩
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      field_simp; linarith
    have := le_csSup hbdd hm
    have : 0 < ε / (2 * ‖w‖) := by positivity
    linarith
  set y := x0 + μs • w with hy
  have hyP : y ∈ P := hμT.2
  -- some constraint is tight at y
  have htight : ∃ l, ⟪u l, y⟫ = h l := by
    by_contra hall
    push_neg at hall
    have hlt : ∀ l, ⟪u l, y⟫ < h l := fun l => lt_of_le_of_ne (hyP l) (hall l)
    have hev : ∀ᶠ μ in 𝓝 μs, ∀ l, ⟪u l, x0 + μ • w⟫ < h l := by
      rw [eventually_all]
      intro l
      have hc : Continuous (fun μ : ℝ => ⟪u l, x0 + μ • w⟫) := by fun_prop
      exact hc.continuousAt.eventually (gt_mem_nhds (hlt l))
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hεP⟩ := hev
    have hm : μs + ε / 2 ∈ T := by
      refine ⟨by linarith, fun l => (hεP ?_ l).le⟩
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]; linarith
    have := le_csSup hbdd hm
    linarith
  obtain ⟨l, hl⟩ := htight
  refine ⟨l, y, ⟨hyP, hl⟩, ?_⟩
  by_cases hxx : x = x0
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hxx]; simp⟩
  · have hwx : w = x - x0 := by rw [hw, if_neg hxx]
    have h1T : (1:ℝ) ∈ T := ⟨zero_le_one, by rw [hwx, one_smul, add_sub_cancel]; exact hx⟩
    have h1 : 1 ≤ μs := le_csSup hbdd h1T
    refine ⟨1 / μs, ⟨by positivity, by rw [div_le_one hμpos]; exact h1⟩, ?_⟩
    rw [hy, add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ hμpos.ne', one_smul, hwx]
    abel

end RLQAux


open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace RLQAux
open RovelliLQG

variable {v : ℕ} (u : Fin v → E3) (h : Fin v → ℝ)

lemma t_le (x0 : E3) (l k : Fin v) (x y y' : E3) (hy : y ∈ polyhedronFace u h l)
    (hy' : y' ∈ polyhedronFace u h k) (t t' : ℝ) (ht' : 0 ≤ t') (ha : ⟪u l, x0⟫ < h l)
    (hx : x = x0 + t • (y - x0)) (hx' : x = x0 + t' • (y' - x0)) : t ≤ t' := by
  have e : t • (y - x0) = t' • (y' - x0) := by
    have := hx.symm.trans hx'; exact add_left_cancel this
  have e2 := congrArg (fun z => ⟪u l, z⟫) e
  simp only [inner_smul_right, inner_sub_right] at e2
  rw [hy.2] at e2
  have h3 : ⟪u l, y'⟫ ≤ h l := hy'.1 l
  have h4 : t' * (⟪u l, y'⟫ - ⟪u l, x0⟫) ≤ t' * (h l - ⟪u l, x0⟫) :=
    mul_le_mul_of_nonneg_left (by linarith) ht'
  have h5 : t * (h l - ⟪u l, x0⟫) ≤ t' * (h l - ⟪u l, x0⟫) := by linarith
  exact le_of_mul_le_mul_right h5 (by linarith)

lemma hyperplane_null (n c : E3) (hn : n ≠ 0) : volume {x : E3 | ⟪n, x - c⟫ = 0} = 0 := by
  have hS : (ℝ ∙ n)ᗮ ≠ ⊤ := by
    intro htop
    have : n ∈ (ℝ ∙ n)ᗮ := by rw [htop]; trivial
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq] at this
    exact hn (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this))
  have h0 := Measure.addHaar_submodule volume _ hS
  have : {x : E3 | ⟪n, x - c⟫ = 0} = (fun z => c + z) '' ((ℝ ∙ n)ᗮ : Set E3) := by
    ext x; simp only [mem_setOf_eq, mem_image, SetLike.mem_coe,
      Submodule.mem_orthogonal_singleton_iff_inner_right]
    constructor
    · intro hx; exact ⟨x - c, hx, by abel⟩
    · rintro ⟨z, hz, rfl⟩; simpa using hz
  rw [this, image_add_left, measure_preimage_add]
  exact h0

lemma inter_null (hu : ∀ l, ‖u l‖ = 1) (hinj : Function.Injective u) (x0 : E3)
    (hx0 : x0 ∈ interior (halfspacePolyhedron u h)) (l k : Fin v) (hlk : l ≠ k) :
    volume (cone x0 (polyhedronFace u h l) ∩ cone x0 (polyhedronFace u h k)) = 0 := by
  have hal := int_strict u h x0 hx0 hu l
  have hak := int_strict u h x0 hx0 hu k
  set a := h l - ⟪u l, x0⟫
  set b := h k - ⟪u k, x0⟫
  have ha : 0 < a := by simp only [a]; linarith
  have hb : 0 < b := by simp only [b]; linarith
  set n := b • u l - a • u k with hn
  have hn0 : n ≠ 0 := by
    intro h0
    rw [hn, sub_eq_zero] at h0
    have hn1 := congrArg norm h0
    rw [norm_smul, norm_smul, hu l, hu k, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha,
      abs_of_pos hb] at hn1
    simp only [mul_one] at hn1
    rw [hn1] at h0
    exact hlk (hinj (smul_right_injective E3 ha.ne' h0))
  apply measure_mono_null _ (hyperplane_null n x0 hn0)
  rintro x ⟨⟨y, hy, t, ht, hx⟩, ⟨y', hy', t', ht', hx'⟩⟩
  have htt : t = t' := le_antisymm (t_le u h x0 l k x y y' hy hy' t t' ht'.1 hal hx hx')
    (t_le u h x0 k l x y' y hy' hy t' t ht.1 hak hx' hx)
  simp only [mem_setOf_eq, hn, inner_sub_left, inner_smul_left, conj_trivial]
  have e1 : ⟪u l, x - x0⟫ = t * a := by
    rw [hx, add_sub_cancel_left, inner_smul_right, inner_sub_right, hy.2]
  have e2 : ⟪u k, x - x0⟫ = t' * b := by
    rw [hx', add_sub_cancel_left, inner_smul_right, inner_sub_right, hy'.2]
  rw [e1, e2, htt]; ring

end RLQAux


open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace RLQAux
open RovelliLQG

variable {v : ℕ} (u : Fin v → E3) (h : Fin v → ℝ)

lemma area_lt_top (hb : Bornology.IsBounded (halfspacePolyhedron u h)) (l : Fin v) :
    planarArea (u l) (polyhedronFace u h l) < ⊤ := by
  unfold planarArea
  exact ((face_compact u h hb l).image (Submodule.orthogonalProjectionOnto (ℝ ∙ u l)ᗮ).continuous).measure_lt_top

lemma vol_P (hu : ∀ l, ‖u l‖ = 1) (hinj : Function.Injective u)
    (hb : Bornology.IsBounded (halfspacePolyhedron u h)) (x0 : E3)
    (hx0 : x0 ∈ interior (halfspacePolyhedron u h)) :
    volume (halfspacePolyhedron u h) =
      ∑ l, ENNReal.ofReal ((h l - ⟪u l, x0⟫) / 3) * planarArea (u l) (polyhedronFace u h l) := by
  have hx0P : x0 ∈ halfspacePolyhedron u h := interior_subset hx0
  have hU : halfspacePolyhedron u h = ⋃ l ∈ (Finset.univ : Finset (Fin v)), cone x0 (polyhedronFace u h l) := by
    ext x; simp only [Finset.mem_univ, iUnion_true, mem_iUnion]
    constructor
    · exact fun hx => exit_point u h hb x0 hx0 x hx
    · rintro ⟨l, hl⟩; exact cone_subset u h x0 hx0P l hl
  rw [hU, measure_biUnion_finset₀]
  · congr 1; funext l
    exact cone_vol (u l) (hu l) x0 _ (face_compact u h hb l) (h l) (fun y hy => hy.2)
      (int_strict u h x0 hx0 hu l)
  · intro l _ k _ hlk
    exact inter_null u h hu hinj x0 hx0 l k hlk
  · intro l _
    exact (cone_compact x0 _ (face_compact u h hb l)).isClosed.measurableSet.nullMeasurableSet

theorem closure_thm (hu : ∀ l, ‖u l‖ = 1) (hinj : Function.Injective u)
    (hb : Bornology.IsBounded (halfspacePolyhedron u h))
    (hint : (interior (halfspacePolyhedron u h)).Nonempty) :
    ∑ l, (planarArea (u l) (polyhedronFace u h l)).toReal • u l = 0 := by
  set A : Fin v → ℝ := fun l => (planarArea (u l) (polyhedronFace u h l)).toReal with hA
  have hfin := area_lt_top u h hb
  have key : ∀ x0 ∈ interior (halfspacePolyhedron u h),
      (volume (halfspacePolyhedron u h)).toReal = ∑ l, (h l - ⟪u l, x0⟫) / 3 * A l := by
    intro x0 hx0
    rw [vol_P u h hu hinj hb x0 hx0, ENNReal.toReal_sum]
    · congr 1; funext l
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal]
      have := int_strict u h x0 hx0 hu l
      apply div_nonneg <;> linarith
    · intro l _
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin l).ne
  obtain ⟨x0, hx0⟩ := hint
  have hopen : IsOpen (interior (halfspacePolyhedron u h)) := isOpen_interior
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hball⟩ := hopen x0 hx0
  have horth : ∀ w : E3, ∑ l, A l * ⟪u l, w⟫ = 0 := by
    intro w
    set c := ε / (2 * (‖w‖ + 1)) with hc
    have hcpos : 0 < c := by positivity
    have hx1 : x0 + c • w ∈ interior (halfspacePolyhedron u h) := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hcpos, hc]
      have h1 : ‖w‖ < ‖w‖ + 1 := by linarith
      calc ε / (2 * (‖w‖ + 1)) * ‖w‖ ≤ ε / (2 * (‖w‖ + 1)) * (‖w‖ + 1) := by gcongr
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    have e := (key x0 hx0).symm.trans (key _ hx1)
    have e2 : ∑ l, (h l - ⟪u l, x0 + c • w⟫) / 3 * A l =
        ∑ l, (h l - ⟪u l, x0⟫) / 3 * A l - c / 3 * ∑ l, A l * ⟪u l, w⟫ := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1; funext l
      rw [inner_add_right, inner_smul_right]; ring
    rw [e2] at e
    have : c / 3 * ∑ l, A l * ⟪u l, w⟫ = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exfalso; have : 0 < c / 3 := by positivity
      linarith
    · exact h0
  set V := ∑ l, A l • u l with hV
  have hVV : ⟪V, V⟫ = 0 := by
    rw [hV, sum_inner]
    simp only [inner_smul_left, conj_trivial]
    exact horth _
  exact inner_self_eq_zero.mp hVV

end RLQAux

open scoped InnerProductSpace in
theorem solution {v : ℕ} (u : Fin v → RovelliLQG.E3) (hu : ∀ l, ‖u l‖ = 1)
    (hinj : Function.Injective u) (h : Fin v → ℝ)
    (hbdd : Bornology.IsBounded (RovelliLQG.halfspacePolyhedron u h))
    (hint : (interior (RovelliLQG.halfspacePolyhedron u h)).Nonempty) :
    ∑ l, (RovelliLQG.planarArea (u l) (RovelliLQG.polyhedronFace u h l)).toReal • u l = 0 :=
  RLQAux.closure_thm u h hu hinj hbdd hint
