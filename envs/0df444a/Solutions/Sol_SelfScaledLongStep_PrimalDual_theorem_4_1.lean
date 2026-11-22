-- Prove2me | solution 1 for SelfScaledLongStep.PrimalDual.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:50:34.498142+00:00
-- url     : https://prove2.me/submissions/926ebf53-1481-4988-ad1d-d3b423e901be

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep Filter Topology

section Helpers

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### Section 1: Proper cone and `sigma` properties -/

private lemma cone_add_mem {K : Set E} (hK : IsProperCone K) {a b : E}
    (ha : a ∈ K) (hb : b ∈ K) : a + b ∈ K := by
  have hconv := hK.2.1 ha hb (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hsmul := hK.2.2.1 _ hconv 2 (by norm_num)
  have heq : (2 : ℝ) • ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) = a + b := by
    rw [smul_add, smul_smul, smul_smul]
    norm_num
  rwa [heq] at hsmul

private lemma cone_smul_interior {K : Set E} (hK : IsProperCone K) {a : E} {t : ℝ}
    (ha : a ∈ interior K) (ht : 0 < t) : t • a ∈ interior K := by
  let hhomeo : Homeomorph E E := Homeomorph.smulOfNeZero t ht.ne'
  have hsub : hhomeo '' K ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hK.2.2.1 y hy t ht.le
  have hmem : t • a ∈ interior (hhomeo '' K) := by
    rw [← hhomeo.image_interior]
    exact ⟨a, ha, rfl⟩
  exact interior_mono hsub hmem

private lemma cone_interior_add_mem {K : Set E} (hK : IsProperCone K) {a b : E}
    (ha : a ∈ interior K) (hb : b ∈ K) : a + b ∈ interior K := by
  have hsub : (fun y => y + b) '' K ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact cone_add_mem hK hy hb
  have hopen : IsOpen ((fun y => y + b) '' interior K) :=
    (Homeomorph.addRight b).isOpenMap _ isOpen_interior
  have hsub' : (fun y => y + b) '' interior K ⊆ K :=
    (Set.image_mono interior_subset).trans hsub
  exact interior_maximal hsub' hopen ⟨a, ha, rfl⟩

private lemma sigma_nonneg_and_mem {K : Set E} (hK : IsProperCone K) {x : E}
    (hx : x ∈ interior K) (p : E) :
    0 ≤ sigma K x p ∧ sigma K x p • x - p ∈ K := by
  set S : Set ℝ := {β : ℝ | 0 ≤ β ∧ β • x - p ∈ K}
  have hS_ne : S.Nonempty := by
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    set β : ℝ := (‖p‖ + 1) / (r / 2)
    have hβ_pos : 0 < β := by positivity
    refine ⟨β, hβ_pos.le, ?_⟩
    have hball : x - β⁻¹ • p ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ_pos)]
      have h1 : β⁻¹ * ‖p‖ = (r / 2) * (‖p‖ / (‖p‖ + 1)) := by
        dsimp [β]; field_simp
      rw [h1]
      have h2 : ‖p‖ / (‖p‖ + 1) < 1 := by
        rw [div_lt_one (by positivity : (0 : ℝ) < ‖p‖ + 1)]
        linarith
      nlinarith
    have hmem : x - β⁻¹ • p ∈ K := interior_subset (hr_sub hball)
    have hsmul := hK.2.2.1 _ hmem β hβ_pos.le
    have heq : β • (x - β⁻¹ • p) = β • x - p := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hβ_pos.ne', one_smul]
    rwa [heq] at hsmul
  have hS_bdd : BddBelow S := ⟨0, fun _ h => h.1⟩
  have hS_closed : IsClosed S := by
    have h1 : IsClosed {β : ℝ | (0 : ℝ) ≤ β} := isClosed_Ici
    have h2 : IsClosed {β : ℝ | β • x - p ∈ K} :=
      hK.1.preimage ((continuous_id.smul continuous_const).sub continuous_const)
    exact h1.inter h2
  exact hS_closed.csInf_mem hS_ne hS_bdd

private lemma step_mem_interior {K : Set E} (hK : IsProperCone K) {x p : E}
    (hx : x ∈ interior K) {t : ℝ} (ht0 : 0 ≤ t) (ht : t * sigma K x p < 1) :
    x - t • p ∈ interior K := by
  obtain ⟨_, hmem⟩ := sigma_nonneg_and_mem hK hx p
  have h1 : (1 - t * sigma K x p) • x ∈ interior K :=
    cone_smul_interior hK hx (by linarith)
  have h2 : t • (sigma K x p • x - p) ∈ K :=
    hK.2.2.1 _ hmem t ht0
  have heq : (1 - t * sigma K x p) • x + t • (sigma K x p • x - p) = x - t • p := by
    rw [sub_smul, one_smul, smul_sub, smul_smul]
    abel
  rw [← heq]
  exact cone_interior_add_mem hK h1 h2

private lemma dualCone_interior_coercive {K : Set E} {s : E}
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    ∃ c > 0, ∀ y ∈ K, c * ‖y‖ ≤ ⟪s, y⟫_ℝ := by
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp isOpen_interior s hs
  refine ⟨r / 2, by positivity, fun y hy => ?_⟩
  by_cases hy0 : y = 0
  · simp [hy0]
  · have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    set u : E := s - ((r / 2) / ‖y‖) • y
    have hu_ball : u ∈ Metric.ball s r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : u - s = -(((r / 2) / ‖y‖) • y) := by simp [u]
      rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_mul_cancel₀ _ hny.ne']
      linarith
    have hu_dual : u ∈ ConvexOptimization.dualCone K := interior_subset (hr_sub hu_ball)
    have h0 : 0 ≤ ⟪y, u⟫_ℝ := hu_dual y hy
    have hcalc : ⟪y, u⟫_ℝ = ⟪s, y⟫_ℝ - (r / 2) * ‖y‖ := by
      dsimp [u]
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
        real_inner_comm y s]
      field_simp [hny.ne']
    linarith

/-! ### Section 2: Calculus, symmetry, and logarithmic homogeneity identities -/

private lemma contDiffAt_F {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) :
    ContDiffAt ℝ 3 F x :=
  hF.1.2.1.contDiffAt (isOpen_interior.mem_nhds hx)

private lemma contDiffAt_gradient_F {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) :
    ContDiffAt ℝ 2 (gradient F) x := by
  have h1 : ContDiffAt ℝ 2 (fderiv ℝ F) x :=
    (contDiffAt_F hF hx).fderiv_right (by norm_num)
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.contDiff.contDiffAt).comp x h1

private lemma contDiffAt_hess_F {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) :
    ContDiffAt ℝ 1 (hess F) x :=
  (contDiffAt_gradient_F hF hx).fderiv_right (by norm_num)

private lemma hasFDerivAt_F {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) :
    HasFDerivAt F (InnerProductSpace.toDual ℝ E (gradient F x)) x := by
  have hd : DifferentiableAt ℝ F x := (contDiffAt_F hF hx).differentiableAt (by norm_num)
  rw [← hasGradientAt_iff_hasFDerivAt]
  exact hd.hasGradientAt

private lemma hasFDerivAt_gradient_F {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) :
    HasFDerivAt (gradient F) (hess F x) x :=
  ((contDiffAt_gradient_F hF hx).differentiableAt (by norm_num)).hasFDerivAt

private lemma hasFDerivAt_hess_F {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) :
    HasFDerivAt (hess F) (fderiv ℝ (hess F) x) x :=
  ((contDiffAt_hess_F hF hx).differentiableAt (by norm_num)).hasFDerivAt

private lemma inner_hess_symm {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) (u v : E) :
    ⟪hess F x u, v⟫_ℝ = ⟪u, hess F x v⟫_ℝ := by
  have hsymm : IsSymmSndFDerivAt ℝ F x :=
    (contDiffAt_F hF hx).isSymmSndFDerivAt (by simp; decide)
  have hfg : fderiv ℝ (fderiv ℝ F) x =
      (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp (hess F x) := by
    have hgrad_eq : fderiv ℝ F = fun y => InnerProductSpace.toDual ℝ E (gradient F y) := by
      ext y h
      simp [gradient]
    rw [hgrad_eq]
    exact (((InnerProductSpace.toDual ℝ E).toContinuousLinearMap.hasFDerivAt).comp x
      (hasFDerivAt_gradient_F hF hx)).fderiv
  have h1 : ⟪hess F x u, v⟫_ℝ = fderiv ℝ (fderiv ℝ F) x u v := by
    rw [hfg]; simp [InnerProductSpace.toDual_apply_apply]
  have h2 : ⟪u, hess F x v⟫_ℝ = fderiv ℝ (fderiv ℝ F) x v u := by
    rw [real_inner_comm, hfg]; simp [InnerProductSpace.toDual_apply_apply]
  rw [h1, h2, hsymm.eq]

private lemma hess_symmetric {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) :
    (hess F x).toLinearMap.IsSymmetric :=
  fun u v => inner_hess_symm hF hx u v

private lemma thirdDeriv_symm_12 {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) (u v w : E) :
    ⟪fderiv ℝ (hess F) x u v, w⟫_ℝ = ⟪fderiv ℝ (hess F) x v u, w⟫_ℝ := by
  set g : E → ℝ := fun y => ⟪gradient F y, w⟫_ℝ
  have hg_c2 : ContDiffAt ℝ 2 g x :=
    (contDiffAt_gradient_F hF hx).inner ℝ contDiffAt_const
  have hg_symm : IsSymmSndFDerivAt ℝ g x :=
    hg_c2.isSymmSndFDerivAt (by simp)
  have hfderiv_g : ∀ᶠ y in 𝓝 x,
      fderiv ℝ g y = (InnerProductSpace.toDual ℝ E w).comp (hess F y) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    have h1 : HasFDerivAt g ((InnerProductSpace.toDual ℝ E w).comp (hess F y)) y := by
      have : g = fun z => InnerProductSpace.toDual ℝ E w (gradient F z) := by
        ext z; simp [g, InnerProductSpace.toDual_apply_apply]
      rw [this]
      exact (InnerProductSpace.toDual ℝ E w).hasFDerivAt.comp y (hasFDerivAt_gradient_F hF hy)
    exact h1.fderiv
  have h2nd : HasFDerivAt (fderiv ℝ g)
      ((ContinuousLinearMap.compL ℝ E E ℝ (InnerProductSpace.toDual ℝ E w)).comp
        (fderiv ℝ (hess F) x)) x := by
    have hcomp := (ContinuousLinearMap.compL ℝ E E ℝ
      (InnerProductSpace.toDual ℝ E w)).hasFDerivAt.comp x (hasFDerivAt_hess_F hF hx)
    exact hcomp.congr_of_eventuallyEq hfderiv_g
  have hval : ∀ a b : E, fderiv ℝ (fderiv ℝ g) x a b = ⟪fderiv ℝ (hess F) x a b, w⟫_ℝ := by
    intro a b
    rw [h2nd.fderiv]
    simp [InnerProductSpace.toDual_apply_apply, real_inner_comm]
  rw [← hval u v, ← hval v u, hg_symm.eq]

private lemma thirdDeriv_symm_23 {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) (u v w : E) :
    ⟪fderiv ℝ (hess F) x u v, w⟫_ℝ = ⟪fderiv ℝ (hess F) x u w, v⟫_ℝ := by
  have heq : (fun y => ⟪hess F y v, w⟫_ℝ) =ᶠ[𝓝 x] (fun y => ⟪hess F y w, v⟫_ℝ) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [inner_hess_symm hF hy v w, real_inner_comm]
  have hleft : HasFDerivAt (fun y => ⟪hess F y v, w⟫_ℝ)
      (((InnerProductSpace.toDual ℝ E w).comp (ContinuousLinearMap.apply ℝ E v)).comp
        (fderiv ℝ (hess F) x)) x := by
    have : (fun y => ⟪hess F y v, w⟫_ℝ) =
        fun y => ((InnerProductSpace.toDual ℝ E w).comp (ContinuousLinearMap.apply ℝ E v)) (hess F y) := by
      ext y; simp [InnerProductSpace.toDual_apply_apply, real_inner_comm]
    rw [this]
    exact ((InnerProductSpace.toDual ℝ E w).comp
      (ContinuousLinearMap.apply ℝ E v)).hasFDerivAt.comp x (hasFDerivAt_hess_F hF hx)
  have hright : HasFDerivAt (fun y => ⟪hess F y w, v⟫_ℝ)
      (((InnerProductSpace.toDual ℝ E v).comp (ContinuousLinearMap.apply ℝ E w)).comp
        (fderiv ℝ (hess F) x)) x := by
    have : (fun y => ⟪hess F y w, v⟫_ℝ) =
        fun y => ((InnerProductSpace.toDual ℝ E v).comp (ContinuousLinearMap.apply ℝ E w)) (hess F y) := by
      ext y; simp [InnerProductSpace.toDual_apply_apply, real_inner_comm]
    rw [this]
    exact ((InnerProductSpace.toDual ℝ E v).comp
      (ContinuousLinearMap.apply ℝ E w)).hasFDerivAt.comp x (hasFDerivAt_hess_F hF hx)
  have hsame := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  have hu := congr_arg (fun L => L u) hsame
  simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using hu

private lemma gradient_hom {K : Set E} (hK : IsProperCone K) {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) {τ : ℝ} (hτ : 0 < τ) :
    gradient F (τ • x) = τ⁻¹ • gradient F x := by
  have hτx : τ • x ∈ interior K := cone_smul_interior hK hx hτ
  have heq : (fun y => F (τ • y)) =ᶠ[𝓝 x] (fun y => F y - ν * Real.log τ) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact hF.2.2.2.1 y hy τ hτ
  have h1 : HasFDerivAt (fun y => F (τ • y))
      ((fderiv ℝ F (τ • x)).comp (τ • ContinuousLinearMap.id ℝ E)) x := by
    have hd : DifferentiableAt ℝ F (τ • x) :=
      (contDiffAt_F hF hτx).differentiableAt (by norm_num)
    exact hd.hasFDerivAt.comp x (τ • ContinuousLinearMap.id ℝ E).hasFDerivAt
  have h2 : HasFDerivAt (fun y => F y - ν * Real.log τ) (fderiv ℝ F x) x := by
    have hd : DifferentiableAt ℝ F x := (contDiffAt_F hF hx).differentiableAt (by norm_num)
    simpa using hd.hasFDerivAt.sub_const (ν * Real.log τ)
  have hsame := (h1.congr_of_eventuallyEq heq.symm).unique h2
  apply ext_inner_right ℝ
  intro h
  have hh := congr_arg (fun L => L h) hsame
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.id_apply, ← inner_gradient_left] at hh
  rw [inner_smul_right] at hh
  rw [inner_smul_left]
  simp only [conj_trivial]
  field_simp [hτ.ne'] at hh ⊢
  linarith

private lemma hess_hom {K : Set E} (hK : IsProperCone K) {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) {τ : ℝ} (hτ : 0 < τ) :
    hess F (τ • x) = τ⁻¹ ^ 2 • hess F x := by
  have hτx : τ • x ∈ interior K := cone_smul_interior hK hx hτ
  have heq : (fun y => gradient F (τ • y)) =ᶠ[𝓝 x] (fun y => τ⁻¹ • gradient F y) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact gradient_hom hK hF hy hτ
  have h1 : HasFDerivAt (fun y => gradient F (τ • y))
      ((hess F (τ • x)).comp (τ • ContinuousLinearMap.id ℝ E)) x :=
    (hasFDerivAt_gradient_F hF hτx).comp x (τ • ContinuousLinearMap.id ℝ E).hasFDerivAt
  have h2 : HasFDerivAt (fun y => τ⁻¹ • gradient F y) (τ⁻¹ • hess F x) x :=
    (hasFDerivAt_gradient_F hF hx).const_smul τ⁻¹
  have hsame := (h1.congr_of_eventuallyEq heq.symm).unique h2
  apply ContinuousLinearMap.ext
  intro h
  have hh := congr_arg (fun L => L h) hsame
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.id_apply] at hh
  rw [map_smul] at hh
  have h3 := congr_arg (fun z => τ⁻¹ • z) hh
  rw [smul_smul, inv_mul_cancel₀ hτ.ne', one_smul, smul_smul, ← sq] at h3
  simpa using h3

private lemma inner_gradient_self {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) :
    ⟪gradient F x, x⟫_ℝ = -ν := by
  have heq : (fun t : ℝ => F (t • x)) =ᶠ[𝓝 (1 : ℝ)] (fun t : ℝ => F x - ν * Real.log t) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hF.2.2.2.1 x hx t ht
  have h1 : HasDerivAt (fun t : ℝ => F (t • x)) ⟪gradient F x, x⟫_ℝ 1 := by
    have hline : HasDerivAt (fun t : ℝ => t • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have hfd : HasFDerivAt F (InnerProductSpace.toDual ℝ E (gradient F x)) ((1 : ℝ) • x) := by
      simpa using hasFDerivAt_F hF hx
    have hd := hfd.comp_hasDerivAt (1 : ℝ) hline
    rwa [InnerProductSpace.toDual_apply_apply] at hd
  have h2 : HasDerivAt (fun t : ℝ => F x - ν * Real.log t) (-ν) 1 := by
    have hl : HasDerivAt Real.log (1 : ℝ)⁻¹ 1 := Real.hasDerivAt_log one_ne_zero
    have := (hl.const_mul ν).const_sub (F x)
    simpa using this
  exact (h1.congr_of_eventuallyEq heq.symm).unique h2

private lemma hess_apply_self {K : Set E} (hK : IsProperCone K) {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) :
    hess F x x = -gradient F x := by
  have heq : (fun t : ℝ => gradient F (t • x)) =ᶠ[𝓝 (1 : ℝ)] (fun t : ℝ => t⁻¹ • gradient F x) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    exact gradient_hom hK hF hx ht
  have h1 : HasDerivAt (fun t : ℝ => gradient F (t • x)) (hess F x x) 1 := by
    have hline : HasDerivAt (fun t : ℝ => t • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have hfd : HasFDerivAt (gradient F) (hess F x) ((1 : ℝ) • x) := by
      simpa using hasFDerivAt_gradient_F hF hx
    exact hfd.comp_hasDerivAt (1 : ℝ) hline
  have h2 : HasDerivAt (fun t : ℝ => t⁻¹ • gradient F x) (-gradient F x) 1 := by
    have hi : HasDerivAt (fun t : ℝ => t⁻¹) (-1 : ℝ) 1 := by
      simpa using (hasDerivAt_inv (one_ne_zero : (1 : ℝ) ≠ 0))
    simpa using hi.smul_const (gradient F x)
  exact (h1.congr_of_eventuallyEq heq.symm).unique h2

private lemma thirdDeriv_apply_self {K : Set E} (hK : IsProperCone K) {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : E} (hx : x ∈ interior K) :
    fderiv ℝ (hess F) x x = (-2 : ℝ) • hess F x := by
  have heq : (fun t : ℝ => hess F (t • x)) =ᶠ[𝓝 (1 : ℝ)] (fun t : ℝ => t⁻¹ ^ 2 • hess F x) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hess_hom hK hF hx ht
  have h1 : HasDerivAt (fun t : ℝ => hess F (t • x)) (fderiv ℝ (hess F) x x) 1 := by
    have hline : HasDerivAt (fun t : ℝ => t • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have hfd : HasFDerivAt (hess F) (fderiv ℝ (hess F) x) ((1 : ℝ) • x) := by
      simpa using hasFDerivAt_hess_F hF hx
    exact hfd.comp_hasDerivAt (1 : ℝ) hline
  have h2 : HasDerivAt (fun t : ℝ => t⁻¹ ^ 2 • hess F x) ((-2 : ℝ) • hess F x) 1 := by
    have hi : HasDerivAt (fun t : ℝ => t⁻¹) (-1 : ℝ) 1 := by
      simpa using (hasDerivAt_inv (one_ne_zero : (1 : ℝ) ≠ 0))
    have hsq : HasDerivAt (fun t : ℝ => t⁻¹ ^ 2) (-2 : ℝ) 1 := by
      have hp := hi.fun_pow 2
      have hval : ((2 : ℕ) : ℝ) * (1 : ℝ)⁻¹ ^ (2 - 1) * (-1 : ℝ) = -2 := by norm_num
      rwa [hval] at hp
    exact hsq.smul_const (hess F x)
  exact (h1.congr_of_eventuallyEq heq.symm).unique h2

private lemma convex_gradient_le {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x y : E} (hx : x ∈ interior K) (hy : y ∈ interior K) :
    F x + ⟪gradient F x, y - x⟫_ℝ ≤ F y := by
  set φ : ℝ → ℝ := fun t => F (x + t • (y - x))
  have hderiv : HasDerivAt φ ⟪gradient F x, y - x⟫_ℝ 0 := by
    have hline : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • (y - x)) (y - x) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const (y - x)
      exact h1.const_add x
    have hfd : HasFDerivAt F (InnerProductSpace.toDual ℝ E (gradient F x)) (x + (0 : ℝ) • (y - x)) := by
      simpa using hasFDerivAt_F hF hx
    have hd := hfd.comp_hasDerivAt (0 : ℝ) hline
    rwa [InnerProductSpace.toDual_apply_apply] at hd
  have hslope : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (φ t - φ 0) / t ≤ F y - F x := by
    intro t ⟨ht0, ht1⟩
    have hconv := hF.1.1.2 hx hy (show (0 : ℝ) ≤ 1 - t by linarith) ht0.le (by ring)
    have hpt : (1 - t) • x + t • y = x + t • (y - x) := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rw [hpt] at hconv
    have hφ0 : φ 0 = F x := by simp [φ]
    rw [hφ0, div_le_iff₀ ht0]
    simp only [smul_eq_mul] at hconv
    linarith
  have htend : Tendsto (fun t : ℝ => (φ t - φ 0) / t) (𝓝[>] 0) (𝓝 ⟪gradient F x, y - x⟫_ℝ) := by
    have h := hderiv.tendsto_slope_zero_right
    simpa [slope_def_field, smul_eq_mul, div_eq_inv_mul] using h
  have hle : ⟪gradient F x, y - x⟫_ℝ ≤ F y - F x := by
    refine le_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hslope t ht
  linarith

private lemma convex_gradient_mono {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x y : E} (hx : x ∈ interior K) (hy : y ∈ interior K) :
    0 ≤ ⟪gradient F x - gradient F y, x - y⟫_ℝ := by
  have h1 := convex_gradient_le hF hx hy
  have h2 := convex_gradient_le hF hy hx
  rw [inner_sub_left]
  have hneg : ⟪gradient F x, y - x⟫_ℝ = -⟪gradient F x, x - y⟫_ℝ := by
    rw [← inner_neg_right, neg_sub]
  linarith

/-! ### Section 3: Symmetric positive definite operators & Theorem 3.1(ii) -/

private lemma spd_equiv {H : E →L[ℝ] E} (hsym : H.toLinearMap.IsSymmetric)
    (hpd : ∀ u : E, u ≠ 0 → 0 < ⟪H u, u⟫_ℝ) :
    ∃ e : E ≃L[ℝ] E,
      e.toContinuousLinearMap = H ∧
      e.symm.toContinuousLinearMap.toLinearMap.IsSymmetric ∧
      (∀ u : E, u ≠ 0 → 0 < ⟪e.symm u, u⟫_ℝ) := by
  have hinj : Function.Injective H.toLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    by_contra hu0
    have hpos := hpd u hu0
    change 0 < ⟪H.toLinearMap u, u⟫_ℝ at hpos
    rw [hu, inner_zero_left] at hpos
    exact lt_irrefl 0 hpos
  have hbij : Function.Bijective H.toLinearMap :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let leq : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective H.toLinearMap hbij
  let e : E ≃L[ℝ] E := leq.toContinuousLinearEquiv
  refine ⟨e, ?_, ?_, ?_⟩
  · ext u; rfl
  · intro u v
    have h1 : e (e.symm u) = u := e.apply_symm_apply u
    have h2 : e (e.symm v) = v := e.apply_symm_apply v
    have he : ∀ z, e z = H z := fun _ => rfl
    change ⟪e.symm u, v⟫_ℝ = ⟪u, e.symm v⟫_ℝ
    conv_lhs => rw [← h2, he]
    conv_rhs => rw [← h1, he]
    exact (hsym (e.symm u) (e.symm v)).symm
  · intro u hu
    have hsu : e.symm u ≠ 0 := by
      intro h0
      have := congr_arg e h0
      rw [e.apply_symm_apply, map_zero] at this
      exact hu this
    have hpos := hpd (e.symm u) hsu
    have he : H (e.symm u) = u := e.apply_symm_apply u
    rw [he, real_inner_comm] at hpos
    exact hpos

private lemma spd_sqrt {C : E →L[ℝ] E} (hsym : C.toLinearMap.IsSymmetric)
    (hpd : ∀ u : E, u ≠ 0 → 0 < ⟪C u, u⟫_ℝ) :
    ∃ S : E →L[ℝ] E,
      S.toLinearMap.IsSymmetric ∧
      (∀ u : E, u ≠ 0 → 0 < ⟪S u, u⟫_ℝ) ∧
      S.comp S = C := by
  have hn : Module.finrank ℝ E = n := finrank_euclideanSpace_fin
  let b : OrthonormalBasis (Fin n) ℝ E := hsym.eigenvectorBasis hn
  let lam : Fin n → ℝ := hsym.eigenvalues hn
  have hlam_pos : ∀ i, 0 < lam i := by
    intro i
    have hbi0 : b i ≠ 0 := by
      intro h0
      have := b.orthonormal.1 i
      rw [h0, norm_zero] at this
      norm_num at this
    have hpos := hpd (b i) hbi0
    have happ : C (b i) = lam i • b i := hsym.apply_eigenvectorBasis hn i
    rw [happ, inner_smul_left, real_inner_self_eq_norm_sq, b.orthonormal.1 i] at hpos
    simpa using hpos
  let S : E →L[ℝ] E :=
    ∑ i : Fin n, (Real.sqrt (lam i) • (InnerProductSpace.toDual ℝ E (b i))).smulRight (b i)
  have hS_apply : ∀ u : E, S u = ∑ i : Fin n, (Real.sqrt (lam i) * ⟪b i, u⟫_ℝ) • b i := by
    intro u
    simp [S, InnerProductSpace.toDual_apply_apply]
  have hS_basis : ∀ j : Fin n, S (b j) = Real.sqrt (lam j) • b j := by
    intro j
    rw [hS_apply]
    rw [Finset.sum_eq_single j]
    · simp [b.orthonormal.1 j]
    · intro i _ hij
      simp [b.orthonormal.2 hij]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  refine ⟨S, ?_, ?_, ?_⟩
  · intro u v
    change ⟪S u, v⟫_ℝ = ⟪u, S v⟫_ℝ
    rw [hS_apply u, hS_apply v, sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_left, inner_smul_right, real_inner_comm (b i) u]
    simp only [conj_trivial]
    ring
  · intro u hu
    rw [hS_apply, sum_inner]
    have hterm : ∀ i : Fin n,
        ⟪(Real.sqrt (lam i) * ⟪b i, u⟫_ℝ) • b i, u⟫_ℝ =
          Real.sqrt (lam i) * (⟪b i, u⟫_ℝ) ^ 2 := by
      intro i
      rw [inner_smul_left]
      simp only [conj_trivial]
      ring
    simp_rw [hterm]
    have hex : ∃ i : Fin n, ⟪b i, u⟫_ℝ ≠ 0 := by
      by_contra hall
      push Not at hall
      have hrepr : ∑ i : Fin n, ⟪b i, u⟫_ℝ • b i = u := b.sum_repr' u
      simp [hall] at hrepr
      exact hu hrepr.symm
    obtain ⟨i₀, hi₀⟩ := hex
    exact Finset.sum_pos'
      (fun i _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
      ⟨i₀, Finset.mem_univ i₀,
        mul_pos (Real.sqrt_pos.mpr (hlam_pos i₀)) (sq_pos_of_ne_zero hi₀)⟩
  · apply ContinuousLinearMap.ext
    intro u
    rw [← b.sum_repr' u]
    simp only [ContinuousLinearMap.comp_apply, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hS_basis j, map_smul, hS_basis j, smul_smul, smul_smul, mul_assoc,
      Real.mul_self_sqrt (hlam_pos j).le]
    have happ : C (b j) = lam j • b j := hsym.apply_eigenvectorBasis hn j
    rw [happ, smul_smul]

private lemma spd_sq_inj {M N : E →L[ℝ] E}
    (hMsym : M.toLinearMap.IsSymmetric) (hMpd : ∀ u : E, u ≠ 0 → 0 < ⟪M u, u⟫_ℝ)
    (hNsym : N.toLinearMap.IsSymmetric) (hNpd : ∀ u : E, u ≠ 0 → 0 < ⟪N u, u⟫_ℝ)
    (hsq : M.comp M = N.comp N) : M = N := by
  have hn : Module.finrank ℝ E = n := finrank_euclideanSpace_fin
  let D : E →L[ℝ] E := M - N
  have hDsym : D.toLinearMap.IsSymmetric := hMsym.sub hNsym
  let b : OrthonormalBasis (Fin n) ℝ E := hDsym.eigenvectorBasis hn
  let μ : Fin n → ℝ := hDsym.eigenvalues hn
  have hμ0 : ∀ i : Fin n, μ i = 0 := by
    intro i
    set u : E := b i
    have hu0 : u ≠ 0 := by
      intro h0
      have hnorm : ‖u‖ = 1 := b.orthonormal.1 i
      rw [h0, norm_zero] at hnorm
      norm_num at hnorm
    have hDu : M u - N u = μ i • u := hDsym.apply_eigenvectorBasis hn i
    have hinner1 : ⟪M u + N u, M u - N u⟫_ℝ = μ i * (⟪M u, u⟫_ℝ + ⟪N u, u⟫_ℝ) := by
      rw [hDu, inner_smul_right, inner_add_left]
    have hinner2 : ⟪M u + N u, M u - N u⟫_ℝ = 0 := by
      rw [inner_add_left, inner_sub_right, inner_sub_right, real_inner_comm (N u) (M u)]
      have hMM : ⟪M u, M u⟫_ℝ = ⟪(M.comp M) u, u⟫_ℝ := (hMsym (M u) u).symm
      have hNN : ⟪N u, N u⟫_ℝ = ⟪(N.comp N) u, u⟫_ℝ := (hNsym (N u) u).symm
      rw [hMM, hNN, hsq]
      ring
    have hpos : 0 < ⟪M u, u⟫_ℝ + ⟪N u, u⟫_ℝ := add_pos (hMpd u hu0) (hNpd u hu0)
    have hmul : μ i * (⟪M u, u⟫_ℝ + ⟪N u, u⟫_ℝ) = 0 := hinner1.symm.trans hinner2
    exact (mul_eq_zero.mp hmul).resolve_right hpos.ne'
  have hD0 : D = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    rw [← b.sum_repr' u, map_sum]
    simp only [map_smul, zero_apply]
    apply Finset.sum_eq_zero
    intro i _
    have happ : D (b i) = μ i • b i := hDsym.apply_eigenvectorBasis hn i
    rw [happ, hμ0 i, zero_smul, smul_zero]
  exact sub_eq_zero.mp hD0

private lemma spd_conj_inj {A B C : E →L[ℝ] E}
    (hAsym : A.toLinearMap.IsSymmetric) (hApd : ∀ u : E, u ≠ 0 → 0 < ⟪A u, u⟫_ℝ)
    (hBsym : B.toLinearMap.IsSymmetric) (hBpd : ∀ u : E, u ≠ 0 → 0 < ⟪B u, u⟫_ℝ)
    (hCsym : C.toLinearMap.IsSymmetric) (hCpd : ∀ u : E, u ≠ 0 → 0 < ⟪C u, u⟫_ℝ)
    (hconj : A.comp (C.comp A) = B.comp (C.comp B)) : A = B := by
  obtain ⟨S, hSsym, hSpd, hSsq⟩ := spd_sqrt hCsym hCpd
  obtain ⟨eS, heS, _, _⟩ := spd_equiv hSsym hSpd
  let M : E →L[ℝ] E := S.comp (A.comp S)
  let N : E →L[ℝ] E := S.comp (B.comp S)
  have hMsym : M.toLinearMap.IsSymmetric := by
    intro u v
    have hS : ∀ a b, ⟪S a, b⟫_ℝ = ⟪a, S b⟫_ℝ := hSsym
    have hA : ∀ a b, ⟪A a, b⟫_ℝ = ⟪a, A b⟫_ℝ := hAsym
    change ⟪S (A (S u)), v⟫_ℝ = ⟪u, S (A (S v))⟫_ℝ
    rw [hS, hA, ← hS]
  have hNsym : N.toLinearMap.IsSymmetric := by
    intro u v
    have hS : ∀ a b, ⟪S a, b⟫_ℝ = ⟪a, S b⟫_ℝ := hSsym
    have hB : ∀ a b, ⟪B a, b⟫_ℝ = ⟪a, B b⟫_ℝ := hBsym
    change ⟪S (B (S u)), v⟫_ℝ = ⟪u, S (B (S v))⟫_ℝ
    rw [hS, hB, ← hS]
  have hSinj : ∀ u : E, u ≠ 0 → S u ≠ 0 := by
    intro u hu h0
    have := hSpd u hu
    rw [h0, inner_zero_left] at this
    exact lt_irrefl 0 this
  have hMpd : ∀ u : E, u ≠ 0 → 0 < ⟪M u, u⟫_ℝ := by
    intro u hu
    have hS : ∀ a b, ⟪S a, b⟫_ℝ = ⟪a, S b⟫_ℝ := hSsym
    change 0 < ⟪S (A (S u)), u⟫_ℝ
    rw [hS]
    exact hApd (S u) (hSinj u hu)
  have hNpd : ∀ u : E, u ≠ 0 → 0 < ⟪N u, u⟫_ℝ := by
    intro u hu
    have hS : ∀ a b, ⟪S a, b⟫_ℝ = ⟪a, S b⟫_ℝ := hSsym
    change 0 < ⟪S (B (S u)), u⟫_ℝ
    rw [hS]
    exact hBpd (S u) (hSinj u hu)
  have hMNsq : M.comp M = N.comp N := by
    ext u
    simp only [M, N, ContinuousLinearMap.comp_apply]
    have h1 : S (S (A (S u))) = C (A (S u)) := by
      have := congr_arg (fun L => L (A (S u))) hSsq
      simpa [ContinuousLinearMap.comp_apply] using this
    have h2 : S (S (B (S u))) = C (B (S u)) := by
      have := congr_arg (fun L => L (B (S u))) hSsq
      simpa [ContinuousLinearMap.comp_apply] using this
    rw [h1, h2]
    have h3 := congr_arg (fun L => L (S u)) hconj
    simp only [ContinuousLinearMap.comp_apply] at h3
    rw [h3]
  have hMN : M = N := spd_sq_inj hMsym hMpd hNsym hNpd hMNsq
  apply ContinuousLinearMap.ext
  intro u
  have hSu : S (eS.symm u) = u := by
    rw [← heS]; exact eS.apply_symm_apply u
  have h1 := congr_arg (fun L => L (eS.symm u)) hMN
  simp only [M, N, ContinuousLinearMap.comp_apply, hSu] at h1
  have h2 := congr_arg eS.symm h1
  have hSinv : ∀ z, eS.symm (S z) = z := by
    intro z; rw [← heS]; exact eS.symm_apply_apply z
  simpa [hSinv] using h2

private lemma hess_conj_eq {K : Set E} {F : E → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {w v : E}
    (hw : w ∈ interior K) (hv : v ∈ interior K)
    (e : E ≃L[ℝ] E) (he : e.toContinuousLinearMap = hess F w)
    (hesym : e.symm.toContinuousLinearMap.toLinearMap.IsSymmetric) :
    hess (conj K F) (hess F w v) =
      e.symm.toContinuousLinearMap.comp ((hess F v).comp e.symm.toContinuousLinearMap) := by
  set U : Set E := e '' interior K
  have hU_open : IsOpen U := e.isOpenMap _ isOpen_interior
  have hs_mem : hess F w v ∈ U := by
    refine ⟨v, hv, ?_⟩
    change e.toContinuousLinearMap v = hess F w v
    rw [he]
  have hconj_eq : ∀ y ∈ U, conj K F y = F (e.symm y) - 2 * F w - ν := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have h1 : e.symm (e z) = z := e.symm_apply_apply z
    have h2 : e z = hess F w z := by
      change e.toContinuousLinearMap z = hess F w z; rw [he]
    rw [h1, h2]
    exact (hF.2 w hw z hz).2
  have hgrad_eq : ∀ᶠ y in 𝓝 (hess F w v),
      gradient (conj K F) y = e.symm (gradient F (e.symm y)) := by
    filter_upwards [hU_open.mem_nhds hs_mem] with y hy
    have hsymy : e.symm y ∈ interior K := by
      rcases hy with ⟨z, hz, rfl⟩
      rwa [e.symm_apply_apply]
    have hloc : conj K F =ᶠ[𝓝 y] fun z => F (e.symm z) - 2 * F w - ν := by
      filter_upwards [hU_open.mem_nhds hy] with z hz
      exact hconj_eq z hz
    have hfd : HasFDerivAt (fun z => F (e.symm z) - 2 * F w - ν)
        ((InnerProductSpace.toDual ℝ E (gradient F (e.symm y))).comp
          e.symm.toContinuousLinearMap) y := by
      have h1 := (hasFDerivAt_F hF.1 hsymy).comp y e.symm.toContinuousLinearMap.hasFDerivAt
      simpa using (h1.sub_const (2 * F w)).sub_const ν
    have hfd' : HasFDerivAt (conj K F)
        ((InnerProductSpace.toDual ℝ E (gradient F (e.symm y))).comp
          e.symm.toContinuousLinearMap) y :=
      hfd.congr_of_eventuallyEq hloc
    apply ext_inner_right ℝ
    intro h
    rw [inner_gradient_left, hfd'.fderiv]
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]
    have := hesym (gradient F (e.symm y)) h
    simpa [ContinuousLinearEquiv.coe_coe] using this.symm
  have hsymv : e.symm (hess F w v) = v := by
    have : hess F w v = e v := by
      change hess F w v = e.toContinuousLinearMap v; rw [he]
    rw [this, e.symm_apply_apply]
  have hfd_rhs : HasFDerivAt (fun y => e.symm (gradient F (e.symm y)))
      (e.symm.toContinuousLinearMap.comp ((hess F v).comp e.symm.toContinuousLinearMap))
      (hess F w v) := by
    have h1 := (hasFDerivAt_gradient_F hF.1 (by rwa [← hsymv] at hv)).comp (hess F w v)
      e.symm.toContinuousLinearMap.hasFDerivAt
    have h2 := e.symm.toContinuousLinearMap.hasFDerivAt.comp (hess F w v) h1
    change HasFDerivAt (fun y => e.symm (gradient F (e.symm y)))
      (e.symm.toContinuousLinearMap.comp ((hess F (e.symm (hess F w v))).comp e.symm.toContinuousLinearMap))
      (hess F w v) at h2
    rwa [hsymv] at h2
  exact (hfd_rhs.congr_of_eventuallyEq hgrad_eq).fderiv

private lemma hess_apply_injective {K : Set E} (hK : IsProperCone K) {F : E → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {x₁ x₂ v : E}
    (hx₁ : x₁ ∈ interior K) (hx₂ : x₂ ∈ interior K) (hv : v ∈ interior K)
    (heq : hess F x₁ v = hess F x₂ v) : x₁ = x₂ := by
  obtain ⟨e₁, he₁, he₁sym, he₁pd⟩ :=
    spd_equiv (hess_symmetric hF.1 hx₁) (fun u hu => hF.1.2.2.2.2 x₁ hx₁ u hu)
  obtain ⟨e₂, he₂, he₂sym, he₂pd⟩ :=
    spd_equiv (hess_symmetric hF.1 hx₂) (fun u hu => hF.1.2.2.2.2 x₂ hx₂ u hu)
  have hc₁ := hess_conj_eq hF hx₁ hv e₁ he₁ he₁sym
  have hc₂ := hess_conj_eq hF hx₂ hv e₂ he₂ he₂sym
  rw [heq] at hc₁
  have hconj : e₁.symm.toContinuousLinearMap.comp ((hess F v).comp e₁.symm.toContinuousLinearMap) =
      e₂.symm.toContinuousLinearMap.comp ((hess F v).comp e₂.symm.toContinuousLinearMap) :=
    hc₁.symm.trans hc₂
  have hinv_eq : e₁.symm.toContinuousLinearMap = e₂.symm.toContinuousLinearMap :=
    spd_conj_inj he₁sym he₁pd he₂sym he₂pd
      (hess_symmetric hF.1 hv) (fun u hu => hF.1.2.2.2.2 v hv u hu) hconj
  have hH_eq : hess F x₁ = hess F x₂ := by
    rw [← he₁, ← he₂]
    apply ContinuousLinearMap.ext
    intro u
    have h1 : e₁.symm (e₂ u) = u := by
      have := congr_arg (fun L => L (e₂ u)) hinv_eq
      simpa [ContinuousLinearEquiv.coe_coe] using this
    have h2 := congr_arg e₁ h1
    simpa [ContinuousLinearEquiv.coe_coe] using h2.symm
  have hgrad_diff : gradient F x₁ - gradient F x₂ = -(hess F x₁ (x₁ - x₂)) := by
    have h1 := hess_apply_self hK hF.1 hx₁
    have h2 := hess_apply_self hK hF.1 hx₂
    rw [← hH_eq] at h2
    rw [map_sub, h1, h2]
    abel
  have hmono := convex_gradient_mono hF.1 hx₁ hx₂
  rw [hgrad_diff, inner_neg_left] at hmono
  by_contra hne
  have hpos := hF.1.2.2.2.2 x₁ hx₁ (x₁ - x₂) (sub_ne_zero.mpr hne)
  linarith

/-! ### Section 4: Global minimum of `Φ` and Corollary 3.2(i) -/

private lemma phi_min_at_z {K : Set E} (hK : IsProperCone K) {F : E → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {z v : E}
    (hz : z ∈ interior K) (hv : v ∈ interior K) :
    ∀ x ∈ interior K,
      -⟪gradient F z, v⟫_ℝ + ⟪hess F z v, z⟫_ℝ ≤ -⟪gradient F x, v⟫_ℝ + ⟪hess F z v, x⟫_ℝ := by
  set Φ : E → ℝ := fun x => -⟪gradient F x, v⟫_ℝ + ⟪hess F z v, x⟫_ℝ
  set M : ℝ := Φ z
  set S : Set E := {x ∈ interior K | Φ x ≤ M}
  have hzS : z ∈ S := ⟨hz, le_rfl⟩
  have hneg_grad_nonneg : ∀ x ∈ interior K, 0 ≤ -⟪gradient F x, v⟫_ℝ := by
    intro x hx
    have hs : hess F x x ∈ interior (ConvexOptimization.dualCone K) := (hF.2 x hx x hx).1
    have h0 : 0 ≤ ⟪v, hess F x x⟫_ℝ := interior_subset hs v (interior_subset hv)
    rw [hess_apply_self hK hF.1 hx, inner_neg_right, real_inner_comm] at h0
    linarith
  have hneg_grad_barrier : ∀ x ∈ interior K, F x - F v + ν ≤ -⟪gradient F x, v⟫_ℝ := by
    intro x hx
    have hle := convex_gradient_le hF.1 hx hv
    rw [inner_sub_right, inner_gradient_self hF.1 hx] at hle
    linarith
  obtain ⟨c, hc_pos, hcoerc⟩ := dualCone_interior_coercive (hF.2 z hz v hv).1
  have hS_bdd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max (M / c) 0, fun x hxS => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : c * ‖x‖ ≤ ⟪hess F z v, x⟫_ℝ := hcoerc x (interior_subset hxS.1)
    have h2 : 0 ≤ -⟪gradient F x, v⟫_ℝ := hneg_grad_nonneg x hxS.1
    have h3 : c * ‖x‖ ≤ M := by
      have : Φ x ≤ M := hxS.2
      dsimp [Φ] at this
      linarith
    have h4 : ‖x‖ ≤ M / c := (le_div_iff₀ hc_pos).mpr (by linarith)
    exact h4.trans (le_max_left _ _)
  have hΦ_cont : ContinuousOn Φ (interior K) := by
    intro x hx
    have hc : ContinuousAt (gradient F) x := (contDiffAt_gradient_F hF.1 hx).continuousAt
    have h1 : ContinuousAt (fun y => -⟪gradient F y, v⟫_ℝ) x :=
      (hc.inner continuousAt_const).neg
    have h2 : ContinuousAt (fun y => ⟪hess F z v, y⟫_ℝ) x :=
      continuousAt_const.inner continuousAt_id
    exact (h1.add h2).continuousWithinAt
  have hS_closed : IsClosed S := by
    rw [← closure_subset_iff_isClosed]
    intro x₀ hx₀
    have hx₀K : x₀ ∈ K := hK.1.closure_subset_iff.mpr (fun y hy => interior_subset hy.1) hx₀
    have hx₀_int : x₀ ∈ interior K := by
      by_contra hnot
      have hfront : x₀ ∈ frontier K := by
        rw [frontier, hK.1.closure_eq]
        exact ⟨hx₀K, hnot⟩
      have htend := hF.1.2.1 x₀ hfront
      have hev := htend.eventually (eventually_gt_atTop (M + F v - ν))
      rw [eventually_nhdsWithin_iff] at hev
      obtain ⟨U, hU_sub, hU_open, hx₀U⟩ := mem_nhds_iff.mp hev
      obtain ⟨y, hyU, hyS⟩ := mem_closure_iff.mp hx₀ U hU_open hx₀U
      have hFy : M + F v - ν < F y := hU_sub hyU hyS.1
      have hpos_lin : 0 ≤ ⟪hess F z v, y⟫_ℝ :=
        le_trans (mul_nonneg hc_pos.le (norm_nonneg y)) (hcoerc y (interior_subset hyS.1))
      have hbar := hneg_grad_barrier y hyS.1
      have hΦy : Φ y ≤ M := hyS.2
      dsimp [Φ] at hΦy
      linarith
    refine ⟨hx₀_int, ?_⟩
    have hcont_at : ContinuousAt Φ x₀ :=
      (hΦ_cont x₀ hx₀_int).continuousAt (isOpen_interior.mem_nhds hx₀_int)
    have htend : Tendsto Φ (𝓝[S] x₀) (𝓝 (Φ x₀)) :=
      hcont_at.tendsto.mono_left nhdsWithin_le_nhds
    have hne : (𝓝[S] x₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx₀
    exact le_of_tendsto htend (eventually_nhdsWithin_of_forall fun y hy => hy.2)
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bdd
  obtain ⟨x_star, hx_star_S, hx_star_min⟩ :=
    hS_compact.exists_isMinOn ⟨z, hzS⟩ (hΦ_cont.mono fun _ h => h.1)
  have hglobal : ∀ x ∈ interior K, Φ x_star ≤ Φ x := by
    intro x hx
    by_cases hle : Φ x ≤ M
    · exact hx_star_min ⟨hx, hle⟩
    · have : Φ x_star ≤ M := hx_star_S.2
      linarith
  have hloc : IsLocalMin Φ x_star :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds hx_star_S.1) fun x hx => hglobal x hx
  have hfd_Φ : HasFDerivAt Φ
      (InnerProductSpace.toDual ℝ E (hess F z v - hess F x_star v)) x_star := by
    have h1 : HasFDerivAt (fun x => -⟪gradient F x, v⟫_ℝ)
        (-((InnerProductSpace.toDual ℝ E v).comp (hess F x_star))) x_star := by
      have : (fun x => -⟪gradient F x, v⟫_ℝ) =
          fun x => -(InnerProductSpace.toDual ℝ E v (gradient F x)) := by
        ext x; simp [InnerProductSpace.toDual_apply_apply]
      rw [this]
      exact ((InnerProductSpace.toDual ℝ E v).hasFDerivAt.comp x_star
        (hasFDerivAt_gradient_F hF.1 hx_star_S.1)).fun_neg
    have h2 : HasFDerivAt (fun x => ⟪hess F z v, x⟫_ℝ)
        (InnerProductSpace.toDual ℝ E (hess F z v)) x_star := by
      have : (fun x => ⟪hess F z v, x⟫_ℝ) = fun x => InnerProductSpace.toDual ℝ E (hess F z v) x := by
        ext x; simp [InnerProductSpace.toDual_apply_apply]
      rw [this]
      exact (InnerProductSpace.toDual ℝ E (hess F z v)).hasFDerivAt
    have hsum := h1.fun_add h2
    have heq_fderiv :
        -((InnerProductSpace.toDual ℝ E v).comp (hess F x_star)) +
          InnerProductSpace.toDual ℝ E (hess F z v) =
        InnerProductSpace.toDual ℝ E (hess F z v - hess F x_star v) := by
      apply ContinuousLinearMap.ext
      intro h
      simp only [add_apply, neg_apply, ContinuousLinearMap.comp_apply,
        InnerProductSpace.toDual_apply_apply, inner_sub_left]
      rw [inner_hess_symm hF.1 hx_star_S.1 v h]
      ring
    rwa [heq_fderiv] at hsum
  have hzero := hloc.fderiv_eq_zero
  rw [hfd_Φ.fderiv] at hzero
  have heq_hess : hess F x_star v = hess F z v := by
    have hsub0 : hess F z v - hess F x_star v = 0 := by
      apply ext_inner_right ℝ
      intro h
      have := congr_arg (fun L => L h) hzero
      rw [InnerProductSpace.toDual_apply_apply, zero_apply] at this
      rw [inner_zero_left]
      exact this
    exact (sub_eq_zero.mp hsub0).symm
  have hx_star_eq : x_star = z := hess_apply_injective hK hF hx_star_S.1 hz hv heq_hess
  intro x hx
  have := hglobal x hx
  rwa [hx_star_eq] at this

private lemma sndDeriv_nonneg_of_isLocalMin {ψ ψ' : ℝ → ℝ} {c : ℝ}
    (hmin : IsLocalMin ψ 0) (hψ'0 : ψ' 0 = 0)
    (hderiv : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt ψ (ψ' t) t)
    (hderiv2 : HasDerivAt ψ' c 0) : 0 ≤ c := by
  by_contra hc
  push Not at hc
  have hslope : Tendsto (fun t : ℝ => (ψ' t - ψ' 0) / t) (𝓝[>] 0) (𝓝 c) := by
    have h := hderiv2.tendsto_slope_zero_right
    simpa [slope_def_field, smul_eq_mul, div_eq_inv_mul] using h
  have hev_neg : ∀ᶠ t in 𝓝[>] (0 : ℝ), ψ' t < 0 := by
    filter_upwards [hslope.eventually (Iio_mem_nhds hc), self_mem_nhdsWithin] with t ht ht0
    rw [hψ'0, sub_zero, div_lt_iff₀ ht0, zero_mul] at ht
    exact ht
  rw [eventually_nhdsWithin_iff] at hev_neg
  have hcomb := hmin.and (hderiv.and hev_neg)
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp hcomb
  have hδ2_pos : 0 < δ / 2 := by positivity
  have hcont : ContinuousOn ψ (Set.Icc 0 (δ / 2)) := by
    intro t ht
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      linarith [ht.2]
    exact (hδ hdist).2.1.continuousAt.continuousWithinAt
  have hdiff : ∀ t ∈ Set.Ioo 0 (δ / 2), HasDerivAt ψ (ψ' t) t := by
    intro t ht
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1.le]
      linarith [ht.2]
    exact (hδ hdist).2.1
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ := exists_hasDerivAt_eq_slope ψ ψ' hδ2_pos hcont hdiff
  have hξ_dist : dist ξ 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hξ_mem.1.le]
    linarith [hξ_mem.2]
  have hψ'_neg : ψ' ξ < 0 := (hδ hξ_dist).2.2 hξ_mem.1
  have hδ2_dist : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ2_pos]
    linarith
  have hmin_δ2 : ψ 0 ≤ ψ (δ / 2) := (hδ hδ2_dist).1
  rw [hξ_eq, div_lt_iff₀ (by linarith : (0 : ℝ) < δ / 2 - 0)] at hψ'_neg
  linarith

private lemma thirdDeriv_nonpos_of_mem_interior {K : Set E} (hK : IsProperCone K)
    {F : E → ℝ} {ν : ℝ} (hF : IsSelfScaledBarrier K F ν)
    {z v : E} (hz : z ∈ interior K) (hv : v ∈ interior K) (u : E) :
    ⟪fderiv ℝ (hess F) z v u, u⟫_ℝ ≤ 0 := by
  set ψ : ℝ → ℝ := fun t => -⟪gradient F (z + t • u), v⟫_ℝ + ⟪hess F z v, z + t • u⟫_ℝ
  set ψ' : ℝ → ℝ := fun t => -⟪hess F (z + t • u) u, v⟫_ℝ + ⟪hess F z v, u⟫_ℝ
  have hopen_t : ∀ᶠ t in 𝓝 (0 : ℝ), z + t • u ∈ interior K := by
    have hcont : Continuous (fun t : ℝ => z + t • u) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hz)
  have hmin : IsLocalMin ψ 0 := by
    rw [IsLocalMin]
    filter_upwards [hopen_t] with t ht
    simpa [ψ] using phi_min_at_z hK hF hz hv (z + t • u) ht
  have hψ'0 : ψ' 0 = 0 := by
    simp only [ψ', zero_smul, add_zero]
    rw [inner_hess_symm hF.1 hz u v, real_inner_comm u]
    ring
  have hderiv : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt ψ (ψ' t) t := by
    filter_upwards [hopen_t] with t ht
    have hline : HasDerivAt (fun s : ℝ => z + s • u) u t := by
      have h0 : HasDerivAt (fun s : ℝ => s • u) u t := by
        simpa using (hasDerivAt_id t).smul_const u
      exact h0.const_add z
    have h1 : HasDerivAt (fun s : ℝ => gradient F (z + s • u)) (hess F (z + t • u) u) t :=
      HasFDerivAt.comp_hasDerivAt t (hasFDerivAt_gradient_F hF.1 ht) hline
    have h2 : HasDerivAt (fun s : ℝ => -⟪gradient F (z + s • u), v⟫_ℝ)
        (-⟪hess F (z + t • u) u, v⟫_ℝ) t := by
      have := (h1.inner ℝ (hasDerivAt_const t v)).fun_neg
      simpa using this
    have h3 : HasDerivAt (fun s : ℝ => ⟪hess F z v, z + s • u⟫_ℝ) ⟪hess F z v, u⟫_ℝ t := by
      have := (hasDerivAt_const t (hess F z v)).inner ℝ hline
      simpa using this
    exact h2.fun_add h3
  have hderiv2 : HasDerivAt ψ' (-⟪fderiv ℝ (hess F) z u u, v⟫_ℝ) 0 := by
    have hline : HasDerivAt (fun s : ℝ => z + s • u) u 0 := by
      have h0 : HasDerivAt (fun s : ℝ => s • u) u 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
      exact h0.const_add z
    have hfd_hess : HasFDerivAt (hess F) (fderiv ℝ (hess F) z) (z + (0 : ℝ) • u) := by
      simpa using hasFDerivAt_hess_F hF.1 hz
    have h1 : HasDerivAt (fun s : ℝ => hess F (z + s • u)) (fderiv ℝ (hess F) z u) 0 :=
      hfd_hess.comp_hasDerivAt (0 : ℝ) hline
    have h2 : HasDerivAt (fun s : ℝ => hess F (z + s • u) u) (fderiv ℝ (hess F) z u u) 0 :=
      (ContinuousLinearMap.apply ℝ E u).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    have h3 : HasDerivAt (fun s : ℝ => -⟪hess F (z + s • u) u, v⟫_ℝ)
        (-⟪fderiv ℝ (hess F) z u u, v⟫_ℝ) 0 := by
      have := (h2.inner ℝ (hasDerivAt_const (0 : ℝ) v)).fun_neg
      simpa using this
    exact h3.add_const ⟪hess F z v, u⟫_ℝ
  have hnonneg : 0 ≤ -⟪fderiv ℝ (hess F) z u u, v⟫_ℝ :=
    sndDeriv_nonneg_of_isLocalMin hmin hψ'0 hderiv hderiv2
  have hsym : ⟪fderiv ℝ (hess F) z v u, u⟫_ℝ = ⟪fderiv ℝ (hess F) z u u, v⟫_ℝ := by
    rw [thirdDeriv_symm_12 hF.1 hz v u u, thirdDeriv_symm_23 hF.1 hz u v u]
  linarith

private lemma thirdDeriv_nonpos_of_mem {K : Set E} (hK : IsProperCone K)
    {F : E → ℝ} {ν : ℝ} (hF : IsSelfScaledBarrier K F ν)
    {z v : E} (hz : z ∈ interior K) (hv : v ∈ K) (u : E) :
    ⟪fderiv ℝ (hess F) z v u, u⟫_ℝ ≤ 0 := by
  have hstep : ∀ ε : ℝ, 0 < ε →
      ⟪fderiv ℝ (hess F) z v u, u⟫_ℝ + ε * ⟪fderiv ℝ (hess F) z z u, u⟫_ℝ ≤ 0 := by
    intro ε hε
    have hvε : v + ε • z ∈ interior K := by
      rw [add_comm]
      exact cone_interior_add_mem hK (cone_smul_interior hK hz hε) hv
    have hle := thirdDeriv_nonpos_of_mem_interior hK hF hz hvε u
    rw [map_add, map_smul] at hle
    simp only [add_apply, smul_apply, inner_add_left, inner_smul_left, conj_trivial] at hle
    exact hle
  have htend : Tendsto
      (fun ε : ℝ => ⟪fderiv ℝ (hess F) z v u, u⟫_ℝ + ε * ⟪fderiv ℝ (hess F) z z u, u⟫_ℝ)
      (𝓝[>] 0) (𝓝 ⟪fderiv ℝ (hess F) z v u, u⟫_ℝ) := by
    have hcont : Continuous (fun ε : ℝ =>
        ⟪fderiv ℝ (hess F) z v u, u⟫_ℝ + ε * ⟪fderiv ℝ (hess F) z z u, u⟫_ℝ) :=
      continuous_const.add (continuous_id.mul continuous_const)
    have h0 := hcont.tendsto 0
    simp only [zero_mul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto htend (eventually_nhdsWithin_of_forall hstep)

end Helpers

theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : α * sigma K x p < 1) :
    x - α • p ∈ interior K ∧
    ∀ v : EuclideanSpace ℝ (Fin n),
      (1 / (1 + α * sigma K x (-p)) ^ 2) * ⟪hess F x v, v⟫_ℝ ≤ ⟪hess F (x - α • p) v, v⟫_ℝ ∧
        ⟪hess F (x - α • p) v, v⟫_ℝ ≤ (1 / (1 - α * sigma K x p) ^ 2) * ⟪hess F x v, v⟫_ℝ := by
  have _ := hν
  refine ⟨step_mem_interior hK hx hα0 hα, fun v => ?_⟩
  set σp : ℝ := sigma K x p
  set σm : ℝ := sigma K x (-p)
  obtain ⟨hσp_nn, hσp_mem⟩ := sigma_nonneg_and_mem hK hx p
  obtain ⟨hσm_nn, hσm_mem⟩ := sigma_nonneg_and_mem hK hx (-p)
  have hσm_mem' : σm • x + p ∈ K := by simpa [σm, sub_neg_eq_add] using hσm_mem
  set φ : ℝ → ℝ := fun t => ⟪hess F (x - t • p) v, v⟫_ℝ
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) α, x - t • p ∈ interior K := by
    intro t ⟨ht0, htα⟩
    have htσ : t * σp < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right htα hσp_nn) hα
    exact step_mem_interior hK hx ht0 htσ
  have hφ_deriv : ∀ t ∈ Set.Icc (0 : ℝ) α,
      HasDerivAt φ (-⟪fderiv ℝ (hess F) (x - t • p) p v, v⟫_ℝ) t := by
    intro t ht
    have hline : HasDerivAt (fun s : ℝ => x - s • p) (-p) t := by
      have h0 : HasDerivAt (fun s : ℝ => s • p) p t := by
        simpa using (hasDerivAt_id t).smul_const p
      exact h0.const_sub x
    have h1 : HasDerivAt (fun s : ℝ => hess F (x - s • p))
        (fderiv ℝ (hess F) (x - t • p) (-p)) t :=
      (hasFDerivAt_hess_F hF.1 (hseg t ht)).comp_hasDerivAt t hline
    have h2 : HasDerivAt (fun s : ℝ => hess F (x - s • p) v)
        (fderiv ℝ (hess F) (x - t • p) (-p) v) t :=
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) v).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt φ ⟪fderiv ℝ (hess F) (x - t • p) (-p) v, v⟫_ℝ t := by
      have := h2.inner ℝ (hasDerivAt_const t v)
      simpa [φ] using this
    simpa [map_neg, inner_neg_left] using h3
  have hφ_cont : ContinuousOn φ (Set.Icc 0 α) :=
    fun t ht => (hφ_deriv t ht).continuousAt.continuousWithinAt
  constructor
  · -- Lower bound: (1 + t * σm)^2 * φ t is nondecreasing on [0, α]
    set fm : ℝ → ℝ := fun t => (1 + t * σm) ^ 2 * φ t
    have hfm_deriv : ∀ t ∈ Set.Icc (0 : ℝ) α,
        HasDerivAt fm
          (2 * σm * (1 + t * σm) * φ t +
            (1 + t * σm) ^ 2 * (-⟪fderiv ℝ (hess F) (x - t • p) p v, v⟫_ℝ)) t := by
      intro t ht
      have hlin : HasDerivAt (fun s : ℝ => 1 + s * σm) σm t := by
        have h0 : HasDerivAt (fun s : ℝ => s * σm) σm t := by
          simpa using (hasDerivAt_id t).mul_const σm
        exact h0.const_add 1
      have hsq : HasDerivAt (fun s : ℝ => (1 + s * σm) ^ 2) (2 * (1 + t * σm) * σm) t := by
        simpa [pow_one] using hlin.fun_pow 2
      have hmul := hsq.fun_mul (hφ_deriv t ht)
      have hderiv_eq : (2 * (1 + t * σm) * σm) * φ t +
          (1 + t * σm) ^ 2 * (-⟪fderiv ℝ (hess F) (x - t • p) p v, v⟫_ℝ) =
          2 * σm * (1 + t * σm) * φ t +
            (1 + t * σm) ^ 2 * (-⟪fderiv ℝ (hess F) (x - t • p) p v, v⟫_ℝ) := by ring
      rwa [hderiv_eq] at hmul
    have hfm_cont : ContinuousOn fm (Set.Icc 0 α) :=
      fun t ht => (hfm_deriv t ht).continuousAt.continuousWithinAt
    have hfm_mono : MonotoneOn fm (Set.Icc 0 α) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 α) hfm_cont
      · intro t ht
        exact (hfm_deriv t (interior_subset ht)).hasDerivWithinAt
      · intro t ht
        have htIcc : t ∈ Set.Icc (0 : ℝ) α := interior_subset ht
        set y := x - t • p
        have hy : y ∈ interior K := hseg t htIcc
        have hself := thirdDeriv_apply_self hK hF.1 hy
        have hself_val : ⟪fderiv ℝ (hess F) y y v, v⟫_ℝ = -2 * φ t := by
          rw [hself]
          simp [φ, y, inner_smul_left]
        have hvec : σm • y + (1 + t * σm) • p = σm • x + p := by
          dsimp [y]
          rw [smul_sub, add_smul, one_smul, smul_smul, mul_comm t σm]
          abel
        have hnonpos : ⟪fderiv ℝ (hess F) y (σm • x + p) v, v⟫_ℝ ≤ 0 :=
          thirdDeriv_nonpos_of_mem hK hF hy hσm_mem' v
        rw [← hvec, map_add, map_smul, map_smul] at hnonpos
        simp only [add_apply, smul_apply, inner_add_left, inner_smul_left, conj_trivial] at hnonpos
        rw [hself_val] at hnonpos
        have hpos_fac : 0 < 1 + t * σm := by nlinarith [htIcc.1, hσm_nn]
        nlinarith
    have hle : fm 0 ≤ fm α := hfm_mono ⟨le_rfl, hα0⟩ ⟨hα0, le_rfl⟩ hα0
    have hpos_α : 0 < (1 + α * σm) ^ 2 := by positivity
    simp only [fm, zero_mul, add_zero, one_pow, one_mul, φ, zero_smul, sub_zero] at hle
    rw [one_div_mul_eq_div, div_le_iff₀ hpos_α]
    linarith
  · -- Upper bound: (1 - t * σp)^2 * φ t is nonincreasing on [0, α]
    set fp : ℝ → ℝ := fun t => (1 - t * σp) ^ 2 * φ t
    have hfp_deriv : ∀ t ∈ Set.Icc (0 : ℝ) α,
        HasDerivAt fp
          (-2 * σp * (1 - t * σp) * φ t +
            (1 - t * σp) ^ 2 * (-⟪fderiv ℝ (hess F) (x - t • p) p v, v⟫_ℝ)) t := by
      intro t ht
      have hlin : HasDerivAt (fun s : ℝ => 1 - s * σp) (-σp) t := by
        have h0 : HasDerivAt (fun s : ℝ => s * σp) σp t := by
          simpa using (hasDerivAt_id t).mul_const σp
        exact h0.const_sub 1
      have hsq : HasDerivAt (fun s : ℝ => (1 - s * σp) ^ 2) (2 * (1 - t * σp) * (-σp)) t := by
        simpa [pow_one] using hlin.fun_pow 2
      have hmul := hsq.fun_mul (hφ_deriv t ht)
      have hderiv_eq : (2 * (1 - t * σp) * (-σp)) * φ t +
          (1 - t * σp) ^ 2 * (-⟪fderiv ℝ (hess F) (x - t • p) p v, v⟫_ℝ) =
          -2 * σp * (1 - t * σp) * φ t +
            (1 - t * σp) ^ 2 * (-⟪fderiv ℝ (hess F) (x - t • p) p v, v⟫_ℝ) := by ring
      rwa [hderiv_eq] at hmul
    have hfp_cont : ContinuousOn fp (Set.Icc 0 α) :=
      fun t ht => (hfp_deriv t ht).continuousAt.continuousWithinAt
    have hfp_anti : AntitoneOn fp (Set.Icc 0 α) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 α) hfp_cont
      · intro t ht
        exact (hfp_deriv t (interior_subset ht)).hasDerivWithinAt
      · intro t ht
        have htIcc : t ∈ Set.Icc (0 : ℝ) α := interior_subset ht
        set y := x - t • p
        have hy : y ∈ interior K := hseg t htIcc
        have hself := thirdDeriv_apply_self hK hF.1 hy
        have hself_val : ⟪fderiv ℝ (hess F) y y v, v⟫_ℝ = -2 * φ t := by
          rw [hself]
          simp [φ, y, inner_smul_left]
        have hvec : σp • y - (1 - t * σp) • p = σp • x - p := by
          dsimp [y]
          rw [smul_sub, sub_smul, one_smul, smul_smul, mul_comm t σp]
          abel
        have hnonpos : ⟪fderiv ℝ (hess F) y (σp • x - p) v, v⟫_ℝ ≤ 0 :=
          thirdDeriv_nonpos_of_mem hK hF hy hσp_mem v
        rw [← hvec, map_sub, map_smul, map_smul] at hnonpos
        simp only [sub_apply, smul_apply, inner_sub_left, inner_smul_left, conj_trivial] at hnonpos
        rw [hself_val] at hnonpos
        have hpos_fac : 0 < 1 - t * σp := by
          have : t * σp ≤ α * σp := mul_le_mul_of_nonneg_right htIcc.2 hσp_nn
          linarith
        nlinarith
    have hle : fp α ≤ fp 0 := hfp_anti ⟨le_rfl, hα0⟩ ⟨hα0, le_rfl⟩ hα0
    have hpos_α : 0 < (1 - α * σp) ^ 2 := sq_pos_of_pos (by linarith)
    simp only [fp, zero_mul, sub_zero, one_pow, one_mul, φ, zero_smul] at hle
    rw [one_div_mul_eq_div, le_div_iff₀ hpos_α]
    linarith
