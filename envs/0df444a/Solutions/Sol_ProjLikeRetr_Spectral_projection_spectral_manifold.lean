-- Prove2me | solution 1 for ProjLikeRetr.Spectral.projection_spectral_manifold
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-16T23:27:14.265759+00:00
-- url     : https://prove2.me/submissions/501895ce-53e4-4a66-9053-9ab7113b5f5d

-- Licensed under Apache 2.0. Full exact spectral-manifold projection theorem.
import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_ProjLikeRetr_Spectral_IsSubmanifold
open scoped Matrix Matrix.Norms.Frobenius
open RandomGradFree.Nonsmooth


open scoped InnerProductSpace
open Set Metric

namespace ProjLikeRetr.Spectral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A derivative close to a bounded-below linear map gives a lower chord bound. -/
theorem chord_lower_of_derivative_close {g : E → F} {s : Set E}
    {L : E →L[ℝ] F} {c : ℝ} (hs : Convex ℝ s)
    (hg : ∀ u ∈ s, DifferentiableAt ℝ g u)
    (hclose : ∀ u ∈ s, ‖fderiv ℝ g u - L‖ ≤ c)
    (hlower : ∀ w, 2 * c * ‖w‖ ≤ ‖L w‖)
    {u v : E} (hu : u ∈ s) (hv : v ∈ s) :
    c * ‖v - u‖ ≤ ‖g v - g u‖ := by
  have hrem := hs.norm_image_sub_le_of_norm_fderiv_le' hg hclose hu hv
  have htri : ‖L (v-u)‖ ≤ ‖g v-g u‖ + ‖g v-g u-L (v-u)‖ := by
    calc
      ‖L (v-u)‖ = ‖(g v-g u) - (g v-g u-L (v-u))‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have := hlower (v-u)
  nlinarith

/-- The quantitative normality argument for uniqueness of a nearest point. -/
theorem eq_of_equal_distance_normal_remainder {g : E → F} {u v : E} {y : F}
    {D : E →L[ℝ] F} {c C ε : ℝ} (hc : 0 < c)
    (hε : 0 ≤ ε) (hsmall : 2 * ε * C < c^2)
    (hchord : c * ‖v-u‖ ≤ ‖g v-g u‖)
    (hrem : ‖g v-g u-D (v-u)‖ ≤ C * ‖v-u‖^2)
    (hnormal : ⟪y-g u, D (v-u)⟫_ℝ = 0)
    (hdist : ‖y-g u‖ = ‖y-g v‖) (hnear : ‖y-g u‖ ≤ ε) : u = v := by
  have hidentity : ‖g v-g u‖^2 = 2 * ⟪y-g u, g v-g u⟫_ℝ := by
    have he : y-g v = (y-g u) - (g v-g u) := by abel
    have hn := norm_sub_sq_real (y-g u) (g v-g u)
    rw [← he, ← hdist] at hn
    linarith
  have hi : ⟪y-g u, g v-g u⟫_ℝ ≤ ε * (C * ‖v-u‖^2) := by
    calc
      ⟪y-g u, g v-g u⟫_ℝ = ⟪y-g u, g v-g u-D (v-u)⟫_ℝ := by
        simp only [inner_sub_right, hnormal, sub_zero]
      _ ≤ ‖y-g u‖ * ‖g v-g u-D (v-u)‖ := real_inner_le_norm _ _
      _ ≤ ε * (C * ‖v-u‖^2) := mul_le_mul hnear hrem (norm_nonneg _) hε
  have hl : c^2 * ‖v-u‖^2 ≤ ‖g v-g u‖^2 := by
    have hh := mul_self_le_mul_self (mul_nonneg hc.le (norm_nonneg (v-u))) hchord
    nlinarith only [hh]
  have hz : ‖v-u‖^2 = 0 := by
    nlinarith [sq_nonneg ‖v-u‖]
  have hn : ‖v-u‖ = 0 := by nlinarith [norm_nonneg (v-u)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

end ProjLikeRetr.Spectral


open scoped InnerProductSpace
open Set Metric
open RandomGradFree.Nonsmooth

namespace ProjLikeRetr.Spectral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [NormedSpace ℝ E] [InnerProductSpace ℝ F] in
/-- A compact local parametrization captures every competitor at least as good as the basepoint. -/
theorem exists_projection_of_compact_localization {M : Set F} {K : Set E}
    {g : E → F} {a : E} {y : F} (hK : IsCompact K) (ha : a ∈ K)
    (hg : ContinuousOn g K) (hM : ∀ u ∈ K, g u ∈ M)
    (hloc : ∀ z ∈ M, ‖y-z‖ ≤ ‖y-g a‖ → ∃ u ∈ K, g u = z) :
    ∃ u ∈ K, IsMetricProjection M y (g u) := by
  obtain ⟨u, hu, hmin⟩ := hK.exists_isMinOn ⟨a, ha⟩
    ((continuousOn_const.sub hg).norm)
  refine ⟨u, hu, hM u hu, ?_⟩
  intro z hz
  by_cases hd : ‖y-z‖ ≤ ‖y-g a‖
  · obtain ⟨v, hv, rfl⟩ := hloc z hz hd
    exact hmin hv
  · exact (hmin ha).trans (le_of_lt (lt_of_not_ge hd))

omit [InnerProductSpace ℝ F] in
/-- Every metric projection stays within twice the distance to any fixed feasible point. -/
theorem projection_near_base {M : Set F} {a y z : F} (ha : a ∈ M)
    (hz : IsMetricProjection M y z) : ‖z-a‖ ≤ 2 * ‖y-a‖ := by
  calc
    ‖z-a‖ = ‖(z-y)+(y-a)‖ := by congr 1; abel
    _ ≤ ‖z-y‖ + ‖y-a‖ := norm_add_le _ _
    _ = ‖y-z‖ + ‖y-a‖ := by rw [norm_sub_rev z y]
    _ ≤ 2 * ‖y-a‖ := by linarith [hz.2 a ha]

/-- At an interior local nearest parameter, the displacement is normal to the derivative. -/
theorem normal_of_local_min_sq {g : E → F} {u : E} {y : F} {D : E →L[ℝ] F}
    (hg : HasFDerivAt g D u)
    (hmin : IsLocalMin (fun v => ‖y-g v‖^2) u) (w : E) :
    ⟪y-g u, D w⟫_ℝ = 0 := by
  have hd := (hg.const_sub y).norm_sq
  have hz := hmin.hasFDerivAt_eq_zero hd
  have he := congrArg (fun L : E →L[ℝ] ℝ => L w) hz
  simp [two_smul] at he
  rw [inner_sub_left]
  linarith

end ProjLikeRetr.Spectral


open Set Metric Filter
open scoped Topology NNReal

namespace ProjLikeRetr.Spectral
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A local Lipschitz bound on the derivative gives a non-sharp quadratic Taylor estimate. -/
theorem remainder_le_of_lipschitz_fderiv {g : E → F} {s : Set E} {K : ℝ≥0}
    (hs : Convex ℝ s) (hg : ∀ u ∈ s, DifferentiableAt ℝ g u)
    (hL : LipschitzOnWith K (fderiv ℝ g) s) {u v : E} (hu : u ∈ s) (hv : v ∈ s) :
    ‖g v-g u-fderiv ℝ g u (v-u)‖ ≤ (K : ℝ) * ‖v-u‖^2 := by
  have hsub : segment ℝ u v ⊆ s := hs.segment_subset hu hv
  have hb : ∀ z ∈ segment ℝ u v, ‖fderiv ℝ g z-fderiv ℝ g u‖ ≤
      (K : ℝ) * ‖v-u‖ := by
    intro z hz
    have hh := hL.dist_le_mul z (hsub hz) u hu
    rw [dist_eq_norm, dist_eq_norm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg)
  have hh := (convex_segment u v).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz => hg z (hsub hz)) hb (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
  nlinarith only [hh]

/-- The derivative of a C² map is Lipschitz on a neighborhood. -/
theorem exists_lipschitz_fderiv_of_contDiffAt_two {g : E → F} {a : E}
    (hg : ContDiffAt ℝ 2 g a) :
    ∃ K : ℝ≥0, ∃ s ∈ 𝓝 a, LipschitzOnWith K (fderiv ℝ g) s := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ g) a := hg.fderiv_right (by norm_num)
  exact hd.exists_lipschitzOnWith

end ProjLikeRetr.Spectral


open Set Metric Filter
open scoped Topology NNReal

namespace ProjLikeRetr.Spectral
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Simultaneous local derivative and quadratic bounds for a C² map. -/
theorem local_c2_bounds {g : E → F} {a : E} {c : ℝ} (hc : 0 < c)
    (hg : ContDiffAt ℝ 2 g a) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      (∀ u ∈ closedBall a r, DifferentiableAt ℝ g u) ∧
      (∀ u ∈ closedBall a r, ‖fderiv ℝ g u-fderiv ℝ g a‖ ≤ c) ∧
      (∀ u ∈ closedBall a r, ∀ v ∈ closedBall a r,
        ‖g v-g u-fderiv ℝ g u (v-u)‖ ≤ C * ‖v-u‖^2) := by
  obtain ⟨K, s, hs, hL⟩ := exists_lipschitz_fderiv_of_contDiffAt_two hg
  have hd : ∀ᶠ u in 𝓝 a, DifferentiableAt ℝ g u :=
    (hg.eventually (by norm_num)).mono (fun u hu => hu.differentiableAt (by norm_num))
  have hclose : ∀ᶠ u in 𝓝 a, ‖fderiv ℝ g u-fderiv ℝ g a‖ < c := by
    have hh := (hg.continuousAt_fderiv (by norm_num)).preimage_mem_nhds
      (ball_mem_nhds (fderiv ℝ g a) hc)
    filter_upwards [hh] with u hu
    simpa only [mem_preimage, mem_ball, dist_eq_norm] using hu
  have hall : {u | u ∈ s ∧ DifferentiableAt ℝ g u ∧
      ‖fderiv ℝ g u-fderiv ℝ g a‖ < c} ∈ 𝓝 a := by
    filter_upwards [hs, hd, hclose] with u hus hud huc
    exact ⟨hus, hud, huc⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hall
  have hsub : closedBall a (ρ/2) ⊆ {u | u ∈ s ∧ DifferentiableAt ℝ g u ∧
      ‖fderiv ℝ g u-fderiv ℝ g a‖ < c} := by
    intro u hu
    apply hball
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hu) (by linarith))
  refine ⟨ρ/2, K, by positivity, K.coe_nonneg, ?_, ?_, ?_⟩
  · exact fun u hu => (hsub hu).2.1
  · exact fun u hu => (hsub hu).2.2.le
  · intro u hu v hv
    exact remainder_le_of_lipschitz_fderiv (convex_closedBall a (ρ/2))
      (fun z hz => (hsub hz).2.1) (hL.mono (fun z hz => (hsub hz).1)) hu hv

end ProjLikeRetr.Spectral


open Set Metric Filter
open scoped Topology InnerProductSpace
open RandomGradFree.Nonsmooth

namespace ProjLikeRetr.Spectral
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F] in
/-- A nearest image point at an interior parameter is a local minimum of squared distance. -/
theorem projection_isLocalMin_sq {g : E → F} {M : Set F} {r : ℝ} {u : E} {y : F}
    (hu : u ∈ ball 0 r) (hM : ∀ v ∈ ball 0 r, g v ∈ M)
    (hp : IsMetricProjection M y (g u)) :
    IsLocalMin (fun v => ‖y-g v‖^2) u := by
  apply IsMinOn.isLocalMin (s := ball 0 r) _ (isOpen_ball.mem_nhds hu)
  intro v hv
  exact pow_le_pow_left₀ (norm_nonneg _) (hp.2 (g v) (hM v hv)) 2

/-- Quantitative compact localization plus normality proves the full global singleton projection. -/
theorem unique_projection_parametric {g : E → F} {M : Set F} {r c C ε : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hε : 0 ≤ ε) (hsmall : 2*ε*C < c^2)
    (hg : ∀ u ∈ closedBall 0 r, DifferentiableAt ℝ g u)
    (hM : ∀ u ∈ closedBall 0 r, g u ∈ M)
    (hchord : ∀ u ∈ closedBall 0 r, ∀ v ∈ closedBall 0 r,
      c*‖v-u‖ ≤ ‖g v-g u‖)
    (hrem : ∀ u ∈ closedBall 0 r, ∀ v ∈ closedBall 0 r,
      ‖g v-g u-fderiv ℝ g u (v-u)‖ ≤ C*‖v-u‖^2)
    {y : F} (hy : ‖y-g 0‖ ≤ ε)
    (hloc : ∀ z ∈ M, ‖y-z‖ ≤ ‖y-g 0‖ → ∃ u ∈ ball 0 r, g u = z) :
    ∃ p : F, {z | IsMetricProjection M y z} = {p} := by
  have hzero : (0 : E) ∈ closedBall 0 r := mem_closedBall_self hr.le
  have hcont : ContinuousOn g (closedBall 0 r) :=
    fun u hu => (hg u hu).continuousAt.continuousWithinAt
  obtain ⟨u₀, hu₀, hp₀⟩ := exists_projection_of_compact_localization
    (isCompact_closedBall (0 : E) r) hzero hcont hM
    (fun z hz hdist => by
      obtain ⟨u, hu, he⟩ := hloc z hz hdist
      exact ⟨u, ball_subset_closedBall hu, he⟩)
  obtain ⟨u, hu, heu⟩ := hloc (g u₀) hp₀.1 (hp₀.2 (g 0) (hM 0 hzero))
  have hp : IsMetricProjection M y (g u) := heu.symm ▸ hp₀
  refine ⟨g u, Set.ext fun z => ?_⟩
  constructor
  · intro hz
    obtain ⟨v, hv, hev⟩ := hloc z hz.1 (hz.2 (g 0) (hM 0 hzero))
    have hvp : IsMetricProjection M y (g v) := hev.symm ▸ hz
    have hmin := projection_isLocalMin_sq hu
      (fun w hw => hM w (ball_subset_closedBall hw)) hp
    have hn := normal_of_local_min_sq
      (hg u (ball_subset_closedBall hu)).hasFDerivAt hmin (v-u)
    have hd : ‖y-g u‖ = ‖y-g v‖ := le_antisymm (hp.2 _ hvp.1) (hvp.2 _ hp.1)
    have he := eq_of_equal_distance_normal_remainder hc hε hsmall
      (hchord u (ball_subset_closedBall hu) v (ball_subset_closedBall hv))
      (hrem u (ball_subset_closedBall hu) v (ball_subset_closedBall hv)) hn hd
      ((hp.2 _ (hM 0 hzero)).trans hy)
    simpa only [mem_singleton_iff] using (hev.symm.trans (congrArg g he.symm))
  · intro hz
    rw [mem_singleton_iff.mp hz]
    exact hp

end ProjLikeRetr.Spectral


open Set Metric Filter
open scoped Topology
open RandomGradFree.Nonsmooth

namespace ProjLikeRetr.Spectral
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem local_unique_projection_of_parametrization {g : E → F} {M : Set F} {c : ℝ}
    (hc : 0 < c) (hg : ContDiffAt ℝ 2 g 0)
    (hlower : ∀ w, 2*c*‖w‖ ≤ ‖fderiv ℝ g 0 w‖)
    (hM : ∀ᶠ u in 𝓝 0, g u ∈ M)
    (hloc : ∀ r > 0, ∃ ρ > 0, ∀ z ∈ M, ‖z-g 0‖ < ρ →
      ∃ u ∈ ball 0 r, g u = z) :
    ∃ ε > 0, ∀ y : F, ‖y-g 0‖ < ε → ∃ p : F, {z | IsMetricProjection M y z} = {p} := by
  obtain ⟨r₀, C, hr₀, hC, hdiff, hclose, hrem⟩ := local_c2_bounds hc hg
  obtain ⟨r₁, hr₁, hrM⟩ := Metric.mem_nhds_iff.mp hM
  let r := min r₀ r₁ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr0 : r ≤ r₀ := by dsimp [r]; have := min_le_left r₀ r₁; linarith [lt_min hr₀ hr₁]
  have hr1 : r < r₁ := by dsimp [r]; have := min_le_right r₀ r₁; linarith [lt_min hr₀ hr₁]
  have hsub : closedBall (0 : E) r ⊆ closedBall 0 r₀ := closedBall_subset_closedBall hr0
  have hmem : ∀ u ∈ closedBall (0 : E) r, g u ∈ M := by
    intro u hu
    apply hrM
    exact mem_ball.mpr ((mem_closedBall.mp hu).trans_lt hr1)
  obtain ⟨ρ, hρ, hlocal⟩ := hloc r hr
  let ε := min (ρ/4) (c^2/(4*(C+1)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hερ : 2*ε < ρ := by have := min_le_left (ρ/4) (c^2/(4*(C+1))); dsimp [ε]; linarith
  have hεC : 2*ε*C < c^2 := by
    have he : ε ≤ c^2/(4*(C+1)) := min_le_right _ _
    have hb : ε*(4*(C+1)) ≤ c^2 := (le_div_iff₀ (by positivity)).mp he
    nlinarith [mul_nonneg hε.le hC]
  refine ⟨ε, hε, ?_⟩
  intro y hy
  apply unique_projection_parametric hr hc hε.le hεC
    (fun u hu => hdiff u (hsub hu)) hmem
    (fun u hu v hv => chord_lower_of_derivative_close (convex_closedBall 0 r₀)
      hdiff hclose hlower (hsub hu) (hsub hv))
    (fun u hu v hv => hrem u (hsub hu) v (hsub hv)) hy.le
  intro z hz hd
  apply hlocal z hz
  have hb : ‖z-g 0‖ ≤ 2*‖y-g 0‖ := by
    calc
      ‖z-g 0‖ ≤ ‖z-y‖+‖y-g 0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2*‖y-g 0‖ := by rw [norm_sub_rev z y]; linarith
  exact hb.trans_lt (by linarith)

end ProjLikeRetr.Spectral


open Set Metric Filter
open scoped Topology

namespace ProjLikeRetr.Spectral

/-- The actual linear slice in the native coordinate chart. -/
def coordinateSlice (N d : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin N)) where
  carrier := {v | ∀ i : Fin N, d ≤ i.val → v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv i hi
    simp [hu i hi, hv i hi]
  smul_mem' := by
    intro c u hu i hi
    simp [hu i hi]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def sliceParam (φ : OpenPartialHomeomorph E
    (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) (a : E) (d : ℕ)
    (u : coordinateSlice (Module.finrank ℝ E) d) : E := φ.symm (φ a + (u : _))

theorem sliceParam_zero (φ : OpenPartialHomeomorph E
    (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) {a : E} (ha : a ∈ φ.source) (d : ℕ) :
    sliceParam φ a d 0 = a := by
  simp [sliceParam, φ.left_inv ha]

theorem sliceParam_contDiffAt (φ : OpenPartialHomeomorph E
    (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) {a : E} {d : ℕ}
    (ha : a ∈ φ.source) (hφ : ContDiffOn ℝ 2 φ.symm φ.target) :
    ContDiffAt ℝ 2 (sliceParam φ a d) 0 := by
  have hc : ContDiffAt ℝ 2
      (fun u : coordinateSlice (Module.finrank ℝ E) d => φ a + (u : _)) 0 :=
    contDiffAt_const.add (coordinateSlice (Module.finrank ℝ E) d).subtypeL.contDiff.contDiffAt
  apply ContDiffAt.comp (f := fun u : coordinateSlice (Module.finrank ℝ E) d => φ a + (u : _))
    (g := φ.symm) 0 _ hc
  simpa using hφ.contDiffAt (φ.open_target.mem_nhds (φ.map_source ha))

/-- The inverse chart is genuinely an inverse on a parameter neighborhood. -/
theorem sliceParam_eventually_right_inv (φ : OpenPartialHomeomorph E
    (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) {a : E} {d : ℕ}
    (ha : a ∈ φ.source) :
    ∀ᶠ u : coordinateSlice (Module.finrank ℝ E) d in 𝓝 0,
      φ (sliceParam φ a d u) = φ a + (u : _) := by
  have hc : ContinuousAt (fun u : coordinateSlice (Module.finrank ℝ E) d => φ a + (u : _)) 0 :=
    continuousAt_const.add (coordinateSlice (Module.finrank ℝ E) d).subtypeL.continuous.continuousAt
  have hh : (fun u : coordinateSlice (Module.finrank ℝ E) d => φ a + (u : _)) ⁻¹' φ.target ∈ 𝓝 0 := by
    apply hc.preimage_mem_nhds
    simpa using φ.open_target.mem_nhds (φ.map_source ha)
  filter_upwards [hh] with u hu
  exact φ.right_inv hu

/-- Differentiating the chart identity gives the actual continuous-linear left inverse. -/
theorem sliceParam_derivative_left_inverse (φ : OpenPartialHomeomorph E
    (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) {a : E} {d : ℕ}
    (ha : a ∈ φ.source) (hφ : ContDiffOn ℝ 2 φ φ.source)
    (hψ : ContDiffOn ℝ 2 φ.symm φ.target) :
    (fderiv ℝ φ a).comp (fderiv ℝ (sliceParam φ a d) 0) =
      (coordinateSlice (Module.finrank ℝ E) d).subtypeL := by
  have hg := (sliceParam_contDiffAt φ (d := d) ha hψ).differentiableAt (by norm_num)
  have hf := (hφ.contDiffAt (φ.open_source.mem_nhds ha)).differentiableAt (by norm_num)
  have hf' : HasFDerivAt φ (fderiv ℝ φ a) (sliceParam φ a d 0) := by
    simpa only [sliceParam_zero φ ha d] using hf.hasFDerivAt
  have hc := hf'.comp 0 hg.hasFDerivAt
  have heq : (φ ∘ sliceParam φ a d) =ᶠ[𝓝 0]
      (fun u : coordinateSlice (Module.finrank ℝ E) d => φ a + (u : _)) :=
    sliceParam_eventually_right_inv φ ha
  have he := hc.congr_of_eventuallyEq heq.symm
  have hi := (coordinateSlice (Module.finrank ℝ E) d).subtypeL.hasFDerivAt (x := 0) |>.const_add (φ a)
  exact he.unique hi

/-- The slice parametrization takes a whole neighborhood into the native manifold. -/
theorem sliceParam_eventually_mem (φ : OpenPartialHomeomorph E
    (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) {a : E} {d : ℕ} {M : Set E}
    (ha : a ∈ φ.source) (haM : a ∈ M)
    (hslice : M ∩ φ.source = {x ∈ φ.source | ∀ i, d ≤ i.val → φ x i = 0}) :
    ∀ᶠ u : coordinateSlice (Module.finrank ℝ E) d in 𝓝 0, sliceParam φ a d u ∈ M := by
  have haS : ∀ i, d ≤ i.val → φ a i = 0 := by
    have hh : a ∈ M ∩ φ.source := ⟨haM, ha⟩
    rw [hslice] at hh
    exact hh.2
  have hc : ContinuousAt (fun u : coordinateSlice (Module.finrank ℝ E) d => φ a + (u : _)) 0 :=
    continuousAt_const.add (coordinateSlice (Module.finrank ℝ E) d).subtypeL.continuous.continuousAt
  have ht : (fun u : coordinateSlice (Module.finrank ℝ E) d => φ a + (u : _)) ⁻¹' φ.target ∈ 𝓝 0 := by
    apply hc.preimage_mem_nhds
    simpa using φ.open_target.mem_nhds (φ.map_source ha)
  filter_upwards [ht] with u hu
  have hh : sliceParam φ a d u ∈ M ∩ φ.source := by
    rw [hslice]
    refine ⟨φ.map_target hu, ?_⟩
    intro i hi
    change φ (φ.symm (φ a + (u : _))) i = 0
    rw [φ.right_inv hu]
    simpa [haS i hi] using u.property i hi
  exact hh.1

/-- Every sufficiently nearby manifold point is represented by an arbitrarily small parameter. -/
theorem sliceParam_localizes (φ : OpenPartialHomeomorph E
    (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) {a : E} {d : ℕ} {M : Set E}
    (ha : a ∈ φ.source) (haM : a ∈ M)
    (hslice : M ∩ φ.source = {x ∈ φ.source | ∀ i, d ≤ i.val → φ x i = 0})
    {r : ℝ} (hr : 0 < r) :
    ∃ ρ > 0, ∀ z ∈ M, ‖z-a‖ < ρ →
      ∃ u : coordinateSlice (Module.finrank ℝ E) d, u ∈ ball 0 r ∧ sliceParam φ a d u = z := by
  have ht : φ ⁻¹' ball (φ a) r ∈ 𝓝 a :=
    (φ.continuousAt ha).preimage_mem_nhds (ball_mem_nhds (φ a) hr)
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (φ.open_source.mem_nhds ha) ht)
  refine ⟨ρ, hρ, ?_⟩
  intro z hz hza
  have hz' := hsub (mem_ball.mpr (by simpa [dist_eq_norm] using hza))
  have haS : ∀ i, d ≤ i.val → φ a i = 0 := by
    have hh : a ∈ M ∩ φ.source := ⟨haM, ha⟩
    rw [hslice] at hh
    exact hh.2
  have hzS : ∀ i, d ≤ i.val → φ z i = 0 := by
    have hh : z ∈ M ∩ φ.source := ⟨hz, hz'.1⟩
    rw [hslice] at hh
    exact hh.2
  let u : coordinateSlice (Module.finrank ℝ E) d :=
    ⟨φ z - φ a, fun i hi => by simp [hzS i hi, haS i hi]⟩
  refine ⟨u, ?_, ?_⟩
  · simpa [u, mem_ball, dist_eq_norm] using hz'.2
  · simpa [sliceParam, u] using φ.left_inv hz'.1

end ProjLikeRetr.Spectral


open Set Metric Filter
open scoped Topology
open RandomGradFree.Nonsmooth

namespace ProjLikeRetr.Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A native C² slice chart has a neighborhood of unique global metric projections. -/
theorem native_local_unique_projection {d : ℕ} {M : Set E} {a : E}
    (hM : IsSubmanifoldAt 2 d M a) :
    ∃ ε > 0, ∀ y : E, ‖y-a‖ < ε → ∃ p : E, {z | IsMetricProjection M y z} = {p} := by
  obtain ⟨haM, φ, ha, hφ, hψ, hslice⟩ := hM
  let S := coordinateSlice (Module.finrank ℝ E) d
  let g : S → E := sliceParam φ a d
  let A := fderiv ℝ φ a
  let L := fderiv ℝ g 0
  have hinv := sliceParam_derivative_left_inverse φ (d := d) ha hφ hψ
  have hnorm : ∀ w : S, ‖w‖ ≤ ‖A‖ * ‖L w‖ := by
    intro w
    have he := congrArg (fun T : S →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => T w) hinv
    change A (L w) = (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) at he
    calc
      ‖w‖ = ‖A (L w)‖ := by rw [he]; rfl
      _ ≤ ‖A‖ * ‖L w‖ := A.le_opNorm _
  let c := 1 / (2 * (‖A‖+1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hlower : ∀ w : S, 2*c*‖w‖ ≤ ‖fderiv ℝ g 0 w‖ := by
    intro w
    change 2*c*‖w‖ ≤ ‖L w‖
    calc
      2*c*‖w‖ = ‖w‖/(‖A‖+1) := by dsimp [c]; field_simp
      _ ≤ ‖L w‖ := (div_le_iff₀ (by positivity)).mpr (by nlinarith [hnorm w, norm_nonneg (L w)])
  have hg0 : g 0 = a := sliceParam_zero φ ha d
  have hg : ContDiffAt ℝ 2 g 0 := sliceParam_contDiffAt φ ha hψ
  have hgm : ∀ᶠ u in 𝓝 (0 : S), g u ∈ M := sliceParam_eventually_mem φ ha haM hslice
  have hloc : ∀ r > 0, ∃ ρ > 0, ∀ z ∈ M, ‖z-g 0‖ < ρ → ∃ u ∈ ball (0 : S) r, g u = z := by
    intro r hr
    simpa only [hg0] using sliceParam_localizes φ (d := d) ha haM hslice hr
  simpa only [hg0] using local_unique_projection_of_parametrization hc hg hlower hgm hloc

end ProjLikeRetr.Spectral


noncomputable section
open Matrix Finset
open ProjLikeRetr.Spectral
open scoped Matrix Matrix.Norms.Frobenius RealInnerProductSpace

namespace SpectralManifoldResearch

 theorem doubly_stochastic_rearrangement {n : ℕ} (x y : Fin n → ℝ)
    (hx : Antitone x) (hy : Antitone y) (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D ∈ doublyStochastic ℝ (Fin n)) :
    x ⬝ᵥ (D *ᵥ y) ≤ x ⬝ᵥ y := by
  obtain ⟨w, hw, hw1, hwD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
  have hperm (σ : Equiv.Perm (Fin n)) :
      x ⬝ᵥ (σ.permMatrix ℝ *ᵥ y) ≤ x ⬝ᵥ y := by
    rw [Matrix.permMatrix_mulVec]
    exact (hx.monovary hy).sum_mul_comp_perm_le_sum_mul (σ := σ)
  calc
    x ⬝ᵥ (D *ᵥ y) = ∑ σ, w σ * (x ⬝ᵥ (σ.permMatrix ℝ *ᵥ y)) := by
      rw [← hwD]
      simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
        dotProduct_smul, smul_eq_mul]
    _ ≤ ∑ σ, w σ * (x ⬝ᵥ y) :=
      Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hperm σ) (hw σ)
    _ = x ⬝ᵥ y := by rw [← Finset.sum_mul, hw1, one_mul]

 theorem eig_sorted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    eig A ∈ sortedDesc n := by
  intro i j hij
  simp only [eig, dif_pos hA]
  exact hA.eigenvalues₀_antitone hij

end SpectralManifoldResearch


noncomputable section
open Matrix Finset
open ProjLikeRetr.Spectral
open scoped Matrix Matrix.Norms.Frobenius RealInnerProductSpace

namespace SpectralManifoldResearch
variable {m n : ℕ}

def matrixVector (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin m × Fin n) := WithLp.toLp 2 (fun ij => A ij.1 ij.2)

def pairing (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

theorem norm_eq_matrixVector (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = ‖matrixVector A‖ := by
  simp [Matrix.frobenius_norm_def, matrixVector, EuclideanSpace.norm_eq,
    Real.sqrt_eq_rpow, Fintype.sum_prod_type]

theorem pairing_inner (A B : Matrix (Fin m) (Fin n) ℝ) :
    pairing A B = ⟪matrixVector A, matrixVector B⟫ := by
  simp [pairing, matrixVector, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fintype.sum_prod_type, mul_comm]

theorem norm_sq_pairing (A : Matrix (Fin m) (Fin n) ℝ) : ‖A‖^2 = pairing A A := by
  rw [norm_eq_matrixVector, pairing_inner, real_inner_self_eq_norm_sq]

theorem pairing_trace (A B : Matrix (Fin m) (Fin n) ℝ) :
    pairing A B = (A.transpose * B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, pairing]
  exact Finset.sum_comm

theorem pairing_comm (A B : Matrix (Fin m) (Fin n) ℝ) : pairing A B = pairing B A := by
  simp only [pairing, mul_comm]

theorem pairing_sub_left (A B C : Matrix (Fin m) (Fin n) ℝ) :
    pairing (A-B) C = pairing A C - pairing B C := by
  simp [pairing, sub_mul, Finset.sum_sub_distrib]

theorem pairing_sub_right (A B C : Matrix (Fin m) (Fin n) ℝ) :
    pairing A (B-C) = pairing A B - pairing A C := by
  simp [pairing, mul_sub, Finset.sum_sub_distrib]

theorem norm_sub_sq (A B : Matrix (Fin m) (Fin n) ℝ) :
    ‖A-B‖^2 = ‖A‖^2 + ‖B‖^2 - 2 * pairing A B := by
  simp only [norm_sq_pairing, pairing_sub_left, pairing_sub_right]
  rw [pairing_comm B A]
  ring

theorem pairing_mul_left (P : Matrix (Fin m) (Fin m) ℝ)
    (A B : Matrix (Fin m) (Fin n) ℝ) : pairing (P*A) B = pairing A (P.transpose*B) := by
  simp only [pairing_trace, Matrix.transpose_mul, Matrix.mul_assoc]

theorem pairing_mul_right (Q : Matrix (Fin n) (Fin n) ℝ)
    (A B : Matrix (Fin m) (Fin n) ℝ) : pairing (A*Q) B = pairing A (B*Q.transpose) := by
  simp only [pairing_trace, Matrix.transpose_mul]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm Q.transpose, Matrix.mul_assoc]

theorem norm_mul_left_of_orthogonal (U : Matrix (Fin m) (Fin m) ℝ)
    (hU : U.transpose * U = 1) (A : Matrix (Fin m) (Fin n) ℝ) : ‖U*A‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_pairing, pairing_mul_left, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    ← norm_sq_pairing]

theorem norm_mul_right_of_orthogonal (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U * U.transpose = 1) (A : Matrix (Fin m) (Fin n) ℝ) : ‖A*U‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_pairing, pairing_mul_right, Matrix.mul_assoc, hU, Matrix.mul_one,
    ← norm_sq_pairing]

theorem pairing_diagonal (x y : Fin n → ℝ) :
    pairing (Matrix.diagonal x) (Matrix.diagonal y) = x ⬝ᵥ y := by
  simp [pairing, Matrix.diagonal_apply, dotProduct]

end SpectralManifoldResearch


noncomputable section
open Matrix Finset
open ProjLikeRetr.Spectral
open scoped Matrix Matrix.Norms.Frobenius RealInnerProductSpace

namespace SpectralManifoldResearch
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

def sortedBasis (hA : A.IsHermitian) : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis
    finrank_euclideanSpace).reindex (finCongr (Fintype.card_fin n))

theorem sortedBasis_apply (hA : A.IsHermitian) (i : Fin n) :
    Matrix.toEuclideanLin A (sortedBasis hA i) = eig A i • sortedBasis hA i := by
  simp [sortedBasis, OrthonormalBasis.reindex_apply, eig, dif_pos hA,
    Matrix.IsHermitian.eigenvalues₀]

def sortedUnitary (hA : A.IsHermitian) : Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix (sortedBasis hA).toBasis,
    (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_unitary (sortedBasis hA)⟩

 theorem sortedUnitary_apply (hA : A.IsHermitian) (i j : Fin n) :
    (sortedUnitary hA : Matrix (Fin n) (Fin n) ℝ) i j = sortedBasis hA j i := rfl

 theorem mul_sortedUnitary (hA : A.IsHermitian) :
    A * (sortedUnitary hA : Matrix (Fin n) (Fin n) ℝ) =
      (sortedUnitary hA : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal (WithLp.ofLp (eig A)) := by
  ext i j
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) (sortedBasis_apply hA j)
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    sortedUnitary_apply, mul_comm] using h

 theorem sorted_diagonalization (hA : A.IsHermitian) :
    A = (sortedUnitary hA : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal (WithLp.ofLp (eig A)) *
      (sortedUnitary hA : Matrix (Fin n) (Fin n) ℝ).transpose := by
  have hu := (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp (sortedUnitary hA).property
  rw [← mul_sortedUnitary, Matrix.mul_assoc, hu, Matrix.mul_one]

 theorem norm_eig (hA : A.IsHermitian) : ‖A‖ = ‖eig A‖ := by
  have hut := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp (sortedUnitary hA).property
  conv_lhs => rw [sorted_diagonalization hA]
  rw [norm_mul_right_of_orthogonal _ (by simpa using hut),
    norm_mul_left_of_orthogonal _ hut, Matrix.frobenius_norm_diagonal]

end SpectralManifoldResearch


noncomputable section
open Matrix Finset
open ProjLikeRetr.Spectral
open scoped Matrix Matrix.Norms.Frobenius RealInnerProductSpace
namespace SpectralManifoldResearch
variable {n : ℕ}

theorem orthogonal_squares_doubly_stochastic (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    (fun i j => Q i j ^ 2 : Matrix (Fin n) (Fin n) ℝ) ∈ doublyStochastic ℝ (Fin n) := by
  refine (mem_doublyStochastic_iff_sum (M := (fun i j => Q i j ^ 2 : Matrix (Fin n) (Fin n) ℝ))).mpr ?_
  refine ⟨fun i j => sq_nonneg _, ?_, ?_⟩
  · intro i
    have h := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ => T i i)
      ((Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp hQ)
    simpa [Matrix.mul_apply, pow_two] using h
  · intro j
    have h := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ => T j j)
      ((Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hQ)
    simpa [Matrix.mul_apply, pow_two] using h

theorem pairing_diagonal_conjugate (x y : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    pairing (Matrix.diagonal x) (Q * Matrix.diagonal y * Q.transpose) =
      x ⬝ᵥ ((fun i j => Q i j ^ 2) *ᵥ y) := by
  simp [pairing, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.mulVec, dotProduct,
    pow_two, mul_left_comm, mul_comm]

theorem pairing_conjugate_reduce (U V : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    pairing (U * Matrix.diagonal x * U.transpose) (V * Matrix.diagonal y * V.transpose) =
      pairing (Matrix.diagonal x)
        ((U.transpose * V) * Matrix.diagonal y * (U.transpose * V).transpose) := by
  rw [pairing_mul_right, Matrix.transpose_transpose, pairing_mul_left]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem pairing_le_eig_dot {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    pairing A B ≤ (WithLp.ofLp (eig A)) ⬝ᵥ (WithLp.ofLp (eig B)) := by
  let U : Matrix (Fin n) (Fin n) ℝ := sortedUnitary hA
  let V : Matrix (Fin n) (Fin n) ℝ := sortedUnitary hB
  have hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ := (sortedUnitary hA).property
  have hV : V ∈ Matrix.orthogonalGroup (Fin n) ℝ := (sortedUnitary hB).property
  have hQ : U.transpose * V ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    apply (Matrix.orthogonalGroup (Fin n) ℝ).mul_mem _ hV
    exact Matrix.transpose_mem_unitaryGroup_iff.mpr hU
  have hD := orthogonal_squares_doubly_stochastic (U.transpose * V) hQ
  have he : pairing A B = (WithLp.ofLp (eig A)) ⬝ᵥ
      ((fun i j => (U.transpose * V) i j ^ 2) *ᵥ WithLp.ofLp (eig B)) := by
    conv_lhs => rw [sorted_diagonalization hA, sorted_diagonalization hB]
    exact (pairing_conjugate_reduce U V _ _).trans (pairing_diagonal_conjugate _ _ _)
  rw [he]
  exact doubly_stochastic_rearrangement _ _ (eig_sorted A hA) (eig_sorted B hB) _ hD

 theorem eig_lipschitz {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : ‖eig A - eig B‖ ≤ ‖A-B‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq]
  have h := pairing_le_eig_dot hA hB
  rw [norm_eig hA, norm_eig hB]
  have hv : ‖eig A - eig B‖^2 = ‖eig A‖^2 + ‖eig B‖^2 -
      2 * ((WithLp.ofLp (eig A)) ⬝ᵥ (WithLp.ofLp (eig B))) := by
    rw [norm_sub_sq_real]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
    simp only [mul_comm]
    ring
  rw [hv]
  linarith

end SpectralManifoldResearch


noncomputable section
open Matrix Finset
open ProjLikeRetr.Spectral
open scoped Matrix Matrix.Norms.Frobenius RealInnerProductSpace
namespace SpectralManifoldResearch
variable {n : ℕ}

theorem eig_list_roots {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    A.charpoly.roots.sort (· ≥ ·) = List.ofFn (WithLp.ofLp (eig A)) := by
  have h := hA.sort_roots_charpoly_eq_eigenvalues₀
  simp only [RCLike.re_to_real, Multiset.map_id'] at h
  rw [h, List.ofFn_congr (Fintype.card_fin n)]
  simp only [eig, dif_pos hA]

theorem eig_eq_of_charpoly {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) :
    eig A = eig B := by
  apply WithLp.ofLp_injective
  apply List.ofFn_inj.mp
  rw [← eig_list_roots hA, ← eig_list_roots hB, h]

theorem eig_diagonal (p : EuclideanSpace ℝ (Fin n)) (hp : p ∈ sortedDesc n) :
    eig (Matrix.diagonal (WithLp.ofLp p)) = p := by
  apply WithLp.ofLp_injective
  apply List.ofFn_inj.mp
  rw [← eig_list_roots (Matrix.isHermitian_diagonal _)]
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Fin.univ_val_map,
      Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simpa only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using
      (show Antitone (WithLp.ofLp p) from hp).sortedGE_ofFn
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

theorem conjugate_diagonal_hermitian (U : Matrix (Fin n) (Fin n) ℝ)
    (p : EuclideanSpace ℝ (Fin n)) :
    (U * Matrix.diagonal (WithLp.ofLp p) * U.transpose).IsHermitian := by
  simpa using Matrix.isHermitian_mul_mul_conjTranspose U (Matrix.isHermitian_diagonal (WithLp.ofLp p))

theorem eig_conjugate_diagonal (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (p : EuclideanSpace ℝ (Fin n)) (hp : p ∈ sortedDesc n) :
    eig (U * Matrix.diagonal (WithLp.ofLp p) * U.transpose) = p := by
  have hc : (U * Matrix.diagonal (WithLp.ofLp p) * U.transpose).charpoly =
      (Matrix.diagonal (WithLp.ofLp p)).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hU, Matrix.one_mul]
  exact (eig_eq_of_charpoly (conjugate_diagonal_hermitian U p)
    (Matrix.isHermitian_diagonal _) hc).trans (eig_diagonal p hp)

end SpectralManifoldResearch


noncomputable section
open Matrix Finset Filter
open ProjLikeRetr.Spectral
open scoped Matrix Matrix.Norms.Frobenius RealInnerProductSpace Topology
namespace SpectralManifoldResearch
variable {n : ℕ}

theorem strict_gap_radius (a : EuclideanSpace ℝ (Fin n)) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : EuclideanSpace ℝ (Fin n), ‖x-a‖ < r →
      ∀ i j : Fin n, a j < a i → x j < x i := by
  have h : ∀ᶠ x : EuclideanSpace ℝ (Fin n) in 𝓝 a,
      ∀ i j : Fin n, a j < a i → x j < x i := by
    simp only [Filter.eventually_all]
    intro i j hij
    exact (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j)
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i)).mem_nhds hij
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨r, hr, fun x hx => hh (by simpa [dist_eq_norm] using hx)⟩

theorem sorted_small_sub (x p : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ sortedDesc n) (htie : ∀ i j, x i = x j → p i = p j) :
    ∃ η : ℝ, 0 < η ∧ x - η • p ∈ sortedDesc n := by
  have h : ∀ᶠ η : ℝ in 𝓝 0, ∀ i j : Fin n, x j < x i →
      x j - η * p j < x i - η * p i := by
    simp only [Filter.eventually_all]
    intro i j hij
    have hc : Continuous (fun η : ℝ => x j - η * p j) := by fun_prop
    have hd : Continuous (fun η : ℝ => x i - η * p i) := by fun_prop
    have hz : x j - (0:ℝ) * p j < x i - 0 * p i := by simpa using hij
    exact (isOpen_lt hc hd).mem_nhds hz
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨r/2, by positivity, ?_⟩
  have he : dist (r/2) (0:ℝ) < r := by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  have hs := hh he
  intro i j hij
  change x j - (r/2) * p j ≤ x i - (r/2) * p i
  rcases (hx i j hij).lt_or_eq with hlt | heq
  · exact (hs i j hlt).le
  · rw [heq, htie j i heq]

end SpectralManifoldResearch


noncomputable section
open Matrix Finset Filter
open ProjLikeRetr.Spectral RandomGradFree.Nonsmooth
open scoped Matrix Matrix.Norms.Frobenius RealInnerProductSpace Topology
namespace SpectralManifoldResearch
variable {n : ℕ}

theorem swap_apply (x : EuclideanSpace ℝ (Fin n)) (i j k : Fin n) :
    permAct (Equiv.swap i j) x k = x (Equiv.swap i j k) := by
  simp [permAct, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem swap_fixed (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) (h : x i = x j) :
    permAct (Equiv.swap i j) x = x := by
  ext k
  rw [swap_apply]
  by_cases hki : k=i
  · subst k; simpa using h.symm
  by_cases hkj : k=j
  · subst k; simpa using h
  · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem perm_norm_sub (σ : Equiv.Perm (Fin n)) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖permAct σ x - permAct σ y‖ = ‖x-y‖ := by
  simpa only [permAct, map_sub] using (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).norm_map (x-y)

theorem dot_swap (x p : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    (∑ k, x k * p (Equiv.swap i j k)) - (∑ k, x k * p k) =
      (x i-x j)*(p j-p i) := by
  rw [← Finset.sum_sub_distrib]
  have he (k : Fin n) : x k * p (Equiv.swap i j k) - x k * p k =
      (if k=i then x i*(p j-p i) else 0) + (if k=j then x j*(p i-p j) else 0) := by
    by_cases hki : k=i
    · subst k; simp [hij, mul_sub]
    by_cases hkj : k=j
    · subst k; simp [hij.symm, mul_sub]
    · simp [hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem norm_sub_swap_le (x p : EuclideanSpace ℝ (Fin n)) (i j : Fin n)
    (hij : i ≠ j) (hx : x j ≤ x i) (hp : p i ≤ p j) :
    ‖x - permAct (Equiv.swap i j) p‖ ≤ ‖x-p‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hn : ‖permAct (Equiv.swap i j) p‖ = ‖p‖ :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)).norm_map p
  have hd := dot_swap (WithLp.ofLp x) (WithLp.ofLp p) i j hij
  have hdot : ⟪x,p⟫ ≤ ⟪x,permAct (Equiv.swap i j) p⟫ := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      swap_apply] at *
    simp only [mul_comm]
    have hz := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hp)
    nlinarith
  rw [norm_sub_sq_real, norm_sub_sq_real, hn]
  linarith

end SpectralManifoldResearch


noncomputable section
open Matrix Finset Filter
open ProjLikeRetr.Spectral RandomGradFree.Nonsmooth
open scoped Matrix Matrix.Norms.Frobenius RealInnerProductSpace Topology
namespace SpectralManifoldResearch
variable {n : ℕ}

theorem local_swap_mem {M : Set (EuclideanSpace ℝ (Fin n))}
    {a p : EuclideanSpace ℝ (Fin n)} {δ : ℝ}
    (hδ : 0 < δ) (ha : a ∈ M) (hp : p ∈ M) (hpb : ‖p-a‖ < δ)
    (hs : IsStronglyLocallySymmetric M a δ)
    (i j : Fin n) (hij : a i = a j) : permAct (Equiv.swap i j) p ∈ M := by
  have hab : a ∈ M ∩ Metric.ball a δ := ⟨ha, by simpa using hδ⟩
  have hpm : p ∈ M ∩ Metric.ball a δ := ⟨hp, by simpa [Metric.mem_ball, dist_eq_norm] using hpb⟩
  have he := hs a hab (Equiv.swap i j) (swap_fixed a i j hij)
  have hm : permAct (Equiv.swap i j) p ∈ permAct (Equiv.swap i j) '' (M ∩ Metric.ball a δ) :=
    ⟨p, hpm, rfl⟩
  rw [he] at hm
  exact hm.1

theorem projection_sorted_and_ties {M : Set (EuclideanSpace ℝ (Fin n))}
    {a x p : EuclideanSpace ℝ (Fin n)} {δ : ℝ}
    (hδ : 0 < δ) (ha : a ∈ M) (has : a ∈ sortedDesc n) (hxs : x ∈ sortedDesc n)
    (hs : IsStronglyLocallySymmetric M a δ)
    (hp : IsMetricProjection M x p)
    (hu : ∀ q, IsMetricProjection M x q → q=p) (hpb : ‖p-a‖ < δ)
    (hgapP : ∀ i j, a j < a i → p j < p i)
    (hgapX : ∀ i j, a j < a i → x j < x i) :
    p ∈ sortedDesc n ∧ ∀ i j, x i=x j → p i=p j := by
  have hswap (i j : Fin n) (he : a i=a j)
      (hd : ‖x-permAct (Equiv.swap i j) p‖ ≤ ‖x-p‖) :
      permAct (Equiv.swap i j) p = p := by
    apply hu
    exact ⟨local_swap_mem hδ ha hp.1 hpb hs i j he, fun q hq => hd.trans (hp.2 q hq)⟩
  constructor
  · intro i j hij
    by_contra hn
    have hlt : p i < p j := lt_of_not_ge hn
    have hne : i ≠ j := by intro he; subst j; exact (lt_irrefl _ hlt)
    have he : a i=a j := by
      apply le_antisymm _ (has i j hij)
      by_contra hn
      have hh := hgapP i j (lt_of_not_ge hn)
      exact (not_lt_of_ge hh.le) hlt
    have hd := norm_sub_swap_le x p i j hne (hxs i j hij) hlt.le
    have hh := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) (hswap i j he hd)
    simp only [swap_apply, Equiv.swap_apply_left] at hh
    linarith
  · intro i j hxij
    have he : a i=a j := by
      rcases lt_trichotomy (a i) (a j) with hlt | he | hgt
      · have hh := hgapX j i hlt; linarith
      · exact he
      · have hh := hgapX i j hgt; linarith
    have hxf := swap_fixed x i j hxij
    have hd : ‖x-permAct (Equiv.swap i j) p‖ = ‖x-p‖ := by
      conv_lhs => rw [← hxf]
      exact perm_norm_sub _ x p
    have hh := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) (hswap i j he hd.le)
    simpa only [swap_apply, Equiv.swap_apply_left] using hh.symm

end SpectralManifoldResearch


noncomputable section
open Matrix Finset Filter
open ProjLikeRetr.Spectral RandomGradFree.Nonsmooth
open scoped Matrix Matrix.Norms.Frobenius RealInnerProductSpace Topology
namespace SpectralManifoldResearch
variable {n : ℕ}

theorem conjugate_sub (U : Matrix (Fin n) (Fin n) ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) :
    U * Matrix.diagonal (WithLp.ofLp x) * U.transpose -
      U * Matrix.diagonal (WithLp.ofLp p) * U.transpose =
      U * Matrix.diagonal (WithLp.ofLp (x-p)) * U.transpose := by
  rw [WithLp.ofLp_sub]
  have hd : Matrix.diagonal (WithLp.ofLp x - WithLp.ofLp p) =
      Matrix.diagonal (WithLp.ofLp x) - Matrix.diagonal (WithLp.ofLp p) :=
    (Matrix.diagonal_sub (WithLp.ofLp x) (WithLp.ofLp p)).symm
  rw [hd, Matrix.mul_sub, Matrix.sub_mul]

theorem conjugate_sub_smul (U : Matrix (Fin n) (Fin n) ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) (η : ℝ) :
    U * Matrix.diagonal (WithLp.ofLp x) * U.transpose -
      η • (U * Matrix.diagonal (WithLp.ofLp p) * U.transpose) =
      U * Matrix.diagonal (WithLp.ofLp (x-η•p)) * U.transpose := by
  rw [WithLp.ofLp_sub, WithLp.ofLp_smul]
  have hd : Matrix.diagonal (WithLp.ofLp x - η • WithLp.ofLp p) =
      Matrix.diagonal (WithLp.ofLp x) - Matrix.diagonal (η • WithLp.ofLp p) :=
    (Matrix.diagonal_sub (WithLp.ofLp x) (η • WithLp.ofLp p)).symm
  rw [hd, Matrix.diagonal_smul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem conjugate_norm (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ) (p : EuclideanSpace ℝ (Fin n)) :
    ‖U * Matrix.diagonal (WithLp.ofLp p) * U.transpose‖ = ‖p‖ := by
  have hu := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hU
  rw [norm_mul_right_of_orthogonal _ (by simpa using hu),
    norm_mul_left_of_orthogonal _ hu, Matrix.frobenius_norm_diagonal]

theorem matrix_projection_of_unique_vector {M : Set (EuclideanSpace ℝ (Fin n))}
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian)
    (p : EuclideanSpace ℝ (Fin n)) (hp : IsMetricProjection M (eig X) p)
    (huniq : ∀ q, IsMetricProjection M (eig X) q → q=p)
    (hps : p ∈ sortedDesc n) (htie : ∀ i j, eig X i=eig X j → p i=p j)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (hdiag : X=U*Matrix.diagonal (WithLp.ofLp (eig X))*U.transpose) :
    {Y | IsMetricProjection (specSet (M ∩ sortedDesc n)) X Y} =
      {U * Matrix.diagonal (WithLp.ofLp p) * U.transpose} := by
  let Z := U * Matrix.diagonal (WithLp.ofLp p) * U.transpose
  have hZ : Z.IsHermitian := conjugate_diagonal_hermitian U p
  have heZ : eig Z=p := eig_conjugate_diagonal U hU p hps
  have hnZ : ‖Z‖=‖p‖ := conjugate_norm U hU p
  have hd : ‖X-Z‖=‖eig X-p‖ := by
    conv_lhs => rw [hdiag]
    rw [show U * Matrix.diagonal (WithLp.ofLp (eig X)) * U.transpose - Z =
      U * Matrix.diagonal (WithLp.ofLp (eig X-p)) * U.transpose from conjugate_sub U _ p]
    exact conjugate_norm U hU _
  have hZmin : IsMetricProjection (specSet (M ∩ sortedDesc n)) X Z := by
    refine ⟨⟨hZ, ?_⟩, ?_⟩
    · rw [heZ]; exact ⟨hp.1,hps⟩
    · intro Y hY
      rw [hd]
      exact (hp.2 (eig Y) hY.2.1).trans (eig_lipschitz hX hY.1)
  have unique (Y : Matrix (Fin n) (Fin n) ℝ)
      (hY : IsMetricProjection (specSet (M ∩ sortedDesc n)) X Y) : Y=Z := by
    have hdist : ‖X-Y‖=‖X-Z‖ := le_antisymm (hY.2 Z hZmin.1) (hZmin.2 Y hY.1)
    have hep : eig Y=p := by
      apply huniq
      refine ⟨hY.1.2.1, fun q hq => ?_⟩
      calc
        ‖eig X-eig Y‖ ≤ ‖X-Y‖ := eig_lipschitz hX hY.1.1
        _ = ‖eig X-p‖ := hdist.trans hd
        _ ≤ ‖eig X-q‖ := hp.2 q hq
    have hnY : ‖Y‖=‖p‖ := (norm_eig hY.1.1).trans (congrArg norm hep)
    have hpair : pairing X Y = (WithLp.ofLp (eig X)) ⬝ᵥ (WithLp.ofLp p) := by
      have hh := congrArg (fun t : ℝ => t^2) (hdist.trans hd)
      rw [norm_sub_sq, norm_eig hX, hnY, norm_sub_sq_real] at hh
      have hi : ⟪eig X,p⟫ = (WithLp.ofLp (eig X)) ⬝ᵥ (WithLp.ofLp p) := by
        simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
      rw [hi] at hh
      linarith
    obtain ⟨η,hη,hηs⟩ := sorted_small_sub (eig X) p (eig_sorted X hX) htie
    have ht : X-η•Z = U*Matrix.diagonal (WithLp.ofLp (eig X-η•p))*U.transpose := by
      conv_lhs => rw [hdiag]
      exact conjugate_sub_smul U _ p η
    have hh : (X-η•Z).IsHermitian := by rw [ht]; exact conjugate_diagonal_hermitian U _
    have he : eig (X-η•Z)=eig X-η•p := by rw [ht]; exact eig_conjugate_diagonal U hU _ hηs
    have bound := pairing_le_eig_dot hh hY.1.1
    rw [he,hep,pairing_sub_left] at bound
    have hsm : pairing (η•Z) Y=η*pairing Z Y := by
      simp [pairing, mul_assoc, Finset.mul_sum]
    have hdot : (WithLp.ofLp (eig X-η•p)) ⬝ᵥ (WithLp.ofLp p) =
        (WithLp.ofLp (eig X)) ⬝ᵥ (WithLp.ofLp p) - η*‖p‖^2 := by
      have hi : (WithLp.ofLp p) ⬝ᵥ (WithLp.ofLp p)=‖p‖^2 := by
        rw [← real_inner_self_eq_norm_sq p]
        simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct,
        smul_eq_mul, hi]
    rw [hsm,hpair,hdot] at bound
    have hge : ‖p‖^2 ≤ pairing Z Y := by nlinarith
    have hz : ‖Y-Z‖^2 ≤ 0 := by
      rw [norm_sub_sq,hnY,hnZ,pairing_comm Y Z]
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (Y-Z)]))
  ext Y
  constructor
  · intro hY; exact unique Y hY
  · intro hY
    have he : Y=Z := hY
    rw [he]
    exact hZmin

end SpectralManifoldResearch


open RandomGradFree.Nonsmooth
open scoped Matrix Matrix.Norms.Frobenius

namespace ProjLikeRetr.Spectral

/-- Theorem 3.9, p. 14 (projection onto spectral manifolds), under the hypotheses of
Theorem 3.5, p. 12. -/
theorem native_spectral_recovery {n d : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (hM : IsSubmanifold 2 d M) (Xbar : Matrix (Fin n) (Fin n) ℝ)
    (hXbar : Xbar ∈ specSet (M ∩ sortedDesc n)) (δ : ℝ) (hδ : 0 < δ)
    (hsym : IsStronglyLocallySymmetric M (eig Xbar) δ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ δ ∧ ∀ X : Matrix (Fin n) (Fin n) ℝ, X.IsHermitian →
      ‖X - Xbar‖ ≤ δ₀ / 2 →
      ∃ p : EuclideanSpace ℝ (Fin n), {z | IsMetricProjection M (eig X) z} = {p} ∧
        ∀ U ∈ Matrix.orthogonalGroup (Fin n) ℝ,
          X = U * Matrix.diagonal (WithLp.ofLp (eig X)) * Uᵀ →
          {Y | IsMetricProjection (specSet (M ∩ sortedDesc n)) X Y} =
            {U * Matrix.diagonal (WithLp.ofLp p) * Uᵀ} := by
  have hb : Xbar.IsHermitian ∧ eig Xbar ∈ M ∩ sortedDesc n := hXbar
  obtain ⟨ε, hε, hlocal⟩ := native_local_unique_projection (hM.2 (eig Xbar) hb.2.1)
  obtain ⟨r, hr, hgap⟩ := SpectralManifoldResearch.strict_gap_radius (eig Xbar)
  let δ₀ := min δ (min ε r) / 2
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hdδ : δ₀ < δ := by
    have := min_le_left δ (min ε r)
    have := lt_min hδ (lt_min hε hr)
    dsimp [δ₀]; linarith
  have hdε : δ₀ < ε := by
    have h1 := min_le_right δ (min ε r)
    have h2 := min_le_left ε r
    have := lt_min hδ (lt_min hε hr)
    dsimp [δ₀]; linarith
  have hdr : δ₀ < r := by
    have h1 := min_le_right δ (min ε r)
    have h2 := min_le_right ε r
    have := lt_min hδ (lt_min hε hr)
    dsimp [δ₀]; linarith
  refine ⟨δ₀, hδ₀, hdδ.le, ?_⟩
  intro X hX hnear
  have hx : ‖eig X-eig Xbar‖ ≤ δ₀/2 :=
    (SpectralManifoldResearch.eig_lipschitz hX hb.1).trans hnear
  obtain ⟨p, hpSet⟩ := hlocal (eig X) (by linarith)
  have hp : IsMetricProjection M (eig X) p := by
    have hh : p ∈ ({p} : Set (EuclideanSpace ℝ (Fin n))) := by simp
    rw [← hpSet] at hh
    exact hh
  have huniq : ∀ q, IsMetricProjection M (eig X) q → q=p := by
    intro q hq
    have hh : q ∈ {z | IsMetricProjection M (eig X) z} := hq
    rw [hpSet] at hh
    exact hh
  have hpnear := projection_near_base hb.2.1 hp
  obtain ⟨hps, htie⟩ := SpectralManifoldResearch.projection_sorted_and_ties
    hδ hb.2.1 hb.2.2 (SpectralManifoldResearch.eig_sorted X hX) hsym hp huniq
    (by linarith) (hgap p (by linarith)) (hgap (eig X) (by linarith))
  refine ⟨p, hpSet, ?_⟩
  intro U hU hdiag
  exact SpectralManifoldResearch.matrix_projection_of_unique_vector hX p hp huniq hps htie U hU hdiag


end ProjLikeRetr.Spectral


open scoped Matrix Matrix.Norms.Frobenius
open RandomGradFree.Nonsmooth

namespace ProjLikeRetr.Spectral

/-- Theorem 3.9, p. 14 (projection onto spectral manifolds), under the hypotheses of
Theorem 3.5, p. 12. -/
theorem projection_spectral_manifold {n d : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (hM : IsSubmanifold 2 d M) (Xbar : Matrix (Fin n) (Fin n) ℝ)
    (hXbar : Xbar ∈ specSet (M ∩ sortedDesc n)) (δ : ℝ) (hδ : 0 < δ)
    (hsym : IsStronglyLocallySymmetric M (eig Xbar) δ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ δ ∧ ∀ X : Matrix (Fin n) (Fin n) ℝ, X.IsHermitian →
      ‖X - Xbar‖ ≤ δ₀ / 2 →
      ∃ p : EuclideanSpace ℝ (Fin n), {z | IsMetricProjection M (eig X) z} = {p} ∧
        ∀ U ∈ Matrix.orthogonalGroup (Fin n) ℝ,
          X = U * Matrix.diagonal (WithLp.ofLp (eig X)) * Uᵀ →
          {Y | IsMetricProjection (specSet (M ∩ sortedDesc n)) X Y} =
            {U * Matrix.diagonal (WithLp.ofLp p) * Uᵀ} := by
  exact native_spectral_recovery M hM Xbar hXbar δ hδ hsym

end ProjLikeRetr.Spectral

open ProjLikeRetr.Spectral

theorem solution {n d : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (hM : IsSubmanifold 2 d M) (Xbar : Matrix (Fin n) (Fin n) ℝ)
    (hXbar : Xbar ∈ specSet (M ∩ sortedDesc n)) (δ : ℝ) (hδ : 0 < δ)
    (hsym : IsStronglyLocallySymmetric M (eig Xbar) δ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ δ ∧ ∀ X : Matrix (Fin n) (Fin n) ℝ, X.IsHermitian →
      ‖X - Xbar‖ ≤ δ₀ / 2 →
      ∃ p : EuclideanSpace ℝ (Fin n), {z | IsMetricProjection M (eig X) z} = {p} ∧
        ∀ U ∈ Matrix.orthogonalGroup (Fin n) ℝ,
          X = U * Matrix.diagonal (WithLp.ofLp (eig X)) * Uᵀ →
          {Y | IsMetricProjection (specSet (M ∩ sortedDesc n)) X Y} =
            {U * Matrix.diagonal (WithLp.ofLp p) * Uᵀ} := ProjLikeRetr.Spectral.projection_spectral_manifold M hM Xbar hXbar δ hδ hsym
