-- Prove2me | solution 1 for VectorValuedHolomorphy.exists_differentiableOn_extension
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:13:05.734847+00:00
-- url     : https://prove2.me/submissions/42e9ad6f-14b1-45d8-b90c-26cc284d2b8d

import Mathlib
import Theorems.Thm_VectorValuedHolomorphy_differentiableOn_iff_forall_strongDual

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace Sol_VectorValuedHolomorphy_exists_differentiableOn_extension

open Bornology Set

/-- The derivative of a curve in a topological vector space is the limit of its slopes. -/
theorem hasDerivAt_iff_tendsto_slope_tvs {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (f : ℂ → E) (z : ℂ)
    (v : E) : HasDerivAt f v z ↔
      Tendsto (fun w ↦ (w - z)⁻¹ • (f w - f z)) (𝓝[≠] z) (𝓝 v) := by
  rw [hasDerivAt_iff_hasFDerivAt, ← hasFDerivWithinAt_univ,
    ← hasFDerivWithinAt_sdiff_singleton_self, ← Set.compl_eq_univ_sdiff,
    hasFDerivWithinAt_iff_isLittleOTVS]
  change (fun w ↦ f w - f z - (w - z) • v) =o[ℂ; 𝓝[≠] z] (fun w ↦ w - z) ↔ _
  rw [Asymptotics.isLittleOTVS_iff_tendsto_inv_smul (by
    filter_upwards with w hw
    simp [sub_eq_zero.mp hw])]
  conv_rhs => rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_congr'
  filter_upwards [eventually_mem_nhdsWithin] with w hw
  simp [smul_sub, inv_smul_smul₀ (sub_ne_zero.mpr hw)]

/-- A continuous linear functional is bounded on a von Neumann bounded set. -/
theorem exists_norm_le_of_isVonNBounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] {s : Set E} (hs : IsVonNBounded ℂ s) (ℓ : StrongDual ℂ E) :
    ∃ C : ℝ, ∀ x ∈ s, ‖ℓ x‖ ≤ C := by
  have h : IsVonNBounded ℂ (ℓ '' s) := hs.image ℓ
  rw [NormedSpace.isVonNBounded_iff] at h
  obtain ⟨C, hC⟩ := h.exists_norm_le
  exact ⟨C, fun x hx ↦ hC _ (mem_image_of_mem _ hx)⟩

/-- If `Z` has no accumulation point in the open set `U`, then `U \ Z` is open. -/
theorem isOpen_diff_of_eventually_notMem {U Z : Set ℂ} (hU : IsOpen U)
    (hZ : ∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, w ∉ Z) : IsOpen (U \ Z) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hzU, hzZ⟩
  filter_upwards [hU.mem_nhds hzU, eventually_nhdsWithin_iff.mp (hZ z hzU)] with w hwU hw
  refine ⟨hwU, ?_⟩
  by_cases hwz : w = z
  · rwa [hwz]
  · exact hw hwz

/-- Every point `z` of `U` is the centre of an open disc contained in `U` which meets `Z` at most
at `z`. -/
theorem exists_ball_subset {U Z : Set ℂ} (hU : IsOpen U)
    (hZ : ∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {z : ℂ} (hz : z ∈ U) {V : Set ℂ} (hV : V ∈ 𝓝 z) :
    ∃ ε : ℝ, 0 < ε ∧ ball z ε ⊆ V ∧ ball z ε \ {z} ⊆ U \ Z := by
  have h : V ∩ (U ∩ {w | w ∈ ({z}ᶜ : Set ℂ) → w ∉ Z}) ∈ 𝓝 z :=
    inter_mem hV (inter_mem (hU.mem_nhds hz) (eventually_nhdsWithin_iff.mp (hZ z hz)))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨ε, hε, fun w hw ↦ (hsub hw).1, ?_⟩
  rintro w ⟨hw, hwz⟩
  exact ⟨(hsub hw).2.1, (hsub hw).2.2 hwz⟩

/-- Existence of the limit at a point of `U`: a holomorphic function which is bounded on a
punctured disc around `z₀` has a limit in `E` at `z₀`. -/
theorem exists_tendsto {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {U Z : Set ℂ} (hU : IsOpen U)
    (hZ : ∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {f : ℂ → E} (hf : DifferentiableOn ℂ f (U \ Z))
    (hb : ∀ z ∈ U, ∃ (c : ℂ) (r : ℝ), z ∈ ball c r ∧ ball c r ⊆ U ∧
      Bornology.IsVonNBounded ℂ (f '' (ball c r \ Z))) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ L : E, Tendsto f (𝓝[≠] z₀) (𝓝 L) := by
  have hUZ : IsOpen (U \ Z) := isOpen_diff_of_eventually_notMem hU hZ
  obtain ⟨c, r, hzc, -, hbdd⟩ := hb z₀ hz₀
  obtain ⟨ε, hε, hεsub, hεZ⟩ := exists_ball_subset hU hZ hz₀ (isOpen_ball.mem_nhds hzc)
  -- the auxiliary function `G w = (w - z₀) • f w`
  let G : ℂ → E := fun w ↦ (w - z₀) • f w
  have hG : DifferentiableOn ℂ G (ball z₀ ε) := by
    rw [VectorValuedHolomorphy.differentiableOn_iff_forall_strongDual isOpen_ball]
    intro ℓ
    have hφ : DifferentiableOn ℂ (fun w ↦ ℓ (f w)) (U \ Z) :=
      (VectorValuedHolomorphy.differentiableOn_iff_forall_strongDual hUZ f).mp hf ℓ
    obtain ⟨C, hC⟩ := exists_norm_le_of_isVonNBounded hbdd ℓ
    have hψ : (fun w ↦ ℓ (G w)) = fun w ↦ (w - z₀) * ℓ (f w) := by
      funext w
      simp [G]
    rw [hψ]
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (ball_mem_nhds z₀ hε)).mp ⟨?_, ?_⟩
    · exact ((differentiableOn_id.sub (differentiableOn_const z₀)).mul hφ).mono hεZ
    · have h0 : Tendsto (fun w : ℂ ↦ ‖w - z₀‖ * C) (𝓝 z₀) (𝓝 0) := by
        have hcont : Continuous (fun w : ℂ ↦ ‖w - z₀‖ * C) := by fun_prop
        simpa using hcont.tendsto z₀
      have hle : ∀ᶠ w in 𝓝 z₀, ‖(w - z₀) * ℓ (f w)‖ ≤ ‖w - z₀‖ * C := by
        filter_upwards [ball_mem_nhds z₀ hε] with w hw
        by_cases hwz : w = z₀
        · simp [hwz]
        · rw [norm_mul]
          refine mul_le_mul_of_nonneg_left (hC _ (mem_image_of_mem f ?_)) (norm_nonneg _)
          exact ⟨hεsub hw, (hεZ ⟨hw, hwz⟩).2⟩
      have ht : Tendsto (fun w : ℂ ↦ (w - z₀) * ℓ (f w)) (𝓝 z₀) (𝓝 0) :=
        squeeze_zero_norm' hle h0
      simpa [ContinuousAt] using ht
  -- `f` is the slope of `G` at `z₀`
  have hGz : DifferentiableAt ℂ G z₀ := hG.differentiableAt (ball_mem_nhds z₀ hε)
  refine ⟨fderiv ℂ G z₀ 1, ?_⟩
  have hslope := (hasDerivAt_iff_tendsto_slope_tvs G z₀ (fderiv ℂ G z₀ 1)).mp
    (hasFDerivAt_iff_hasDerivAt.mp hGz.hasFDerivAt)
  refine hslope.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with w hw
  simp [G, inv_smul_smul₀ (sub_ne_zero.mpr hw)]

end Sol_VectorValuedHolomorphy_exists_differentiableOn_extension

open Sol_VectorValuedHolomorphy_exists_differentiableOn_extension in
theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {U Z : Set ℂ} (hU : IsOpen U)
    (hZ : ∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {f : ℂ → E} (hf : DifferentiableOn ℂ f (U \ Z))
    (hb : ∀ z ∈ U, ∃ (c : ℂ) (r : ℝ), z ∈ ball c r ∧ ball c r ⊆ U ∧
      Bornology.IsVonNBounded ℂ (f '' (ball c r \ Z))) :
    ∃ g : ℂ → E, DifferentiableOn ℂ g U ∧ Set.EqOn g f (U \ Z) ∧
      ∀ g' : ℂ → E, DifferentiableOn ℂ g' U → Set.EqOn g' f (U \ Z) → Set.EqOn g' g U := by
  classical
  have hUZ : IsOpen (U \ Z) := isOpen_diff_of_eventually_notMem hU hZ
  -- the extension: the limit of `f` at the points of `Z`, and `f` elsewhere
  let g : ℂ → E := fun z ↦ if z ∈ Z then limUnder (𝓝[≠] z) f else f z
  have hgf : ∀ z, z ∉ Z → g z = f z := fun z hz ↦ if_neg hz
  -- `f` tends to `g z` at every point `z` of `U`
  have hlim : ∀ z ∈ U, Tendsto f (𝓝[≠] z) (𝓝 (g z)) := by
    intro z hz
    by_cases hzZ : z ∈ Z
    · have hgz : g z = limUnder (𝓝[≠] z) f := if_pos hzZ
      rw [hgz]
      exact tendsto_nhds_limUnder (exists_tendsto hU hZ hf hb hz)
    · rw [hgf z hzZ]
      exact ((hf.continuousOn.continuousAt (hUZ.mem_nhds ⟨hz, hzZ⟩)).tendsto).mono_left
        nhdsWithin_le_nhds
  -- `g` and `f` agree on a punctured neighbourhood of every point of `U`
  have hev : ∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, g w = f w := by
    intro z hz
    filter_upwards [hZ z hz] with w hw
    exact hgf w hw
  refine ⟨g, ?_, fun z hz ↦ hgf z hz.2, ?_⟩
  · -- `g` is weakly holomorphic, hence holomorphic
    rw [VectorValuedHolomorphy.differentiableOn_iff_forall_strongDual hU]
    intro ℓ z hz
    have hφ : DifferentiableOn ℂ (fun w ↦ ℓ (f w)) (U \ Z) :=
      (VectorValuedHolomorphy.differentiableOn_iff_forall_strongDual hUZ f).mp hf ℓ
    obtain ⟨ε, hε, -, hεZ⟩ := exists_ball_subset hU hZ hz univ_mem
    have hd : DifferentiableOn ℂ (fun w ↦ ℓ (g w)) (ball z ε) := by
      refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
        (ball_mem_nhds z hε)).mp ⟨?_, ?_⟩
      · refine (hφ.mono hεZ).congr fun w hw ↦ ?_
        show ℓ (g w) = ℓ (f w)
        rw [hgf w (hεZ hw).2]
      · rw [continuousAt_iff_punctured_nhds]
        have h1 : Tendsto (fun w ↦ ℓ (f w)) (𝓝[≠] z) (𝓝 (ℓ (g z))) :=
          (ℓ.continuous.tendsto (g z)).comp (hlim z hz)
        refine h1.congr' ?_
        filter_upwards [hev z hz] with w hw
        rw [hw]
    exact (hd.differentiableAt (ball_mem_nhds z hε)).differentiableWithinAt
  · -- uniqueness: a holomorphic extension is continuous, so its values on `Z` are limits of `f`
    intro g' hg' hg'f z hz
    have hc : Tendsto g' (𝓝[≠] z) (𝓝 (g' z)) :=
      ((hg'.continuousOn.continuousAt (hU.mem_nhds hz)).tendsto).mono_left nhdsWithin_le_nhds
    have hc' : Tendsto f (𝓝[≠] z) (𝓝 (g' z)) := by
      refine hc.congr' ?_
      filter_upwards [hZ z hz, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz)] with w hwZ hwU
      exact hg'f ⟨hwU, hwZ⟩
    exact tendsto_nhds_unique hc' (hlim z hz)
