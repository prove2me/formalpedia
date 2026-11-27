-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HolomorphicImplicitGraph_proof_32f8f2cccda3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:57:23.037216+00:00
-- url     : https://prove2.me/submissions/b39ff1e4-8fa0-4847-85ea-08cd14973d0a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsHolomorphicImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PHolomorphicImplicitGraph
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HolomorphicImplicitGraph_exists_coordSplitting_e16b4bef2921

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Module Function
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace HolomorphicImplicitGraph
theorem _root_.solution : HolomorphicImplicitGraph.Statement := by
  classical
  intro n m f y V hf hV hyV hfy hK

  let L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin (n - m) → ℂ) :=
    LinearMap.pi fun i => (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ)
  obtain ⟨e, he⟩ := exists_coordSplitting L (by rw [LinearMap.ker_pi]; exact hK)

  let F : EuclideanSpace ℂ (Fin n) → (Fin n → ℂ) := fun z j =>
    Sum.elim (fun _ => z j) (fun i => f i z) (e j)
  let D : EuclideanSpace ℂ (Fin n) → (EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) := fun z =>
    ContinuousLinearMap.pi fun j =>
      Sum.elim (fun _ => EuclideanSpace.proj j) (fun i => fderiv ℂ (f i) z) (e j)
  have hFd : ∀ z, HasFDerivAt F (D z) z := by
    intro z
    refine hasFDerivAt_pi.2 fun j => ?_
    rcases h : e j with k | i
    · simp only [Sum.elim_inl]
      exact (EuclideanSpace.proj (𝕜 := ℂ) j).hasFDerivAt
    · simp only [Sum.elim_inr]
      exact ((hf i).differentiable one_ne_zero z).hasFDerivAt
  have hFc : ContDiff ℂ 1 F := by
    refine contDiff_pi.2 fun j => ?_
    rcases h : e j with k | i
    · simp only [F, h, Sum.elim_inl]
      exact (EuclideanSpace.proj (𝕜 := ℂ) j).contDiff
    · simp only [F, h, Sum.elim_inr]
      exact hf i

  have hDy : Injective (D y) := by
    refine (injective_iff_map_eq_zero (D y)).2 fun v hv => he v (fun j k hj => ?_) ?_
    · have := congr_fun hv j
      simpa [D, hj] using this
    · funext i
      have := congr_fun hv (e.symm (Sum.inr i))
      simpa [D, L] using this
  let A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) :=
    (LinearEquiv.ofInjectiveOfFinrankEq (D y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) hDy
      (by simp)).toContinuousLinearEquiv
  have hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) = D y := by
    ext1 v
    rfl
  let P := hFc.contDiffAt.toOpenPartialHomeomorph F (f' := A) (by rw [hA]; exact hFd y) one_ne_zero

  let W : Set (EuclideanSpace ℂ (Fin n)) := (fun z => fderiv ℂ F z) ⁻¹'
    Set.range ((↑) : (EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ)) → _)
  have hW : IsOpen W := ContinuousLinearEquiv.isOpen.preimage (hFc.continuous_fderiv one_ne_zero)
  have hyW : y ∈ W := ⟨A, by rw [hA]; exact (hFd y).fderiv.symm⟩
  have hWinj : ∀ z ∈ W, Injective (D z) := by
    rintro z ⟨A', hA'⟩
    have hA'' : (A' : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F z := hA'
    rw [← (hFd z).fderiv, ← hA'']
    exact A'.injective
  let U := P.source ∩ V ∩ W
  have hU : IsOpen U := (P.open_source.inter hV).inter hW
  have hyU : y ∈ U := ⟨⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, hyV⟩, hyW⟩

  let ι : EuclideanSpace ℂ (Fin m) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun j =>
    Sum.elim (fun k => EuclideanSpace.proj k) (fun _ => (0 : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ)) (e j)
  let g := P.symm
  let Φ : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m)) := fun x =>
    WithLp.toLp 2 fun i => g (ι x) (e.symm (Sum.inr i))
  let Ω : Set (EuclideanSpace ℂ (Fin m)) := ι ⁻¹' (P.target ∩ g ⁻¹' U)
  have hΩ : IsOpen Ω := (P.isOpen_inter_preimage_symm hU).preimage ι.continuous
  have hG : ∀ x, ι x ∈ P.target → graphPt e Φ x = g (ι x) := by
    intro x hx
    have hFg : F (g (ι x)) = ι x := P.right_inv hx
    refine PiLp.ext fun j => ?_
    have hj := congr_fun hFg j
    rcases h : e j with k | i
    · simp [graphPt, F, ι, h] at hj ⊢
      exact hj.symm
    · have hs : e.symm (Sum.inr i) = j := e.symm_apply_eq.2 h.symm
      simp [graphPt, Φ, h, hs]
  have hzero : ∀ x, ι x ∈ P.target → ∀ i, f i (g (ι x)) = 0 := by
    intro x hx i
    have := congr_fun (P.right_inv hx) (e.symm (Sum.inr i))
    simpa [P, F, ι] using this
  let pin : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin m) := fun z =>
    WithLp.toLp 2 fun k => z (e.symm (Sum.inl k))
  have hFpin : ∀ z, (∀ i, f i z = 0) → F z = ι (pin z) := by
    intro z hz
    funext j
    rcases h : e j with k | i
    · have hs : e.symm (Sum.inl k) = j := e.symm_apply_eq.2 h.symm
      simp [F, ι, pin, h, hs]
    · simp [F, ι, h, hz i]
  have hgdiff : ∀ x ∈ Ω, DifferentiableAt ℂ g (ι x) := by
    intro x hx
    obtain ⟨A', hA'⟩ := hx.2.2
    have h1 : HasFDerivAt P (A' : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) (P.symm (ι x)) := by
      rw [hA']
      exact (hFd _).differentiableAt.hasFDerivAt
    exact (P.contDiffAt_symm hx.1 h1 hFc.contDiffAt).differentiableAt one_ne_zero
  refine ⟨e, Ω, Φ, U, hU, hyU, fun z hz => hz.1.2, hΩ, ?_, ?_, ?_⟩
  · intro x hx
    refine (differentiableAt_euclidean.2 fun i => ?_).differentiableWithinAt
    show DifferentiableAt ℂ (fun x => g (ι x) (e.symm (Sum.inr i))) x
    exact (EuclideanSpace.proj (𝕜 := ℂ) (e.symm (Sum.inr i))).differentiableAt.comp x
      ((hgdiff x hx).comp x ι.differentiableAt)
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hG x hx.1]
      exact ⟨hx.2, hzero x hx.1⟩
    · rintro ⟨hzU, hz0⟩
      have hFz := hFpin z hz0
      have ht : ι (pin z) ∈ P.target := by
        rw [← hFz]
        exact P.map_source hzU.1.1
      have hgz : g (ι (pin z)) = z := by
        rw [← hFz]
        exact P.left_inv hzU.1.1
      refine ⟨pin z, ⟨ht, ?_⟩, by rw [hG _ ht, hgz]⟩
      show g (ι (pin z)) ∈ U
      rw [hgz]
      exact hzU
  · intro x hx
    have hgx := hgdiff x hx
    let g' := fderiv ℂ g (ι x)
    have hGd : HasFDerivAt (graphPt e Φ) (g'.comp ι) x := by
      have h1 : HasFDerivAt (fun x => g (ι x)) (g'.comp ι) x :=
        hgx.hasFDerivAt.comp x ι.hasFDerivAt
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hΩ.mem_nhds hx] with x' hx' using hG x' hx'.1
    have hDg : ∀ w, D (g (ι x)) (g' w) = w := by
      have h1 : HasFDerivAt (fun w => F (g w)) ((D (g (ι x))).comp g') (ι x) :=
        (hFd _).comp (ι x) hgx.hasFDerivAt
      have h2 : HasFDerivAt (fun w => F (g w)) (ContinuousLinearMap.id ℂ (Fin n → ℂ)) (ι x) := by
        refine (hasFDerivAt_id (ι x)).congr_of_eventuallyEq ?_
        filter_upwards [P.open_target.mem_nhds hx.1] with w hw using P.right_inv hw
      intro w
      have := congr_arg (fun T => T w) (h1.unique h2)
      simpa using this
    rw [hGd.fderiv, hG x hx.1]
    ext u
    simp only [LinearMap.mem_range, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨v, rfl⟩ i
      have := congr_fun (hDg (ι v)) (e.symm (Sum.inr i))
      simpa [D, ι] using this
    · intro hu
      refine ⟨pin u, ?_⟩
      show g' (ι (pin u)) = u
      apply hWinj _ hx.2.2
      rw [hDg]
      funext j
      rcases h : e j with k | i
      · have hs : e.symm (Sum.inl k) = j := e.symm_apply_eq.2 h.symm
        simp [D, ι, pin, h, hs]
      · have h2 : D (g (ι x)) u j = 0 := by
          simp only [D, ContinuousLinearMap.pi_apply, h, Sum.elim_inr]
          exact hu i
        rw [h2]
        simp [ι, h]
end HolomorphicImplicitGraph
end GroundTheory.Heights₂.Heights
