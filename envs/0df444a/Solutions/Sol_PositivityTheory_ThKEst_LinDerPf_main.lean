-- Prove2me | solution 1 for PositivityTheory.ThKEst.LinDerPf.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:23.016572+00:00
-- url     : https://prove2.me/submissions/36669dc2-eafd-4a52-9403-399b794f21ea

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA
import Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_coords
import Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_gr_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.LinDerPf
open Filter Topology Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {a : A →L[ℝ] A}
namespace PositivityTheory.ThKEst.LinDerPf
theorem _root_.solution [FiniteDimensional ℝ A] (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) :
    ∃ (m : ℕ) (Y : Fin m → A) (c : Fin m → A →ₗ[ℝ] ℝ), (∀ i, a (Y i) = -Y i) ∧ ∀ Z : A,
      (∀ t : ℝ, Gr a (NormedSpace.exp (t • Z))) → ∃ s : Fin m → ℝ → ℝ, (∀ i, s i 0 = 0) ∧ (∀ i, HasDerivAt (s i) (c i Z) 0) ∧
        ∀ᶠ t in 𝓝 (0 : ℝ), NormedSpace.exp (t • Z) = (List.ofFn fun i => NormedSpace.exp (s i t • Y i)).prod := by
  have : CompleteSpace A := FiniteDimensional.complete ℝ A
  let L : Submodule ℝ A := LinearMap.ker ((a : A →ₗ[ℝ] A) + LinearMap.id)
  have hL : ∀ x, x ∈ L ↔ a x = -x := fun x => by
    simp [L, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]
  let b := Module.finBasis ℝ L
  obtain ⟨q, hq⟩ := L.subtype.exists_leftInverse_of_injective L.ker_subtype
  have hq' : ∀ x : L, q x = x := fun x => LinearMap.congr_fun hq x
  let c : A →L[ℝ] (Fin (Module.finrank ℝ L) → ℝ) := LinearMap.toContinuousLinearMap (b.equivFun.toLinearMap ∘ₗ q)
  have hc0 : ∀ x : L, c x = b.equivFun x := fun x => by
    change b.equivFun (q x) = _
    rw [hq']
  refine ⟨_, fun i => b i, fun i => (LinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).comp (c.comp (pr a)).toLinearMap,
    fun i => (hL _).1 (b i).2, fun Z hZ => ?_⟩
  obtain ⟨s, s0, sd, se⟩ := coords ha h1 (fun i => (b i : A)) (fun i => (hL _).1 (b i).2) c
    (fun s => by
      have : (∑ i, s i • (b i : A)) = ((b.equivFun.symm s : L) : A) := by simp [Module.Basis.equivFun_symm_apply]
      rw [this, hc0, LinearEquiv.apply_symm_apply])
    (fun x y hx hy e => by
      have e1 := (hc0 ⟨x, (hL x).2 hx⟩).symm.trans (e.trans (hc0 ⟨y, (hL y).2 hy⟩))
      exact congrArg Subtype.val (b.equivFun.injective e1))
    (fun i t => NormedSpace.exp (t • (b i : A)))
    (fun i => by simpa using hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (b i : A) (0 : ℝ))
    (fun i => by simp)
    (fun i t => gr_exp ha h1 (by rw [map_smul, (hL _).1 (b i).2, smul_neg]))
    (fun t => NormedSpace.exp (t • Z)) Z
    (by simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)) (by simp) hZ
  exact ⟨fun i t => s t i, fun i => congrFun s0 i, fun i => hasDerivAt_pi.1 sd i, se⟩
end PositivityTheory.ThKEst.LinDerPf
