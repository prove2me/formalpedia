-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.cmat_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:10.303673+00:00
-- url     : https://prove2.me/submissions/2bcf5c75-7440-496b-880a-8de77f2a23fb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
open NumberField Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution (A : HLat K) (σ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V)
    (hf : LinearIndependent K f) : Function.Injective (cmat A σ f).mulVec := by
  set Y : Matrix A.ι (Fin m) K := Matrix.of fun k i => A.b.repr (f i) k with hY
  have hYc : ∀ c : Fin m → K, Y *ᵥ c = ⇑(A.b.repr (∑ i, c i • f i)) := by
    intro c; ext k
    simp [hY, Matrix.mulVec, dotProduct, map_sum, Finsupp.finsetSum_apply, mul_comm]
  have hker : LinearMap.ker (Matrix.mulVecLin Y) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have h0 : A.b.repr (∑ i, c i • f i) = 0 := by
      ext k; have := congrFun hc k; rw [Matrix.mulVecLin_apply, hYc] at this; simpa using this
    have h1 : ∑ i, c i • f i = 0 := A.b.repr.injective (by rw [h0, map_zero])
    exact funext (Fintype.linearIndependent_iff.1 hf c h1)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  set L := LinearMap.toMatrix' g
  have hLY : L * Y = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    have hYY : LinearMap.toMatrix' (Matrix.mulVecLin Y) = Y := by
      ext i j; simp [LinearMap.toMatrix'_apply]
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, hYY] at this
  have hmap : L.map σ * cmat A σ f = 1 := by
    have : cmat A σ f = Y.map σ := by ext; simp [cmat, hY]
    rw [this, ← Matrix.map_mul, hLY, Matrix.map_one _ (map_zero σ) (map_one σ)]
  intro a b hab
  have := congrArg (L.map σ).mulVec hab
  simpa [mulVec_mulVec, hmap] using this
end PI.DvRows.GramDeterminantPositive
