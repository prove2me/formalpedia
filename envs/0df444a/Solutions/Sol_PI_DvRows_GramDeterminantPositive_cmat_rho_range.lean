-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.cmat_rho_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:13.751844+00:00
-- url     : https://prove2.me/submissions/be3c836a-7cef-4850-866f-27e873f2cc67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
import Theorems.Thm_PI_DvRows_GramDeterminantPositive_rho_apply
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
theorem _root_.solution (A : HLat K) (e : Module.End K A.V) (he : e * e = e)
    (hCe : ∀ i j, IsCM (A.b.repr (e (A.b j)) i)) (σ : K →+* ℂ) {N m : ℕ} (w : Fin N → A.V)
    (hw : Submodule.span K (Set.range w) = LinearMap.range e) (y : Fin m → A.V)
    (hy : ∀ i, y i ∈ LinearMap.range e) :
    ∃ T0 : Matrix (Fin N) (Fin m) ℂ, cmat A (rho σ) y = cmat A σ w * T0 := by
  have hc : ∀ l, ∃ c : Fin N → K, ∑ j, c j • w j = e (A.b l) := fun l => by
    have : e (A.b l) ∈ Submodule.span K (Set.range w) := hw ▸ LinearMap.mem_range_self e _
    exact (Submodule.mem_span_range_iff_exists_fun K).1 this
  choose c hc using hc
  refine ⟨Matrix.of fun j i => ∑ l, σ (c l j) * rho σ (A.b.repr (y i) l), ?_⟩
  ext k i
  have hyi : e (y i) = y i := by
    obtain ⟨x, hx⟩ := hy i; rw [← hx, ← Module.End.mul_apply, he]
  have h1 : A.b.repr (y i) k = ∑ l, A.b.repr (e (A.b l)) k * A.b.repr (y i) l := by
    conv_lhs => rw [← hyi]
    rw [← LinearMap.toMatrix_mulVec_repr A.b A.b e]
    simp [Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply]
  have h2 : ∀ l, A.b.repr (e (A.b l)) k = ∑ j, c l j * A.b.repr (w j) k := fun l => by
    rw [← hc l]; simp [map_sum, Finsupp.finsetSum_apply]
  have h3 : ∀ l, rho σ (A.b.repr (e (A.b l)) k) = σ (A.b.repr (e (A.b l)) k) := fun l => by
    rw [rho_apply, hCe k l σ, star_star]
  simp only [cmat, of_apply, Matrix.mul_apply]
  rw [h1, map_sum]
  simp_rw [map_mul, h3, h2, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end PI.DvRows.GramDeterminantPositive
