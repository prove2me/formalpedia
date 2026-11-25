-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagFormDiv_mem_diag_of_quot_d965dd32f5f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:57:35.858364+00:00
-- url     : https://prove2.me/submissions/56864ae9-1e3b-4e58-b3b8-beb922dec723

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_multiConeMap_of_homog_3655d6d60990
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_not_mem_ker_iff_aeval_ne_69965e549228
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multiConeMap_eq_f5c45a24f8f1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.Inter
namespace DiagFormDiv
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a : Fin 2 → Φ) (ha : AlgebraicIndependent Ω a) {n : ℕ} {g h : MRing (T.wwIdx ι ν κ)}
    (hg : IsMultiHomog g (T.wwDeg n 1)) (hh : IsMultiHomog h (T.wwDeg (n + 3) 0))
    (hq : aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h) :
    g ∈ T.wwIdeal x δ e φ (a 0) (a 0) := by
  have key : ∀ b : Fin 2 → Φ, (MvPolynomial.map (aeval b : MvPolynomial (Fin 2) Ω →ₐ[Ω] Φ).toRingHom)
      (DiagonalOrder.polyConeMap x δ e φ g * ∏ k, X k ^ T.wwDeg (n + 3) 0 k -
        C (X 1 - X 0) * DiagonalOrder.polyConeMap x δ e φ h * ∏ k, X k ^ T.wwDeg n 1 k) =
      C (aeval (T.wwCoord x δ e φ (b 0) (b 1)) g - (b 1 - b 0) * aeval (T.wwCoord x δ e φ (b 0) (b 1)) h) *
        ((∏ k, X k ^ T.wwDeg n 1 k) * ∏ k, X k ^ T.wwDeg (n + 3) 0 k) := by
    intro b
    have e1 := DiagRAux.multiConeMap_of_homog (T.wwCoord x δ e φ (b 0) (b 1)) g _ hg
    have e2 := DiagRAux.multiConeMap_of_homog (T.wwCoord x δ e φ (b 0) (b 1)) h _ hh
    rw [DiagonalOrder.multiConeMap_eq, RingHom.comp_apply] at e1 e2
    rw [map_sub, map_mul, map_mul, map_mul, e1, e2]
    simp only [map_prod, map_pow, map_X, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_mul, aeval_X]
    ring
  have hZ : DiagonalOrder.polyConeMap x δ e φ g * ∏ k, X k ^ T.wwDeg (n + 3) 0 k -
      C (X 1 - X 0) * DiagonalOrder.polyConeMap x δ e φ h * ∏ k, X k ^ T.wwDeg n 1 k = 0 := by
    apply MvPolynomial.map_injective _ (algebraicIndependent_iff_injective_aeval.mp ha)
    rw [key a, hq, T.diagSec, sub_self, C_0, zero_mul, map_zero]
  have h0 := key (fun _ => a 0)
  rw [hZ, map_zero, sub_self, zero_mul, sub_zero] at h0
  have hm : ((∏ k, (X k : MvPolynomial T.WBlk Φ) ^ T.wwDeg n 1 k) * ∏ k, X k ^ T.wwDeg (n + 3) 0 k) ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k))
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k))
  have hv : aeval (T.wwCoord x δ e φ (a 0) (a 0)) g = 0 :=
    C_eq_zero.1 ((mul_eq_zero.1 h0.symm).resolve_right hm)
  by_contra hn
  exact (DiagRAux.not_mem_ker_iff_aeval_ne _ g _ hg).1 hn hv
end DiagFormDiv
end GroundTheory.Heights₂.Heights.Inter
