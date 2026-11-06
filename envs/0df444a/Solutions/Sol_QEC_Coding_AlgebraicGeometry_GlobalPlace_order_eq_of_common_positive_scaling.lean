-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.order_eq_of_common_positive_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:47:26.976569+00:00
-- url     : https://prove2.me/submissions/c658f31a-ded1-4f37-8be3-6d93d0a243f5

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_uniformizer


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
theorem _root_.solution
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P Q : GlobalPlace k K) (e f : ℕ) (he : 0 < e) (hf : 0 < f)
    (h : ∀ x : K, (e : ℤ) * P.order x = (f : ℤ) * Q.order x) :
    P.order = Q.order := by
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  have hf' : (0 : ℤ) < f := by exact_mod_cast hf
  have hP := h P.uniformizer
  have hQ := h Q.uniformizer
  rw [P.order_uniformizer, mul_one] at hP
  rw [Q.order_uniformizer, mul_one] at hQ
  have hQu : 0 < Q.order P.uniformizer :=
    (mul_pos_iff_of_pos_left hf').mp (by rwa [← hP])
  have hPu : 0 < P.order Q.uniformizer :=
    (mul_pos_iff_of_pos_left he').mp (by rwa [hQ])
  have hfe : (f : ℤ) ≤ e := by
    calc
      (f : ℤ) = f * 1 := (mul_one _).symm
      _ ≤ f * Q.order P.uniformizer :=
        mul_le_mul_of_nonneg_left (by omega) hf'.le
      _ = e := hP.symm
  have hef : (e : ℤ) ≤ f := by
    calc
      (e : ℤ) = e * 1 := (mul_one _).symm
      _ ≤ e * P.order Q.uniformizer :=
        mul_le_mul_of_nonneg_left (by omega) he'.le
      _ = f := hQ
  have heq : (e : ℤ) = f := le_antisymm hef hfe
  funext x
  have hx := h x
  rw [heq] at hx
  exact mul_left_cancel₀ (ne_of_gt hf') hx
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
