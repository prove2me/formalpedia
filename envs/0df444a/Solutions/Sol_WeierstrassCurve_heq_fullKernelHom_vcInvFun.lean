-- Prove2me | solution 1 for WeierstrassCurve.heq_fullKernelHom_vcInvFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/bd6f1c62-ccd7-5998-97ff-28a8032db493

import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_variableChange_vcInvFun
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_heq_fullKernelHom_vcInvFun
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply"

set_option autoImplicit false

namespace P2MKcA
namespace WidthB2
namespace VeluHomVC

open WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F]

def castPt {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (P₂ : W₂.toAffine.Point) : castPt e P = P₂ ↔ HEq P P₂ := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

theorem coordsOrZero_castPt {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    (castPt e P).coordsOrZero = P.coordsOrZero := by
  subst e; rfl

section Transport

variable (W : WeierstrassCurve F) (C : VariableChange F)

theorem nsmul_vcInvFun (Q : W.toAffine.Point) (k : ℕ) :
    k • Point.vcInvFun C W.toAffine Q = Point.vcInvFun C W.toAffine (k • Q) := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih, succ_nsmul, Point.vcInvFun_add]

theorem zsmul_vcInvFun (Q : W.toAffine.Point) (m : ℤ) :
    m • Point.vcInvFun C W.toAffine Q = Point.vcInvFun C W.toAffine (m • Q) :=
  (map_zsmul (AddMonoidHom.mk' (Point.vcInvFun C W.toAffine) (Point.vcInvFun_add C W.toAffine))
    m Q).symm

theorem vcInvFun_injective : Function.Injective (Point.vcInvFun C W.toAffine) :=
  (Point.vcFun_rightInverse (C := C) (W := W.toAffine)).injective

theorem coordsOrZero_vcInvFun {P : W.toAffine.Point} (hP : P ≠ 0) :
    (Point.vcInvFun C W.toAffine P).coordsOrZero =
      (vcXInv C P.coordsOrZero.1, vcYInv C P.coordsOrZero.1 P.coordsOrZero.2) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

theorem vcInvFun_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) : Point.vcInvFun C W.toAffine P ≠ 0 := by
  intro h0
  apply hP
  apply vcInvFun_injective W C
  rw [h0, Point.vcInvFun_zero]

theorem mem_zmultiples_of_vcInvFun_mem {P Q : W.toAffine.Point}
    (h : Point.vcInvFun C W.toAffine P ∈ AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine Q)) :
    P ∈ AddSubgroup.zmultiples Q := by
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  rw [zsmul_vcInvFun] at hm
  have := vcInvFun_injective W C hm
  rw [← this]
  exact AddSubgroup.zsmul_mem_zmultiples Q m

theorem vcInvFun_mem_zmultiples {P Q : W.toAffine.Point} (h : P ∈ AddSubgroup.zmultiples Q) :
    Point.vcInvFun C W.toAffine P ∈ AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine Q) := by
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  rw [← zsmul_vcInvFun]
  exact AddSubgroup.zsmul_mem_zmultiples _ m

end Transport

theorem main (W : WeierstrassCurve F) (C : VariableChange F)
    (Q : W.toAffine.Point) {N : ℕ} (hQ : addOrderOf Q = N)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (φ' : (C • W).toAffine.Point →+
      ((C • W).fullKernelQuotient (Point.vcInvFun C W.toAffine Q) N).toAffine.Point)
    (hφ'ker : φ'.ker = AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine Q))
    (hφ' : ∀ P : (C • W).toAffine.Point, P ∉ AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine Q) →
      (φ' P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Point.vcInvFun C W.toAffine Q).coordsOrZero.1 -
              (k • Point.vcInvFun C W.toAffine Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Point.vcInvFun C W.toAffine Q).coordsOrZero.2 -
              (k • Point.vcInvFun C W.toAffine Q).coordsOrZero.2)))
    (P : W.toAffine.Point) :
    HEq (φ' (Point.vcInvFun C W.toAffine P))
      (Point.vcInvFun C (W.fullKernelQuotient Q N).toAffine (φ P)) := by
  have hcurve := WeierstrassCurve.fullKernelQuotient_variableChange_vcInvFun W C Q hQ
  rw [← castPt_eq_iff_heq hcurve]
  by_cases hPQ : P ∈ AddSubgroup.zmultiples Q
  ·
    have h1 : φ P = 0 := by rw [← AddMonoidHom.mem_ker, hφker]; exact hPQ
    have h2 : φ' (Point.vcInvFun C W.toAffine P) = 0 := by
      rw [← AddMonoidHom.mem_ker, hφ'ker]; exact vcInvFun_mem_zmultiples W C hPQ
    rw [h1, h2, map_zero, Point.vcInvFun_zero]

  have hP'Q : Point.vcInvFun C W.toAffine P ∉
      AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine Q) :=
    fun h => hPQ (mem_zmultiples_of_vcInvFun_mem W C h)
  have hφP : φ P ≠ 0 := by
    intro h0; apply hPQ; rw [← hφker]; exact h0
  have hφ'P : φ' (Point.vcInvFun C W.toAffine P) ≠ 0 := by
    intro h0; apply hP'Q; rw [← hφ'ker]; exact h0
  have hP0 : P ≠ 0 := fun h0 => hPQ (by rw [h0]; exact zero_mem _)
  have hkQ : ∀ k ∈ Finset.Icc 1 (N - 1), k • Q ≠ 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  have hPkQ : ∀ k ∈ Finset.Icc 1 (N - 1), P + k • Q ≠ 0 := by
    intro k hk h0
    apply hPQ
    rw [add_eq_zero_iff_eq_neg] at h0
    rw [h0]
    exact neg_mem (AddSubgroup.nsmul_mem_zmultiples Q k)
  apply eq_of_coordsOrZero_eq
  · intro h0
    exact hφ'P ((castPt hcurve).injective (h0.trans (map_zero _).symm))
  · exact vcInvFun_ne_zero _ C hφP
  rw [coordsOrZero_castPt, hφ' _ hP'Q, coordsOrZero_vcInvFun _ C hφP, hφ P hPQ,
    coordsOrZero_vcInvFun W C hP0]

  have hsum1 : ∑ k ∈ Finset.Icc 1 (N - 1),
      ((Point.vcInvFun C W.toAffine P + k • Point.vcInvFun C W.toAffine Q).coordsOrZero.1 -
        (k • Point.vcInvFun C W.toAffine Q).coordsOrZero.1) =
      ∑ k ∈ Finset.Icc 1 (N - 1),
        (vcXInv C (P + k • Q).coordsOrZero.1 - vcXInv C (k • Q).coordsOrZero.1) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [nsmul_vcInvFun, ← Point.vcInvFun_add, coordsOrZero_vcInvFun W C (hPkQ k hk),
      coordsOrZero_vcInvFun W C (hkQ k hk)]
  have hsum2 : ∑ k ∈ Finset.Icc 1 (N - 1),
      ((Point.vcInvFun C W.toAffine P + k • Point.vcInvFun C W.toAffine Q).coordsOrZero.2 -
        (k • Point.vcInvFun C W.toAffine Q).coordsOrZero.2) =
      ∑ k ∈ Finset.Icc 1 (N - 1),
        (vcYInv C (P + k • Q).coordsOrZero.1 (P + k • Q).coordsOrZero.2 -
          vcYInv C (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [nsmul_vcInvFun, ← Point.vcInvFun_add, coordsOrZero_vcInvFun W C (hPkQ k hk),
      coordsOrZero_vcInvFun W C (hkQ k hk)]
  simp only
  rw [hsum1, hsum2, Prod.mk.injEq]
  have dX : ∀ a b : F, vcXInv C a - vcXInv C b = ((C.u⁻¹ : Fˣ) : F) ^ 2 * (a - b) := by
    intro a b; simp only [vcXInv]; ring
  have dY : ∀ a b c d : F, vcYInv C a b - vcYInv C c d =
      ((C.u⁻¹ : Fˣ) : F) ^ 3 * ((b - d) - C.s * (a - c)) := by
    intro a b c d; simp only [vcYInv]; ring
  constructor
  ·
    rw [Finset.sum_congr rfl (fun k _ => dX _ _), ← Finset.mul_sum]
    simp only [vcXInv]
    ring
  ·
    rw [Finset.sum_congr rfl (fun k _ => dY _ _ _ _), ← Finset.mul_sum, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    simp only [vcYInv]
    ring

end P2MKcA.WidthB2.VeluHomVC

open WeierstrassCurve WeierstrassCurve.Affine

universe u in
theorem solution
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (C : VariableChange F)
    (Q : W.toAffine.Point) {N : ℕ} (hQ : addOrderOf Q = N)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (φ' : (C • W).toAffine.Point →+
      ((C • W).fullKernelQuotient (Point.vcInvFun C W.toAffine Q) N).toAffine.Point)
    (hφ'ker : φ'.ker = AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine Q))
    (hφ' : ∀ P : (C • W).toAffine.Point, P ∉ AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine Q) →
      (φ' P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Point.vcInvFun C W.toAffine Q).coordsOrZero.1 -
              (k • Point.vcInvFun C W.toAffine Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Point.vcInvFun C W.toAffine Q).coordsOrZero.2 -
              (k • Point.vcInvFun C W.toAffine Q).coordsOrZero.2)))
    (P : W.toAffine.Point) :
    HEq (φ' (Point.vcInvFun C W.toAffine P))
      (Point.vcInvFun C (W.fullKernelQuotient Q N).toAffine (φ P)) :=
  P2MKcA.WidthB2.VeluHomVC.main W C Q hQ φ hφker hφ φ' hφ'ker hφ' P

end S_WeierstrassCurve_heq_fullKernelHom_vcInvFun
end P2MW
export P2MW.S_WeierstrassCurve_heq_fullKernelHom_vcInvFun (solution)
