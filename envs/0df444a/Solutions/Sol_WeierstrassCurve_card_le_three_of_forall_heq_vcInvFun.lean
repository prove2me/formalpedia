-- Prove2me | solution 1 for WeierstrassCurve.card_le_three_of_forall_heq_vcInvFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a23a5088-f840-582c-ad7b-5e1df1c0ec6f

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_card_le_three_of_forall_heq_vcInvFun

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_card_le_three_of_forall_heq_vcInvFun.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_le_three_of_forall_heq_vcInvFun.WeierstrassCurve.Affine Polynomial"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine VariableChange.one_def VariableChange.ext a₃ a₁ variableChange_a₃ a₄ a₂ a₆ toAffine variableChange_a₁ VariableChange"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "equation_iff' Point.some Point.some.injEq Nonsingular Point vcXInv vcYInv vcX_vcXInv vcY_vcYInv nonsingular_variableChange_iff Point.vcInvFun"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

variable {K : Type*} [Field K]

theorem heq_point_some_iff {V V' : Affine K} (hV : V = V') {x y x' y' : K}
    (h : V.Nonsingular x y) (h' : V'.Nonsingular x' y') :
    HEq (Point.some x y h) (Point.some x' y' h') ↔ x = x' ∧ y = y' := by
  subst hV
  simp only [heq_eq_eq, Point.some.injEq]

theorem point_some_eq_some {W : Affine K} {x₁ y₁ x₂ y₂ : K} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

namespace Point p2m_export "WeierstrassCurve.Affine.Point" "some some.injEq zero vcInvFun" end Point
p2m_open_scoped "WeierstrassCurve.Affine.Point" in

def Point.yCoord {W : Affine K} : W.Point → Option K
  | .zero => none
  | .some _ y _ => Option.some y

theorem card_le_three_of_forall_x_eq [DecidableEq K] (W : Affine K) (F : Finset W.Point)
    (x₀ : K) (hx : ∀ {x y : K} (h : W.Nonsingular x y), Point.some x y h ∈ F → x = x₀) :
    F.card ≤ 3 := by
  classical

  set q : K[X] := X ^ 2 + C (W.a₁ * x₀ + W.a₃) * X -
    C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hq
  have hqdeg : q.natDegree = 2 := by rw [hq]; compute_degree!
  have hq0 : q ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hqdeg; exact absurd hqdeg (by norm_num)
  have heval : ∀ y : K, q.eval y =
      y ^ 2 + (W.a₁ * x₀ + W.a₃) * y - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) := by
    intro y; simp only [hq, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]

  have hinj : Set.InjOn Point.yCoord (F : Set W.Point) := by
    rintro P hP Q hQ hPQ
    rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
    · rfl
    · exact absurd hPQ (by simp [Point.yCoord])
    · exact absurd hPQ (by simp [Point.yCoord])
    · simp only [Point.yCoord, Option.some.injEq] at hPQ
      exact point_some_eq_some ((hx h₁ hP).trans (hx h₂ hQ).symm) hPQ

  have himg : F.image Point.yCoord ⊆ insert none (q.roots.toFinset.image Option.some) := by
    intro o ho
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ho
    rcases P with _ | ⟨x, y, h⟩
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨y, ?_, rfl⟩)
      have hxx : x = x₀ := hx h hP
      subst hxx
      rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot.def, heval]
      have hE := (W.equation_iff' x y).mp h.left
      linear_combination hE
  calc F.card = (F.image Point.yCoord).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (insert none (q.roots.toFinset.image Option.some) : Finset (Option K)).card :=
        Finset.card_le_card himg
    _ ≤ (q.roots.toFinset.image Option.some).card + 1 := Finset.card_insert_le _ _
    _ ≤ q.roots.toFinset.card + 1 := by gcongr; exact Finset.card_image_le
    _ ≤ Multiset.card q.roots + 1 := by gcongr; exact Multiset.toFinset_card_le _
    _ ≤ q.natDegree + 1 := by gcongr; exact card_roots' q
    _ = 3 := by rw [hqdeg]

theorem card_le_one_of_forall_not_mem (W : Affine K) (F : Finset W.Point)
    (hno : ∀ {x y : K} (h : W.Nonsingular x y), Point.some x y h ∉ F) : F.card ≤ 1 := by
  refine Finset.card_le_one.mpr fun P hP Q hQ => ?_
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · exact absurd hQ (hno h₂)
  · exact absurd hP (hno h₁)
  · exact absurd hP (hno h₁)

end WeierstrassCurve.Affine

theorem solution
    {K : Type*} [Field K] [DecidableEq K] (E : WeierstrassCurve K)
    (β : WeierstrassCurve.VariableChange K) (hβ : β • E = E) (h1 : β ≠ 1)
    (hneg : β ≠ ⟨-1, 0, -E.a₁, -E.a₃⟩)
    (F : Finset E.toAffine.Point) (hF : ∀ P ∈ F, HEq (Point.vcInvFun β E.toAffine P) P) :
    F.card ≤ 3 := by

  have key : ∀ {x y : K} (h : E.toAffine.Nonsingular x y), Point.some x y h ∈ F →
      (β.u : K) ^ 2 * x + β.r = x ∧
        (β.u : K) ^ 3 * y + (β.u : K) ^ 2 * β.s * x + β.t = y := by
    intro x y h hmem
    have hns : (β • E.toAffine).toAffine.Nonsingular (vcXInv β x) (vcYInv β x y) :=
      (nonsingular_variableChange_iff (vcXInv β x) (vcYInv β x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv])
    have hP : HEq (Point.some (vcXInv β x) (vcYInv β x y) hns) (Point.some x y h) := hF _ hmem
    obtain ⟨hX, hY⟩ := (heq_point_some_iff hβ hns h).mp hP
    have hA := vcX_vcXInv (C := β) x
    have hB := vcY_vcYInv (C := β) x y
    rw [hX] at hA
    rw [hX, hY] at hB
    exact ⟨hA, hB⟩
  by_cases hU2 : (β.u : K) ^ 2 = 1
  · by_cases hr : β.r = 0
    · by_cases hu1 : (β.u : K) = 1
      ·
        by_cases hs : β.s = 0
        ·
          have ht : β.t ≠ 0 := by
            intro ht
            apply h1
            rw [VariableChange.one_def]
            exact VariableChange.ext (Units.ext (by rw [Units.val_one]; exact hu1)) hr hs ht
          refine (card_le_one_of_forall_not_mem E.toAffine F fun {x y} h hmem => ?_).trans (by norm_num)
          obtain ⟨-, hB⟩ := key h hmem
          rw [hu1, hs] at hB
          apply ht
          linear_combination hB
        ·
          refine card_le_three_of_forall_x_eq E.toAffine F (-β.t / β.s) fun {x y} h hmem => ?_
          obtain ⟨-, hB⟩ := key h hmem
          rw [hu1] at hB
          rw [eq_div_iff hs]
          linear_combination hB
      ·
        exfalso
        have hUneg : (β.u : K) = -1 := by
          have hprod : ((β.u : K) - 1) * ((β.u : K) + 1) = 0 := by linear_combination hU2
          rcases mul_eq_zero.mp hprod with h | h
          · exact absurd (by linear_combination h) hu1
          · linear_combination h
        have h2 : (2 : K) ≠ 0 := by
          intro h2
          apply hu1
          rw [hUneg]
          linear_combination -h2
        have hw : ((β.u⁻¹ : Kˣ) : K) = -1 := by
          have h := β.u.inv_mul
          rw [hUneg] at h
          linear_combination -h
        have ha1 := congrArg WeierstrassCurve.a₁ hβ
        rw [variableChange_a₁, hw] at ha1
        have ha3 := congrArg WeierstrassCurve.a₃ hβ
        rw [variableChange_a₃, hw, hr] at ha3
        have hs : β.s = -E.a₁ := by
          have h' : (2 : K) * (β.s + E.a₁) = 0 := by linear_combination -ha1
          rcases mul_eq_zero.mp h' with h | h
          · exact absurd h h2
          · linear_combination h
        have ht : β.t = -E.a₃ := by
          have h' : (2 : K) * (β.t + E.a₃) = 0 := by linear_combination -ha3
          rcases mul_eq_zero.mp h' with h | h
          · exact absurd h h2
          · linear_combination h
        exact hneg (VariableChange.ext
          (Units.ext (by rw [Units.val_neg, Units.val_one]; exact hUneg)) hr hs ht)
    ·
      refine (card_le_one_of_forall_not_mem E.toAffine F fun {x y} h hmem => ?_).trans (by norm_num)
      obtain ⟨hA, -⟩ := key h hmem
      apply hr
      linear_combination hA - x * hU2
  ·
    refine card_le_three_of_forall_x_eq E.toAffine F (β.r / (1 - (β.u : K) ^ 2)) fun {x y} h hmem => ?_
    obtain ⟨hA, -⟩ := key h hmem
    rw [eq_div_iff (sub_ne_zero.mpr (fun h' => hU2 h'.symm))]
    linear_combination -hA

end S_WeierstrassCurve_card_le_three_of_forall_heq_vcInvFun
end P2MW
export P2MW.S_WeierstrassCurve_card_le_three_of_forall_heq_vcInvFun (solution)
