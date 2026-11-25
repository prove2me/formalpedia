-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.card_quot_eq_natAbs_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:28:03.543032+00:00
-- url     : https://prove2.me/submissions/6526345b-04d6-4efb-a39b-fd402197b26d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_IndexSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CardQuotEqNatAbsNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S] [Module.Free ℤ S]
    [Module.Finite ℤ S] (f : S) (hf : f ≠ 0) :
    Nat.card (S ⧸ Ideal.span {f}) = (Algebra.norm ℤ f).natAbs := by
  classical
  let N : Submodule ℤ S := (Ideal.span {f}).restrictScalars ℤ
  have hmem : ∀ x : S, f * x ∈ N := fun x => Ideal.mul_mem_right x _ (Ideal.subset_span rfl)
  let g : S →+ N :=
    { toFun := fun x => ⟨f * x, hmem x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [mul_add] }
  have hbij : Function.Bijective g := by
    constructor
    · intro x y hxy
      have h1 : f * x = f * y := congrArg Subtype.val hxy
      exact mul_left_cancel₀ hf h1
    · rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      exact ⟨a, by ext; simp [g, mul_comm]⟩
  let e : S ≃+ N := AddEquiv.ofBijective g hbij
  have h := Submodule.natAbs_det_equiv N e
  have hlin : N.subtype ∘ₗ (e : S →+ N).toIntLinearMap = Algebra.lmul ℤ S f := by
    ext x
    rfl
  rw [hlin, ← Algebra.norm_apply] at h
  rw [h]
  exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ (Ideal.span {f})).toEquiv.symm
end ReciprocityTheory.ChartRestriction.G.AI
