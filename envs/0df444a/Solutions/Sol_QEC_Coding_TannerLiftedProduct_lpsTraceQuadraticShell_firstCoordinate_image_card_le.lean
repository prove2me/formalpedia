-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsTraceQuadraticShell_firstCoordinate_image_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:10:40.863939+00:00
-- url     : https://prove2.me/submissions/d4ca440e-765c-420d-9d46-00e5cb64d6d3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceQuadraticShell_firstCoordinate_congruence
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceQuadraticShell_firstCoordinate_bounds
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerSet_card_le_negativeRoot_class
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerSet_card_le_positiveRoot_class

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q r : ℕ) (hq : q.Prime)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) :
    ((lpsTraceQuadraticShell q (r^2)).image LPSQuaternion.a).card ≤ 2*(2*r/q^2+1) := by
  classical
  let s := (lpsTraceQuadraticShell q (r^2)).image LPSQuaternion.a
  let sm := s.filter fun x => ((q^2 : ℕ) : ℤ) ∣ x+(r : ℤ)
  let sp := s.filter fun x => ((q^2 : ℕ) : ℤ) ∣ x-(r : ℤ)
  have hsub : s ⊆ sm ∪ sp := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    have hc := lpsTraceQuadraticShell_firstCoordinate_congruence q r hq hqr t ht
    rcases hc with hc | hc
    · apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩, by exact_mod_cast hc⟩)
    · apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩, by exact_mod_cast hc⟩)
  have hm : sm.card ≤ 2*r/q^2+1 := by
    apply lpsIntegerSet_card_le_negativeRoot_class sm r (q^2)
    intro x hx
    obtain ⟨hxS,hxd⟩ := Finset.mem_filter.mp hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hxS
    have hb := lpsTraceQuadraticShell_firstCoordinate_bounds q r hq.pos t ht
    exact ⟨hb.1,hb.2,hxd⟩
  have hp : sp.card ≤ 2*r/q^2+1 := by
    apply lpsIntegerSet_card_le_positiveRoot_class sp r (q^2)
    intro x hx
    obtain ⟨hxS,hxd⟩ := Finset.mem_filter.mp hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hxS
    have hb := lpsTraceQuadraticShell_firstCoordinate_bounds q r hq.pos t ht
    exact ⟨hb.1,hb.2,hxd⟩
  calc
    s.card ≤ (sm ∪ sp).card := Finset.card_le_card hsub
    _ ≤ sm.card+sp.card := Finset.card_union_le _ _
    _ ≤ 2*(2*r/q^2+1) := by omega
end QEC.Coding.TannerLiftedProduct
