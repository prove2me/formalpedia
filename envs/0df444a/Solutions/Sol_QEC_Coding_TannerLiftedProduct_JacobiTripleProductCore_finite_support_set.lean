-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_support_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:14:14.930391+00:00
-- url     : https://prove2.me/submissions/0ae00320-16a8-4b50-9b4b-1c11a7f56da7

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (d : ℕ) :
    Set.Finite {p : ℤ × ℕ | p.1.natAbs ^ 2 + p.2 ≤ d} := by
  apply ((Set.finite_Icc (-d : ℤ) d).prod (Set.finite_Iic d)).subset
  rintro ⟨m, ℓ⟩ (h : m.natAbs ^ 2 + ℓ ≤ d)
  simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Iic]
  have habs : m.natAbs ≤ d := by nlinarith
  have habsz : (m.natAbs : ℤ) ≤ d := by exact_mod_cast habs
  exact ⟨⟨by
    have hneg := Int.le_natAbs (a := -m)
    rw [Int.natAbs_neg] at hneg
    omega,
    Int.le_natAbs.trans habsz⟩, by omega⟩
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
