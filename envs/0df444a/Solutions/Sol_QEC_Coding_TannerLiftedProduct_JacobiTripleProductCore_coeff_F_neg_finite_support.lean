-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_F_neg_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:40.009507+00:00
-- url     : https://prove2.me/submissions/07ea2702-e797-427f-b7cf-f2fc4a012504

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finite_neg_support_set
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_F_vanishes

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (d : ℕ) :
    ∃ (S_fin : Finset (ℕ × ℕ)), ∀ p : ℕ × ℕ, p ∉ S_fin →
      (PowerSeries.coeff d) (F (-(↑p.1 + 1), p.2)) = 0 := by
  obtain ⟨S_fin, hS⟩ := (finite_neg_support_set d).exists_finset
  exact ⟨S_fin, fun p hp ↦ coeff_F_vanishes _ _ d (by
    simp only [hS, Set.mem_setOf_eq] at hp
    omega)⟩
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
