-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.V_coeff_neg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:15:43.774613+00:00
-- url     : https://prove2.me/submissions/641f9416-476a-437e-ac0d-7872da29ba02

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (ℓ : ℕ) (d : ℤ) (hd : d < 0) :
    (V ℓ).coeff d = 0 := by
  simp only [V, ι_hahn, HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_notin_range (by simp_all)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
