-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:25.071962+00:00
-- url     : https://prove2.me/submissions/0cf1d2c7-32a8-4a8e-959f-250a50c24bbe

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {R' : Type*} [CommRing R'] (A Q : R') (n : ℕ) :
    qPoch A Q (n + 1) = (1 - A) * qPoch (A * Q) Q n := by
  simp only [qPoch]
  rw [Finset.prod_range_succ']
  simp only [pow_zero, mul_one]
  rw [mul_comm]
  exact congr_arg ((1 - A) * ·) (Finset.prod_congr rfl fun i _ => by ring)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
