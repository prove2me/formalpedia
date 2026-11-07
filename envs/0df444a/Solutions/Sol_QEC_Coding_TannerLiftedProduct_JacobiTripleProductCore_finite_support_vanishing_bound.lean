-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_support_vanishing_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:35.818697+00:00
-- url     : https://prove2.me/submissions/73f6ea4d-5c77-48d7-90dc-91dfa6773455

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {G_type : Type*} [AddCommGroup G_type]
    {f : ℕ → G_type} (hf : (Function.support f).Finite) :
    ∃ N, ∀ i, N < i → f i = 0 :=
  (Set.exists_upper_bound_image _ id hf).imp fun _ hN i hi =>
    Function.notMem_support.mp (fun hmem => Nat.not_lt.mpr (hN i hmem) hi)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
