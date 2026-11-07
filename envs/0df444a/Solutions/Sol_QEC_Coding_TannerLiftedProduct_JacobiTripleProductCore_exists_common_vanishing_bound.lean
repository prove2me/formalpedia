-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exists_common_vanishing_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:39:52.179323+00:00
-- url     : https://prove2.me/submissions/a49a7e8f-9e2b-41b0-9df1-db2915e32d48

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finite_support_vanishing_bound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {G_type : Type*} [AddCommGroup G_type]
    {t w u : ℕ → G_type}
    (ht : (Function.support t).Finite)
    (hw : (Function.support w).Finite)
    (hu : (Function.support u).Finite) :
    ∃ N, ∀ i, N < i → t i = 0 ∧ w i = 0 ∧ u i = 0 :=
  (finite_support_vanishing_bound ht).elim fun Nt hNt =>
    (finite_support_vanishing_bound hw).elim fun Nw hNw =>
    (finite_support_vanishing_bound hu).elim fun Nu hNu =>
    ⟨max Nt (max Nw Nu), fun i hi =>
      ⟨hNt i (by omega), hNw i (by omega), hNu i (by omega)⟩⟩
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
