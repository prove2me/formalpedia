-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCoprimeMaximalIdeal_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:29:18.755038+00:00
-- url     : https://prove2.me/submissions/37d00cbe-483a-4330-aa49-11b9f91bc9c2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {R : Type*} [CommRing R] (I J : Ideal R) [J.IsMaximal]
    (hc : IsCoprime I J) : I ≠ ⊥ := by
  intro hi
  have h := hc.sup_eq
  rw [hi,bot_sup_eq] at h
  exact (inferInstance : J.IsMaximal).ne_top h
end QEC.Coding.TannerLiftedProduct
