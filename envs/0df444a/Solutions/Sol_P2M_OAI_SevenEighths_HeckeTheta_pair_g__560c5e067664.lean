-- Prove2me | solution 1 for P2M_OAI_SevenEighths_HeckeTheta_pair_g__560c5e067664
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:03:52.441301+00:00
-- url     : https://prove2.me/submissions/7a50aef2-129c-4330-a05d-23c4e7f54d19

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta

theorem solution {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).g₀ = 2 * dualScalar N * ∑ a, w a := by
  simp only [pair, finitePair, parityPair, ThetaProduct.rectangularPair,
    ThetaProduct.product, ThetaProduct.scaledEvenPair, ThetaProduct.rescale,
    HurwitzZeta.hurwitzEvenFEPair, one_mul, mul_one]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  simp_rw [← two_mul]
  rw [← Finset.mul_sum]
  simp only [← Finset.sum_mul, dualScalar]
  ring
