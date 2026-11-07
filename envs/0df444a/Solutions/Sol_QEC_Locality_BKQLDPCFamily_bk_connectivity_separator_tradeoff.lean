-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.bk_connectivity_separator_tradeoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:26:04.988253+00:00
-- url     : https://prove2.me/submissions/f0564c74-7f3b-4aa8-9164-1d1936d76563

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_TwoPassDimension
import Definitions.Def_QEC_Results_LocalityBounds_ConnectivitySeparator
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_exists_bk_logarithmic_gap_tradeoff
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_exists_bk_uniform_gap_tradeoff

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]
namespace QEC.Locality.BKQLDPCFamily
theorem _root_.solution
    (family : BKQLDPCFamily iota kappa) (hcofinal : family.HasCofinalValidIndices) :
    (∀ gamma : ℝ, 0 < gamma →
      family.EventuallyOnValidIndices (fun i ↦
        gamma ≤ (1 - family.cMax i) * Real.log i.1) →
      ∃ K : ℝ, 0 < K ∧ family.EventuallyOnValidIndices (fun i ↦
        (family.encodedQubits i.1 : ℝ) ≤ K * i.1 *
          (family.distance i.1 : ℝ) ^ (2 * (family.cMax i - 1)) *
            (Real.log i.1) ^ 2)) ∧
      (family.UniformCMaxBelowOne →
        ∃ K : ℝ, 0 < K ∧ family.EventuallyOnValidIndices (fun i ↦
          (family.encodedQubits i.1 : ℝ) ≤ K * i.1 *
            (family.distance i.1 : ℝ) ^ (2 * (family.cMax i - 1)))) := by
  constructor
  · intro gamma hgamma hgap
    exact family.exists_bk_logarithmic_gap_tradeoff hcofinal hgamma hgap
  · intro huniform
    exact family.exists_bk_uniform_gap_tradeoff hcofinal huniform
end QEC.Locality.BKQLDPCFamily
