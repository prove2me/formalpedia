-- Prove2me | solution 1 for UpperTheory.Ram.Fun.sum_padicValNat_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:49:04.054841+00:00
-- url     : https://prove2.me/submissions/6153fde3-00b7-44a6-91c5-a45fe1938750

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPrimeOfDifferentLe
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IsDedekindDomain Finset
noncomputable section
open UpperTheory UpperTheory.Ram UpperTheory.Ram.Fun
namespace UpperTheory.Ram.Fun
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, (padicValNat l n : ℝ) * Real.log l ≤ Real.log n := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ l ∈ S, (padicValNat l n : ℝ) * Real.log l
      = ∑ l ∈ S, (n.factorization l : ℝ) * Real.log l :=
        Finset.sum_congr rfl fun l hl => by rw [Nat.factorization_def n (hS l hl)]
    _ ≤ ∑ l ∈ S ∪ n.factorization.support, (n.factorization l : ℝ) * Real.log l :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun l _ _ =>
          mul_nonneg (by positivity) (Real.log_natCast_nonneg l)
    _ = ∑ l ∈ n.factorization.support, (n.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_subset Finset.subset_union_right fun l _ hl => ?_).symm
        rw [Finsupp.notMem_support_iff.1 hl]; simp
end UpperTheory.Ram.Fun
