-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootsOfUnityValuation_one_sub_pow_associated_33a809d88cd3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:48.806472+00:00
-- url     : https://prove2.me/submissions/b6aa0c54-08e2-4745-a7b7-396e6d1cb839

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PRootsOfUnityValuation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootsOfUnityValuation_associated_sub_comm_33c5a4c402df

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RootsOfUnityValuation
variable {A : Type*} [CommRing A] [IsDomain A]
namespace GroundTheory.Heights₂.Heights.RootsOfUnityValuation
theorem _root_.solution {l : ℕ} (hl : l.Prime) {ζ : A} (hζ : IsPrimitiveRoot ζ l) :
    Associated ((1 - ζ) ^ (l - 1)) (l : A) := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, (Nat.sub_add_cancel hl.one_lt.le).symm⟩
  have h := hζ.prod_one_sub_pow_eq_order
  have h1 : (1 - ζ) ^ n = ∏ _k ∈ range n, (1 - ζ) := by simp
  rw [Nat.add_sub_cancel, h1]
  push_cast
  rw [← h]
  refine Associated.prod _ _ _ fun k hk => ?_
  have hcop : (k + 1).Coprime (n + 1) :=
    (Nat.coprime_of_lt_prime (by omega) (by simpa using Finset.mem_range.1 hk) hl).symm
  exact (associated_sub_comm 1 ζ).trans
    ((hζ.associated_sub_one_pow_sub_one_of_coprime hcop).trans (associated_sub_comm _ _))
end GroundTheory.Heights₂.Heights.RootsOfUnityValuation
