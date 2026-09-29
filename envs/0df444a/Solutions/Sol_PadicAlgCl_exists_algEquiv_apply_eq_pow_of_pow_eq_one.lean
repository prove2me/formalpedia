-- Prove2me | solution 1 for PadicAlgCl.exists_algEquiv_apply_eq_pow_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d74a6bbe-a5e3-5af1-aef4-13affd89d816

import Mathlib
import Theorems.Thm_IntermediateField_exists_frobenius_adjoin_rootsOfUnity_padic
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramification_inertia_Rw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_algEquiv_apply_eq_pow_of_pow_eq_one

set_option autoImplicit false

theorem solution (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N) :
    ∃ φ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ∀ w : PadicAlgCl p, w ^ (p ^ N - 1) = 1 → φ w = w ^ p := by
  obtain ⟨φ, a, -, hcard, hφ⟩ :=
    IntermediateField.exists_frobenius_adjoin_rootsOfUnity_padic p ⊥ N hN
  obtain ⟨e, f, -, hf, -, hcard', hef⟩ :=
    ExtCitation.LocalLevel.exists_ramification_inertia_Rw p (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))

  rw [IntermediateField.finrank_bot] at hef
  have hf1 : f = 1 := by
    have hle : f ≤ 1 := Nat.le_of_dvd Nat.one_pos (Dvd.intro_left e hef)
    omega
  rw [hf1, pow_one] at hcard'
  have ha1 : a = 1 := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    show p ^ a = p ^ 1
    rw [pow_one, ← hcard, hcard']

  refine ⟨(φ.liftNormal (PadicAlgCl p)).restrictScalars ℚ_[p], fun w hw => ?_⟩
  have hwmem : w ∈ IntermediateField.adjoin (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
      {ζ : PadicAlgCl p | ζ ^ (p ^ N - 1) = 1} :=
    IntermediateField.subset_adjoin _ _ hw
  have key := hφ ⟨w, hwmem⟩ hw
  rw [ha1, pow_one] at key
  have h1 : φ.liftNormal (PadicAlgCl p) w =
      ((φ ⟨w, hwmem⟩ : IntermediateField.adjoin (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
        {ζ : PadicAlgCl p | ζ ^ (p ^ N - 1) = 1}) : PadicAlgCl p) :=
    AlgEquiv.liftNormal_commutes φ (PadicAlgCl p) ⟨w, hwmem⟩
  show φ.liftNormal (PadicAlgCl p) w = w ^ p
  rw [h1, key]

end S_PadicAlgCl_exists_algEquiv_apply_eq_pow_of_pow_eq_one
end P2MW
export P2MW.S_PadicAlgCl_exists_algEquiv_apply_eq_pow_of_pow_eq_one (solution)
