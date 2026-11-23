-- Prove2me | solution 1 for SPP.nonwitnessGroup_lt_lt_of_not_isPrimePow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:21:13.240502+00:00
-- url     : https://prove2.me/submissions/bd13dbf1-efd8-4c93-9892-2d387e4a4bdf

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_nonwitnessGroup_le_G
import Theorems.Thm_SPP_G_lt_F_of_not_isPrimePow
import Theorems.Thm_SPP_F_lt_top_of_not_carmichael
import Theorems.Thm_SPP_G_eq_H
import Theorems.Thm_SPP_H_le_H_of_dvd
import Theorems.Thm_SPP_H_inf_H_lt_H_inf_H_inf_H
import Theorems.Thm_SPP_H_lt_H_inf_H
import Theorems.Thm_SPP_eq_mul_mul_of_carmichael

set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}
namespace SPP
theorem _root_.solution [Fact (1 < n)] (ho : Odd n) (hnpp : ¬IsPrimePow n) :
    ∃ K : Subgroup (ZMod n)ˣ, nonwitnessGroup n < K ∧ K < ⊤ := by
  have hnp : ¬n.Prime := fun np ↦ hnpp np.isPrimePow
  by_cases hc : FPP.Carmichael n
  · rcases eq_mul_mul_of_carmichael hc hnp with ⟨m₁, m₂, m₃, hn, h₁₂, h₁₃, h₂₃, h₁, h₂, h₃⟩
    use H ((dvd_mul_right (m₁ * m₂) m₃).trans (dvd_of_eq hn.symm)) ⊓
      H ((dvd_mul_left m₃ (m₁ * m₂)).trans (dvd_of_eq hn.symm))
    constructor
    · calc
        _ ≤ G n := nonwitnessGroup_le_G
        _ = H (dvd_refl n) := G_eq_H
        _ = H (dvd_of_eq hn.symm) := le_antisymm (H_le_H_of_dvd (dvd_of_eq hn.symm) (dvd_refl n))
          (H_le_H_of_dvd (dvd_of_eq hn) (dvd_of_eq hn.symm))
        _ < _ := H_lt_H_inf_H ((by decide : 2 < 2 * 2).trans (by gcongr)) h₃
          (h₁₃.mul_left h₂₃) (dvd_of_eq hn.symm)
    · calc
        _ < H _ ⊓ H _ ⊓ H _ := H_inf_H_lt_H_inf_H_inf_H h₁ h₂ (h₁₂.mul_right h₁₃) (dvd_of_eq hn.symm)
        _ ≤ ⊤ := le_top
  · use F n
    constructor
    · calc
        _ ≤ G n := nonwitnessGroup_le_G
        _ < F n := G_lt_F_of_not_isPrimePow ho hnpp
    · exact F_lt_top_of_not_carmichael hc
end SPP
