-- Prove2me | solution 1 for Psi.dyck_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:48:52.917304+00:00
-- url     : https://prove2.me/submissions/2feb7d9b-8e45-48b8-905b-1f3d764fc19d

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_dyck_leading
import Theorems.Thm_Psi_noDD_validFrom_gen
import Theorems.Thm_Psi_isDyckAux_iff
import Theorems.Thm_Psi_runHeight_append
import Theorems.Thm_Psi_runHeight_flatten_UD
import Theorems.Thm_Psi_runHeight_replicate_false
import Theorems.Thm_Psi_runHeight_replicate_true
import Theorems.Thm_Psi_runHeight_shift
import Theorems.Thm_Psi_validFrom_append


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (π : List Bool) (b : ℕ) (ρ ρ' : List Bool)
    (hd : IsDyck π) (hne : π ≠ [])
    (hstruct : π.drop (2 * cUD π + 1)
      = ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ')
    (hρDD : hasDD ρ = false) (hρU : ρ = [] ∨ ρ.head? = some true) :
    IsDyck (ρ ++ ρ') := by
  have hlead := dyck_leading π hd hne
  rw [hstruct] at hlead
  have hvρ0 : validFrom ρ 0 :=
    noDD_validFrom_gen ρ 0 le_rfl hρDD (by rcases hρU with h | h <;> rw [h] <;> simp)
  have hshift : runHeight ρ 1 = runHeight ρ 0 + 1 := by
    have := runHeight_shift ρ 0 1; simpa using this
  have hcast : runHeight ρ 1 + (b : ℤ) - ((b + 1 : ℕ) : ℤ) = runHeight ρ 0 := by
    rw [hshift]; push_cast; ring
  have hd2 := hd
  rw [IsDyck, isDyckAux_iff] at hd2
  obtain ⟨hv, he⟩ := hd2
  rw [hlead] at hv he
  rw [validFrom_append, runHeight_flatten_UD] at hv
  have hvM : validFrom (ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ') 1 := by
    have := hv.2; simpa [validFrom] using this
  rw [runHeight_append, runHeight_flatten_UD] at he
  have heM : runHeight (ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ') 1 = 0 := by
    simpa [runHeight] using he
  rw [show ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ'
      = ρ ++ (List.replicate b true ++ (List.replicate (b + 1) false ++ ρ')) from by
      simp [List.append_assoc]] at hvM heM
  rw [validFrom_append] at hvM
  rw [runHeight_append] at heM
  have hvρ' : validFrom ρ' (runHeight ρ 0) := by
    have h2 := hvM.2
    rw [validFrom_append, runHeight_replicate_true] at h2
    have h3 := h2.2
    rw [validFrom_append, runHeight_replicate_false] at h3
    rw [hcast] at h3; exact h3.2
  have herρ' : runHeight ρ' (runHeight ρ 0) = 0 := by
    rw [runHeight_append, runHeight_replicate_true, runHeight_append, runHeight_replicate_false] at heM
    rw [hcast] at heM; exact heM
  rw [IsDyck, isDyckAux_iff]
  exact ⟨by rw [validFrom_append]; exact ⟨hvρ0, hvρ'⟩, by rw [runHeight_append]; exact herρ'⟩
end Psi
