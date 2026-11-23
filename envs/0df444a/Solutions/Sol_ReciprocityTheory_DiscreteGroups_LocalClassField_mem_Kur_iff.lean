-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:53.530798+00:00
-- url     : https://prove2.me/submissions/0008934e-c468-4af5-8019-67c663940df8

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kn_le_Kur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kn_mono
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_Kn_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) (x : PadicAlgCl p) :
    x ∈ MaximalUnramifiedExtension p K ↔ ∃ n, 0 < n ∧ x ∈ Kn p K n := by
  constructor
  · intro hx
    have hdir : Directed (· ≤ ·) (fun n : ℕ => Kn p K (n + 1)) := by
      intro i j
      refine ⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩
      · have : (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1) := Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))
        change Kn p K (i + 1) ≤ Kn p K ((i + 1) * (j + 1) - 1 + 1)
        rw [this]; exact Kn_mono p K hK (Dvd.intro _ rfl)
      · have : (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1) := Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))
        change Kn p K (j + 1) ≤ Kn p K ((i + 1) * (j + 1) - 1 + 1)
        rw [this]; exact Kn_mono p K hK (Dvd.intro_left _ rfl)
    have h := IntermediateField.coe_iSup_of_directed hdir
    have hx' : x ∈ ((⨆ n : ℕ, Kn p K (n + 1) : IntermediateField ℚ_[p] (PadicAlgCl p)) : Set (PadicAlgCl p)) := hx
    rw [h] at hx'
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx'
    exact ⟨k + 1, Nat.succ_pos k, hk⟩
  · rintro ⟨n, hn, hx⟩
    exact Kn_le_Kur hn hx
end ReciprocityTheory.DiscreteGroups.LocalClassField
