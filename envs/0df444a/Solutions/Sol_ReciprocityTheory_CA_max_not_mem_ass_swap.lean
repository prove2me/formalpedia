-- Prove2me | solution 1 for ReciprocityTheory.CA.max_not_mem_ass_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:41.527438+00:00
-- url     : https://prove2.me/submissions/dfb5a566-7f20-4b9b-af70-4abaf0dd3ce2

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Theorems.Thm_ReciprocityTheory_CA_exch_socle
import Theorems.Thm_ReciprocityTheory_CA_socle_of_max_mem_ass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R]
namespace ReciprocityTheory.CA
theorem _root_.solution {x y w : R} (hy : y ∈ maximalIdeal R) (rx : IsSMulRegular M x)
    (ry : IsSMulRegular M y) (hw : w ∈ maximalIdeal R) (rw : IsSMulRegular (QuotSMulTop y M) w) :
    maximalIdeal R ∉ associatedPrimes R (QuotSMulTop x M) := by
  intro h
  obtain ⟨a, ha, hz⟩ := socle_of_max_mem_ass h
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  have ha' : a ∉ x • (⊤ : Submodule R M) := fun h' => ha ((Submodule.Quotient.mk_eq_zero _).mpr h')
  have hz' : ∀ z ∈ maximalIdeal R, z • a ∈ x • (⊤ : Submodule R M) := fun z hz0 =>
    (Submodule.Quotient.mk_eq_zero _).mp (by rw [Submodule.Quotient.mk_smul]; exact hz z hz0)
  obtain ⟨b, hb, hzb⟩ := exch_socle hy rx ry ha' hz'
  have hb0 : (Submodule.Quotient.mk b : QuotSMulTop y M) ≠ 0 :=
    fun h' => hb ((Submodule.Quotient.mk_eq_zero _).mp h')
  apply hb0
  apply rw
  show w • _ = w • (0 : QuotSMulTop y M)
  rw [smul_zero, ← Submodule.Quotient.mk_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hzb w hw)
end ReciprocityTheory.CA
