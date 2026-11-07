-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_site_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:57:34.288474+00:00
-- url     : https://prove2.me/submissions/e40b66d5-ebcf-4a09-a4c9-b9ba7f0478cd

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_cons_eq_firstParity
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_sublist
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_openStripListAux_lower

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
theorem _root_.solution
    {L start : Nat} {width₀ : Nat} {widths : List Nat}
    {R : Finset (Site L)}
    (hR :
      R ∈ secondParity
        (openStripListAux L start (width₀ :: widths)))
    {p : Site L} (hp : p ∈ R) :
    start + width₀ ≤ p.1.val := by
  rw [openStripListAux, secondParity_cons_eq_firstParity] at hR
  have hRAll :
      R ∈ openStripListAux L (start + width₀) widths :=
    (firstParity_sublist _).subset hR
  exact mem_openStripListAux_lower hRAll hp
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
