-- Prove2me | solution 1 for QEC.Locality.symplectic_orthogonal_sup_eq_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:11:36.766241+00:00
-- url     : https://prove2.me/submissions/cb29664a-670c-4ad4-bceb-d9c5b4864fba

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Theorems.Thm_QEC_Locality_symplecticForm_add_left

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (U V : Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι)) :
    FiniteSymplectic.form.orthogonal (U ⊔ V) =
      FiniteSymplectic.form.orthogonal U ⊓ FiniteSymplectic.form.orthogonal V := by
  ext x
  constructor
  · intro hx
    exact ⟨fun u hu => hx u (Submodule.mem_sup_left hu),
      fun v hv => hx v (Submodule.mem_sup_right hv)⟩
  · rintro ⟨hU, hV⟩ y hy
    rcases Submodule.mem_sup.mp hy with ⟨u, hu, v, hv, rfl⟩
    have hu0 : symplecticForm u x = 0 := hU u hu
    have hv0 : symplecticForm v x = 0 := hV v hv
    change symplecticForm (u + v) x = 0
    rw [symplecticForm_add_left, hu0, hv0, add_zero]
end QEC.Locality
