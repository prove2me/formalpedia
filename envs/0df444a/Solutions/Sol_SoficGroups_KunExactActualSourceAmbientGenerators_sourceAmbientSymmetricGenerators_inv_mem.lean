-- Prove2me | solution 1 for SoficGroups.KunExactActualSourceAmbientGenerators.sourceAmbientSymmetricGenerators_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/e61ff9ce-1bfc-4ee5-b786-df3657e07f39

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunExactActualSourceAmbientGenerators
open SoficGroups.KunExactKazhdanGeneratorChange
namespace SoficGroups.KunExactActualSourceAmbientGenerators
theorem _root_.solution
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (g : SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode)
    (hg : g ∈ sourceAmbientSymmetricGenerators SΓ) :
    g⁻¹ ∈ sourceAmbientSymmetricGenerators SΓ := by
  classical
  have hcases :
      g = 1 ∨
        g ∈ sourcePositiveGenerators SΓ ∨
        ∃ y ∈ sourcePositiveGenerators SΓ, y⁻¹ = g := by
    simpa [sourceAmbientSymmetricGenerators, Finset.mem_image] using hg
  rcases hcases with rfl | hgpos | ⟨y, hy, rfl⟩
  · simp [sourceAmbientSymmetricGenerators]
  · have hinv :
        g⁻¹ ∈ (sourcePositiveGenerators SΓ).image
          (fun x => x⁻¹) :=
      Finset.mem_image.mpr ⟨g, hgpos, rfl⟩
    simp [sourceAmbientSymmetricGenerators, hinv]
  · simp [sourceAmbientSymmetricGenerators, hy]
end SoficGroups.KunExactActualSourceAmbientGenerators
