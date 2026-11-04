-- Prove2me | solution 1 for ThreeSum.LightExtensionMenuMatrix.value_is_rowMenu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:03.804108+00:00
-- url     : https://prove2.me/submissions/51920757-2912-4817-912e-4831b070e1e9

import Definitions.Def_Submission_ThreeSum_LightExtensionFieldMultiply
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuSemantics
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_trajectory_rowMenu
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_lt


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionMenuMatrix
open TernaryExtensionEncoding
set_option maxHeartbeats 2000000
variable {p : ℕ} [Fact p.Prime] {f : Polynomial (ZMod p)}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
namespace ThreeSum.LightExtensionMenuMatrix
theorem _root_.solution (hf : f.Monic) (hd : 0 < f.natDegree)
    (J r : ℕ) (hr : r < (p^f.natDegree)*(p^f.natDegree)) {i : ℕ} (hi : i < J+2) :
    LightExtensionSeedMatrix.value (encodedMul hf) (p^f.natDegree) p r
      (TernarySignedLayout.offset J i)=
      (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (seed hf r hr)
        ⟨TernarySignedLayout.offset J i,TernarySignedLayout.offset_lt hi⟩).val := by
  let q := p^f.natDegree
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos _
  have hx : r/q < q := (Nat.div_lt_iff_lt_mul hq).mpr hr
  have hy : r%q < q := Nat.mod_lt r hq
  have hex : encode hf ((encodedEquiv hf).symm ⟨r/q,hx⟩)=r/q := by
    exact congrArg Fin.val ((encodedEquiv hf).apply_symm_apply ⟨r/q,hx⟩)
  have hey : encode hf ((encodedEquiv hf).symm ⟨r%q,hy⟩)=r%q := by
    exact congrArg Fin.val ((encodedEquiv hf).apply_symm_apply ⟨r%q,hy⟩)
  have h := trajectory_rowMenu hf hd (J+2)
    ((encodedEquiv hf).symm ⟨r/q,hx⟩) ((encodedEquiv hf).symm ⟨r%q,hy⟩)
    ⟨TernarySignedLayout.offset J i,TernarySignedLayout.offset_lt hi⟩
  rw [hex,hey] at h
  exact h
end ThreeSum.LightExtensionMenuMatrix
