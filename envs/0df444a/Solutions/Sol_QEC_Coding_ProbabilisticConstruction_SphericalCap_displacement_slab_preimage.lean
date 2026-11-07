-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.displacement_slab_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:55.358417+00:00
-- url     : https://prove2.me/submissions/58de6e46-89af-4c7d-9950-f0b2740cb2ac

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {R : ℝ} (hR : 0 < R) (n : Sphere) (d h : ℝ) :
    (fun s : Sphere => R • (s : Space)) ⁻¹' slab n d h =
      zone n ((d-h)/R) ((d+h)/R) := by
  ext s
  simp only [slab,zone,mem_preimage,mem_setOf_eq,real_inner_smul_right,abs_le]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(div_le_iff₀ hR).mpr (by nlinarith), (le_div_iff₀ hR).mpr (by nlinarith)⟩
  · rintro ⟨h1,h2⟩
    have h1 := (div_le_iff₀ hR).mp h1
    have h2 := (le_div_iff₀ hR).mp h2
    constructor <;> nlinarith
end QEC.Coding.ProbabilisticConstruction.SphericalCap
