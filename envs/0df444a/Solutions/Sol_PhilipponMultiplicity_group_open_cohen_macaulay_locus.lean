-- Prove2me | solution 1 for PhilipponMultiplicity.group_open_cohen_macaulay_locus
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-29T11:15:00.556636+00:00
-- url     : https://prove2.me/submissions/bb819014-176e-4b45-ba7f-85778f5b5cea

import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_Degree

import Theorems.Thm_PhilipponMultiplicity_group_has_regular_homogeneous_representative
import Theorems.Thm_PhilipponMultiplicity_regular_group_representatives_give_cm_locus
import Theorems.Thm_PhilipponMultiplicity_group_representative_local_rings_equiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open PhilipponMultiplicity
noncomputable section

theorem solution
    (K : Type*) [NontriviallyNormedField K] [IsAlgClosed K]
    (G : EmbeddedGroupProduct K) :
    ∃ U : TopologicalSpace.Opens (MaximalSpectrum G.CoordinateRing),
      (∀ r : GroupHomogeneousRepresentative G, representativeMaximalIdeal G r ∈ U) ∧
      (∀ m ∈ U, G.vanishingIdeal Set.univ ≤ m.asIdeal →
        ∃ r : GroupHomogeneousRepresentative G, representativeMaximalIdeal G r = m) ∧
      Hilbert.IsLocallyCohenMacaulayOn K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) U := by
  obtain ⟨r,hr⟩ := group_has_regular_homogeneous_representative K G
  letI := hr
  apply regular_group_representatives_give_cm_locus K G
  intro s
  obtain ⟨e⟩ := group_representative_local_rings_equiv K G r s
  exact IsRegularLocalRing.of_ringEquiv
    (R := (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) ⧸
      (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
        (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal))) e
