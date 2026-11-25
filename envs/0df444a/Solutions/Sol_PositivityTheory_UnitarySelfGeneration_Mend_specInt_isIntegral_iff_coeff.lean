-- Prove2me | solution 1 for PositivityTheory.UnitarySelfGeneration.Mend.specInt_isIntegral_iff_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:09.127108+00:00
-- url     : https://prove2.me/submissions/c927129f-f50d-43b7-ac83-80516690575a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_HomogeneousNonvanishing_SpectralNormIntegrality_SpecInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open PositivityTheory PositivityTheory.UnitarySelfGeneration PositivityTheory.UnitarySelfGeneration.Mend
open Polynomial
namespace PositivityTheory.UnitarySelfGeneration.Mend
theorem _root_.solution {K L : Type*} [Field K] [Field L] [Algebra K L] (O : ValuationSubring K)
    [Algebra O L] [IsScalarTower O K L] (y : L) (hy : IsIntegral K y) :
    IsIntegral O y ↔ ∀ n, (minpoly K y).coeff n ∈ O := by
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K h, coeff_map]
    exact Subtype.property _
  · intro h
    have hl : minpoly K y ∈ lifts (algebraMap O K) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hy)
    refine ⟨q, hm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap K, hq, minpoly.aeval]
end PositivityTheory.UnitarySelfGeneration.Mend
