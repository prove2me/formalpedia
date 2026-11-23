-- Prove2me | solution 1 for PositivityTheory.FamInh.val_int_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:27.63795+00:00
-- url     : https://prove2.me/submissions/83a32e9a-1a0c-4307-88ac-0c3c4e149f60

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_WeilBound_CoreStatements_PlaceConnectedComponents_ArtinA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
open PositivityTheory PositivityTheory.FamInh
variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
variable [IsGalois K L]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}
omit [IsAlgClosure K Ω] [IsAlgClosure L Ω]
namespace PositivityTheory.FamInh
theorem _root_.solution (A : ValuationSubring Ω) (x : 𝓞 L) : A.valuation (algebraMap L Ω (x : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A
    (x.isIntegral_coe.map ((algebraMap L Ω).toIntAlgHom)))
end PositivityTheory.FamInh
