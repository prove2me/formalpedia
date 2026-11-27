-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.T2.exists_dec_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:39:53.456978+00:00
-- url     : https://prove2.me/submissions/f4ac7b1e-3e70-4301-8a22-73666cc7d739

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_WachLatticeTwists_CharacterSplitJumps_Statement
import Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_Statement
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_TraceFormulas_LatDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.T2
open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable [hT2Core : Fact Core]
namespace ReciprocityTheory.ChartRestriction.T2
theorem _root_.solution {p : ℕ} [Fact p.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (i : ↥(A.decompositionSubgroup F) ≃ₜ* GK p K),
      (∀ (O : Type) [CommRing O] (ε : ↥(A.decompositionSubgroup F) →* Oˣ),
        IsCycOn p (A.decompositionSubgroup F) ε → IsCyc p K (carry i ε)) ∧
      (∀ g : ↥(A.decompositionSubgroup F), i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v → Module.finrank ℚ_[p] K = locDeg v := hT2Core.out.dec A hp
end ReciprocityTheory.ChartRestriction.T2
