-- Prove2me | solution 1 for P2M_Formalism_MainNotions_N_Br___cont_43903f940a18
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:46:19.75824+00:00
-- url     : https://prove2.me/submissions/463c4496-c6dc-4914-8ad5-ada632d0af14

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.WeaklyAdmissibleFiltrations Module
noncomputable section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations Module
open Formalism Formalism.MainNotions Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N.Br
variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)
namespace Formalism.MainNotions.N.Br
theorem _root_.solution : Continuous (ι Bw) := Bw.e_symm_cont
end Formalism.MainNotions.N.Br
