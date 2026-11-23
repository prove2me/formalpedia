-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__emptyPlaces_natAct_93c637f18902
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:30.695306+00:00
-- url     : https://prove2.me/submissions/9fa9e0c0-400c-4f64-8dbe-aa17a028b3f3

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GPlacesExampleNatAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.BasicNotions NumberField IsDedekindDomain
open Formalism.MainNotions.G
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (p : ℕ) (A : ∀ v, GL (Fin ((emptyPlaces p).m + 1)) ((emptyPlaces p).Qq v)) :
    (emptyPlaces p).natAct A = LinearMap.id := by
  have hs : ∀ G, (emptyPlaces p).subst G = AlgHom.id _ _ := by
    intro G
    apply MvPolynomial.algHom_ext
    rintro ⟨v, _⟩
    exact v.elim0
  unfold Places.natAct
  rw [hs, Finset.prod_eq_one (fun v _ => v.elim0), one_smul]
  rfl
end Formalism.BasicNotions.Examples₂
