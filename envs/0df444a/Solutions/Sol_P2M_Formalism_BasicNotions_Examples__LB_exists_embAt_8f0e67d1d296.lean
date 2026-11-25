-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_exists_embAt_8f0e67d1d296
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:43:20.275223+00:00
-- url     : https://prove2.me/submissions/fe66ad12-61b0-4619-b200-a9321a99a5b6

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocG
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_exists_emb_1690c8e74711
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_isAlgClosureQ_74b0853cbd95
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_val_lt_one_iff_ff0494b5971d
import Theorems.Thm_ReciprocityTheory_Gal_isPlaceOver_placeOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime]
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ φ : F →+* PadicAlgCl l, ∀ x : 𝓞 F, x ∈ w.asIdeal ↔ ‖φ (x : F)‖ < 1 := by
  have hA := isPlaceOver_placeOf (AlgebraicClosure F) w
  have hAl : (placeOf (AlgebraicClosure F) w).valuation ((l : ℕ) : AlgebraicClosure F) < 1 := by
    have := (hA ((l : ℕ) : 𝓞 F)).mpr hw
    simpa using this
  haveI : IsAlgClosure ℚ (AlgebraicClosure F) := isAlgClosureQ F (AlgebraicClosure F)
  obtain ⟨j, hj⟩ := exists_emb (l := l) _ hAl
  exact ⟨j.comp (algebraMap F (AlgebraicClosure F)), fun x => by
    rw [← hA x, val_lt_one_iff hj]; rfl⟩
end Formalism.BasicNotions.Examples₂.LB
