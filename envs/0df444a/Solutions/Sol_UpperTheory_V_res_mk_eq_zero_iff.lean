-- Prove2me | solution 1 for UpperTheory.V.res_mk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:54.265381+00:00
-- url     : https://prove2.me/submissions/bfe3320a-3400-40e8-b9c0-c48691e80477

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
open UpperTheory UpperTheory.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable {τ : F ≃+* F} {σ : Ω ≃+* Ω}
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
namespace UpperTheory.V
theorem _root_.solution (D : LData F Ω l) (e : ℤ) (v : D.S) (z : Z1 (qzTw D e)) :
    resH1 (qzTw D e) (locFam D.S D.A v) (continuous_locFam D.S D.A v) (Submodule.Quotient.mk z) = 0 ↔
      ∃ m, ∀ g : Dec (F := F) (D.A v), z.1 (toGS Ω _ g.1) = qzTw D e (toGS Ω _ g.1) m - m :=
  (Submodule.Quotient.mk_eq_zero _).trans (mem_coboundaries1 _ _)
end UpperTheory.V
