-- Prove2me | solution 1 for UpperTheory.V.exists_cocycle_h1TwistConjByLift_mk_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:05.796702+00:00
-- url     : https://prove2.me/submissions/d49a91b3-876e-4c13-8ace-c0c66c1c3241

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
theorem _root_.solution (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ) (z : Z1 (qzTw D e)) :
    ∃ z' : Z1 (qzTw D e), h1TwistConjByLift D e h (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ g, z'.1 g = twScal l σ e • z.1 (conjGS D h g) :=
  ⟨_, rfl, fun _ => rfl⟩
end UpperTheory.V
