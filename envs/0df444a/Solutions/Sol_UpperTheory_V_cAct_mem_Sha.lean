-- Prove2me | solution 1 for UpperTheory.V.cAct_mem_Sha
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:47:51.852977+00:00
-- url     : https://prove2.me/submissions/81389edb-e32e-49e7-804a-8868044b518a

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
import Theorems.Thm_UpperTheory_V_galois_action_preserves_sha


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.Top
open UpperTheory UpperTheory.V
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime]
namespace UpperTheory.V
theorem _root_.solution (D : LData E Ω l) (e : ℤ) {x : H1 (qzTw D e)} (hx : x ∈ Sha D e) : cAct D e x ∈ Sha D e :=
  galois_action_preserves_sha D e _ hx
end UpperTheory.V
