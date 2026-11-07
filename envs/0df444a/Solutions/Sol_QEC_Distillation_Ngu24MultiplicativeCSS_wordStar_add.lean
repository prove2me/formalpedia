-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.wordStar_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:22:25.578651+00:00
-- url     : https://prove2.me/submissions/141f5e14-f7b8-4619-b49c-9f14978681dd

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Semantics
open scoped BigOperators
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_23
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_24
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_25
omit [Fintype F] [Fintype I]
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution (x y z : Word F I) :
    wordStar (x + y) z = wordStar x z + wordStar y z := by
  ext i
  exact add_mul _ _ _
end QEC.Distillation.Ngu24MultiplicativeCSS
