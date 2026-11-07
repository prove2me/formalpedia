-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.starSquare_triple_pairing_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:11:01.857726+00:00
-- url     : https://prove2.me/submissions/443ea74a-18e4-49c8-a367-4e5df88e361d

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
open QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
namespace QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
theorem _root_.solution (data : SourceInput F I Logical)
    {x y z : Word F I} (hx : x ∈ data.code.carrier) (hy : y ∈ data.code.carrier)
    (hz : z ∈ data.code.carrier) :
    wordPairing (wordStar x y) z = 0 := by
  have hxy : wordStar x y ∈ data.code.dual.carrier :=
    data.starSquare_le_dual (wordStar_mem_starSquare data.code hx hy)
  exact data.code.orthogonal_of_mem_dual hxy hz
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
