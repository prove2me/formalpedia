-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine.scalar_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:16:46.655771+00:00
-- url     : https://prove2.me/submissions/1fcefa87-640b-49fc-8e14-71b67ee3d7d2

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldInverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSquareRootMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSInverseMachine

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
namespace QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine
theorem _root_.solution {p:ℕ} (a:LPSResiduePrime p) :
    (scalar a:ZMod a.q)=(lpsEffectiveDegreeRoot a)⁻¹ := ZMod.natCast_zmod_val _
end QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine
