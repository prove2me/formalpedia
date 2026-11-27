-- Prove2me | solution 1 for P2M_Formalism_L2_PjFree_intFrNe_of__7f5ea7e93907
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:51:02.417916+00:00
-- url     : https://prove2.me/submissions/ecf7b7f8-7a13-436e-9ccd-d22f8740a228

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Theorems.Thm_Formalism_L2_PjFree_algPtLa_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.PjFree
theorem _root_.solution (hN : XoNumPt Xo c) (hL : LocFld) (hE : IntFrExt Xo c) : IntFrNe Xo c (algCls Xo c) := by
  intro la
  obtain ⟨T, io, e, hO, hF, x, hx⟩ := algPtLa_of hN hL la
  obtain ⟨T', i, r, hr, hv, hF', y, hy⟩ := hE T io hF x hx
  refine ⟨T', i.comp io, r * e, ?_, y, ?_⟩
  · unfold OverLa at hO ⊢
    refine ⟨Nat.mul_pos hr hO.1, fun a => ?_⟩
    rw [RingHom.comp_apply, hv, hO.2 a]
    push_cast
    ring
  · unfold algCls IntFr.IsAlg
    exact hF'
end Formalism.L2.PjFree
