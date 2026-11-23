-- Prove2me | solution 1 for P2M_Formalism_L2_PjFree_regular__int_f20b464cd2c4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:32.772801+00:00
-- url     : https://prove2.me/submissions/971aac22-08f7-4a52-950a-8e468a18b366

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegLaw
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree

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
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
namespace Formalism.L2.PjFree
namespace regular₂
theorem _root_.solution {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (h : regular₂ Xo c U) {a n} (hd : Dom a n)
    {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n)
    (h0 : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) :
    ∀ la, ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, 0 ≤ v f :=
  fun la v hv => (h.1.1 ⟨(a, n), hd⟩ ⟨f, hf⟩ fun la y => h0 la y.1 y.2).1 la ⟨v, hv⟩
end regular₂
end Formalism.L2.PjFree
