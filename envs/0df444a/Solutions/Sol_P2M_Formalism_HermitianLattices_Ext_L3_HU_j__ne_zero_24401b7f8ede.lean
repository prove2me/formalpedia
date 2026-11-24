-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_HU_j__ne_zero_24401b7f8ede
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:47.419389+00:00
-- url     : https://prove2.me/submissions/bc00a1d1-790d-4c37-bc54-785b345cee2e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {a : 𝓞 F} (ha : a ≠ 0) : jK (ι a) ≠ 0 := by
  intro h0
  apply ha
  have h1 : algebraMap F K (a : F) = 0 := h0
  rw [map_eq_zero] at h1
  first
  | exact_mod_cast h1
  | exact RingOfIntegers.ext h1
end Formalism.HermitianLattices.Ext.L3.HU
