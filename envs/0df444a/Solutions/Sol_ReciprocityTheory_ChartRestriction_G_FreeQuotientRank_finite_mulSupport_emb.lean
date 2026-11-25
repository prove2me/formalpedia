-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finite_mulSupport_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:23.687707+00:00
-- url     : https://prove2.me/submissions/9242e32d-b54d-4701-a03a-7152543c377f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hadamard
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution {x : K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖FinitePlace.embedding v x‖).Finite := by
  have h : (Function.mulSupport fun w : FinitePlace K => w x).Finite :=
    FinitePlace.mulSupport_finite hx
  refine (h.image FinitePlace.maximalIdeal).subset ?_
  intro v hv
  refine ⟨FinitePlace.mk v, ?_, FinitePlace.maximalIdeal_mk v⟩
  simpa [Function.mem_mulSupport, FinitePlace.mk_apply] using hv
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
