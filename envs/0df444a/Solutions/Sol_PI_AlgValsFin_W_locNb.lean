-- Prove2me | solution 1 for PI.AlgValsFin.W.locNb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:07.781568+00:00
-- url     : https://prove2.me/submissions/df57b981-9bb0-474d-bbeb-9341bb6eca9b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_InvMemUFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Neutral.B1 Topology
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L))
    (s : Set ((v.adicCompletionIntegers L : Set (v.adicCompletion L))))
    (hs : s ∈ 𝓝 (⟨1, (v.adicCompletionIntegers L).one_mem⟩ : (v.adicCompletionIntegers L : Set (v.adicCompletion L)))) :
    ∃ n : ℕ, ∀ y : (v.adicCompletionIntegers L : Set (v.adicCompletion L)),
      Valued.v ((y : v.adicCompletion L) - 1) ≤ exp (-(n : ℤ)) → y ∈ s := by
  rw [mem_nhds_subtype] at hs
  obtain ⟨u, hu, hsub⟩ := hs
  rw [Valued.mem_nhds] at hu
  obtain ⟨γ, hγ⟩ := hu
  obtain ⟨n, hn⟩ := exists_exp_neg_natCast_lt (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  refine ⟨n, fun y hy => hsub (hγ ?_)⟩
  show Valued.v.restrict ((y : v.adicCompletion L) - 1) < γ.1
  rw [← MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.lt_iff_lt, Valuation.embedding_restrict]
  exact lt_of_le_of_lt hy hn
end PI.AlgValsFin.W
