-- Prove2me | solution 1 for PI.SqPairLocal.Mdl.ball_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:35.982581+00:00
-- url     : https://prove2.me/submissions/e07b01ef-75cc-4435-ac71-faac6d57d838

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SigKApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_PowerSeriesExpansionImageDenseWithDenominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain HeightOneSpectrum WithZero IsLocalRing Topology Filter
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
open PI PI.SqPairLocal PI.SqPairLocal.Mdl
open PI.SqPairLocal Formalism.BasicNotions.Examples₂
variable {E : Type} [Field E] [NumberField E] [StarRing E] (v : HeightOneSpectrum (𝓞 E))
namespace PI.SqPairLocal.Mdl
theorem _root_.solution (x : v.adicCompletion E) {s : Set (v.adicCompletion E)} (hs : s ∈ 𝓝 x) :
    ∃ K : ℕ, ∀ z : v.adicCompletion E, Valued.v (z - x) ≤ exp (-(K : ℤ)) → z ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hs
  have h0 : embedding γ.1 ≠ 0 := fun h =>
    γ.ne_zero (embedding_injective (h.trans (map_zero _).symm))
  obtain ⟨K, hK⟩ := wz_exists_nat_lt _ h0
  refine ⟨K, fun z hz => hγ ?_⟩
  show Valued.v.restrict (z - x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hz hK
end PI.SqPairLocal.Mdl
