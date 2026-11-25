-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.small_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:27:55.322987+00:00
-- url     : https://prove2.me/submissions/f6b5def2-1300-4d26-abfd-dbae2b968884

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology WithZero Filter
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (v : HeightOneSpectrum R) {s : Set (v.adicCompletion K)}
    (hs : s ∈ 𝓝 (0 : v.adicCompletion K)) :
    ∃ n : ℕ, ∀ x, Valued.v x ≤ exp (-(n : ℤ)) → x ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hg := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  refine ⟨(log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1, fun x hx => hγ ?_⟩
  show Valued.v.restrict x < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt hx ?_
  calc exp (-(((log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1 : ℕ) : ℤ))
      < exp (log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) := exp_lt_exp.2 (by omega)
    _ = _ := exp_log hg
end ReciprocityTheory.ChartRestriction.G.SA
