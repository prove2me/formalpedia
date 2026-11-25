-- Prove2me | solution 1 for PositivityTheory.KCo.top_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:44.914804+00:00
-- url     : https://prove2.me/submissions/05ec331e-75fd-4b3c-9a65-917f76d37d8f

import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_LocConstChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLevi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_TopOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.KCo
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open scoped TensorProduct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.KCo
theorem _root_.solution {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (Φ : V →ₗ[ℂ] U) {R N : Submodule ℂ V}
    (hK : ∀ f, Φ f = 0 → f ∈ R) (hR : R ≤ N) (h : N.map Φ = ⊤) : N = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : Φ v ∈ N.map Φ := by rw [h]; exact Submodule.mem_top
  obtain ⟨n, hn, hnv⟩ := hv
  have hker : v - n ∈ N := hR (hK _ (by rw [map_sub, hnv, sub_self]))
  have := N.add_mem hker hn
  simpa using this
end PositivityTheory.KCo
