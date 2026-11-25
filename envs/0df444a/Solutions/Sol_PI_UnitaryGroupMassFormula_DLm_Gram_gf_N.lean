-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DLm.Gram.gf_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:18.079197+00:00
-- url     : https://prove2.me/submissions/126dfb20-804a-4b9b-bf9f-804345ca5510

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFramesCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFdGramCut
import Theorems.Thm_PI_UnitaryGroupMassFormula_DLm_Gram_one_mem_UW
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_inv
import Theorems.Thm_Formalism_QuantumDeterminants_dInv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm PI.UnitaryGroupMassFormula.DLm.Gram
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace PI.UnitaryGroupMassFormula.DLm.Gram
theorem _root_.solution (D : B.RealPlaceData k r Wp Wq) {g n n' : B.Mat k r} (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    Gf k r D.z D.z' (n⁻¹ * g * n') = Gf k r D.z D.z' g := by
  have hs : n⁻¹ ∈ Sset k r D.z := by
    simp only [Sset, Set.mem_setOf_eq]
    exact ⟨1, one_mem_UW D.z, n⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn, by rw [one_mul]⟩
  have hs' : n' ∈ Sset k r D.z' := by
    simp only [Sset, Set.mem_setOf_eq]
    exact ⟨1, one_mem_UW D.z', n', hn', by rw [one_mul]⟩
  have hD := Formalism.QuantumDeterminants.dInv
  unfold DInv at hD
  simp only [Gf, hD k r D.z D.z' D.z_mem D.z'_mem _ hs _ hs' g]
end PI.UnitaryGroupMassFormula.DLm.Gram
