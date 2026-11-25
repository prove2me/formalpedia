-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:19.725947+00:00
-- url     : https://prove2.me/submissions/3b9907ab-d260-40a5-9f34-886a3f27f196

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_GradeColMatMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Submodule
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {k : Type} [Field k] {n : ℕ}
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution {ι : Type} (b : Module.Basis ι k (Fin n → k)) (g : Matrix (Fin n) (Fin n) k) (d : ι → k)
    (hg : ∀ i, g *ᵥ b i = d i • b i) (S : Set ι) (c : k) (hS : ∀ i ∈ S, d i = c) (y : Fin n → k)
    (hy : y ∈ span k (b '' S)) : g *ᵥ y = c • y := by
  let f : (Fin n → k) →ₗ[k] (Fin n → k) := Matrix.toLin' g - c • LinearMap.id
  have hle : span k (b '' S) ≤ LinearMap.ker f := by
    rw [span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp [f, Matrix.toLin'_apply, hg, hS i hi]
  have := hle hy
  simp only [LinearMap.mem_ker, f, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Matrix.toLin'_apply] at this
  exact sub_eq_zero.mp this
end PositivityTheory.RgUd.T.Nil.Orb.BReps
