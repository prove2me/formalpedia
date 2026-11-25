-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.smul_hermO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:10.497772+00:00
-- url     : https://prove2.me/submissions/27a51f73-9299-4f30-adc3-a51343d1867f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolC
import Theorems.Thm_PI_VolStabSW_SdDualW_crd_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.VolAAW
theorem _root_.solution (σ : E →ₐ[F] E) (a : ℕ) :
    ∀ s ∈ v.adicCompletionIntegers F, ∀ S ∈ (hermO b v σ a : Set (HermR (Fv F v) σ a)),
      ∃ S' ∈ (hermO b v σ a : Set (HermR (Fv F v) σ a)),
        ∀ T, pairHerm (Fv F v) σ a S' T = s * pairHerm (Fv F v) σ a S T := by
  intro s hs S hS
  have hmem : s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ HermR (Fv F v) σ a := by
    intro p q
    simp only [Matrix.smul_apply, sigR_smul, S.2 p q]
  refine ⟨⟨_, hmem⟩, ?_, fun T => ?_⟩
  · intro p q k
    have := crd_smul v b s ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q) k
    simp only [crd] at this
    show (Algebra.TensorProduct.basis (Fv F v) b).repr
      (s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q) k ∈ _
    rw [this]
    exact mul_mem hs (hS p q k)
  · simp only [pairHerm, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul,
      smul_eq_mul]
    ring
end PI.VolStabSW.VolAAW
