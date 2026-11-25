-- Prove2me | solution 1 for PI.VolStabW.smul_mem_hermO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:43.713803+00:00
-- url     : https://prove2.me/submissions/c49dadf6-a3b7-499e-a5fc-c5479e05ee3b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI
import Theorems.Thm_PI_VolStabW_coe_hermSMul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
namespace PI.VolStabW
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
    {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) {S : HermR (Fv F v) σ a}
    (hS : S ∈ hermO b v σ a) : s • S ∈ hermO b v σ a := by
  have hS' : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F := hS
  show ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      (((s • S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈
        v.adicCompletionIntegers F
  intro i j k
  rw [coe_hermSMul]
  simp only [Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hs (hS' i j k)
end PI.VolStabW
