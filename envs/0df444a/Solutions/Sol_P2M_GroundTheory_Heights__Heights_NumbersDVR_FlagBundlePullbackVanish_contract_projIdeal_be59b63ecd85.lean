-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_contract_projIdeal_be59b63ecd85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:44.546798+00:00
-- url     : https://prove2.me/submissions/4b8c3767-960c-4094-81a4-7b096270788c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundlePullbackVanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundlePullbackVanish
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundlePullbackVanish
theorem _root_.solution {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
    {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) {N M : ℕ} {E : Type} [AddCommGroup E]
    [Module Ω E] (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    {Φ : Type} [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ) :
    FieldNumbers.contractPrime Function.Embedding.some (projIdeal F y w φ t) =
      pointIdeal (ι := fun k => bundleIdx ι M (Function.Embedding.some k)) F y := by
  let ψ : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename Option.some).toRingHom.comp (MvPolynomial.map (algebraMap Ω Φ))
  have hψ : Function.Injective ψ :=
    (rename_injective _ (Option.some_injective K)).comp
      (map_injective _ (algebraMap Ω Φ).injective)
  ext x
  simp only [FieldNumbers.contractPrime, projIdeal, pointIdeal, Ideal.mem_comap, RingHom.mem_ker]
  refine Iff.trans ?_ (map_eq_zero_iff ψ hψ)
  refine Iff.of_eq (congrArg (· = 0) ?_)
  induction x using MvPolynomial.induction_on with
  | C r =>
    simp [ψ, pointConeMap, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X, eval₂Hom_X', pointConeMap, aeval_X]
    simp [ψ, FieldNumbers.blockIncl, projCoord]
    exact Or.inl rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundlePullbackVanish
