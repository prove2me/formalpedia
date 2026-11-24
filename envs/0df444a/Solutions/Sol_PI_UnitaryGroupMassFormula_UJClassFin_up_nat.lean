-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.up_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:53:42.076929+00:00
-- url     : https://prove2.me/submissions/6bcfa492-9f92-4f51-a305-d9c253fe5128

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_nat_mult


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution {M : ℕ} (L : Set (Fin M → E))
    (h4 : ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) :
    ∃ u : ℕ, 0 < u ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((u : F) • x i) := by
  obtain ⟨c, hc, hL⟩ := h4
  obtain ⟨u, hu, c', huc⟩ := nat_mult c hc
  refine ⟨u, hu, fun x hx i => ?_⟩
  have : (u : F) • x i = (c' : F) • ((c : F) • x i) := by
    rw [smul_smul]
    congr 1
    have := congrArg (algebraMap (𝓞 F) F) huc
    rw [map_natCast, map_mul] at this
    rw [this, mul_comm]
  rw [this, Algebra.smul_def]
  exact (IsIntegral.algebraMap (c'.isIntegral_coe)).mul (hL x hx i)
end PI.UnitaryGroupMassFormula.UJClassFin
