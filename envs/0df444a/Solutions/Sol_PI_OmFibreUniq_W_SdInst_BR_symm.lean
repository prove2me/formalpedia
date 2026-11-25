-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdInst.BR_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:59:52.90241+00:00
-- url     : https://prove2.me/submissions/456477a8-02af-4e69-ad07-cc2e032081d1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExInst
import Theorems.Thm_PI_VolStabSW_HasDens_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdInst
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd PI.OmFibreUniq.W.SdAbs
open PI.VolStabSW PI.VolStabSW.SdUniqW PI.VolStabSW.SdDualW PI.AdicCompletionValuation
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.OmFibreUniq.W.SdInst
theorem _root_.solution (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n a : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X Y : Fin a → Fin n → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X Y = BR (Fv F v) σ J Y X := by
  let φ : (Fv F v ⊗[F] E) →ₐ[Fv F v] (Fv F v ⊗[F] E) :=
    Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ
  have hφ : ∀ z, sigR (Fv F v) σ z = φ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [φ, sigR, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hinv : ∀ z, φ (φ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [φ, Algebra.TensorProduct.map_tmul, hσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let e := AlgEquiv.ofBijective φ (Function.Involutive.bijective hinv)
  have htr : ∀ z, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ z) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z := by
    intro z
    rw [hφ]
    exact Algebra.trace_eq_of_algEquiv e z
  have hss : ∀ z, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
    intro z
    rw [hφ, hφ]
    exact hinv z
  have hsJ : ∀ i j, sigR (Fv F v) σ (JR (Fv F v) J i j) = JR (Fv F v) J j i := by
    intro i j
    simp [JR, inclR, sigR, Algebra.TensorProduct.map_tmul, hJ]
  have hsym : ∀ x y : Fin n → Fv F v ⊗[F] E,
      hR (Fv F v) σ J x y = sigR (Fv F v) σ (hR (Fv F v) σ J y x) := by
    intro x y
    unfold hR Formalism.UG.hform
    simp only [map_sum, map_mul, hss, hsJ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold BR
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hsym, htr]
end PI.OmFibreUniq.W.SdInst
