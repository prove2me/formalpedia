-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.skew_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:53:56.759233+00:00
-- url     : https://prove2.me/submissions/c177bf29-a033-46c8-b39f-43c954c6f19f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SigmaMemIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Cayley
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SkewApprox
import Theorems.Thm_PI_UnitaryApproxFinWork_dv_two
import Theorems.Thm_PI_UnitaryApproxFinWork_MC_of_entries
import Theorems.Thm_PI_UnitaryApproxFinWork_MS_cT
import Theorems.Thm_PI_UnitaryApproxFinWork_MS_sub
import Theorems.Thm_PI_UnitaryApproxFinWork_dv_mul
import Theorems.Thm_PI_UnitaryApproxFinWork_sigR_dv
import Theorems.Thm_PI_UnitaryApproxFinWork_sigR_inclE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
namespace PI.UnitaryApproxFinWork
theorem _root_.solution (hAE : ApproxE) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (Y : (v : HeightOneSpectrum (𝓞 F)) → Matrix n n (E ⊗[F] v.adicCompletion F))
    (hY : ∀ v ∈ T, PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (Y v) = -Y v) (δ : 𝓞 F) (hδ : δ ≠ 0) :
    ∃ Y' : Matrix n n E, PI.UnitaryApproxDefs.cT (σ : E →+* E) Y' = -Y' ∧
      ∀ v ∈ T, MC E v δ (Y'.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) - Y v) := by
  have h2δ : (2 * δ : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hδ
  have hz : ∀ i j, ∃ e : E, ∀ v ∈ T,
      Cong E v (2 * δ) (Y v i j - PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) e) :=
    fun i j => hAE F E T (fun v => Y v i j) (2 * δ) h2δ
  choose Z hZ using hz
  refine ⟨Matrix.of fun i j => (2⁻¹ : E) * (Z i j - σ (Z j i)), ?_, fun v hv => ?_⟩
  · ext i j
    show (σ : E →+* E) ((2⁻¹ : E) * (Z j i - σ (Z i j))) = -((2⁻¹ : E) * (Z i j - σ (Z j i)))
    simp only [AlgHom.coe_toRingHom, map_mul, map_inv₀, map_ofNat, map_sub, hσ]
    ring
  · obtain ⟨A, hAS, hAeq⟩ := MC_of_entries (E := E) (v := v) (d := 2 * δ)
      (M := Y v - (Matrix.of Z).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) (fun i j => hZ i j v hv)
    refine ⟨PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) A - A, MS_sub (MS_cT σ hAS) hAS, ?_⟩
    ext i j
    have e1 := congrFun (congrFun hAeq i) j
    have e2 := congrArg (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (congrFun (congrFun hAeq j) i)
    have e3 := congrFun (congrFun (hY v hv) i) j
    change PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (Y v j i) = -(Y v i j) at e3
    change Y v i j - PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (Z i j) = dv E v (2 * δ) * A i j at e1
    change PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (Y v j i - PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (Z j i)) =
      PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (dv E v (2 * δ) * A j i) at e2
    rw [map_sub, map_mul, sigR_inclE, sigR_dv] at e2
    rw [dv_mul, dv_two] at e1 e2
    change PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) ((2⁻¹ : E) * (Z i j - σ (Z j i))) - Y v i j =
      dv E v δ * (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (A j i) - A i j)
    have hh : PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (2⁻¹ : E) * 2 = 1 := by
      rw [← map_ofNat (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero,
        map_one]
    rw [map_mul, map_sub]
    linear_combination (-(PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (2⁻¹ : E))) * e1 +
      (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (2⁻¹ : E)) * e2 -
      (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (2⁻¹ : E)) * e3 +
      (Y v i j + dv E v δ * (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (A j i) - A i j)) * hh
end PI.UnitaryApproxFinWork
