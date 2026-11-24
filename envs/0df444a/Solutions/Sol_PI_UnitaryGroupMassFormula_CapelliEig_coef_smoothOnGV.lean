-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CapelliEig.coef_smoothOnGV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:51:12.768791+00:00
-- url     : https://prove2.me/submissions/42a93a1f-ce7c-4f53-955c-d3104f3dc00f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_CoreDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CapelliEig
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.CapelliEig
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (τ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)) (P : Hs →L[ℂ] Wp) (Q : Wq →L[ℂ] Hs)
    (hQ : ∀ w, Formalism.REAL.SmoothOnGV ε (fun x => τ x (Q w))) :
    Formalism.REAL.SmoothOnGV ε (fun x => P.comp ((τ x).comp Q)) := by
  intro g₀ hg₀
  let b := Module.finBasis ℂ Wq
  let c : Fin (Module.finrank ℂ Wq) → (Wq →L[ℂ] ℂ) := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  choose U F hUo hgU hF hEq using fun i => hQ (b i) g₀ hg₀
  refine ⟨⋂ i, U i, fun g => ∑ i, (c i).smulRight (P (F i g)), isOpen_iInter_of_finite hUo,
    Set.mem_iInter.2 hgU, ?_, ?_⟩
  · refine ContDiffOn.sum fun i _ => ?_
    have hL : ContDiff ℝ ∞ (fun y : Hs => (c i).smulRight (P y)) :=
      (((ContinuousLinearMap.smulRightL ℂ Wq Wp (c i)).comp P).restrictScalars ℝ).contDiff
    exact hL.comp_contDiffOn ((hF i).mono (Set.iInter_subset _ i))
  · intro g hg hgJ
    have h' : ∀ i, F i g = τ g (Q (b i)) := fun i => (hEq i g (Set.mem_iInter.1 hg i) hgJ).symm
    ext w
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_sum',
      Finset.sum_apply, ContinuousLinearMap.smulRight_apply, h', c,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul]
end PI.UnitaryGroupMassFormula.CapelliEig
