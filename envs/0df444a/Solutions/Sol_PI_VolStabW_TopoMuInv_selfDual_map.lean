-- Prove2me | solution 1 for PI.VolStabW.TopoMuInv.selfDual_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:37:44.99787+00:00
-- url     : https://prove2.me/submissions/4ddd0dd8-c7b9-4be2-ac11-877ea2705cbf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoFibInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMuInv
import Theorems.Thm_PI_VolStabW_TopoMuInv_BR_smul_left
import Theorems.Thm_P2M_PI_VolStabW_TopoMuInv_smul_neg__7eb46811fd83

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.TopoMuInv
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabW.TopoMuInv
theorem _root_.solution (ψR : R → ℂ) {n : ℕ} (μ : Measure (Fin n → Fin M → R ⊗[F] E))
    (hμ : SdW F E σ M J R ψR n μ) (h : HA R σ J) :
    SdW F E σ M J R ψR n (μ.map (fun X => h • X)) := by
  let e := PI.VolStabW.smulHomeo R σ (a := n) J h
  let em := e.toMeasurableEquiv
  have hmap : μ.map (fun X => h • X) = μ.map em := rfl
  have : μ.IsAddHaarMeasure := hμ.1
  refine ⟨?_, fun Φ hc hcs hI z => ?_⟩
  · exact (smulAddEquiv R σ J h n).isAddHaarMeasure_map μ e.continuous e.symm.continuous
  rw [hmap] at hI ⊢
  let Fh : (Fin n → Fin M → R ⊗[F] E) → ℂ := fun w =>
    ∫ x, Φ (h • x) * ψR (BR R σ J x w) ∂μ
  have hin : ∀ y, ∫ x, Φ x * ψR (BR R σ J x y) ∂(μ.map em) = Fh (h⁻¹ • y) := fun y => by
    rw [integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Φ (h • x) * ψR (BR R σ J (h • x) y) = Φ (h • x) * ψR (BR R σ J x (h⁻¹ • y))
    rw [BR_smul_left]
  have hI' : Integrable Fh μ := by
    rw [integrable_map_equiv] at hI
    refine hI.congr (Filter.Eventually.of_forall fun y => ?_)
    show ∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em) = Fh y
    rw [hin, inv_smul_smul]
  have key := hμ.2 (fun x => Φ (h • x)) (hc.comp e.continuous) (hcs.comp_homeomorph e) hI'
    (h⁻¹ • z)
  rw [integral_map_equiv]
  have e3 : (fun y => (∫ x, Φ x * ψR (BR R σ J x (em y)) ∂(μ.map em)) *
      ψR (BR R σ J (em y) z)) = fun y => Fh y * ψR (BR R σ J y (h⁻¹ • z)) := by
    funext y
    show (∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em)) * ψR (BR R σ J (h • y) z) = _
    rw [hin, inv_smul_smul, BR_smul_left]
  rw [e3]
  refine key.trans ?_
  show Φ (h • -(h⁻¹ • z)) = Φ (-z)
  rw [smul_neg', smul_inv_smul]
end PI.VolStabW.TopoMuInv
