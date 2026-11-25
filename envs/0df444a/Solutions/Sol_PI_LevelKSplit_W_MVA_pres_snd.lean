-- Prove2me | solution 1 for PI.LevelKSplit.W.MVA.pres_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:26:14.49066+00:00
-- url     : https://prove2.me/submissions/1faa303d-8dba-44ea-bd89-ff1cc6b9c957

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MapFstConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousFirstOrbitMap
import Theorems.Thm_PI_LevelKSplit_W_MVA_cancel_prod
import Theorems.Thm_PI_LevelKSplit_W_MVA_continuous_psiE
import Theorems.Thm_PI_LevelKSplit_W_MVA_continuous_psiE_symm
import Theorems.Thm_PI_LevelKSplit_W_MVA_continuous_lin
import Theorems.Thm_PI_LevelKSplit_W_ExC_continuous_lin
import Theorems.Thm_PI_LevelKSplit_W_MVA_psi_lin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.MVA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [LocallyCompactSpace R1] [T2Space R1]
  [SecondCountableTopology R1]
  [TopologicalSpace R2] [IsTopologicalRing R2] [LocallyCompactSpace R2] [T2Space R2]
  [SecondCountableTopology R2]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.LevelKSplit.W.MVA
theorem _root_.solution
    (hV : ∀ (g : HA (R1 × R2) σ J) (ν : Measure (Fin M → (R1 × R2) ⊗[F] E)),
      ν.IsAddHaarMeasure → ν.map (lin (R1 × R2) σ J g) = ν)
    (g : HA R2 σ J) (μ : Measure (Fin M → R2 ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (lin R2 σ J g) = μ := by
  let ν1 : Measure (Fin M → R1 ⊗[F] E) := Measure.addHaar
  let e := psiE (F := F) (E := E) (M := M) R1 R2
  have hc : Continuous e := continuous_psiE R1 R2
  have hcs : Continuous e.symm := continuous_psiE_symm R1 R2
  let P0 : Measure ((Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E)) := ν1.prod μ
  have : P0.IsAddHaarMeasure := inferInstance
  let P : Measure (Fin M → (R1 × R2) ⊗[F] E) := P0.map e.symm
  have : P.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map P0 hcs hc
  have hP := hV (lift R1 R2 σ J g) P inferInstance
  have hl1 := continuous_lin (R1 × R2) σ J (lift R1 R2 σ J g)
  have hl2 := continuous_lin R2 σ J g
  have hPe : P.map e = P0 := by
    rw [Measure.map_map hc.measurable hcs.measurable]
    have : (e ∘ e.symm) = id := funext e.apply_symm_apply
    rw [this, Measure.map_id]
  have key : P0.map (Prod.map id (lin R2 σ J g)) = P0 := by
    have h1 : (Prod.map id (lin R2 σ J g)) ∘ e = e ∘ (lin (R1 × R2) σ J (lift R1 R2 σ J g)) := by
      funext x
      exact (psi_lin R1 R2 σ J g x).symm
    calc P0.map (Prod.map id (lin R2 σ J g))
        = (P.map e).map (Prod.map id (lin R2 σ J g)) := by rw [hPe]
      _ = P.map ((Prod.map id (lin R2 σ J g)) ∘ e) :=
          Measure.map_map (measurable_id.prodMap hl2.measurable) hc.measurable
      _ = P.map (e ∘ (lin (R1 × R2) σ J (lift R1 R2 σ J g))) := by rw [h1]
      _ = (P.map (lin (R1 × R2) σ J (lift R1 R2 σ J g))).map e :=
          (Measure.map_map hc.measurable hl1.measurable).symm
      _ = P0 := by rw [hP, hPe]
  rw [← Measure.map_prod_map ν1 μ measurable_id hl2.measurable, Measure.map_id] at key
  exact (cancel_prod ν1 _ _ key).symm ▸ rfl
end PI.LevelKSplit.W.MVA
