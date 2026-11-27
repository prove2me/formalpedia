-- Prove2me | solution 1 for P2M_HcInf_haar_unique__ccef7ee8667f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:28.607653+00:00
-- url     : https://prove2.me/submissions/e47db4e9-658f-4712-b87a-fdf8ec863929

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExTop
import Theorems.Thm_HcInf_cd_haar_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.StandardLattice HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes HcS.L2.Fam.SG.Tau
  HcS.L2.Fam.SG.Tau.InfCmpCut Matrix MeasureTheory Filter Topology
open scoped TensorProduct ENNReal NNReal
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (T : Type) [Fintype T] (cd : CDHaar)
namespace HcInf
theorem _root_.solution : HaarUnique F E hc T cd := by
  intro W P Q Φ hmul hΦ hΦs μ hμ
  haveI : SigmaFinite (cd.cd P Q) := cd_haar_finite cd P Q
  haveI : (cd.cd P Q).IsHaarMeasure := cd.haar P Q
  haveI : (μ.map Φ).IsMulLeftInvariant := by
    constructor
    intro h
    have hLg : (fun x => Φ.symm h * x) = Φ.symm ∘ (fun y => h * y) ∘ Φ := by
      funext x
      apply Φ.injective
      simp [hmul]
    have hLgm : Measurable (fun x => Φ.symm h * x) := by
      rw [hLg]
      exact Φ.symm.measurable.comp ((measurable_const_mul h).comp Φ.measurable)
    have hc : (fun x => h * x) ∘ Φ = Φ ∘ (fun x => Φ.symm h * x) := by
      funext x
      simp [hmul]
    rw [Measure.map_map (measurable_const_mul h) Φ.measurable, hc,
      ← Measure.map_map Φ.measurable hLgm, map_mul_left_eq_self]
  haveI : IsFiniteMeasureOnCompacts (μ.map Φ) := by
    constructor
    intro K hK
    rw [MeasurableEquiv.map_apply]
    have hpre : Φ ⁻¹' K = Φ.symm '' K := by
      ext x
      constructor
      · intro hx
        exact ⟨Φ x, hx, Φ.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [hpre]
    exact (hK.image hΦs).measure_lt_top
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul (μ.map Φ) (Measure.pi fun _ : T => cd.cd P Q)⟩
end HcInf
