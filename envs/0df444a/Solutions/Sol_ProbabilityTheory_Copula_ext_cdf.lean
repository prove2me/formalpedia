-- Prove2me | solution 1 for ProbabilityTheory.Copula.ext_cdf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:48:11.094357+00:00
-- url     : https://prove2.me/submissions/44c2ba11-cedc-4af7-9f37-0bb1a266aa5f

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_dim_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_ext
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
attribute [local simp] ProbabilityTheory.Copula.cdf_dim_zero
attribute [local simp] ProbabilityTheory.Copula.cdf_one
attribute [local simp] ProbabilityTheory.Copula.cdf_update_one
attribute [local simp] ProbabilityTheory.Copula.cdf_zero
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory MeasurableSpace Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution {C D : Copula d} (h : ∀ u, C.cdf u = D.cdf u) : C = D := by
  classical
  apply ext
  let S : Fin d → Set (Set I) := fun _ => range Iic
  have hgen (i : Fin d) : generateFrom (S i) = (inferInstance : MeasurableSpace I) :=
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic I)).symm
  have hspan (i : Fin d) : IsCountablySpanning (S i) := by
    refine ⟨fun _ : ℕ => univ, fun _ => ?_, ?_⟩
    · refine ⟨1, ?_⟩
      ext x
      simp [unitInterval.le_one']
    · apply Subset.antisymm (subset_univ _)
      intro x _
      exact mem_iUnion.mpr ⟨0, mem_univ x⟩
  refine ext_of_generate_finite _ (generateFrom_eq_pi hgen hspan).symm
    (IsPiSystem.pi fun _ => isPiSystem_Iic) ?_ (by simp)
  rintro _ ⟨s, hs, rfl⟩
  have hs' : ∀ i, ∃ u : I, Iic u = s i := fun i => hs i (mem_univ i)
  choose u hu using hs'
  have hbox : Set.pi univ s = Iic u := by
    ext x
    simp only [mem_univ_pi, ← hu, mem_Iic, Pi.le_def]
  rw [hbox]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (h u)
end ProbabilityTheory.Copula
