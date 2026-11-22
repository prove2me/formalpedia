-- Prove2me | solution 1 for ZhangYeung.IdentDistrib.condMutualInfo_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:10:04.652051+00:00
-- url     : https://prove2.me/submissions/68797ea7-5d72-4c22-9f12-14a3e16c4939

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_condEntropy_eq
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk
public import Theorems.Thm_ProbabilityTheory_IsUniform_comp
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_eq


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
open ZhangYeung
namespace ZhangYeung
namespace _root_.ZhangYeung.IdentDistrib
theorem _root_.solution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {S T U : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    [Finite S] [Finite T] [Finite U]
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
    {X' : Ω' → S} {Y' : Ω' → T} {Z' : Ω' → U}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hX' : Measurable X') (hY' : Measurable Y') (hZ' : Measurable Z')
    (h : IdentDistrib (fun ω => (X ω, Y ω, Z ω))
                      (fun ω' => (X' ω', Y' ω', Z' ω')) μ μ') :
    I[X : Y | Z; μ] = I[X' : Y' | Z'; μ'] := by
  have hXZ : IdentDistrib (fun ω => (X ω, Z ω)) (fun ω' => (X' ω', Z' ω')) μ μ' :=
    h.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hYZ : IdentDistrib (fun ω => (Y ω, Z ω)) (fun ω' => (Y' ω', Z' ω')) μ μ' :=
    h.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
  have hXYZ : IdentDistrib (fun ω => ((X ω, Y ω), Z ω))
      (fun ω' => ((X' ω', Y' ω'), Z' ω')) μ μ' :=
    h.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  have eHX : H[X | Z; μ] = H[X' | Z'; μ'] :=
    IdentDistrib.condEntropy_eq hX hZ hX' hZ' hXZ
  have eHY : H[Y | Z; μ] = H[Y' | Z'; μ'] :=
    IdentDistrib.condEntropy_eq hY hZ hY' hZ' hYZ
  have eHXY : H[⟨X, Y⟩ | Z; μ] = H[⟨X', Y'⟩ | Z'; μ'] :=
    IdentDistrib.condEntropy_eq (hX.prodMk hY) hZ (hX'.prodMk hY') hZ' hXYZ
  calc I[X : Y | Z; μ]
      = H[X | Z; μ] + H[Y | Z; μ] - H[⟨X, Y⟩ | Z; μ] :=
        ProbabilityTheory.condMutualInfo_eq hX hY hZ μ
    _ = H[X' | Z'; μ'] + H[Y' | Z'; μ'] - H[⟨X', Y'⟩ | Z'; μ'] := by rw [eHX, eHY, eHXY]
    _ = I[X' : Y' | Z'; μ'] := (ProbabilityTheory.condMutualInfo_eq hX' hY' hZ' μ').symm
end _root_.ZhangYeung.IdentDistrib
end ZhangYeung
