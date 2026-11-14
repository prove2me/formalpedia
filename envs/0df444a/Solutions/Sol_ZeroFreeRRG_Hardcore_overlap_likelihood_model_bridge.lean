-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.overlap_likelihood_model_bridge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:47:42.427747+00:00
-- url     : https://prove2.me/submissions/fde144ae-c995-4e08-92bc-4c01dd4be373
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20
import Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_limsup_mean_small_on
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t)
    (hcompact : IsCompact (cavityLaws m t))
    (hdirac : diracPi m t ∈ cavityLaws m t)
    (hbethe : ContinuousOn (betheK m t d) (cavityLaws m t))
    (hbase : betheK m t d (diracPi m t) = 0)
    (hpert : ContinuousOn (fun ν : ProbabilityMeasure (m.Spin → ℝ) =>
      (d:ℝ) * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
        ∂(ν : Measure (m.Spin → ℝ))) (cavityLaws m t))
    (hpertzero : (d:ℝ) * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
      ∂((diracPi m t : ProbabilityMeasure (m.Spin → ℝ)) : Measure (m.Spin → ℝ)) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ N : ℕ,
      ∀ n ≥ N, Even (n*d) →
        (1:ℝ)/n * plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) ≤ ε*s := by
  classical
  let K := cavityLaws m t
  let f := betheK m t d
  let g := fun ν : ProbabilityMeasure (m.Spin → ℝ) =>
    (d:ℝ) * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
      ∂(ν : Measure (m.Spin → ℝ))
  have hnonpos : ∀ ν ∈ K, f ν ≤ 0 := by
    intro ν hν
    by_cases he : ν = diracPi m t
    · subst ν
      simpa [f,hbase]
    · exact (hC1 ν hν he).le
  have hunique : ∀ ν ∈ K, f ν = 0 → ν = diracPi m t := by
    intro ν hν hf
    by_contra he
    have hh := hC1 ν hν he
    change betheK m t d ν = 0 at hf
    linarith
  let E := fun s n => (1:ℝ)/n * plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U)
  have hlim : ∀ s : ℝ, 0 < s → s < 1 → ∃ ν ∈ K,
      limsup (fun n => (E s n : EReal)) (atTop ⊓ 𝓟 {n : ℕ | Even (n*d)}) ≤ (f ν+s*g ν : ℝ) := by
    intro s hs hs1
    obtain ⟨ν,hν,hmax,hfirst,hsecond⟩ := (lemma_4_20 m hm d hd t ht).2.2 s hs.le hs1.le
    refine ⟨ν,hν,?_⟩
    have hh := hfirst.trans hsecond
    simpa only [E,f,g,mul_assoc,mul_left_comm,mul_comm] using hh
  exact overlap_limsup_mean_small_on K hcompact f g hbethe hpert (diracPi m t) hdirac
    hnonpos hbase hunique hpertzero E {n : ℕ | Even (n*d)} hlim
