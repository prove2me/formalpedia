-- Prove2me | solution 1 for SingleMachineSched.LPRelax.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:07:23.253374+00:00
-- url     : https://prove2.me/submissions/c2a53ada-a93a-4f44-be36-0452b1fa8156

import Definitions.Def_SingleMachineSched_Shared_PreemptiveSchedule
import Definitions.Def_SingleMachineSched_Shared_RelaxationR
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic
open MeasureTheory Set

private theorem bounded_integrable (A : Set ℝ) (hA : Bornology.IsBounded A) : IntegrableOn (fun t : ℝ => t) A :=
  (continuous_id.continuousOn.integrableOn_compact hA.isCompact_closure).mono_set subset_closure

private theorem interval_minimum (A : Set ℝ) (hA : MeasurableSet A)
    (hbound : Bornology.IsBounded A) (a p : ℝ) (hp : 0 ≤ p)
    (hsub : A ⊆ Ici a) (hvol : volume A=ENNReal.ofReal p) :
    p*(a+p/2) ≤ ∫ t in A,t ∧
      ((∫ t in A,t)=p*(a+p/2) ↔ A =ᵐ[volume] Ico a (a+p)) := by
  let d := a+p
  let J := Ico a d
  have had : a ≤ d := by dsimp [d];linarith
  have hJ : MeasurableSet J := measurableSet_Ico
  have hiA : IntegrableOn (fun t : ℝ => t) A := bounded_integrable A hbound
  have hiJ : IntegrableOn (fun t : ℝ => t) J := continuous_id.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hcA : IntegrableOn (fun _ : ℝ => d) A := integrableOn_const (by rw [hvol];finiteness)
  have hcJ : IntegrableOn (fun _ : ℝ => d) J := integrableOn_const (by dsimp [J];rw [Real.volume_Ico];exact ENNReal.ofReal_ne_top)
  have hvA : volume.real A=p := by simp [Measure.real,hvol,ENNReal.toReal_ofReal hp]
  have hvJ : volume.real J=p := by simp [Measure.real,J,d,Real.volume_Ico,ENNReal.toReal_ofReal hp]
  have hintJ : (∫ t in J,t)=p*(a+p/2) := by
    dsimp [J]
    rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le had,integral_id]
    dsimp [d]
    ring
  let f : ℝ → ℝ := J.indicator (fun t => t-d)
  let g : ℝ → ℝ := A.indicator (fun t => t-d)
  have hf : Integrable f := (hiJ.sub hcJ).integrable_indicator hJ
  have hg : Integrable g := (hiA.sub hcA).integrable_indicator hA
  have hfg (t : ℝ) : f t ≤ g t := by
    dsimp [f,g]
    by_cases htA : t∈A <;> by_cases htJ : t∈J
    · simp only [indicator_of_mem htA,indicator_of_mem htJ]
      exact le_rfl
    · simp only [indicator_of_mem htA,indicator_of_notMem htJ]
      have hta := hsub htA
      have htd : d ≤ t := le_of_not_gt (fun hh => htJ ⟨hta,hh⟩)
      linarith only [htd]
    · simp only [indicator_of_notMem htA,indicator_of_mem htJ]
      exact sub_nonpos.mpr htJ.2.le
    · simp only [indicator_of_notMem htA,indicator_of_notMem htJ,le_refl]
  have hfval : (∫ t,f t)=p*(a+p/2)-p*d := by
    rw [integral_indicator hJ,integral_sub hiJ hcJ,hintJ,setIntegral_const,hvJ,smul_eq_mul]
  have hgval : (∫ t,g t)=(∫ t in A,t)-p*d := by
    rw [integral_indicator hA,integral_sub hiA hcA,setIntegral_const,hvA,smul_eq_mul]
  have hineq := integral_mono hf hg hfg
  rw [hfval,hgval] at hineq
  refine ⟨by linarith only [hineq],?_⟩
  have hei : ((∫ t in A,t)=p*(a+p/2)) ↔ (∫ t,f t)=(∫ t,g t) := by rw [hfval,hgval];constructor <;> intro h <;> linarith only [h]
  rw [hei,integral_eq_iff_of_ae_le hf hg (Filter.Eventually.of_forall hfg)]
  constructor
  · intro he
    filter_upwards [he,volume.ae_ne d] with t ht hne
    apply propext
    change (t∈A ↔ t∈J)
    dsimp [f,g] at ht
    by_cases htA : t∈A <;> by_cases htJ : t∈J
    · exact iff_of_true htA htJ
    · simp only [indicator_of_mem htA,indicator_of_notMem htJ] at ht
      exact (hne (by linarith only [ht])).elim
    · simp only [indicator_of_notMem htA,indicator_of_mem htJ] at ht
      exact (hne (by linarith only [ht])).elim
    · exact iff_of_false htA htJ
  · intro he
    filter_upwards [he] with t ht
    change J.indicator (fun t : ℝ => t-d) t=A.indicator (fun t : ℝ => t-d) t
    by_cases htA : t∈A
    · have htJ : t∈J := ht.mp htA
      simp only [indicator_of_mem htA,indicator_of_mem htJ]
    · have htJ : t∉J := fun hj => htA (ht.mpr hj)
      simp only [indicator_of_notMem htA,indicator_of_notMem htJ]

theorem solution {n : ℕ} (p r : Fin n → ℕ) (hp : ∀ j,0 < p j) (A : Fin n → Set ℝ)
    (hA : SingleMachineSched.Shared.IsPreemptiveSchedule p r A) (S : Finset (Fin n)) (hS : S.Nonempty) :
    SingleMachineSched.Shared.pSum p S*(SingleMachineSched.Shared.rmin r S hS+SingleMachineSched.Shared.pSum p S/2) ≤
        ∑ j ∈ S,(p j : ℝ)*SingleMachineSched.Shared.meanBusyTime p A j ∧
      ((∑ j ∈ S,(p j : ℝ)*SingleMachineSched.Shared.meanBusyTime p A j)=
          SingleMachineSched.Shared.pSum p S*(SingleMachineSched.Shared.rmin r S hS+SingleMachineSched.Shared.pSum p S/2) ↔
        (⋃ j ∈ S,A j) =ᵐ[volume] Ico (SingleMachineSched.Shared.rmin r S hS)
          (SingleMachineSched.Shared.rmin r S hS+SingleMachineSched.Shared.pSum p S)) := by
  let U := ⋃ j ∈ S,A j
  have hU : MeasurableSet U := MeasurableSet.biUnion S.finite_toSet.countable (fun j _ => hA.measurable j)
  have hUb : Bornology.IsBounded U := (Bornology.isBounded_biUnion_finset S).mpr (fun j _ => hA.bounded j)
  have hdis : (↑S : Set (Fin n)).PairwiseDisjoint A := fun i hi j hj hij => hA.disjoint hij
  have hUsub : U ⊆ Ici (SingleMachineSched.Shared.rmin r S hS) := by
    intro t ht
    obtain ⟨j,hj,htj⟩ := mem_iUnion₂.mp ht
    exact (Finset.inf'_le (fun j => (r j : ℝ)) hj).trans (hA.release j htj)
  have hvol : volume U=ENNReal.ofReal (SingleMachineSched.Shared.pSum p S) := by
    rw [measure_biUnion_finset hdis (fun j _ => hA.measurable j)]
    simp only [hA.volume_eq,SingleMachineSched.Shared.pSum]
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Nat.cast_nonneg _)]
    simp
  have hint : (∫ t in U,t)=∑ j ∈ S,(p j : ℝ)*SingleMachineSched.Shared.meanBusyTime p A j := by
    rw [integral_biUnion_finset S (fun j _ => hA.measurable j) hdis (fun j _ => bounded_integrable _ (hA.bounded j))]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [SingleMachineSched.Shared.meanBusyTime]
    have hpj : (p j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hp j))
    field_simp
  have htot : 0 ≤ SingleMachineSched.Shared.pSum p S := Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)
  simpa only [hint] using interval_minimum U hU hUb (SingleMachineSched.Shared.rmin r S hS) (SingleMachineSched.Shared.pSum p S) htot hUsub hvol
