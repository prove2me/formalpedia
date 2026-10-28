-- Prove2me | solution 1 for SecretaryPred.LearnedDynkin.case_iii
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T07:02:37.02943+00:00
-- url     : https://prove2.me/submissions/4fa627f9-4e44-44da-8dbe-150029d2f803

import Definitions.Def_SecretaryPred_LearnedDynkin_Setting
import Init
import Mathlib


section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory

 theorem no_deviates {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (i : Fin n) : ¬ Deviates theta v vhat i := by
  have hn : i ∉ Mset theta v vhat := by rw [hM]; simp
  simpa [Mset] using hn

 theorem no_secretary {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (t : Fin n → ℝ) (i : Fin n) :
    ¬ SecretaryAt theta v vhat t i := by
  rintro ⟨j,_,hj⟩
  exact no_deviates hM j hj

 theorem stops_iff {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (tau : ℝ) (ihat : Fin n) (t : Fin n → ℝ) (i : Fin n) :
    Stops theta tau v vhat ihat t i ↔ i=ihat := by
  simp [Stops,no_secretary hM]

 theorem hired_iff {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (tau : ℝ) (ihat : Fin n) (t : Fin n → ℝ) (i : Fin n) :
    Hired theta tau v vhat ihat t i ↔ i=ihat := by
  simp only [Hired,stops_iff hM]
  constructor
  · exact And.left
  · intro h
    subst i
    refine ⟨rfl,?_⟩
    intro j hj he
    subst j
    exact lt_irrefl _ hj

 theorem value_eq {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (tau : ℝ) (ihat : Fin n) (t : Fin n → ℝ) :
    algValue theta tau v vhat ihat t = v ihat := by
  classical
  simp [algValue,hired_iff hM]

 theorem arrival_probability (n : ℕ) : IsProbabilityMeasure (arrivalLaw n) := by
  constructor
  simp [arrivalLaw,Measure.restrict_apply,Real.volume_Icc_pi]

 theorem expected_eq {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (tau : ℝ) (ihat : Fin n) :
    expectedValue theta tau v vhat ihat = v ihat := by
  letI := arrival_probability n
  simp [expectedValue,value_eq hM]

 theorem consistency {n : ℕ} (v vhat : Fin n → ℝ) (ihat : Fin n)
    (hihat : ∀ j,vhat j≤vhat ihat) (eps : ℝ) (heps : 0≤eps)
    (herr : ∀ i,|v i-vhat i|≤eps*v i) (j : Fin n) :
    (1-eps)/(1+eps)*v j ≤ v ihat := by
  have hl := (abs_le.mp (herr j)).2
  have hr := (abs_le.mp (herr ihat)).1
  have hpred := hihat j
  have hden : 0 < 1+eps := by linarith
  rw [div_mul_eq_mul_div,div_le_iff₀ hden]
  nlinarith
end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory

def classicalSuccess {n : ℕ} (tau : ℝ) (v : Fin n → ℝ) (istar : Fin n)
    (t : Fin n → ℝ) : Prop :=
  tau < t istar ∧ ∀ j, tau < t j → t j < t istar → ¬ BestSoFar v t j

theorem beats_asymm {n : ℕ} {v : Fin n → ℝ} {i j : Fin n}
    (h : Beats v i j) : ¬ Beats v j i := by
  rintro h'
  rcases h with h | ⟨he,h⟩ <;> rcases h' with h' | ⟨he',h'⟩
  · exact lt_asymm h h'
  · simpa [he'] using h
  · simpa [he] using h'
  · exact lt_asymm h h'

theorem best_star {n : ℕ} {v : Fin n → ℝ} {istar : Fin n}
    (hs : ∀ j, j≠istar → Beats v istar j) (t : Fin n → ℝ) : BestSoFar v t istar := by
  intro j hj
  apply hs j
  intro h
  subst j
  exact lt_irrefl _ hj

theorem secretary_star {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ} {istar : Fin n}
    (hd : Deviates theta v vhat istar) (t : Fin n → ℝ) : SecretaryAt theta v vhat t istar :=
  ⟨istar,le_rfl,hd⟩

theorem star_stops_iff {n : ℕ} {theta tau : ℝ} {v vhat : Fin n → ℝ} {ihat istar : Fin n}
    (hs : ∀ j, j≠istar → Beats v istar j) (hd : Deviates theta v vhat istar)
    (t : Fin n → ℝ) : Stops theta tau v vhat ihat t istar ↔ tau < t istar := by
  simp [Stops,secretary_star hd t,best_star hs t]

theorem classical_implies_hired {n : ℕ} {theta tau : ℝ} {v vhat : Fin n → ℝ}
    {istar : Fin n} (hs : ∀ j,j≠istar → Beats v istar j)
    (hd : Deviates theta v vhat istar) {t : Fin n → ℝ}
    (hc : classicalSuccess tau v istar t) : Hired theta tau v vhat istar t istar := by
  refine ⟨(star_stops_iff hs hd t).mpr hc.1,?_⟩
  intro j hj hstop
  rcases hstop with ⟨_,he⟩ | ⟨_,ht,hb⟩
  · subst j
    exact lt_irrefl _ hj
  · exact hc.2 j ht hj hb

theorem best_before_cutoff {n : ℕ} {tau : ℝ} {v : Fin n → ℝ} {istar k : Fin n}
    {t : Fin n → ℝ} (ht : tau < t istar) (hk : t k ≤ tau)
    (hb : ∀ j,t j < t istar → j≠k → Beats v k j) : classicalSuccess tau v istar t := by
  refine ⟨ht,?_⟩
  intro j hj hjs hbest
  have hkj : t k < t j := lt_of_le_of_lt hk hj
  have hjk : j≠k := by intro h; subst j; exact lt_irrefl _ hkj
  exact beats_asymm (hb j hjs hjk) (hbest k hkj)

theorem no_earlier_after_cutoff {n : ℕ} {tau : ℝ} {v : Fin n → ℝ} {istar : Fin n}
    {t : Fin n → ℝ} (ht : tau < t istar) (hprev : ∀ j,t j < t istar → t j ≤ tau) :
    classicalSuccess tau v istar t :=
  ⟨ht,fun j hj hjs _ => (not_lt_of_ge (hprev j hjs)) hj⟩

theorem bestSoFar_measurable {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    MeasurableSet {t : Fin n → ℝ | BestSoFar v t i} := by
  simp only [BestSoFar,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)).imp
    (MeasurableSet.const (Beats v i j))

theorem classical_measurable {n : ℕ} (tau : ℝ) (v : Fin n → ℝ) (istar : Fin n) :
    MeasurableSet {t : Fin n → ℝ | classicalSuccess tau v istar t} := by
  have hm : MeasurableSet {t : Fin n → ℝ |
      ∀ j,tau < t j → t j < t istar → ¬ BestSoFar v t j} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact (measurableSet_lt measurable_const (measurable_pi_apply j)).imp
      ((measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply istar)).imp
        (bestSoFar_measurable v j).compl)
  exact (measurableSet_lt measurable_const (measurable_pi_apply istar)).inter hm

theorem case_i_of_classical_bound {n : ℕ} {theta tau : ℝ} {v vhat : Fin n → ℝ}
    {istar : Fin n} (hs : ∀ j,j≠istar → Beats v istar j)
    (hd : Deviates theta v vhat istar)
    (hprob : tau * Real.log (1/tau) ≤
      (arrivalLaw n).real {t | classicalSuccess tau v istar t}) :
    tau * Real.log (1/tau) ≤ (arrivalLaw n).real {t | Hired theta tau v vhat istar t istar} := by
  letI := arrival_probability n
  apply hprob.trans
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun t ht => classical_implies_hired hs hd ht)

end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory

theorem classical_one_iff (tau : ℝ) (v : Fin 1 → ℝ) (t : Fin 1 → ℝ) :
    classicalSuccess tau v 0 t ↔ tau < t 0 := by
  simp [classicalSuccess,Fin.forall_fin_one]

theorem one_arrival_after (tau : ℝ) (h0 : 0 ≤ tau) (h1 : tau ≤ 1) :
    (arrivalLaw 1).real {t | tau < t 0} = 1-tau := by
  have hs : {t : Fin 1 → ℝ | tau < t 0} ∩
      Set.univ.pi (fun _ : Fin 1 => Set.Icc (0:ℝ) 1) =
      Set.univ.pi (fun _ : Fin 1 => Set.Ioc tau 1) := by
    ext t
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_univ_pi,Fin.forall_fin_one,
      Set.mem_Icc,Set.mem_Ioc]
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · exact fun h => ⟨h.1,le_trans h0 h.1.le,h.2⟩
  unfold Measure.real arrivalLaw
  rw [Measure.restrict_apply (measurableSet_lt measurable_const (measurable_pi_apply 0)),hs]
  rw [Real.volume_pi_Ioc_toReal (fun _ : Fin 1 => h1)]
  simp

theorem dynkin_scalar_bound (tau : ℝ) (h0 : 0 < tau) :
    tau*Real.log (1/tau) ≤ 1-tau := by
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (one_div_pos.mpr h0)) h0.le
  calc
    tau*Real.log (1/tau) ≤ tau*(1/tau-1) := h
    _ = 1-tau := by field_simp

theorem one_classical_probability (tau : ℝ) (h0 : 0 ≤ tau) (h1 : tau ≤ 1)
    (v : Fin 1 → ℝ) :
    (arrivalLaw 1).real {t | classicalSuccess tau v 0 t} = 1-tau := by
  simp only [classical_one_iff]
  exact one_arrival_after tau h0 h1

theorem one_case_i (theta tau : ℝ) (v vhat : Fin 1 → ℝ)
    (h0 : 0 < tau) (h1 : tau < 1) (hd : Deviates theta v vhat 0) :
    tau*Real.log (1/tau) ≤ (arrivalLaw 1).real {t | Hired theta tau v vhat 0 t 0} := by
  apply case_i_of_classical_bound (istar:=0) (by intro j hj; exact False.elim (hj (Subsingleton.elim _ _))) hd
  rw [one_classical_probability tau h0.le h1.le v]
  exact dynkin_scalar_bound tau h0

theorem one_hired_iff (theta tau : ℝ) (v vhat : Fin 1 → ℝ)
    (hd : Deviates theta v vhat 0) (t : Fin 1 → ℝ) :
    Hired theta tau v vhat 0 t 0 ↔ tau < t 0 := by
  unfold Hired
  rw [star_stops_iff (by intro j hj; exact False.elim (hj (Subsingleton.elim _ _))) hd]
  simp [Fin.forall_fin_one]

theorem one_hire_probability (theta tau : ℝ) (v vhat : Fin 1 → ℝ)
    (hd : Deviates theta v vhat 0) (h0 : 0 ≤ tau) (h1 : tau ≤ 1) :
    (arrivalLaw 1).real {t | Hired theta tau v vhat 0 t 0} = 1-tau := by
  simp only [one_hired_iff theta tau v vhat hd]
  exact one_arrival_after tau h0 h1

end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory
open scoped BigOperators

def successBox {n : ℕ} (tau : ℝ) (istar : Fin n) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun i => Set.Ioc (if i=istar then tau else 0) (if i=istar then 1 else tau))

theorem successBox_measurable {n : ℕ} (tau : ℝ) (istar : Fin n) :
    MeasurableSet (successBox tau istar) := by
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

theorem successBox_subset_cube {n : ℕ} (tau : ℝ) (istar : Fin n)
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) :
    successBox tau istar ⊆ Set.univ.pi (fun _ : Fin n => Set.Icc (0:ℝ) 1) := by
  intro t ht
  simp only [successBox,Set.mem_univ_pi,Set.mem_Ioc] at ht
  simp only [Set.mem_univ_pi,Set.mem_Icc]
  intro i
  by_cases hi : i=istar
  · subst i
    have h := ht istar
    simp only [ite_true] at h
    exact ⟨h0.trans h.1.le,h.2⟩
  · have h := ht i
    simp only [hi,ite_false] at h
    exact ⟨h.1.le,h.2.trans h1⟩

theorem successBox_probability {n : ℕ} (tau : ℝ) (istar : Fin n)
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) :
    (arrivalLaw n).real (successBox tau istar) = (1-tau)*tau^(n-1) := by
  unfold Measure.real arrivalLaw
  rw [Measure.restrict_apply (successBox_measurable tau istar),
    Set.inter_eq_left.mpr (successBox_subset_cube tau istar h0 h1)]
  unfold successBox
  rw [Real.volume_pi_Ioc_toReal (fun i => by split_ifs <;> assumption)]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ istar)]
  have hr : (∏ i ∈ Finset.univ.erase istar,
      ((if i=istar then (1:ℝ) else tau)-(if i=istar then tau else 0))) = tau^(n-1) := by
    calc
      _ = ∏ i ∈ Finset.univ.erase istar, tau := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [Finset.ne_of_mem_erase hi]
      _ = _ := by simp
  rw [hr]
  simp [mul_comm]

theorem successBox_classical {n : ℕ} {tau : ℝ} {v : Fin n → ℝ} {istar : Fin n}
    {t : Fin n → ℝ} (ht : t ∈ successBox tau istar) : classicalSuccess tau v istar t := by
  simp only [successBox,Set.mem_univ_pi,Set.mem_Ioc] at ht
  have hs : tau < t istar := by simpa using (ht istar).1
  apply no_earlier_after_cutoff hs
  intro j hj
  have hn : j≠istar := by intro h; subst j; exact lt_irrefl _ hj
  simpa [hn] using (ht j).2

theorem successBox_hire_lower_bound {n : ℕ} {theta tau : ℝ} {v vhat : Fin n → ℝ}
    {istar : Fin n} (h0 : 0 ≤ tau) (h1 : tau ≤ 1)
    (hs : ∀ j,j≠istar → Beats v istar j) (hd : Deviates theta v vhat istar) :
    (1-tau)*tau^(n-1) ≤ (arrivalLaw n).real {t | Hired theta tau v vhat istar t istar} := by
  letI := arrival_probability n
  rw [← successBox_probability tau istar h0 h1]
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun t ht => classical_implies_hired hs hd (successBox_classical ht))

end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory
open scoped BigOperators

theorem beats_total {n : ℕ} (v : Fin n → ℝ) {i j : Fin n} (hne : i≠j) :
    Beats v i j ∨ Beats v j i := by
  rcases lt_trichotomy (v j) (v i) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_or_gt_of_ne hne with hij | hji
    · exact Or.inl (Or.inr ⟨h,hij⟩)
    · exact Or.inr (Or.inr ⟨h.symm,hji⟩)
  · exact Or.inr (Or.inl h)

def noEarlier {n : ℕ} (tau : ℝ) (istar : Fin n) : Set (Fin n → ℝ) :=
  {t | tau<t istar ∧ ∀ k,k≠istar → t istar≤t k}

def cutoffWinner {n : ℕ} (tau : ℝ) (v : Fin n → ℝ) (istar j : Fin n) : Set (Fin n → ℝ) :=
  {t | j≠istar ∧ tau<t istar ∧ t j≤tau ∧ ∀ k,k≠istar → Beats v k j → t istar≤t k}

theorem noEarlier_success {n : ℕ} {tau : ℝ} {v : Fin n → ℝ} {istar : Fin n}
    {t : Fin n → ℝ} (ht : t ∈ noEarlier tau istar) : classicalSuccess tau v istar t := by
  apply no_earlier_after_cutoff ht.1
  intro j hj
  have hn : j≠istar := by intro h; subst j; exact lt_irrefl _ hj
  exact False.elim (not_lt_of_ge (ht.2 j hn) hj)

theorem cutoffWinner_success {n : ℕ} {tau : ℝ} {v : Fin n → ℝ} {istar j : Fin n}
    {t : Fin n → ℝ} (ht : t ∈ cutoffWinner tau v istar j) : classicalSuccess tau v istar t := by
  apply best_before_cutoff ht.2.1 ht.2.2.1
  intro k hk hkj
  rcases beats_total v hkj with h | h
  · have hks : k≠istar := by intro hh; subst k; exact lt_irrefl _ hk
    exact False.elim (not_lt_of_ge (ht.2.2.2 k hks h) hk)
  · exact h

theorem noEarlier_disjoint_winner {n : ℕ} (tau : ℝ) (v : Fin n → ℝ) (istar j : Fin n) :
    Disjoint (noEarlier tau istar) (cutoffWinner tau v istar j) := by
  apply Set.disjoint_left.mpr
  intro t hn hw
  exact not_lt_of_ge ((hn.2 j hw.1).trans hw.2.2.1) hw.2.1

theorem winner_disjoint {n : ℕ} (tau : ℝ) (v : Fin n → ℝ) (istar : Fin n)
    {j k : Fin n} (hjk : j≠k) :
    Disjoint (cutoffWinner tau v istar j) (cutoffWinner tau v istar k) := by
  apply Set.disjoint_left.mpr
  intro t hj hk
  rcases beats_total v hjk with h | h
  · exact not_lt_of_ge ((hk.2.2.2 j hj.1 h).trans hj.2.2.1) hj.2.1
  · exact not_lt_of_ge ((hj.2.2.2 k hk.1 h).trans hk.2.2.1) hk.2.1

theorem noEarlier_measurable {n : ℕ} (tau : ℝ) (istar : Fin n) :
    MeasurableSet (noEarlier tau istar) := by
  have hm : MeasurableSet {t : Fin n → ℝ | ∀ k,k≠istar → t istar≤t k} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro hk
    exact measurableSet_le (measurable_pi_apply istar) (measurable_pi_apply k)
  exact (measurableSet_lt measurable_const (measurable_pi_apply istar)).inter hm

theorem cutoffWinner_measurable {n : ℕ} (tau : ℝ) (v : Fin n → ℝ) (istar j : Fin n) :
    MeasurableSet (cutoffWinner tau v istar j) := by
  have hm : MeasurableSet {t : Fin n → ℝ | ∀ k,k≠istar → Beats v k j → t istar≤t k} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro hk
    apply MeasurableSet.iInter
    intro hb
    exact measurableSet_le (measurable_pi_apply istar) (measurable_pi_apply k)
  exact (MeasurableSet.const (j≠istar)).inter
    ((measurableSet_lt measurable_const (measurable_pi_apply istar)).inter
      ((measurableSet_le (measurable_pi_apply j) measurable_const).inter hm))

def successCell {n : ℕ} (tau : ℝ) (v : Fin n → ℝ) (istar : Fin n) :
    Option {j : Fin n // j≠istar} → Set (Fin n → ℝ)
  | none => noEarlier tau istar
  | some j => cutoffWinner tau v istar j

theorem cells_measurable {n : ℕ} (tau : ℝ) (v : Fin n → ℝ) (istar : Fin n)
    (i : Option {j : Fin n // j≠istar}) : MeasurableSet (successCell tau v istar i) := by
  cases i with
  | none => exact noEarlier_measurable tau istar
  | some j => exact cutoffWinner_measurable tau v istar j

theorem cells_disjoint {n : ℕ} (tau : ℝ) (v : Fin n → ℝ) (istar : Fin n) :
    Pairwise (fun i j => Disjoint (successCell tau v istar i) (successCell tau v istar j)) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some k => exact noEarlier_disjoint_winner tau v istar k
  | some k =>
    cases j with
    | none => exact (noEarlier_disjoint_winner tau v istar k).symm
    | some l =>
      apply winner_disjoint
      intro h
      exact hij (congrArg some (Subtype.ext h))

theorem cell_success {n : ℕ} {tau : ℝ} {v : Fin n → ℝ} {istar : Fin n}
    {i : Option {j : Fin n // j≠istar}} {t : Fin n → ℝ}
    (ht : t ∈ successCell tau v istar i) : classicalSuccess tau v istar t := by
  cases i with
  | none => exact noEarlier_success ht
  | some j => exact cutoffWinner_success ht

theorem sum_cells_le_hiring {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (istar : Fin n)
    (hs : ∀ j,j≠istar → Beats v istar j) (hd : Deviates theta v vhat istar) :
    (∑ i, (arrivalLaw n).real (successCell tau v istar i)) ≤
      (arrivalLaw n).real {t | Hired theta tau v vhat istar t istar} := by
  letI := arrival_probability n
  rw [← measureReal_iUnion_fintype (cells_disjoint tau v istar) (cells_measurable tau v istar)]
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  intro t ht
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ht
  exact classical_implies_hired hs hd (cell_success hi)

end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred
open MeasureTheory
open scoped BigOperators

def classicalDensity (N : ℕ) (tau t : ℝ) : ℝ :=
  (1-t)^N+tau*∑ k ∈ Finset.range N,(1-t)^k

theorem finite_geom_identity (N : ℕ) (t : ℝ) :
    t*(∑ k ∈ Finset.range N,(1-t)^k)=1-(1-t)^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,pow_succ,mul_add,ih]
    ring

theorem density_identity (N : ℕ) (tau t : ℝ) :
    t*classicalDensity N tau t=tau+(t-tau)*(1-t)^N := by
  unfold classicalDensity
  calc
    _ = t*(1-t)^N+tau*(t*∑ k ∈ Finset.range N,(1-t)^k) := by ring
    _ = _ := by rw [finite_geom_identity]; ring

theorem density_ge_inverse (N : ℕ) (tau t : ℝ) (ht : 0<t) (hlo : tau≤t) (hhi : t≤1) :
    tau/t ≤ classicalDensity N tau t := by
  apply (div_le_iff₀ ht).mpr
  rw [mul_comm,density_identity]
  have h : 0 ≤ (t-tau)*(1-t)^N := mul_nonneg (sub_nonneg.mpr hlo) (pow_nonneg (sub_nonneg.mpr hhi) _)
  linarith

theorem density_continuous (N : ℕ) (tau : ℝ) : Continuous (classicalDensity N tau) := by
  unfold classicalDensity
  fun_prop

theorem integral_inverse_cutoff (tau : ℝ) (h0 : 0<tau) :
    (∫ t in tau..1,tau/t)=tau*Real.log (1/tau) := by
  simp only [div_eq_mul_inv,intervalIntegral.integral_const_mul]
  rw [integral_inv_of_pos h0 zero_lt_one]
  simp only [one_div,one_mul]

theorem integral_density_lower_bound (N : ℕ) (tau : ℝ) (h0 : 0<tau) (h1 : tau≤1) :
    tau*Real.log (1/tau) ≤ ∫ t in tau..1,classicalDensity N tau t := by
  rw [← integral_inverse_cutoff tau h0]
  have hc : ContinuousOn (fun t : ℝ => tau/t) (Set.Icc tau 1) :=
    continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (h0.trans_le ht.1))
  apply intervalIntegral.integral_mono_on h1 (hc.intervalIntegrable_of_Icc h1)
    ((density_continuous N tau).intervalIntegrable tau 1)
  intro t ht
  exact density_ge_inverse N tau t (h0.trans_le ht.1) ht.1 ht.2

theorem one_candidate_density (tau t : ℝ) : classicalDensity 0 tau t=1 := by
  simp [classicalDensity]

theorem upper_endpoint_density (N : ℕ) (tau : ℝ) :
    classicalDensity (N+1) tau 1=tau := by
  by_cases h : N=0
  · subst N; simp [classicalDensity]
  · simp [classicalDensity,Finset.sum_range_succ,h]

theorem case_i_of_cell_integral {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (istar : Fin n)
    (h0 : 0<tau) (h1 : tau≤1)
    (hs : ∀ j,j≠istar → SecretaryPred.LearnedDynkin.Beats v istar j)
    (hd : SecretaryPred.LearnedDynkin.Deviates theta v vhat istar)
    (hcell : (∫ t in tau..1,classicalDensity (n-1) tau t) ≤
      ∑ i,(SecretaryPred.LearnedDynkin.arrivalLaw n).real (successCell tau v istar i)) :
    tau*Real.log (1/tau) ≤ (SecretaryPred.LearnedDynkin.arrivalLaw n).real
      {t | SecretaryPred.LearnedDynkin.Hired theta tau v vhat istar t istar} :=
  (integral_density_lower_bound (n-1) tau h0 h1).trans
    (hcell.trans (sum_cells_le_hiring theta tau v vhat istar hs hd))

end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory
open scoped BigOperators

def winnerBox {n : ℕ} (tau s : ℝ) (j : Fin n) (B : Finset (Fin n)) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun i => Set.Ioc (if i∈B then s else 0) (if i=j then tau else 1))

theorem winnerBox_measurable {n : ℕ} (tau s : ℝ) (j : Fin n) (B : Finset (Fin n)) :
    MeasurableSet (winnerBox tau s j B) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

theorem winnerBox_subset_cube {n : ℕ} (tau s : ℝ) (j : Fin n) (B : Finset (Fin n))
    (h0 : 0 ≤ s) (h1 : tau ≤ 1) :
    winnerBox tau s j B ⊆ Set.univ.pi (fun _ : Fin n => Set.Icc (0:ℝ) 1) := by
  intro t ht
  simp only [winnerBox,Set.mem_univ_pi,Set.mem_Ioc] at ht
  simp only [Set.mem_univ_pi,Set.mem_Icc]
  intro i
  have h := ht i
  constructor
  · by_cases hi : i∈B
    · simp only [hi,ite_true] at h
      exact h0.trans h.1.le
    · simpa only [hi,ite_false] using h.1.le
  · by_cases hi : i=j
    · have hu := h.2
      rw [if_pos hi] at hu
      exact hu.trans h1
    · simpa only [hi,ite_false] using h.2

theorem indicator_power_product {n : ℕ} (B : Finset (Fin n)) (q : ℝ) :
    (∏ i : Fin n,if i∈B then q else 1)=q^B.card := by
  classical
  calc
    _ = ∏ i ∈ B,if i∈B then q else 1 := by
      exact (Finset.prod_subset (Finset.subset_univ B) (fun i hi hn => by simp [hn])).symm
    _ = _ := by simp

theorem winnerBox_probability {n : ℕ} (tau s : ℝ) (j : Fin n) (B : Finset (Fin n))
    (hj : j∉B) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (arrivalLaw n).real (winnerBox tau s j B)=tau*(1-s)^B.card := by
  unfold Measure.real arrivalLaw
  rw [Measure.restrict_apply (winnerBox_measurable tau s j B),
    Set.inter_eq_left.mpr (winnerBox_subset_cube tau s j B hs0 ht1)]
  unfold winnerBox
  have hends (i : Fin n) : (if i∈B then s else 0)  ≤  (if i=j then tau else 1) := by
    by_cases hi : i=j
    · subst i; simp [hj,ht0]
    · by_cases hB : i∈B
      · simpa [hi,hB] using hs1
      · simp [hi,hB]
  rw [Real.volume_pi_Ioc_toReal hends]
  have hf (i : Fin n) : (if i=j then tau else (1:ℝ))-(if i∈B then s else 0) =
      (if i=j then tau else 1)*(if i∈B then 1-s else 1) := by
    by_cases hi : i=j
    · subst i; simp [hj]
    · by_cases hb : i∈B <;> simp [hi,hb]
  simp_rw [hf]
  rw [Finset.prod_mul_distrib,indicator_power_product]
  simp

noncomputable def betterOthers {n : ℕ} (v : Fin n → ℝ) (istar j : Fin n) : Finset (Fin n) :=
  by classical exact Finset.univ.filter (fun k => k≠istar ∧ Beats v k j)

theorem self_not_betterOthers {n : ℕ} (v : Fin n → ℝ) (istar j : Fin n) :
    j∉betterOthers v istar j := by
  classical
  intro h
  have hb : Beats v j j := (Finset.mem_filter.mp h).2.2
  exact beats_asymm hb hb

theorem box_update_winner {n : ℕ} {tau s : ℝ} {v : Fin n → ℝ} {istar j : Fin n}
    (hj : j≠istar) (hs : tau<s) {x : Fin n → ℝ}
    (hx : x ∈ winnerBox tau s j (betterOthers v istar j)) :
    Function.update x istar s ∈ cutoffWinner tau v istar j := by
  have hbox : ∀ k,(if k∈betterOthers v istar j then s else 0)<x k ∧
      x k ≤ (if k=j then tau else 1) := by
    simpa only [winnerBox,Set.mem_univ_pi,Set.mem_Ioc] using hx
  refine ⟨hj,by simpa using hs,?_,?_⟩
  · simpa [Function.update_of_ne hj] using (hbox j).2
  · intro k hks hb
    have hkB : k∈betterOthers v istar j := by simp [betterOthers,hks,hb]
    have h := (hbox k).1
    simp only [hkB,ite_true] at h
    simpa [Function.update_of_ne hks] using h.le

theorem winner_slice_probability {n : ℕ} (tau s : ℝ) (v : Fin n → ℝ) (istar j : Fin n)
    (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (arrivalLaw n).real (winnerBox tau s j (betterOthers v istar j)) =
      tau*(1-s)^(betterOthers v istar j).card :=
  winnerBox_probability tau s j _ (self_not_betterOthers v istar j) ht0 ht1 hs0 hs1

theorem noEarlier_box_probability {n : ℕ} (s : ℝ) (istar : Fin n)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (arrivalLaw n).real (winnerBox 1 s istar (Finset.univ.erase istar))=(1-s)^(n-1) := by
  rw [winnerBox_probability 1 s istar _ (by simp) (by norm_num) (by norm_num) hs0 hs1]
  simp

theorem noEarlier_box_update {n : ℕ} {tau s : ℝ} {istar : Fin n} {x : Fin n → ℝ}
    (hs : tau<s) (hx : x ∈ winnerBox 1 s istar (Finset.univ.erase istar)) :
    Function.update x istar s ∈ noEarlier tau istar := by
  have hbox : ∀ k,(if k∈Finset.univ.erase istar then s else 0)<x k ∧
      x k ≤ (if k=istar then (1:ℝ) else 1) := by
    simpa only [winnerBox,Set.mem_univ_pi,Set.mem_Ioc] using hx
  refine ⟨by simpa using hs,?_⟩
  intro k hks
  have hk : k ∈ Finset.univ.erase istar := by simp [hks]
  have h := (hbox k).1
  simp only [hk,ite_true] at h
  simpa [Function.update_of_ne hks] using h.le

end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory

noncomputable def uniformTime : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)

instance uniformTime_probability : IsProbabilityMeasure uniformTime := by
  constructor
  simp [uniformTime]

theorem arrival_eq_pi (n : ℕ) : arrivalLaw n=Measure.pi (fun _ : Fin n => uniformTime) := by
  unfold arrivalLaw uniformTime
  exact Measure.restrict_pi_pi (fun _ => volume) (fun _ => Set.Icc (0:ℝ) 1)

theorem split_arrival_preserving {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i)
      (arrivalLaw (n+1)) (uniformTime.prod (arrivalLaw n)) := by
  rw [arrival_eq_pi,arrival_eq_pi]
  exact measurePreserving_piFinSuccAbove (fun _ => uniformTime) i

theorem insert_arrival_preserving {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (fun p : ℝ × (Fin n → ℝ) => Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) i p.1 p.2)
      (uniformTime.prod (arrivalLaw n)) (arrivalLaw (n+1)) :=
  MeasurePreserving.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i)
    (split_arrival_preserving i)

theorem measurable_insert {n : ℕ} (i : Fin (n+1)) :
    Measurable (fun p : ℝ × (Fin n → ℝ) => Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) i p.1 p.2) :=
  (insert_arrival_preserving i).measurable

theorem arrival_slice_formula {n : ℕ} (i : Fin (n+1)) (A : Set (Fin (n+1) → ℝ))
    (hA : MeasurableSet A) :
    arrivalLaw (n+1) A = ∫⁻ s,arrivalLaw n {x | Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) i s x ∈ A} ∂uniformTime := by
  letI := arrival_probability n
  rw [← (insert_arrival_preserving i).measure_preimage hA.nullMeasurableSet]
  exact Measure.prod_apply (hA.preimage (measurable_insert i))

theorem measurable_update_fixed {n : ℕ} (i : Fin n) (s : ℝ) :
    Measurable (fun x : Fin n → ℝ => Function.update x i s) := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j=i
  · subst j
    simpa using (measurable_const : Measurable (fun _ : Fin n → ℝ => s))
  · simpa [Function.update_of_ne h] using (measurable_pi_apply j : Measurable (fun x : Fin n → ℝ => x j))

theorem update_section_measure {n : ℕ} (i : Fin (n+1)) (s : ℝ)
    (A : Set (Fin (n+1) → ℝ)) (hA : MeasurableSet A) :
    arrivalLaw (n+1) {x | Function.update x i s ∈ A} =
      arrivalLaw n {x | Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) i s x ∈ A} := by
  change arrivalLaw (n+1) ((fun x => Function.update x i s) ⁻¹' A)=_
  rw [arrival_slice_formula i _ (hA.preimage (measurable_update_fixed i s))]
  simp only [Set.mem_preimage,Fin.update_insertNth]
  simp

theorem arrival_resampling_formula {n : ℕ} (i : Fin (n+1)) (A : Set (Fin (n+1) → ℝ))
    (hA : MeasurableSet A) :
    arrivalLaw (n+1) A =
      ∫⁻ s,arrivalLaw (n+1) {x | Function.update x i s ∈ A} ∂uniformTime := by
  rw [arrival_slice_formula i A hA]
  apply lintegral_congr
  intro s
  exact (update_section_measure i s A hA).symm

theorem measurable_section_measure {n : ℕ} (i : Fin (n+1))
    (A : Set (Fin (n+1) → ℝ)) (hA : MeasurableSet A) :
    Measurable (fun s => arrivalLaw (n+1) {x | Function.update x i s ∈ A}) := by
  letI := arrival_probability n
  simp_rw [update_section_measure i _ A hA]
  exact measurable_measure_prodMk_left (hA.preimage (measurable_insert i))

theorem arrival_resampling_real {n : ℕ} (i : Fin (n+1)) (A : Set (Fin (n+1) → ℝ))
    (hA : MeasurableSet A) :
    (arrivalLaw (n+1)).real A =
      ∫ s,(arrivalLaw (n+1)).real {x | Function.update x i s ∈ A} ∂uniformTime := by
  letI := arrival_probability (n+1)
  unfold Measure.real
  rw [arrival_resampling_formula i A hA]
  exact (integral_toReal (measurable_section_measure i A hA).aemeasurable
    (Filter.Eventually.of_forall (fun _ => measure_lt_top _ _))).symm

theorem integrable_section_real {n : ℕ} (i : Fin (n+1)) (A : Set (Fin (n+1) → ℝ))
    (hA : MeasurableSet A) :
    Integrable (fun s => (arrivalLaw (n+1)).real {x | Function.update x i s ∈ A}) uniformTime := by
  letI := arrival_probability (n+1)
  apply integrable_toReal_of_lintegral_ne_top (measurable_section_measure i A hA).aemeasurable
  rw [← arrival_resampling_formula i A hA]
  exact measure_ne_top _ _

theorem integral_slice_lower {n : ℕ} (i : Fin (n+1)) (A : Set (Fin (n+1) → ℝ))
    (hA : MeasurableSet A) (tau : ℝ) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hbound : ∀ s ∈ Set.Ioc tau 1,
      f s ≤ (arrivalLaw (n+1)).real {x | Function.update x i s ∈ A}) :
    (∫ s in tau..1,f s) ≤ (arrivalLaw (n+1)).real A := by
  let g := fun s => (arrivalLaw (n+1)).real {x | Function.update x i s ∈ A}
  have hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume := integrable_section_real i A hA
  have hsub : Set.Ioc tau 1 ⊆ Set.Icc (0:ℝ) 1 := fun s hs => ⟨ht0.trans hs.1.le,hs.2⟩
  rw [intervalIntegral.integral_of_le ht1,arrival_resampling_real i A hA]
  change (∫ s in Set.Ioc tau 1,f s) ≤ ∫ s in Set.Icc (0:ℝ) 1,g s
  apply (setIntegral_mono_on (hf.intervalIntegrable tau 1).1 (hg.mono_set hsub)
    measurableSet_Ioc hbound).trans
  exact setIntegral_mono_set hg (Filter.Eventually.of_forall (fun s => ENNReal.toReal_nonneg))
    (Filter.Eventually.of_forall hsub)

end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin
open scoped BigOperators

theorem beats_trans {n : ℕ} {v : Fin n → ℝ} {i j k : Fin n}
    (hij : Beats v i j) (hjk : Beats v j k) : Beats v i k := by
  rcases hij with hij | ⟨hij,hij'⟩ <;> rcases hjk with hjk | ⟨hjk,hjk'⟩
  · exact Or.inl (hjk.trans hij)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨hjk.trans hij, hij'.trans hjk'⟩

theorem better_rank_strict {n : ℕ} (v : Fin n → ℝ) (istar : Fin n)
    {j k : Fin n} (hj : j≠istar) (hjk : Beats v j k) :
    (betterOthers v istar j).card < (betterOthers v istar k).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    obtain ⟨hzs,hzj⟩ := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzs,beats_trans hzj hjk⟩
  · intro he
    have hmem : j∈betterOthers v istar k := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj,hjk⟩
    rw [← he] at hmem
    exact self_not_betterOthers v istar j hmem

theorem better_rank_lt {n : ℕ} (v : Fin n → ℝ) (istar j : Fin n) (hj : j≠istar) :
    (betterOthers v istar j).card < n-1 := by
  classical
  have hs : betterOthers v istar j ⊂ Finset.univ.erase istar := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro z hz
      exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hz).2.1,Finset.mem_univ _⟩
    · intro he
      have hm : j∈Finset.univ.erase istar := by simp [hj]
      rw [← he] at hm
      exact self_not_betterOthers v istar j hm
  simpa using Finset.card_lt_card hs

noncomputable def winnerRank {n : ℕ} (v : Fin n → ℝ) (istar : Fin n)
    (j : {j : Fin n // j≠istar}) : Fin (n-1) :=
  ⟨(betterOthers v istar j).card,better_rank_lt v istar j j.property⟩

theorem winnerRank_injective {n : ℕ} (v : Fin n → ℝ) (istar : Fin n) :
    Function.Injective (winnerRank v istar) := by
  intro j k he
  by_contra hne
  have hv : j.val≠k.val := fun h => hne (Subtype.ext h)
  have hcard : (betterOthers v istar j).card=(betterOthers v istar k).card := congrArg Fin.val he
  rcases beats_total v hv with h | h
  · exact (ne_of_lt (better_rank_strict v istar j.property h)) hcard
  · exact (ne_of_lt (better_rank_strict v istar k.property h)) hcard.symm

theorem others_card {n : ℕ} (istar : Fin n) :
    Fintype.card {j : Fin n // j≠istar}=n-1 := by
  simp

theorem winnerRank_bijective {n : ℕ} (v : Fin n → ℝ) (istar : Fin n) :
    Function.Bijective (winnerRank v istar) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨winnerRank_injective v istar,by simp [others_card]⟩

theorem rank_power_sum {n : ℕ} (v : Fin n → ℝ) (istar : Fin n) (q : ℝ) :
    (∑ j : {j : Fin n // j≠istar},q^(betterOthers v istar j).card) =
      ∑ k ∈ Finset.range (n-1),q^k := by
  let e := Equiv.ofBijective (winnerRank v istar) (winnerRank_bijective v istar)
  have he := e.sum_comp (fun k : Fin (n-1) => q^k.val)
  simpa [e,winnerRank,Fin.sum_univ_eq_sum_range] using he

end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory
open scoped BigOperators

theorem winner_integral_lower {n : ℕ} (tau : ℝ) (v : Fin (n+1) → ℝ)
    (istar j : Fin (n+1)) (hj : j≠istar) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) :
    (∫ s in tau..1,tau*(1-s)^(betterOthers v istar j).card) ≤
      (arrivalLaw (n+1)).real (cutoffWinner tau v istar j) := by
  letI := arrival_probability (n+1)
  apply integral_slice_lower istar _ (cutoffWinner_measurable tau v istar j) tau ht0 ht1 _
    (by fun_prop)
  intro s hs
  rw [← winner_slice_probability tau s v istar j ht0 ht1 (ht0.trans hs.1.le) hs.2]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono (fun x hx => box_update_winner hj hs.1 hx)

theorem noEarlier_integral_lower {n : ℕ} (tau : ℝ) (istar : Fin (n+1))
    (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) :
    (∫ s in tau..1,(1-s)^n) ≤ (arrivalLaw (n+1)).real (noEarlier tau istar) := by
  letI := arrival_probability (n+1)
  apply integral_slice_lower istar _ (noEarlier_measurable tau istar) tau ht0 ht1 _ (by fun_prop)
  intro s hs
  have hb := noEarlier_box_probability s istar (ht0.trans hs.1.le) hs.2
  simp only [Nat.add_sub_cancel] at hb
  rw [← hb]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono (fun x hx => noEarlier_box_update hs.1 hx)

end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory
open scoped BigOperators

theorem density_as_cells {n : ℕ} (tau : ℝ) (v : Fin (n+1) → ℝ)
    (istar : Fin (n+1)) (s : ℝ) :
    classicalDensity n tau s = (1-s)^n +
      ∑ j : {j : Fin (n+1) // j≠istar},tau*(1-s)^(betterOthers v istar j).card := by
  rw [← Finset.mul_sum,rank_power_sum]
  simp [classicalDensity]

theorem integral_density_cells {n : ℕ} (tau : ℝ) (v : Fin (n+1) → ℝ)
    (istar : Fin (n+1)) (ht0 : 0≤tau) (ht1 : tau≤1) :
    (∫ s in tau..1,classicalDensity n tau s) ≤
      ∑ i,(arrivalLaw (n+1)).real (successCell tau v istar i) := by
  classical
  simp_rw [density_as_cells tau v istar]
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous (fun s : ℝ => (1-s)^n)).intervalIntegrable tau 1)
    ((by fun_prop : Continuous (fun s : ℝ => ∑ j : {j : Fin (n+1) // j≠istar},
      tau*(1-s)^(betterOthers v istar j).card)).intervalIntegrable tau 1)]
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun (j : {j : Fin (n+1) // j≠istar}) hj =>
    (by fun_prop : Continuous (fun s : ℝ => tau*(1-s)^(betterOthers v istar j).card)).intervalIntegrable tau 1)]
  rw [Fintype.sum_option]
  exact add_le_add (noEarlier_integral_lower tau istar ht0 ht1)
    (Finset.sum_le_sum (fun j hj => winner_integral_lower tau v istar j j.property ht0 ht1))

theorem case_i_complete {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (istar : Fin n)
    (h0 : 0<tau) (h1 : tau≤1) (hs : ∀ j,j≠istar → Beats v istar j)
    (hd : Deviates theta v vhat istar) :
    tau*Real.log (1/tau) ≤ (arrivalLaw n).real {t | Hired theta tau v vhat istar t istar} := by
  cases n with
  | zero => exact Fin.elim0 istar
  | succ n =>
    apply case_i_of_cell_integral theta tau v vhat istar h0 h1 hs hd
    simpa using integral_density_cells tau v istar h0.le h1

end Queelius.SecretaryPred

open SecretaryPred.LearnedDynkin in
theorem case_i_solution (n : ℕ) (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat istar : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hvhat : ∀ i, 0 ≤ vhat i) (hihat : ∀ j, vhat j ≤ vhat ihat)
    (histar : ∀ j, j ≠ istar → Beats v istar j)
    (htheta : 0 ≤ theta) (htau0 : 0 < tau) (htau1 : tau < 1)
    (hcase : ihat = istar) (hstarM : Deviates theta v vhat istar) :
    tau * Real.log (1 / tau) ≤ (arrivalLaw n).real {t | Hired theta tau v vhat ihat t istar} := by
  subst ihat
  exact Queelius.SecretaryPred.case_i_complete theta tau v vhat istar htau0 htau1.le histar hstarM

end

section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory

theorem classical_probability {n : ℕ} (tau : ℝ) (v : Fin n → ℝ) (istar : Fin n)
    (h0 : 0 < tau) (h1 : tau ≤ 1) :
    tau * Real.log (1 / tau) ≤
      (arrivalLaw n).real {t | classicalSuccess tau v istar t} := by
  cases n with
  | zero => exact Fin.elim0 istar
  | succ n =>
    letI := arrival_probability (n+1)
    apply (integral_density_lower_bound n tau h0 h1).trans
    apply (integral_density_cells tau v istar h0.le h1).trans
    rw [← measureReal_iUnion_fintype (cells_disjoint tau v istar) (cells_measurable tau v istar)]
    apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
    intro t ht
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
    exact cell_success hi

theorem prediction_disabled {n : ℕ} {theta tau : ℝ} {v vhat : Fin n → ℝ}
    {ihat : Fin n} (hd : Deviates theta v vhat ihat) (t : Fin n → ℝ) (j : Fin n) :
    Stops theta tau v vhat ihat t j ↔
      SecretaryAt theta v vhat t j ∧ tau < t j ∧ BestSoFar v t j := by
  constructor
  · rintro (⟨hn, rfl⟩ | h)
    · exact False.elim (hn ⟨j, le_rfl, hd⟩)
    · exact h
  · exact Or.inr

theorem classical_hired_deviating_prediction {n : ℕ} {theta tau : ℝ}
    {v vhat : Fin n → ℝ} {ihat istar : Fin n}
    (hs : ∀ j, j ≠ istar → Beats v istar j)
    (hd : Deviates theta v vhat istar) (hhat : Deviates theta v vhat ihat)
    {t : Fin n → ℝ} (hc : classicalSuccess tau v istar t) :
    Hired theta tau v vhat ihat t istar := by
  refine ⟨(star_stops_iff hs hd t).mpr hc.1, ?_⟩
  intro j hj hjstop
  have h := (prediction_disabled hhat t j).mp hjstop
  exact hc.2 j h.2.1 hj h.2.2

theorem case_iii_complete {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ)
    (ihat istar : Fin n) (h0 : 0 < tau) (h1 : tau ≤ 1)
    (hs : ∀ j, j ≠ istar → Beats v istar j)
    (hd : Deviates theta v vhat istar) (hhat : Deviates theta v vhat ihat) :
    tau * Real.log (1 / tau) ≤ (arrivalLaw n).real {t | Hired theta tau v vhat ihat t istar} := by
  letI := arrival_probability n
  apply (classical_probability tau v istar h0 h1).trans
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun _ ht => classical_hired_deviating_prediction hs hd hhat ht)

theorem two_candidate_consistency {n : ℕ} (theta : ℝ) (v vhat : Fin n → ℝ)
    (ihat istar : Fin n) (htheta : 0 ≤ theta) (hpred : vhat istar ≤ vhat ihat)
    (hh : ¬ Deviates theta v vhat ihat) (hs : ¬ Deviates theta v vhat istar) :
    (1-theta)/(1+theta)*v istar ≤ v ihat := by
  have hh' := (abs_le.mp (le_of_not_gt hh)).1
  have hs' := (abs_le.mp (le_of_not_gt hs)).2
  have hden : 0 < 1+theta := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith

end Queelius.SecretaryPred

namespace SecretaryPred.LearnedDynkin
theorem inequality_2 (n : ℕ) (theta : ℝ) (v vhat : Fin n → ℝ) (ihat istar : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hvhat : ∀ i, 0 ≤ vhat i) (hihat : ∀ j, vhat j ≤ vhat ihat)
    (histar : ∀ j, j ≠ istar → Beats v istar j) (htheta : 0 ≤ theta)
    (hhatM : ¬ Deviates theta v vhat ihat) (hstarM : ¬ Deviates theta v vhat istar) :
    (1 - theta) / (1 + theta) * v istar ≤ v ihat :=
  Queelius.SecretaryPred.two_candidate_consistency theta v vhat ihat istar htheta
    (hihat istar) hhatM hstarM
end SecretaryPred.LearnedDynkin

open SecretaryPred.LearnedDynkin in
theorem solution (n : ℕ) (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat istar : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hvhat : ∀ i, 0 ≤ vhat i) (hihat : ∀ j, vhat j ≤ vhat ihat)
    (histar : ∀ j, j ≠ istar → Beats v istar j)
    (htheta : 0 ≤ theta) (htau0 : 0 < tau) (htau1 : tau < 1)
    (hcase : ihat ≠ istar) (hhatM : Deviates theta v vhat ihat)
    (hstarM : Deviates theta v vhat istar) :
    tau * Real.log (1 / tau) ≤ (arrivalLaw n).real {t | Hired theta tau v vhat ihat t istar} :=
  Queelius.SecretaryPred.case_iii_complete theta tau v vhat ihat istar htau0 htau1.le
    histar hstarM hhatM

end

section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory
open scoped BigOperators

def firstBefore {n : ℕ} (D : Finset (Fin n)) (i : Fin n) : Set (Fin n → ℝ) :=
  {t | ∀ j ∈ D, t i < t j}

theorem firstBefore_measurable {n : ℕ} (D : Finset (Fin n)) (i : Fin n) :
    MeasurableSet (firstBefore D i) := by
  simp only [firstBefore, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  exact measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)

theorem uniform_later (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    uniformTime.real (Set.Ioi s) = 1-s := by
  have he : Set.Ioi s ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc s 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,h0.trans h.1.le,h.2⟩⟩
  simp [Measure.real,uniformTime,Measure.restrict_apply,he,Real.volume_Ioc,h1]

theorem firstBefore_section {n : ℕ} (D : Finset (Fin n)) (i : Fin n) (hi : i ∉ D)
    (s : ℝ) :
    {x | Function.update x i s ∈ firstBefore D i} =
      Set.univ.pi (fun j => if j ∈ D then Set.Ioi s else Set.univ) := by
  classical
  ext x
  simp only [firstBefore,Set.mem_ofPred_eq,Function.update_self,Set.mem_univ_pi]
  constructor
  · intro h j
    by_cases hj : j ∈ D
    · have hji : j ≠ i := by rintro rfl; exact hi hj
      simpa [hj,Function.update_of_ne hji] using h j hj
    · simp [hj]
  · intro h j hj
    have hji : j ≠ i := by rintro rfl; exact hi hj
    simpa [hj,Function.update_of_ne hji] using h j

theorem firstBefore_slice_probability {n : ℕ} (D : Finset (Fin n)) (i : Fin n)
    (hi : i ∉ D) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    (arrivalLaw n).real {x | Function.update x i s ∈ firstBefore D i} = (1-s)^D.card := by
  classical
  rw [firstBefore_section D i hi s,arrival_eq_pi]
  unfold Measure.real
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  have hp : (∏ j : Fin n, (uniformTime (if j ∈ D then Set.Ioi s else Set.univ)).toReal) =
      ∏ j : Fin n, if j ∈ D then 1-s else 1 := by
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hd : j ∈ D
    · simpa only [if_pos hd,Measure.real] using uniform_later s h0 h1
    · simp [hd]
  rw [hp]
  simp

theorem integral_one_sub_pow (m : ℕ) :
    (∫ s in (0:ℝ)..1, (1-s)^m) = 1 / ((m:ℝ)+1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^m) 1]
  simp [integral_pow]

theorem firstBefore_probability {n : ℕ} (D : Finset (Fin n)) (i : Fin n) (hi : i ∉ D) :
    (arrivalLaw n).real (firstBefore D i) = 1 / ((D.card:ℝ)+1) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [arrival_resampling_real i _ (firstBefore_measurable D i)]
    have he : (∫ s, (arrivalLaw (n+1)).real {x | Function.update x i s ∈ firstBefore D i} ∂uniformTime) =
        ∫ s in Set.Icc (0:ℝ) 1, (1-s)^D.card := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact firstBefore_slice_probability D i hi s hs.1 hs.2
    rw [he,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact integral_one_sub_pow D.card

theorem firstBefore_hired {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n)
    {t : Fin n → ℝ} (h : t ∈ firstBefore (Mset theta v vhat) ihat) :
    Hired theta tau v vhat ihat t ihat := by
  have hn : ¬ SecretaryAt theta v vhat t ihat := by
    rintro ⟨j,hj,hd⟩
    exact not_lt_of_ge hj (h j (by simp [Mset,hd]))
  refine ⟨Or.inl ⟨hn,rfl⟩,?_⟩
  intro j hj hstop
  rcases hstop with ⟨_,rfl⟩ | ⟨hs,_,_⟩
  · exact lt_irrefl _ hj
  · obtain ⟨k,hk,hd⟩ := hs
    exact hn ⟨k,hk.trans hj.le,hd⟩

theorem prediction_hiring_lower {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ)
    (ihat : Fin n) (hh : ¬ Deviates theta v vhat ihat) :
    1 / (((Mset theta v vhat).card:ℝ)+1) ≤
      (arrivalLaw n).real {t | Hired theta tau v vhat ihat t ihat} := by
  letI := arrival_probability n
  rw [← firstBefore_probability (Mset theta v vhat) ihat (by simpa [Mset] using hh)]
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun _ ht => firstBefore_hired theta tau v vhat ihat ht)

end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory
open scoped BigOperators
open Classical

theorem secretaryAt_measurable {n : ℕ} (theta : ℝ) (v vhat : Fin n → ℝ) (i : Fin n) :
    MeasurableSet {t | SecretaryAt theta v vhat t i} := by
  simp only [SecretaryAt,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  exact (measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i)).inter
    (MeasurableSet.const (Deviates theta v vhat j))

theorem stops_measurable {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat i : Fin n) :
    MeasurableSet {t | Stops theta tau v vhat ihat t i} :=
  ((secretaryAt_measurable theta v vhat i).compl.inter (MeasurableSet.const (i=ihat))).union
    ((secretaryAt_measurable theta v vhat i).inter
      ((measurableSet_lt measurable_const (measurable_pi_apply i)).inter (bestSoFar_measurable v i)))

theorem hired_measurable {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat i : Fin n) :
    MeasurableSet {t | Hired theta tau v vhat ihat t i} := by
  have hm : MeasurableSet {t : Fin n → ℝ | ∀ j, t j < t i → ¬ Stops theta tau v vhat ihat t j} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)).imp
      (stops_measurable theta tau v vhat ihat j).compl
  exact (stops_measurable theta tau v vhat ihat i).inter hm

theorem hired_reward_integrable {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat i : Fin n) :
    Integrable (fun t => if Hired theta tau v vhat ihat t i then v i else 0) (arrivalLaw n) := by
  classical
  letI := arrival_probability n
  have he : (fun t => if Hired theta tau v vhat ihat t i then v i else 0) =
      {t | Hired theta tau v vhat ihat t i}.indicator (fun _ => v i) := by
    funext t
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  rw [he]
  exact (integrable_const (v i) : Integrable (fun _ : Fin n → ℝ => v i) (arrivalLaw n)).indicator
    (hired_measurable theta tau v vhat ihat i)

theorem expected_reward_sum {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n) :
    expectedValue theta tau v vhat ihat =
      ∑ i, (arrivalLaw n).real {t | Hired theta tau v vhat ihat t i} * v i := by
  classical
  unfold expectedValue algValue
  rw [integral_finsetSum _ (fun i _ => hired_reward_integrable theta tau v vhat ihat i)]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Set.indicator,Set.mem_ofPred_eq,smul_eq_mul] using
    integral_indicator_const (μ := arrivalLaw n) (v i) (hired_measurable theta tau v vhat ihat i)

theorem expected_reward_single_lower {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ)
    (ihat i : Fin n) (hv : ∀ j, 0 ≤ v j) :
    (arrivalLaw n).real {t | Hired theta tau v vhat ihat t i} * v i ≤
      expectedValue theta tau v vhat ihat := by
  rw [expected_reward_sum]
  exact Finset.single_le_sum
    (f := fun k => (arrivalLaw n).real {t | Hired theta tau v vhat ihat t k} * v k)
    (fun j _ => mul_nonneg measureReal_nonneg (hv j)) (Finset.mem_univ i)

theorem expected_reward_pair_lower {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ)
    (ihat i j : Fin n) (hij : i ≠ j) (hv : ∀ k, 0 ≤ v k) :
    (arrivalLaw n).real {t | Hired theta tau v vhat ihat t i} * v i +
      (arrivalLaw n).real {t | Hired theta tau v vhat ihat t j} * v j ≤
      expectedValue theta tau v vhat ihat := by
  classical
  rw [expected_reward_sum]
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (s := ({i,j} : Finset (Fin n))) (t := Finset.univ)
    (f := fun k => (arrivalLaw n).real {t | Hired theta tau v vhat ihat t k} * v k)
    (Finset.subset_univ _) (fun k _ _ => mul_nonneg measureReal_nonneg (hv k))
  simpa [hij] using h

theorem prediction_expected_lower {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ)
    (ihat : Fin n) (hv : ∀ j, 0 ≤ v j) (hh : ¬ Deviates theta v vhat ihat) :
    v ihat / (((Mset theta v vhat).card:ℝ)+1) ≤ expectedValue theta tau v vhat ihat := by
  have h := mul_le_mul_of_nonneg_right (prediction_hiring_lower theta tau v vhat ihat hh) (hv ihat)
  calc
    _ ≤ (arrivalLaw n).real {t | Hired theta tau v vhat ihat t ihat} * v ihat := by
      simpa [div_eq_mul_inv,mul_comm] using h
    _ ≤ _ := expected_reward_single_lower theta tau v vhat ihat ihat hv

theorem both_deviate_expected_lower {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ)
    (ihat istar : Fin n) (hv : ∀ j, 0 ≤ v j) (h0 : 0 < tau) (h1 : tau ≤ 1)
    (hs : ∀ j, j ≠ istar → Beats v istar j)
    (hd : Deviates theta v vhat istar) (hhat : Deviates theta v vhat ihat) :
    (tau * Real.log (1/tau)) * v istar ≤ expectedValue theta tau v vhat ihat :=
  (mul_le_mul_of_nonneg_right
    (case_iii_complete theta tau v vhat ihat istar h0 h1 hs hd hhat) (hv istar)).trans
    (expected_reward_single_lower theta tau v vhat ihat istar hv)

/-- The remaining case(vi) obligation is the secretary-mode probability for the true best. -/
theorem case_vi_of_best_probability {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ)
    (ihat istar : Fin n) (hv : ∀ j, 0 ≤ v j) (htheta : 0 ≤ theta)
    (hneq : ihat ≠ istar) (hpred : vhat istar ≤ vhat ihat)
    (hh : ¬ Deviates theta v vhat ihat) (hs : ¬ Deviates theta v vhat istar)
    (q : ℝ) (hq : q ≤ (arrivalLaw n).real {t | Hired theta tau v vhat ihat t istar}) :
    (1 / (((Mset theta v vhat).card:ℝ)+1) * ((1-theta)/(1+theta)) + q) * v istar ≤
      expectedValue theta tau v vhat ihat := by
  have hc := two_candidate_consistency theta v vhat ihat istar htheta hpred hh hs
  have hinv : 0 ≤ 1 / (((Mset theta v vhat).card:ℝ)+1) := by positivity
  have hhiring := prediction_hiring_lower theta tau v vhat ihat hh
  have ha := (mul_le_mul_of_nonneg_left hc hinv).trans
    (mul_le_mul_of_nonneg_right hhiring (hv ihat))
  have hb := mul_le_mul_of_nonneg_right hq (hv istar)
  have hp := expected_reward_pair_lower theta tau v vhat ihat ihat istar hneq hv
  nlinarith

end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred.Controls
open SecretaryPred.LearnedDynkin MeasureTheory

 theorem firstBefore_self_empty {n : ℕ} (D : Finset (Fin n)) (i : Fin n) (hi : i ∈ D) :
    firstBefore D i = ∅ := by
  ext t
  simp only [firstBefore,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
  intro h
  exact lt_irrefl _ (h i hi)

 theorem firstBefore_empty_probability {n : ℕ} (i : Fin n) :
    (arrivalLaw n).real (firstBefore ∅ i) = 1 := by
  simpa using firstBefore_probability ∅ i (by simp)

 theorem one_competitor_probability :
    (arrivalLaw 2).real (firstBefore ({1} : Finset (Fin 2)) 0) = 1/2 := by
  have h := firstBefore_probability ({1} : Finset (Fin 2)) 0 (by decide)
  norm_num at h
  exact h

 theorem equal_arrivals_not_first (t : Fin 2 → ℝ) (ht : t 0 = t 1) :
    t ∉ firstBefore ({1} : Finset (Fin 2)) 0 := by
  intro h
  exact lt_irrefl _ (ht ▸ h 1 (by simp))

 theorem prediction_hired_at_one_iff {n : ℕ} (theta : ℝ) (v vhat : Fin n → ℝ)
    (ihat : Fin n) (t : Fin n → ℝ) (ht : ∀ i,t i ≤ 1) :
    Hired theta 1 v vhat ihat t ihat ↔ t ∈ firstBefore (Mset theta v vhat) ihat := by
  constructor
  · intro hh j hj
    have hd : Deviates theta v vhat j := by simpa [Mset] using hj
    rcases hh.1 with ⟨hn,_⟩ | ⟨_,hbad,_⟩
    · exact lt_of_not_ge (fun hle => hn ⟨j,hle,hd⟩)
    · exact False.elim (not_lt_of_ge (ht ihat) hbad)
  · exact firstBefore_hired theta 1 v vhat ihat

end Queelius.SecretaryPred.Controls

end
