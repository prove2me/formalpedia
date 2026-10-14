-- Prove2me | solution 1 for OnlineStochMatching.TSM.fact_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T06:27:40.338992+00:00
-- url     : https://prove2.me/submissions/6d5aba6e-5058-48a1-88c4-98b579ac908e

import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Model

open MeasureTheory

namespace OnlineStochMatching.TSM

theorem rk_mcd_mgf {Ω : Type*} [MeasurableSpace Ω] (B t : ℝ) : ∀ (m : ℕ)
    (μ : Fin m → Measure Ω), (∀ i, IsProbabilityMeasure (μ i)) → ∀ (c : Fin m → ℝ)
    (f : (Fin m → Ω) → ℝ), Measurable f → (∀ x, |f x| ≤ B) →
    (∀ x i z, |f x - f (Function.update x i z)| ≤ c i) →
    ∫ x, Real.exp (t * (f x - ∫ y, f y ∂(Measure.pi μ))) ∂(Measure.pi μ)
      ≤ Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
  intro m
  induction m with
  | zero =>
    intro μ hμ c f hf hB hbd
    have hcst : ∀ x, f x = f (fun i => i.elim0) := fun x => congrArg f (Subsingleton.elim _ _)
    simp [hcst]
  | succ m ih =>
    intro μ hμ c f hf hB hbd
    set πm : Measure (Fin m → Ω) := Measure.pi fun j => μ j.succ with hπm
    haveI : IsProbabilityMeasure πm := by rw [hπm]; infer_instance
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => Ω) 0 with he
    have hmp : MeasurePreserving e (Measure.pi μ) ((μ 0).prod πm) := by
      have := measurePreserving_piFinSuccAbove μ 0
      have h2 : (fun j : Fin m => μ (Fin.succAbove 0 j)) = fun j => μ j.succ := by
        funext j; simp
      rw [h2] at this
      exact this
    have hes : ∀ p : Ω × (Fin m → Ω), e.symm p = Fin.cons p.1 p.2 := by
      intro p
      simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
    have hint : ∀ φ : (Fin (m+1) → Ω) → ℝ, ∫ x, φ x ∂(Measure.pi μ)
        = ∫ p, φ (Fin.cons p.1 p.2) ∂((μ 0).prod πm) := by
      intro φ
      rw [← hmp.symm.integral_comp' (g := φ)]
      simp only [hes]
    obtain ⟨a0⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure (μ 0)
    have hc : 0 ≤ c 0 := (abs_nonneg _).trans (hbd (fun _ => a0) 0 a0)
    have hgm : Measurable (fun p : Ω × (Fin m → Ω) => f (Fin.cons p.1 p.2)) := by
      have : (fun p : Ω × (Fin m → Ω) => f (Fin.cons p.1 p.2)) = f ∘ e.symm := by
        funext p; simp [hes]
      rw [this]; exact hf.comp e.symm.measurable
    have hgint : Integrable (fun p : Ω × (Fin m → Ω) => f (Fin.cons p.1 p.2)) ((μ 0).prod πm) :=
      Integrable.mono' (integrable_const B) hgm.aestronglyMeasurable
        (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hB _)
    set h : Ω → ℝ := fun a => ∫ y, f (Fin.cons a y) ∂πm with hh
    have hhm : Measurable h := by
      have := StronglyMeasurable.integral_prod_right (ν := πm)
        (f := fun a y => f (Fin.cons a y)) hgm.stronglyMeasurable
      exact this.measurable
    have hhB : ∀ a, |h a| ≤ B := by
      intro a
      have : ‖h a‖ ≤ B := by
        refine (norm_integral_le_of_norm_le_const (C := B) ?_).trans (by simp)
        exact ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hB _
      simpa [Real.norm_eq_abs] using this
    have hslice : ∀ a, Integrable (fun y => f (Fin.cons a y)) πm := by
      intro a
      exact Integrable.mono' (integrable_const B)
        (hgm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hB _)
    have hhd : ∀ a a', h a - h a' ≤ c 0 := by
      intro a a'
      simp only [hh]
      rw [← integral_sub (hslice a) (hslice a')]
      have : ∫ y, (f (Fin.cons a y) - f (Fin.cons a' y)) ∂πm ≤ ∫ _y, c 0 ∂πm := by
        refine integral_mono (by exact (hslice a).sub (hslice a')) (integrable_const (c 0)) ?_
        intro y
        have := hbd (Fin.cons a y) 0 a'
        rw [Fin.update_cons_zero] at this
        exact (le_abs_self _).trans this
      simpa using this
    set E := ∫ y, f y ∂(Measure.pi μ) with hE
    have hE' : E = ∫ a, h a ∂(μ 0) := by
      rw [hE, hint f]
      exact integral_prod _ hgint
    have hK : ∀ a, ∫ y, Real.exp (t * (f (Fin.cons a y) - h a)) ∂πm
        ≤ Real.exp (t ^ 2 * (∑ j : Fin m, c j.succ ^ 2) / 8) := by
      intro a
      refine ih (fun j => μ j.succ) (fun j => hμ _) (fun j => c j.succ)
        (fun y => f (Fin.cons a y)) (hgm.comp (measurable_const.prodMk measurable_id))
        (fun y => hB _) ?_
      intro x i z
      rw [Fin.cons_update]
      exact hbd _ _ _
    set K := Real.exp (t ^ 2 * (∑ j : Fin m, c j.succ ^ 2) / 8) with hKdef
    set lo := sInf (Set.range h) with hlo
    have hbdd : BddBelow (Set.range h) := ⟨-B, by
      rintro _ ⟨a, rfl⟩; have := hhB a; exact (abs_le.mp this).1⟩
    have hIcc : ∀ a, h a - E ∈ Set.Icc (lo - E) (lo + c 0 - E) := by
      intro a
      constructor
      · have : lo ≤ h a := csInf_le hbdd ⟨a, rfl⟩
        linarith
      · have : h a - c 0 ≤ lo := le_csInf ⟨h a0, a0, rfl⟩ (by
          rintro _ ⟨a', rfl⟩; have := hhd a a'; linarith)
        linarith
    have hX0 : ∫ a, (h a - E) ∂(μ 0) = 0 := by
      rw [integral_sub, hE']
      · simp
      · exact Integrable.mono' (integrable_const B) hhm.aestronglyMeasurable
          (ae_of_all _ fun a => by simpa [Real.norm_eq_abs] using hhB a)
      · exact integrable_const _
    have hsg := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hhm.sub measurable_const).aemeasurable (ae_of_all _ hIcc) hX0
    have hmgf := hsg.mgf_le t
    have hcc : (((‖lo + c 0 - E - (lo - E)‖₊ / 2) ^ 2 : NNReal) : ℝ) = c 0 ^ 2 / 4 := by
      have : lo + c 0 - E - (lo - E) = c 0 := by ring
      rw [this]
      push_cast
      rw [Real.norm_eq_abs, abs_of_nonneg hc]; ring
    rw [hcc] at hmgf
    unfold ProbabilityTheory.mgf at hmgf
    rw [hint]
    have hexpint : Integrable (fun p : Ω × (Fin m → Ω) =>
        Real.exp (t * (f (Fin.cons p.1 p.2) - E))) ((μ 0).prod πm) := by
      refine Integrable.mono' (integrable_const (Real.exp (|t| * (B + |E|)))) ?_ ?_
      · exact (Real.measurable_exp.comp ((hgm.sub measurable_const).const_mul t)).aestronglyMeasurable
      · refine ae_of_all _ fun p => ?_
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have h1 := hB (Fin.cons p.1 p.2)
        calc t * (f (Fin.cons p.1 p.2) - E) ≤ |t * (f (Fin.cons p.1 p.2) - E)| := le_abs_self _
          _ = |t| * |f (Fin.cons p.1 p.2) - E| := abs_mul _ _
          _ ≤ |t| * (B + |E|) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact (abs_sub _ _).trans (by linarith)
    rw [integral_prod _ hexpint]
    have hhint : Integrable (fun a => Real.exp (t * (h a - E))) (μ 0) := by
      refine Integrable.mono' (integrable_const (Real.exp (|t| * (B + |E|)))) ?_ ?_
      · exact (Real.measurable_exp.comp ((hhm.sub measurable_const).const_mul t)).aestronglyMeasurable
      · refine ae_of_all _ fun a => ?_
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have h1 := hhB a
        calc t * (h a - E) ≤ |t * (h a - E)| := le_abs_self _
          _ = |t| * |h a - E| := abs_mul _ _
          _ ≤ |t| * (B + |E|) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact (abs_sub _ _).trans (by linarith)
    calc ∫ a, ∫ y, Real.exp (t * (f (Fin.cons (a, y).1 (a, y).2) - E)) ∂πm ∂(μ 0)
        ≤ ∫ a, Real.exp (t * (h a - E)) * K ∂(μ 0) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun a => integral_nonneg fun y =>
            (Real.exp_pos _).le) (hhint.mul_const K) (ae_of_all _ fun a => ?_)
          have heq : ∀ y, Real.exp (t * (f (Fin.cons (a, y).1 (a, y).2) - E))
              = Real.exp (t * (h a - E)) * Real.exp (t * (f (Fin.cons a y) - h a)) := by
            intro y; rw [← Real.exp_add]; ring_nf
          simp only [heq]
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (hK a) (Real.exp_pos _).le
      _ = (∫ a, Real.exp (t * (h a - E)) ∂(μ 0)) * K := integral_mul_const _ _
      _ ≤ Real.exp (c 0 ^ 2 / 4 * t ^ 2 / 2) * K :=
          mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
          rw [hKdef, ← Real.exp_add, Fin.sum_univ_succ]; ring_nf

theorem rk_bdd_diff {Ω : Type*} {m : ℕ} (c : Fin m → ℝ) (f : (Fin m → Ω) → ℝ)
    (hbd : ∀ x i z, |f x - f (Function.update x i z)| ≤ c i) (x y : Fin m → Ω) :
    |f x - f y| ≤ ∑ i, c i := by
  classical
  have key : ∀ s : Finset (Fin m), |f x - f (s.piecewise y x)| ≤ ∑ i ∈ s, c i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.piecewise_insert, Finset.sum_insert hi]
      have := hbd (s.piecewise y x) i (y i)
      calc |f x - f (Function.update (s.piecewise y x) i (y i))|
          ≤ |f x - f (s.piecewise y x)| + |f (s.piecewise y x) - f (Function.update (s.piecewise y x) i (y i))| :=
            abs_sub_le _ _ _
        _ ≤ _ := by linarith
  simpa using key Finset.univ

theorem mcdiarmid_core {A : Type*} [MeasurableSpace A] (n : ℕ)
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) (c : Fin n → ℝ)
    (hc : ∀ (i : Fin n) (x : Fin n → A) (a : A), |f x - f (Function.update x i a)| ≤ c i)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ f x - ∫ y, f y ∂(Measure.pi μ)} ≤
      ENNReal.ofReal (Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2)) := by
  set πn := Measure.pi μ with hπn
  set S := ∑ i, c i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp only [div_zero, Real.exp_zero, ENNReal.ofReal_one]; exact prob_le_one
  obtain ⟨x0⟩ : Nonempty (Fin n → A) := ⟨fun i => (nonempty_of_isProbabilityMeasure (μ i)).some⟩
  set B := |f x0| + ∑ i, c i with hB
  have hBd : ∀ x, |f x| ≤ B := by
    intro x
    have := rk_bdd_diff c f (fun x i z => hc i x z) x x0
    have := abs_sub_abs_le_abs_sub (f x) (f x0)
    linarith
  set E := ∫ y, f y ∂πn with hE
  set s : ℝ := 4 * t / S with hs
  have hs0 : 0 ≤ s := by positivity
  have hmgf := rk_mcd_mgf B s n μ (fun i => inferInstance) c f hf hBd (fun x i z => hc i x z)
  have hint : Integrable (fun x => Real.exp (s * (f x - E))) πn := by
    refine Integrable.mono' (integrable_const (Real.exp (|s| * (B + |E|)))) ?_ ?_
    · exact (Real.measurable_exp.comp ((hf.sub measurable_const).const_mul s)).aestronglyMeasurable
    · refine ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h1 := hBd x
      calc s * (f x - E) ≤ |s * (f x - E)| := le_abs_self _
        _ = |s| * |f x - E| := abs_mul _ _
        _ ≤ |s| * (B + |E|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact (abs_sub _ _).trans (by linarith)
  have hch := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := πn)
    (X := fun x => f x - E) t hs0 hint
  unfold ProbabilityTheory.mgf at hch
  have hfin : Real.exp (-s * t) * Real.exp (s ^ 2 * S / 8) = Real.exp (-2 * t ^ 2 / S) := by
    rw [← Real.exp_add]; congr 1
    rw [hs]; field_simp; ring
  have hreal : πn.real {x | t ≤ f x - E} ≤ Real.exp (-2 * t ^ 2 / S) := by
    refine hch.trans ?_
    rw [← hfin]
    exact mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal

section Fin
open Finset

theorem mcd_count {X : Type} [Fintype X] [Nonempty X] (n : ℕ) (f : (Fin n → X) → ℝ) (c : ℝ)
    (hc : ∀ x i z, |f x - f (Function.update x i z)| ≤ c) (t : ℝ) (ht : 0 < t) :
    ((Finset.univ.filter fun x => t ≤ f x - (∑ y, f y) / (Fintype.card X : ℝ) ^ n).card : ℝ)
      / (Fintype.card X : ℝ) ^ n ≤ Real.exp (-2 * t ^ 2 / (n * c ^ 2)) := by
  classical
  letI : MeasurableSpace X := ⊤
  haveI : MeasurableSingletonClass X := ⟨fun _ => trivial⟩
  set μ : Measure X := (PMF.uniformOfFintype X).toMeasure with hμ
  haveI : IsProbabilityMeasure μ := PMF.toMeasure.isProbabilityMeasure _
  set π : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => μ) with hπ
  have hf : Measurable f := measurable_of_countable f
  have key := mcdiarmid_core n (fun _ => μ) f hf (fun _ => c) (fun i x a => hc x i a) t ht
  set p : ℝ := ((Fintype.card X : ℝ))⁻¹ with hp
  have hsing : ∀ a : X, μ.real {a} = p := by
    intro a
    rw [Measure.real, hμ, PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a),
      PMF.uniformOfFintype_apply]
    simp [hp]
  have hpisingle : ∀ x : Fin n → X, π.real {x} = p ^ n := by
    intro x
    rw [Measure.real, hπ, Measure.pi_singleton]
    rw [ENNReal.toReal_prod]
    have h3 : ∀ a : X, (μ {a}).toReal = p := hsing
    simp [h3]
  have hint : ∫ y, f y ∂π = (∑ y, f y) / (Fintype.card X : ℝ) ^ n := by
    rw [integral_fintype (Integrable.of_finite)]
    simp only [hpisingle, smul_eq_mul]
    rw [← Finset.mul_sum, hp, inv_pow]
    ring
  rw [hint] at key
  set S := Finset.univ.filter fun x => t ≤ f x - (∑ y, f y) / (Fintype.card X : ℝ) ^ n with hS
  have hset : {x | t ≤ f x - (∑ y, f y) / (Fintype.card X : ℝ) ^ n} = (S : Set (Fin n → X)) := by
    ext x; simp [hS]
  rw [hset] at key
  have hm : π.real (S : Set (Fin n → X)) = S.card * p ^ n := by
    rw [Measure.real, ← sum_measure_singleton, ENNReal.toReal_sum]
    · have h4 : ∀ x ∈ S, (π {x}).toReal = p ^ n := fun x _ => hpisingle x
      rw [Finset.sum_congr rfl h4]; simp
    · intro x _; exact measure_ne_top _ _
  have h2 : π.real (S : Set (Fin n → X)) ≤ Real.exp (-2 * t ^ 2 / ∑ i : Fin n, c ^ 2) := by
    rw [Measure.real]
    have := ENNReal.toReal_mono (by simp) key
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  rw [hm] at h2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  rw [hp, inv_pow] at h2
  rw [div_eq_mul_inv]
  exact h2

end Fin

section Balls

lemma q_le (n : ℕ) (hn : 1 ≤ n) : (1 - 1 / (n : ℝ)) ^ n ≤ Real.exp (-1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 1 - 1 / (n : ℝ) ≤ Real.exp (-(1 / (n : ℝ))) := by
    have := Real.add_one_le_exp (-(1 / (n : ℝ)))
    linarith
  have h0 : 0 ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn']; exact_mod_cast hn
    linarith
  calc (1 - 1 / (n : ℝ)) ^ n ≤ (Real.exp (-(1 / (n : ℝ)))) ^ n := pow_le_pow_left₀ h0 h1 n
    _ = Real.exp (-1) := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp

lemma q_ge (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (-1) * (1 - 1 / (n : ℝ)) ≤ (1 - 1 / (n : ℝ)) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  push_cast
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have e1 : 1 - 1 / ((m : ℝ) + 1) = m / (m + 1) := by field_simp; ring
  rw [e1, pow_succ]
  have h0 : 0 ≤ (m : ℝ) / (m + 1) := by positivity
  apply mul_le_mul_of_nonneg_right _ h0
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · simp [Real.exp_le_one_iff]
  · have hmr : (0 : ℝ) < m := by exact_mod_cast hm1
    have h1 : ((m : ℝ) + 1) / m ≤ Real.exp (1 / (m : ℝ)) := by
      have := Real.add_one_le_exp (1 / (m : ℝ))
      calc ((m : ℝ) + 1) / m = 1 / m + 1 := by field_simp; ring
        _ ≤ _ := this
    have h2 : (((m : ℝ) + 1) / m) ^ m ≤ Real.exp 1 := by
      calc (((m : ℝ) + 1) / m) ^ m ≤ (Real.exp (1 / (m : ℝ))) ^ m :=
            pow_le_pow_left₀ (by positivity) h1 m
        _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp
    have h3 : ((m : ℝ) / (m + 1)) ^ m = (((m : ℝ) + 1) / m)⁻¹ ^ m := by
      rw [inv_div]
    rw [h3, inv_pow, Real.exp_neg]
    exact inv_anti₀ (by positivity) h2


lemma empty_card (n : ℕ) (b : Fin n) :
    (Finset.univ.filter fun y : Fin n → Fin n => ∀ t, y t ≠ b).card = (n - 1) ^ n := by
  have : (Finset.univ.filter fun y : Fin n → Fin n => ∀ t, y t ≠ b) =
      Fintype.piFinset (fun _ : Fin n => (Finset.univ.erase b)) := by
    ext y; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]
  simp [Finset.card_erase_of_mem]

lemma cov_sum (n : ℕ) (hn : 1 ≤ n) (B : Finset (Fin n)) :
    (∑ y : Fin n → Fin n, ((B.filter fun b => ∃ t, y t = b).card : ℝ)) =
      B.card * ((n : ℝ) ^ n - ((n : ℝ) - 1) ^ n) := by
  have h1 : ∀ y : Fin n → Fin n, ((B.filter fun b => ∃ t, y t = b).card : ℝ) =
      ∑ b ∈ B, if ∃ t, y t = b then (1 : ℝ) else 0 := by
    intro y
    rw [Finset.card_filter]; push_cast; rfl
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ b : Fin n, (∑ y : Fin n → Fin n, if ∃ t, y t = b then (1 : ℝ) else 0) =
      (n : ℝ) ^ n - ((n : ℝ) - 1) ^ n := by
    intro b
    rw [Finset.sum_boole]
    have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → Fin n)))
      (fun y => ∃ t, y t = b)
    have h4 : (Finset.univ.filter fun y : Fin n → Fin n => ¬ ∃ t, y t = b).card = (n - 1) ^ n := by
      rw [← empty_card n b]
      congr 1; ext y; simp
    rw [h4] at h3
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h3
    have h5 : ((Finset.univ.filter fun y : Fin n → Fin n => ∃ t, y t = b).card : ℝ) + ((n - 1 : ℕ) : ℝ) ^ n
        = (n : ℝ) ^ n := by exact_mod_cast h3
    rw [Nat.cast_sub hn] at h5
    push_cast at h5
    linarith
  simp only [h2]
  simp
  ring

lemma cov_bd (n : ℕ) (B : Finset (Fin n)) (x : Fin n → Fin n) (i : Fin n) (z : Fin n) :
    (B.filter fun b => ∃ t, x t = b).card ≤
      (B.filter fun b => ∃ t, (Function.update x i z) t = b).card + 1 := by
  calc (B.filter fun b => ∃ t, x t = b).card
      ≤ ((B.filter fun b => ∃ t, (Function.update x i z) t = b) ∪ {x i}).card := by
        apply Finset.card_le_card
        intro b hb
        rw [Finset.mem_filter] at hb
        obtain ⟨hbB, t, ht⟩ := hb
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
        by_cases hti : t = i
        · right; rw [← ht, hti]
        · left; exact ⟨hbB, t, by rw [Function.update_of_ne hti]; exact ht⟩
    _ ≤ _ := Finset.card_union_le _ _ |>.trans (by simp)


theorem fact_1_core (n : ℕ) (B : Finset (Fin n)) (ε : ℝ) (hε : 0 < ε) :
    1 - 2 * Real.exp (-(ε ^ 2 * n / 2)) ≤
      prob n (fun balls : Fin n → Fin n =>
        (B.card : ℝ) * (1 - 1 / Real.exp 1) - ε * n ≤
            ((B.filter fun b => ∃ t, balls t = b).card : ℝ) ∧
          ((B.filter fun b => ∃ t, balls t = b).card : ℝ) ≤
            (B.card : ℝ) * (1 - 1 / Real.exp 1 + 1 / (Real.exp 1 * n)) + ε * n) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : 0 ≤ prob 0 (fun balls : Fin 0 → Fin 0 =>
        (B.card : ℝ) * (1 - 1 / Real.exp 1) - ε * (0 : ℕ) ≤
            ((B.filter fun b => ∃ t, balls t = b).card : ℝ) ∧
          ((B.filter fun b => ∃ t, balls t = b).card : ℝ) ≤
            (B.card : ℝ) * (1 - 1 / Real.exp 1 + 1 / (Real.exp 1 * (0 : ℕ))) + ε * (0 : ℕ)) := by
      unfold prob; positivity
    have h2 : (1 : ℝ) - 2 * Real.exp (-(ε ^ 2 * ((0 : ℕ) : ℝ) / 2)) ≤ 0 := by norm_num
    exact h2.trans this
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < (n : ℝ) ^ n := by positivity
  set f : (Fin n → Fin n) → ℝ := fun x => ((B.filter fun b => ∃ t, x t = b).card : ℝ) with hf
  set E : ℝ := (∑ y, f y) / (n : ℝ) ^ n with hE
  have hq : (1 - 1 / (n : ℝ)) ^ n = ((n : ℝ) - 1) ^ n / (n : ℝ) ^ n := by
    rw [← div_pow]; congr 1; field_simp
  have hEval : E = B.card * (1 - (1 - 1 / (n : ℝ)) ^ n) := by
    rw [hE]; simp only [hf]; rw [cov_sum n hn B, hq]
    field_simp
  have hexp : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg]; simp
  have hlo : (B.card : ℝ) * (1 - 1 / Real.exp 1) ≤ E := by
    rw [hEval, ← hexp]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    linarith [q_le n hn]
  have hhi : E ≤ (B.card : ℝ) * (1 - 1 / Real.exp 1 + 1 / (Real.exp 1 * n)) := by
    rw [hEval]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have := q_ge n hn
    have e2 : 1 / (Real.exp 1 * n) = Real.exp (-1) * (1 / n) := by
      rw [hexp]; field_simp
    rw [e2, ← hexp]
    nlinarith [this]
  have hbd : ∀ x i z, |f x - f (Function.update x i z)| ≤ 1 := by
    intro x i z
    have a1 := cov_bd n B x i z
    have a2 := cov_bd n B (Function.update x i z) i (x i)
    rw [Function.update_idem, Function.update_eq_self] at a2
    have a1' : f x ≤ f (Function.update x i z) + 1 := by simp only [hf]; exact_mod_cast a1
    have a2' : f (Function.update x i z) ≤ f x + 1 := by simp only [hf]; exact_mod_cast a2
    rw [abs_le]; constructor <;> linarith
  have hbd' : ∀ x i z, |(fun x => - f x) x - (fun x => - f x) (Function.update x i z)| ≤ 1 := by
    intro x i z
    have := hbd x i z
    simp only
    rw [show -f x - -f (Function.update x i z) = -(f x - f (Function.update x i z)) by ring, abs_neg]
    exact this
  have ht : 0 < ε * n := by positivity
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have up := mcd_count (X := Fin n) n f 1 hbd (ε * n) ht
  have lo := mcd_count (X := Fin n) n (fun x => - f x) 1 hbd' (ε * n) ht
  simp only [Fintype.card_fin] at up lo
  rw [Finset.sum_neg_distrib, neg_div] at lo
  have hexpo : Real.exp (-2 * (ε * n) ^ 2 / (n * 1 ^ 2)) = Real.exp (-(2 * ε ^ 2 * n)) := by
    congr 1; field_simp
  rw [hexpo] at up lo
  rw [← hE] at up lo
  -- the three sets
  set U := Finset.univ.filter (fun x => ε * n ≤ f x - E) with hU
  set L := Finset.univ.filter (fun x => ε * n ≤ -f x - -E) with hL
  set G := Finset.univ.filter (fun x : Fin n → Fin n => (B.card : ℝ) * (1 - 1 / Real.exp 1) - ε * n ≤ f x ∧
      f x ≤ (B.card : ℝ) * (1 - 1 / Real.exp 1 + 1 / (Real.exp 1 * n)) + ε * n) with hG
  have hcover : (Finset.univ : Finset (Fin n → Fin n)) ⊆ G ∪ U ∪ L := by
    intro x _
    simp only [Finset.mem_union, hG, hU, hL, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h1 : (B.card : ℝ) * (1 - 1 / Real.exp 1) - ε * n ≤ f x
    · by_cases h2 : f x ≤ (B.card : ℝ) * (1 - 1 / Real.exp 1 + 1 / (Real.exp 1 * n)) + ε * n
      · left; left; exact ⟨h1, h2⟩
      · left; right; linarith
    · right; linarith
  have hcardN : ((Finset.univ : Finset (Fin n → Fin n)).card : ℝ) = (n : ℝ) ^ n := by simp
  have hle : (n : ℝ) ^ n ≤ G.card + U.card + L.card := by
    rw [← hcardN]
    have := (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    exact_mod_cast this
  have hUl : (U.card : ℝ) ≤ (n : ℝ) ^ n * Real.exp (-(2 * ε ^ 2 * n)) := by
    have := (div_le_iff₀ hN).1 up
    linarith
  have hLl : (L.card : ℝ) ≤ (n : ℝ) ^ n * Real.exp (-(2 * ε ^ 2 * n)) := by
    have := (div_le_iff₀ hN).1 lo
    linarith
  have hexp2 : Real.exp (-(2 * ε ^ 2 * n)) ≤ Real.exp (-(ε ^ 2 * n / 2)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ ε ^ 2 * n := by positivity
    linarith
  have hprob : prob n (fun balls : Fin n → Fin n =>
        (B.card : ℝ) * (1 - 1 / Real.exp 1) - ε * n ≤
            ((B.filter fun b => ∃ t, balls t = b).card : ℝ) ∧
          ((B.filter fun b => ∃ t, balls t = b).card : ℝ) ≤
            (B.card : ℝ) * (1 - 1 / Real.exp 1 + 1 / (Real.exp 1 * n)) + ε * n) = G.card / (n : ℝ) ^ n := by
    unfold prob
    simp only [Fintype.card_fin]
    congr 3
    ext x; simp [hG, hf]
  rw [hprob, le_div_iff₀ hN]
  have h3 : (n : ℝ) ^ n * Real.exp (-(ε ^ 2 * n / 2)) ≥ (n : ℝ) ^ n * Real.exp (-(2 * ε ^ 2 * n)) :=
    mul_le_mul_of_nonneg_left hexp2 hN.le
  nlinarith

end Balls

section Fact2
open Finset

def Unsat {n c : ℕ} (Ba : Fin c → Fin n) (R : Finset (Fin c)) (x : Fin n → Fin n) : Prop :=
  (∀ j, j ∉ R → ∀ t, x t ≠ Ba j) ∧ (∀ j ∈ R, ∀ t t', x t = Ba j → x t' = Ba j → t = t')

open Classical in
lemma unsat_count {n c : ℕ} (Ba : Fin c → Fin n) (hB : Function.Injective Ba)
    (R : Finset (Fin c)) (hcn : c ≤ n) :
    (Finset.univ.filter fun x : Fin n → Fin n => Unsat Ba R x).card ≤
      ∑ R' ∈ R.powerset, n ^ R'.card * (n - c) ^ (n - R'.card) := by
  classical
  let T : (R' : Finset (Fin c)) → (↥R' → Fin n) → Fin n → Finset (Fin n) := fun R' ψ t =>
    Finset.univ.filter fun b => (∀ j : ↥R', ψ j = t → b = Ba j) ∧
      ((∀ j : ↥R', ψ j ≠ t) → ∀ j : Fin c, b ≠ Ba j)
  let Box : (R' : Finset (Fin c)) → (↥R' → Fin n) → Finset (Fin n → Fin n) := fun R' ψ =>
    Fintype.piFinset (T R' ψ)
  have hsub : (Finset.univ.filter fun x : Fin n → Fin n => Unsat Ba R x) ⊆
      R.powerset.biUnion (fun R' => (Finset.univ : Finset (↥R' → Fin n)).biUnion (fun ψ => Box R' ψ)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨_, hu1, hu2⟩ := hx
    rw [Finset.mem_biUnion]
    refine ⟨R.filter (fun j => ∃ t, x t = Ba j), Finset.mem_powerset.2 (Finset.filter_subset _ _), ?_⟩
    rw [Finset.mem_biUnion]
    have hex : ∀ j : ↥(R.filter (fun j => ∃ t, x t = Ba j)), ∃ t, x t = Ba j := fun j =>
      (Finset.mem_filter.1 j.2).2
    refine ⟨fun j => Classical.choose (hex j), Finset.mem_univ _, ?_⟩
    rw [Fintype.mem_piFinset]
    intro t
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro j hj
      rw [← hj]; exact Classical.choose_spec (hex j)
    · intro hall j hxt
      by_cases hjR : j ∈ R
      · have hj' : j ∈ R.filter (fun j => ∃ t, x t = Ba j) :=
          Finset.mem_filter.2 ⟨hjR, t, hxt⟩
        have := hu2 j hjR t _ hxt (Classical.choose_spec (hex ⟨j, hj'⟩))
        exact hall ⟨j, hj'⟩ this.symm
      · exact hu1 j hjR t hxt
  have hbox : ∀ (R' : Finset (Fin c)) (ψ : ↥R' → Fin n), (Box R' ψ).card ≤ (n - c) ^ (n - R'.card) := by
    intro R' ψ
    simp only [Box]
    rw [Fintype.card_piFinset]
    by_cases hinj : Function.Injective ψ
    · have h1 : ∀ t, (T R' ψ t).card ≤ if (∃ j : ↥R', ψ j = t) then 1 else n - c := by
        intro t
        split_ifs with h
        · obtain ⟨j, hj⟩ := h
          calc (T R' ψ t).card ≤ ({Ba j} : Finset (Fin n)).card := by
                apply Finset.card_le_card
                intro b hb
                simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hb
                rw [Finset.mem_singleton]; exact hb.1 j hj
            _ = 1 := by simp
        · push_neg at h
          have : T R' ψ t = Finset.univ \ Finset.univ.image Ba := by
            ext b
            simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
              Finset.mem_image, not_exists]
            constructor
            · intro hb j h'; exact hb.2 h j h'.symm
            · intro hb; exact ⟨fun j hj => (h j hj).elim, fun _ j h' => hb j h'.symm⟩
          rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
            Finset.card_image_of_injective _ hB]
          simp
      calc ∏ t, (T R' ψ t).card ≤ ∏ t : Fin n, (if (∃ j : ↥R', ψ j = t) then 1 else n - c) :=
            Finset.prod_le_prod' (fun t _ => h1 t)
        _ = (n - c) ^ (n - R'.card) := by
            rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
            congr 1
            have h2 : (Finset.univ.filter fun t : Fin n => (∃ j : ↥R', ψ j = t)) =
                Finset.univ.image ψ := by
              ext t; simp
            have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
              (fun t : Fin n => (∃ j : ↥R', ψ j = t))
            rw [h2, Finset.card_image_of_injective _ hinj] at h3
            simp only [Finset.card_univ, Fintype.card_coe, Fintype.card_fin] at h3
            omega
    · rw [Function.Injective] at hinj
      push_neg at hinj
      obtain ⟨j, j', hjj, hne⟩ := hinj
      have : T R' ψ (ψ j) = ∅ := by
        ext b
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨h1, _⟩
        have a1 := h1 j rfl
        have a2 := h1 j' hjj.symm
        exact hne (Subtype.ext (hB (a1.symm.trans a2)))
      rw [Finset.prod_eq_zero (Finset.mem_univ (ψ j)) (by rw [this]; simp)]
      exact Nat.zero_le _
  calc _ ≤ (R.powerset.biUnion (fun R' => (Finset.univ : Finset (↥R' → Fin n)).biUnion
          (fun ψ => Box R' ψ))).card := Finset.card_le_card hsub
    _ ≤ ∑ R' ∈ R.powerset, ((Finset.univ : Finset (↥R' → Fin n)).biUnion (fun ψ => Box R' ψ)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ R' ∈ R.powerset, ∑ ψ : (↥R' → Fin n), (Box R' ψ).card :=
        Finset.sum_le_sum (fun R' _ => Finset.card_biUnion_le)
    _ ≤ ∑ R' ∈ R.powerset, ∑ ψ : (↥R' → Fin n), (n - c) ^ (n - R'.card) :=
        Finset.sum_le_sum (fun R' _ => Finset.sum_le_sum (fun ψ _ => hbox R' ψ))
    _ = ∑ R' ∈ R.powerset, n ^ R'.card * (n - c) ^ (n - R'.card) := by
        apply Finset.sum_congr rfl
        intro R' _
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, smul_eq_mul]

end Fact2


section Fact2b

lemma q_pow_bound (n c : ℕ) (hc : c ^ 2 < n) :
    (1 - (c : ℝ) / n) ^ (n - c) ≤ Real.exp (-(c : ℝ)) * ((n : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hc)
  have hc2 : ((c : ℝ)) ^ 2 < n := by exact_mod_cast hc
  have hcn : c ≤ n := by nlinarith [Nat.zero_le c, Nat.le_self_pow (two_ne_zero) c]
  have hcn' : (c : ℝ) ≤ n := by exact_mod_cast hcn
  set q : ℝ := 1 - (c : ℝ) / n with hq
  have hq0 : 0 ≤ q := by
    rw [hq, sub_nonneg, div_le_one hn]; exact hcn'
  have hq1 : q ≤ 1 := by
    rw [hq]; have : 0 ≤ (c : ℝ) / n := by positivity
    linarith
  have h1 : q ^ n ≤ Real.exp (-(c : ℝ)) := by
    have h : q ≤ Real.exp (-((c : ℝ) / n)) := by
      have := Real.add_one_le_exp (-((c : ℝ) / n)); rw [hq]; linarith
    calc q ^ n ≤ (Real.exp (-((c : ℝ) / n))) ^ n := pow_le_pow_left₀ hq0 h n
      _ = Real.exp (-(c : ℝ)) := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h2 : 1 - (c : ℝ) ^ 2 / n ≤ q ^ c := by
    have := one_add_mul_le_pow (a := -((c : ℝ) / n)) (by
      have : (c : ℝ) / n ≤ 1 := by rw [div_le_one hn]; exact hcn'
      have : 0 ≤ (c : ℝ) / n := by positivity
      linarith) c
    have e : 1 + (c : ℝ) * -((c : ℝ) / n) = 1 - (c : ℝ) ^ 2 / n := by ring
    rw [e] at this
    have e2 : 1 + -((c : ℝ) / n) = q := by rw [hq]; ring
    rw [e2] at this
    exact this
  have h3 : 0 < 1 - (c : ℝ) ^ 2 / n := by
    have : (c : ℝ) ^ 2 / n < 1 := by rw [div_lt_one hn]; exact hc2
    linarith
  have h4 : q ^ (n - c) * (1 - (c : ℝ) ^ 2 / n) ≤ Real.exp (-(c : ℝ)) := by
    calc q ^ (n - c) * (1 - (c : ℝ) ^ 2 / n) ≤ q ^ (n - c) * q ^ c :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hq0 _)
      _ = q ^ n := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := h1
  have e3 : (n : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2) = (1 - (c : ℝ) ^ 2 / n)⁻¹ := by
    field_simp
  rw [e3, ← div_eq_mul_inv, le_div_iff₀ h3]
  exact h4

lemma sat_bound (n c s : ℕ) (hc : c ^ 2 < n) (hs : s ≤ c) :
    (n : ℝ) ^ s * (((n - c : ℕ) : ℝ)) ^ (n - s) ≤
      (n : ℝ) ^ n * (Real.exp (-(c : ℝ)) * ((n : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2))) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hc)
  have hcn : c ≤ n := by nlinarith [Nat.zero_le c, Nat.le_self_pow (two_ne_zero) c]
  have hcn' : (c : ℝ) ≤ n := by exact_mod_cast hcn
  have hsn : s ≤ n := hs.trans hcn
  set q : ℝ := 1 - (c : ℝ) / n with hq
  have hq0 : 0 ≤ q := by
    rw [hq, sub_nonneg, div_le_one hn]; exact hcn'
  have hq1 : q ≤ 1 := by
    rw [hq]; have : 0 ≤ (c : ℝ) / n := by positivity
    linarith
  have e1 : ((n - c : ℕ) : ℝ) = n * q := by
    rw [Nat.cast_sub hcn, hq]; field_simp
  have e2 : (n : ℝ) ^ s * (((n - c : ℕ) : ℝ)) ^ (n - s) = (n : ℝ) ^ n * q ^ (n - s) := by
    rw [e1, mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hsn]
  rw [e2]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc q ^ (n - s) ≤ q ^ (n - c) := pow_le_pow_of_le_one hq0 hq1 (by omega)
    _ ≤ _ := q_pow_bound n c hc

end Fact2b


section Fact2c
open Finset

/-- satisfied predicate -/
def Sat {n c : ℕ} (Ba : Fin c → Fin n) (R : Finset (Fin c)) (x : Fin n → Fin n) : Prop :=
  (∃ j, j ∉ R ∧ 1 ≤ (Finset.univ.filter fun t => x t = Ba j).card) ∨
    (∃ j, j ∈ R ∧ 2 ≤ (Finset.univ.filter fun t => x t = Ba j).card)

lemma not_sat_iff {n c : ℕ} (Ba : Fin c → Fin n) (R : Finset (Fin c)) (x : Fin n → Fin n) :
    ¬ Sat Ba R x ↔ Unsat Ba R x := by
  unfold Sat Unsat
  push_neg
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j hj t ht => ?_, fun j hj t t' ht ht' => ?_⟩
    · have := h1 j hj
      have h0 : (Finset.univ.filter fun t => x t = Ba j).card = 0 := by omega
      rw [Finset.card_eq_zero] at h0
      have : t ∈ (Finset.univ.filter fun t => x t = Ba j) := by simp [ht]
      rw [h0] at this; simp at this
    · have := h2 j hj
      have h1' : (Finset.univ.filter fun t => x t = Ba j).card ≤ 1 := by omega
      rw [Finset.card_le_one] at h1'
      exact h1' t (by simp [ht]) t' (by simp [ht'])
  · rintro ⟨h1, h2⟩
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have : (Finset.univ.filter fun t => x t = Ba j) = ∅ := by
        ext t; simp [h1 j hj t]
      rw [this]; simp
    · have : (Finset.univ.filter fun t => x t = Ba j).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro t ht t' ht'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
        exact h2 j hj t t' ht ht'
      omega

lemma sat_mono {n c : ℕ} (Ba : Fin c → Fin n) (R : Finset (Fin c)) (x : Fin n → Fin n)
    (i z : Fin n) (h : ∀ j, Ba j ≠ x i) (hs : Sat Ba R x) : Sat Ba R (Function.update x i z) := by
  have key : ∀ j, (Finset.univ.filter fun t => x t = Ba j) ⊆
      (Finset.univ.filter fun t => (Function.update x i z) t = Ba j) := by
    intro j t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    have hti : t ≠ i := by
      rintro rfl; exact h j ht.symm
    rw [Function.update_of_ne hti]; exact ht
  rcases hs with ⟨j, hj, hc⟩ | ⟨j, hj, hc⟩
  · exact Or.inl ⟨j, hj, hc.trans (Finset.card_le_card (key j))⟩
  · exact Or.inr ⟨j, hj, hc.trans (Finset.card_le_card (key j))⟩

end Fact2c


section Fact2d
open Finset

theorem fact_2_core (n c ℓ d : ℕ) (hcn : c ^ 2 < n) (B : Fin ℓ → Fin c → Fin n)
    (hB : ∀ a, Function.Injective (B a))
    (hd : ∀ b : Fin n, (Finset.univ.filter fun a : Fin ℓ => ∃ j, B a j = b).card ≤ d)
    (R : Finset (Fin c)) (ε : ℝ) (hε : 0 < ε) :
    1 - 2 * Real.exp (-(ε ^ 2 * n / 2)) ≤
      prob n (fun balls : Fin n → Fin n =>
        (ℓ : ℝ) * (1 - 2 ^ R.card / Real.exp 1 ^ c) - ε * d * n
            - (2 ^ R.card * (c : ℝ) ^ 2 / Real.exp 1 ^ c) * ((ℓ : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2)) ≤
          ((Finset.univ.filter fun a : Fin ℓ =>
              (∃ j, j ∉ R ∧ 1 ≤ (Finset.univ.filter fun t => balls t = B a j).card) ∨
              (∃ j, j ∈ R ∧ 2 ≤ (Finset.univ.filter fun t => balls t = B a j).card)).card : ℝ)) := by
  classical
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hcn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < (n : ℝ) ^ n := by positivity
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcn2 : c ≤ n := by nlinarith [Nat.zero_le c, Nat.le_self_pow (two_ne_zero) c]
  have hc2 : (c : ℝ) ^ 2 < n := by exact_mod_cast hcn
  have hpos : (0 : ℝ) < (n : ℝ) - (c : ℝ) ^ 2 := by linarith
  set f : (Fin n → Fin n) → ℝ :=
    fun x => ((Finset.univ.filter fun a : Fin ℓ => Sat (B a) R x).card : ℝ) with hf
  have hfx : ∀ x : Fin n → Fin n, ((Finset.univ.filter fun a : Fin ℓ =>
              (∃ j, j ∉ R ∧ 1 ≤ (Finset.univ.filter fun t => x t = B a j).card) ∨
              (∃ j, j ∈ R ∧ 2 ≤ (Finset.univ.filter fun t => x t = B a j).card)).card : ℝ) = f x := by
    intro x; simp only [hf, Sat]; congr 2; ext a; simp
  set LB0 : ℝ := (ℓ : ℝ) * (1 - 2 ^ R.card / Real.exp 1 ^ c)
    - (2 ^ R.card * (c : ℝ) ^ 2 / Real.exp 1 ^ c) * ((ℓ : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2)) with hLB0
  set K : ℝ := Real.exp (-(c : ℝ)) * ((n : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2)) with hK
  have hLBK : LB0 = (ℓ : ℝ) * (1 - 2 ^ R.card * K) := by
    have h1 : Real.exp 1 ^ c = Real.exp c := by rw [← Real.exp_nat_mul]; simp
    rw [hLB0, hK, h1, Real.exp_neg]
    field_simp
    ring
  -- expectation
  have hcount : ∀ a : Fin ℓ, ((Finset.univ.filter fun x : Fin n → Fin n => Sat (B a) R x).card : ℝ) ≥
      (n : ℝ) ^ n - 2 ^ R.card * ((n : ℝ) ^ n * K) := by
    intro a
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → Fin n)))
      (fun x => Sat (B a) R x)
    have h2 : (Finset.univ.filter fun x : Fin n → Fin n => ¬ Sat (B a) R x) =
        Finset.univ.filter fun x : Fin n → Fin n => Unsat (B a) R x := by
      ext x; simp [not_sat_iff]
    rw [h2] at h1
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h1
    have h3 := unsat_count (B a) (hB a) R hcn2
    have h4 : ((Finset.univ.filter fun x : Fin n → Fin n => Unsat (B a) R x).card : ℝ) ≤
        2 ^ R.card * ((n : ℝ) ^ n * K) := by
      have h5 : ((∑ R' ∈ R.powerset, n ^ R'.card * (n - c) ^ (n - R'.card) : ℕ) : ℝ) ≤
          ∑ R' ∈ R.powerset, ((n : ℝ) ^ n * K) := by
        push_cast
        apply Finset.sum_le_sum
        intro R' hR'
        have hs : R'.card ≤ c := by
          calc R'.card ≤ R.card := Finset.card_le_card (Finset.mem_powerset.1 hR')
            _ ≤ c := by simpa using Finset.card_le_univ R
        exact sat_bound n c R'.card hcn hs
      calc _ ≤ ((∑ R' ∈ R.powerset, n ^ R'.card * (n - c) ^ (n - R'.card) : ℕ) : ℝ) := by
            exact_mod_cast h3
        _ ≤ _ := h5
        _ = _ := by rw [Finset.sum_const, Finset.card_powerset]; simp
    have h6 : ((Finset.univ.filter fun x : Fin n → Fin n => Sat (B a) R x).card : ℝ) +
        ((Finset.univ.filter fun x : Fin n → Fin n => Unsat (B a) R x).card : ℝ) = (n : ℝ) ^ n := by
      exact_mod_cast h1
    linarith
  have hsum : ∑ x, f x = ∑ a : Fin ℓ,
      ((Finset.univ.filter fun x : Fin n → Fin n => Sat (B a) R x).card : ℝ) := by
    simp only [hf, Finset.card_filter]
    push_cast
    exact Finset.sum_comm
  set E : ℝ := (∑ y, f y) / (n : ℝ) ^ n with hE
  have hEge : LB0 ≤ E := by
    rw [hE, le_div_iff₀ hN, hsum, hLBK]
    calc (ℓ : ℝ) * (1 - 2 ^ R.card * K) * (n : ℝ) ^ n
        = ∑ a : Fin ℓ, ((n : ℝ) ^ n - 2 ^ R.card * ((n : ℝ) ^ n * K)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun a _ => hcount a)
  -- bounded differences
  have hS : ∀ x i z, f x ≤ f (Function.update x i z) + d := by
    intro x i z
    have hsub : (Finset.univ.filter fun a : Fin ℓ => Sat (B a) R x) ⊆
        (Finset.univ.filter fun a : Fin ℓ => Sat (B a) R (Function.update x i z)) ∪
        (Finset.univ.filter fun a : Fin ℓ => ∃ j, B a j = x i) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at ha ⊢
      by_cases h : ∃ j, B a j = x i
      · right; exact h
      · left; push_neg at h; exact sat_mono (B a) R x i z h ha
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 := hd (x i)
    simp only [hf]
    exact_mod_cast this.trans (Nat.add_le_add_left h2 _)
  have hbd : ∀ x i z, |(fun x => -f x) x - (fun x => -f x) (Function.update x i z)| ≤ d := by
    intro x i z
    have a1 := hS x i z
    have a2 := hS (Function.update x i z) i (x i)
    rw [Function.update_idem, Function.update_eq_self] at a2
    simp only
    rw [abs_le]; constructor <;> linarith
  by_cases hd0 : d = 0
  · -- degenerate case
    have hLB : LB0 ≤ 0 := by
      subst hd0
      have hlc : ℓ = 0 ∨ c = 0 := by
        by_contra hh
        push_neg at hh
        have hl : 0 < ℓ := Nat.pos_of_ne_zero hh.1
        have hc : 0 < c := Nat.pos_of_ne_zero hh.2
        have := hd (B ⟨0, hl⟩ ⟨0, hc⟩)
        have hmem : (⟨0, hl⟩ : Fin ℓ) ∈ (Finset.univ.filter fun a : Fin ℓ => ∃ j, B a j = B ⟨0, hl⟩ ⟨0, hc⟩) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨⟨0, hc⟩, rfl⟩
        have := Finset.card_pos.2 ⟨_, hmem⟩
        omega
      rcases hlc with rfl | rfl
      · rw [hLB0]; simp
      · have : R = ∅ := Finset.eq_empty_of_isEmpty R
        rw [hLB0, this]; simp
    have hall : ∀ x : Fin n → Fin n, ((ℓ : ℝ) * (1 - 2 ^ R.card / Real.exp 1 ^ c) - ε * d * n
            - (2 ^ R.card * (c : ℝ) ^ 2 / Real.exp 1 ^ c) * ((ℓ : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2)) ≤
          ((Finset.univ.filter fun a : Fin ℓ =>
              (∃ j, j ∉ R ∧ 1 ≤ (Finset.univ.filter fun t => x t = B a j).card) ∨
              (∃ j, j ∈ R ∧ 2 ≤ (Finset.univ.filter fun t => x t = B a j).card)).card : ℝ)) := by
      intro x
      have h0 : (0 : ℝ) ≤ ((Finset.univ.filter fun a : Fin ℓ =>
              (∃ j, j ∉ R ∧ 1 ≤ (Finset.univ.filter fun t => x t = B a j).card) ∨
              (∃ j, j ∈ R ∧ 2 ≤ (Finset.univ.filter fun t => x t = B a j).card)).card : ℝ) :=
        Nat.cast_nonneg _
      have : ε * (d : ℝ) * n = 0 := by simp [hd0]
      rw [this]
      have : (ℓ : ℝ) * (1 - 2 ^ R.card / Real.exp 1 ^ c) - 0
            - (2 ^ R.card * (c : ℝ) ^ 2 / Real.exp 1 ^ c) * ((ℓ : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2)) = LB0 := by
        rw [hLB0]; ring
      linarith
    have hprob : prob n (fun balls : Fin n → Fin n =>
        (ℓ : ℝ) * (1 - 2 ^ R.card / Real.exp 1 ^ c) - ε * d * n
            - (2 ^ R.card * (c : ℝ) ^ 2 / Real.exp 1 ^ c) * ((ℓ : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2)) ≤
          ((Finset.univ.filter fun a : Fin ℓ =>
              (∃ j, j ∉ R ∧ 1 ≤ (Finset.univ.filter fun t => balls t = B a j).card) ∨
              (∃ j, j ∈ R ∧ 2 ≤ (Finset.univ.filter fun t => balls t = B a j).card)).card : ℝ)) = 1 := by
      unfold prob
      simp only [Fintype.card_fin]
      rw [Finset.filter_true_of_mem (fun x _ => hall x)]
      simp [hN.ne']
    rw [hprob]
    have := Real.exp_pos (-(ε ^ 2 * n / 2))
    linarith
  · have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    have ht : 0 < ε * d * n := by positivity
    have lo := mcd_count (X := Fin n) n (fun x => - f x) d hbd (ε * d * n) ht
    simp only [Fintype.card_fin] at lo
    rw [Finset.sum_neg_distrib, neg_div] at lo
    have hexpo : Real.exp (-2 * (ε * d * n) ^ 2 / (n * (d : ℝ) ^ 2)) = Real.exp (-(2 * ε ^ 2 * n)) := by
      congr 1; field_simp
    rw [hexpo] at lo
    rw [← hE] at lo
    set L := Finset.univ.filter (fun x => ε * d * n ≤ -f x - -E) with hL
    set G := Finset.univ.filter (fun x : Fin n → Fin n => LB0 - ε * d * n ≤ f x) with hG
    have hcover : (Finset.univ : Finset (Fin n → Fin n)) ⊆ G ∪ L := by
      intro x _
      simp only [Finset.mem_union, hG, hL, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h1 : LB0 - ε * d * n ≤ f x
      · left; exact h1
      · right; linarith
    have hcardN : ((Finset.univ : Finset (Fin n → Fin n)).card : ℝ) = (n : ℝ) ^ n := by simp
    have hle : (n : ℝ) ^ n ≤ G.card + L.card := by
      rw [← hcardN]
      have := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
      exact_mod_cast this
    have hLl : (L.card : ℝ) ≤ (n : ℝ) ^ n * Real.exp (-(2 * ε ^ 2 * n)) := by
      have := (div_le_iff₀ hN).1 lo
      linarith
    have hexp2 : Real.exp (-(2 * ε ^ 2 * n)) ≤ Real.exp (-(ε ^ 2 * n / 2)) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ ε ^ 2 * n := by positivity
      linarith
    have hprob : prob n (fun balls : Fin n → Fin n =>
        (ℓ : ℝ) * (1 - 2 ^ R.card / Real.exp 1 ^ c) - ε * d * n
            - (2 ^ R.card * (c : ℝ) ^ 2 / Real.exp 1 ^ c) * ((ℓ : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2)) ≤
          ((Finset.univ.filter fun a : Fin ℓ =>
              (∃ j, j ∉ R ∧ 1 ≤ (Finset.univ.filter fun t => balls t = B a j).card) ∨
              (∃ j, j ∈ R ∧ 2 ≤ (Finset.univ.filter fun t => balls t = B a j).card)).card : ℝ)) =
        G.card / (n : ℝ) ^ n := by
      unfold prob
      simp only [Fintype.card_fin]
      congr 3
      ext x
      simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hfx x]
      simp only [hLB0]
      constructor <;> intro h <;> linarith
    rw [hprob, le_div_iff₀ hN]
    have h3 : (n : ℝ) ^ n * Real.exp (-(ε ^ 2 * n / 2)) ≥ (n : ℝ) ^ n * Real.exp (-(2 * ε ^ 2 * n)) :=
      mul_le_mul_of_nonneg_left hexp2 hN.le
    have h4 : 0 < (n : ℝ) ^ n * Real.exp (-(ε ^ 2 * n / 2)) := by positivity
    nlinarith

end Fact2d

end OnlineStochMatching.TSM

open OnlineStochMatching.TSM


theorem solution (n c ℓ d : ℕ) (hcn : c ^ 2 < n) (B : Fin ℓ → Fin c → Fin n)
    (hB : ∀ a, Function.Injective (B a))
    (hd : ∀ b : Fin n, (Finset.univ.filter fun a : Fin ℓ => ∃ j, B a j = b).card ≤ d)
    (R : Finset (Fin c)) (ε : ℝ) (hε : 0 < ε) :
    1 - 2 * Real.exp (-(ε ^ 2 * n / 2)) ≤
      prob n (fun balls : Fin n → Fin n =>
        (ℓ : ℝ) * (1 - 2 ^ R.card / Real.exp 1 ^ c) - ε * d * n
            - (2 ^ R.card * (c : ℝ) ^ 2 / Real.exp 1 ^ c) * ((ℓ : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2)) ≤
          ((Finset.univ.filter fun a : Fin ℓ =>
              (∃ j, j ∉ R ∧ 1 ≤ (Finset.univ.filter fun t => balls t = B a j).card) ∨
              (∃ j, j ∈ R ∧ 2 ≤ (Finset.univ.filter fun t => balls t = B a j).card)).card : ℝ)) := by
  exact fact_2_core n c ℓ d hcn B hB hd R ε hε
