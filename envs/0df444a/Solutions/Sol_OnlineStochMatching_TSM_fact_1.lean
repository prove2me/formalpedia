-- Prove2me | solution 1 for OnlineStochMatching.TSM.fact_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T06:18:47.889982+00:00
-- url     : https://prove2.me/submissions/5bc62815-03f0-45c2-9bbf-294451fe24cb

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
end OnlineStochMatching.TSM

open OnlineStochMatching.TSM


theorem solution (n : ℕ) (B : Finset (Fin n)) (ε : ℝ) (hε : 0 < ε) :
    1 - 2 * Real.exp (-(ε ^ 2 * n / 2)) ≤
      prob n (fun balls : Fin n → Fin n =>
        (B.card : ℝ) * (1 - 1 / Real.exp 1) - ε * n ≤
            ((B.filter fun b => ∃ t, balls t = b).card : ℝ) ∧
          ((B.filter fun b => ∃ t, balls t = b).card : ℝ) ≤
            (B.card : ℝ) * (1 - 1 / Real.exp 1 + 1 / (Real.exp 1 * n)) + ε * n) := by
  exact fact_1_core n B ε hε
