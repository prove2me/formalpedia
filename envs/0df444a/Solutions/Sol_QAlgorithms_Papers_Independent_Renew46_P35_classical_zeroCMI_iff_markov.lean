-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P35.classical_zeroCMI_iff_markov
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T01:37:29.859221+00:00
-- url     : https://prove2.me/submissions/55a3c08c-137b-4df5-97be-023ca87d702c

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P35
noncomputable section

open scoped Matrix ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Renew46.P35
open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted interfaces, inspected in the pinned library.

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Dependency50.P21 (petz)

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P22 (quantumMI)

theorem g65b_map_zero {α β : Type*} (p : PMF α) (g : α → β) (x : α)
    (h : (p.map g) (g x) = 0) : p x = 0 := by
  by_contra hx
  have : g x ∈ (p.map g).support := (PMF.mem_support_map_iff _ _ _).2 ⟨x, hx, rfl⟩
  exact this h

theorem g65b_prod_apply {A C : Type*} (p : PMF A) (q : PMF C) (a : A) (c : C) :
    pmfProduct p q (a, c) = p a * q c := by
  unfold pmfProduct
  rw [PMF.bind_apply]
  have : ∀ a', (q.map fun c' => (a', c')) (a, c) = if a' = a then q c else 0 := by
    intro a'
    rw [PMF.map_apply]
    by_cases h : a' = a
    · subst h; simp
    · simp [Ne.symm h, h]
  simp only [this, mul_ite, mul_zero]
  rw [tsum_ite_eq]

theorem g65b_fib {A B C : Type*} (p : PMF (A × (B × C))) (a : A) (b : B) :
    (p.map fun x => (x.1, x.2.1)) (a, b) = ∑' c, p (a, (b, c)) := by
  rw [PMF.map_apply]
  refine (show _ = ∑' a', ∑' bc : B × C, (if (a, b) = (a', bc.1) then p (a', bc) else 0) by
    convert (ENNReal.tsum_prod (f := fun a' bc => if (a, b) = (a', bc.1) then p (a', bc) else 0))).trans ?_
  rw [tsum_eq_single a (by intro a' ha; simp [Ne.symm ha])]
  refine (show _ = ∑' b', ∑' c : C, (if (a, b) = (a, b') then p (a, (b', c)) else 0) by
    convert (ENNReal.tsum_prod (f := fun b' c => if (a, b) = (a, b') then p (a, (b', c)) else 0))).trans ?_
  rw [tsum_eq_single b (by intro b' hb; simp [Ne.symm hb])]
  simp

theorem g65b_mi_zero {A C : Type*} (q : PMF (A × C)) :
    discreteMI q = 0 ↔ q = pmfProduct (q.map Prod.fst) (q.map Prod.snd) := by
  letI : MeasurableSpace (A × C) := ⊤
  haveI : MeasurableSingletonClass (A × C) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  unfold discreteMI
  rw [ENNReal.div_eq_zero_iff]
  simp only [ENNReal.ofReal_ne_top, or_false]
  rw [InformationTheory.klDiv_eq_zero_iff, PMF.toMeasure_inj]

/-- PDF pp.2–3, Theorem 1: zero CMI, conditional independence and both Markov factorizations.
Conditional PMFs at null events are arbitrary normalized completions. -/
theorem solution {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C]
    (p : PMF (A × (B × C))) (cond : B → PMF (A × C)) (ba : A → PMF B)
    (hcond : ∀ b, (p.map fun x => x.2.1) b ≠ 0 → ∀ a c,
      cond b (a, c) = p (a, (b, c)) / (p.map fun x => x.2.1) b)
    (hba : ∀ a, (p.map Prod.fst) a ≠ 0 → ∀ b,
      ba a b = (p.map fun x => (x.1, x.2.1)) (a, b) / (p.map Prod.fst) a) :
    let independent := ∀ b, (p.map fun x => x.2.1) b ≠ 0 →
      cond b = pmfProduct ((cond b).map Prod.fst) ((cond b).map Prod.snd)
    (classicalCMI p cond = 0 ↔ independent) ∧
    (independent ↔ ∀ a b c,
      p (a, (b, c)) = (p.map fun x => x.2.1) b *
        ((cond b).map Prod.fst) a * ((cond b).map Prod.snd) c ∧
      p (a, (b, c)) = (p.map Prod.fst) a * ba a b * ((cond b).map Prod.snd) c) := by
  intro independent
  set pB := p.map fun x => x.2.1 with hpB
  set pA := p.map Prod.fst with hpA
  -- p(a,b,c) = pB b * cond b (a,c)
  have hfac : ∀ a b c, p (a, (b, c)) = pB b * cond b (a, c) := by
    intro a b c
    by_cases hb : pB b = 0
    · rw [hb, zero_mul]
      exact g65b_map_zero p (fun x => x.2.1) (a, (b, c)) hb
    · rw [hcond b hb a c, ENNReal.mul_div_cancel hb (PMF.apply_ne_top _ _)]
  refine ⟨?_, ?_⟩
  · unfold classicalCMI
    rw [ENNReal.tsum_eq_zero]
    refine forall_congr' (fun b => ?_)
    by_cases hb : pB b = 0
    · simp only [← hpB, hb, if_true, ne_eq, not_true_eq_false, false_implies]
    · simp only [← hpB, hb, if_false, mul_eq_zero, false_or, ne_eq, not_false_eq_true,
        true_implies]
      exact g65b_mi_zero (cond b)
  · constructor
    · intro hind
      have h1a : ∀ a b c, p (a, (b, c)) =
          pB b * ((cond b).map Prod.fst) a * ((cond b).map Prod.snd) c := by
        intro a b c
        rw [hfac, mul_assoc]
        by_cases hb : pB b = 0
        · rw [hb, zero_mul, zero_mul]
        · congr 1
          conv_lhs => rw [hind b hb]
          exact g65b_prod_apply _ _ a c
      intro a b c
      have h1 := h1a a b c
      refine ⟨h1, ?_⟩
      by_cases ha : pA a = 0
      · rw [ha, zero_mul, zero_mul]
        exact g65b_map_zero p Prod.fst (a, (b, c)) ha
      · rw [hba a ha b, ENNReal.mul_div_cancel ha (PMF.apply_ne_top _ _), g65b_fib]
        have : ∑' c', p (a, (b, c')) = pB b * ((cond b).map Prod.fst) a := by
          simp only [h1a a b]
          rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
        rw [this, h1]
    · intro h b hb
      ext ⟨a, c⟩
      rw [g65b_prod_apply]
      have h1 := (h a b c).1
      rw [hfac, mul_assoc] at h1
      exact (ENNReal.mul_right_inj hb (PMF.apply_ne_top _ _)).1 h1



end
