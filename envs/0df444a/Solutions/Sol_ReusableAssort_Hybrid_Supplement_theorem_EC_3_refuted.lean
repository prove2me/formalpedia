-- Prove2me | solution 1 for ReusableAssort.Hybrid.Supplement.theorem_EC_3_refuted
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:07.814498+00:00
-- url     : https://prove2.me/submissions/75f8e133-c910-443f-af10-29a9490e4d6f

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Supplement_AdvBookingCounterexample

open ReusableAssort
open ReusableAssort.Hybrid
open ReusableAssort.Hybrid.Supplement

/-- Refutation of Theorem EC.3 with Algorithm 5 as printed: the second factor of x
in the unconditional target y cuts revenue in half on an optimal normalized LP assignment. -/
theorem solution :
    advCounterI.Assumptions ∧ cmin advCounterI = 100 ∧
    advOneOptimal advCounterI advCounterX advCounterY ∧
    (∑ S ∈ advCounterI.feas, advCounterX S) = 1 ∧
    advOneObj advCounterI advCounterY = 1 ∧
    (∀ γ ∈ Set.Icc (0 : ℝ) 1,
      expRevAlg5One advCounterI advCounterX advCounterY γ = (1 - γ) / 2) ∧
    (∃ γ, IsGammaStar 100 γ) ∧
    (∀ γ, IsGammaStar 100 γ →
      expRevAlg5One advCounterI advCounterX advCounterY γ <
        (1 - epsStar 100) * advOneObj advCounterI advCounterY) := by
          have hs01 : ({0,1} : Finset (Fin 2)).sort (· ≤ ·) = [0,1] := by
            rw [Finset.sort_insert (r := fun x1 x2 : Fin 2 => x1 ≤ x2) (s := {1}) (a := 0) (by decide) (by decide)]; simp
          have hms : ∀ le : Fin 2 → Fin 2 → Bool, le 0 1 = false → ([0,1] : List (Fin 2)).mergeSort le = [1,0] := by
            intro le h
            simp [List.mergeSort, List.MergeSort.Internal.splitInTwo, h]
          have hr0 : ReusableAssort.Hybrid.ratio (advCounterI.phi 0) {0,1} (advCounterY {0,1}) 0 = 1/2 := by
            simp [ReusableAssort.Hybrid.ratio, advCounterI, advCounterY]
          have hr1 : ReusableAssort.Hybrid.ratio (advCounterI.phi 0) {0,1} (advCounterY {0,1}) 1 = 1 := by
            simp [ReusableAssort.Hybrid.ratio, advCounterI]
          have hsl : sortedList (advCounterI.phi 0) {0,1} (advCounterY {0,1}) = [1,0] := by
            unfold sortedList; rw [hs01]; apply hms; rw [hr0, hr1]; norm_num
          have hcard : ({0,1} : Finset (Fin 2)).card = 2 := by decide
          have hq0 : qprob (advCounterI.phi 0) {0,1} (advCounterY {0,1}) 0 = 0 := by
            simp [qprob, hsl, hr0, hr1]
          have hq1 : qprob (advCounterI.phi 0) {0,1} (advCounterY {0,1}) 1 = 1/2 := by
            simp [qprob, hsl, hr0, hr1, hcard]; norm_num
          have hq2 : qprob (advCounterI.phi 0) {0,1} (advCounterY {0,1}) 2 = 1/2 := by
            simp [qprob, hsl, hr0, hr1, hcard]
          have hsub1 : ∀ U : Finset (Fin 2), 0 ∈ U → ∀ p, subAssortAux 1 (advCounterI.phi 0) {1} p U = 0 := by
            intro U hU p
            have h1 : U ≠ ∅ := by rintro rfl; simp at hU
            have h2 : U ≠ {1} := by rintro rfl; simp at hU
            simp [subAssortAux, h1, h2]
          have hB : ∀ U : Finset (Fin 2), 0 ∈ U → subAssort (advCounterI.phi 0) {0,1} (advCounterY {0,1}) U = if U = {0,1} then 1/2 else 0 := by
            intro U h0
            have h1 : U ≠ ∅ := by rintro rfl; simp at h0
            have hne : ({0,1} : Finset (Fin 2)) ≠ ∅ := by decide
            have hIco : Finset.Ico 1 2 = {1} := by decide
            have ht : (List.take 1 ([1,0] : List (Fin 2))).toFinset = {1} := by decide
            rw [subAssort, hcard, subAssortAux, hcard, hq0, hq2, hsl, if_neg hne, hIco, Finset.sum_singleton, ht, hsub1 U h0, if_neg h1]
            split_ifs <;> simp
          have hB0 : subAssort (advCounterI.phi 0) {0,1} (advCounterY {0,1}) {0} = 0 := by
            rw [hB _ (by decide)]; rw [if_neg (by decide)]
          have hB1 : subAssort (advCounterI.phi 0) {0,1} (advCounterY {0,1}) {0,1} = 1/2 := by
            rw [hB _ (by decide)]; rw [if_pos rfl]
          have hA : ∀ p : Fin 2 → ℝ, p 0 = 1/2 → subAssort (advCounterI.phi 0) {0} p {0} = 1/2 := by
            intro p hp
            simp [subAssort, subAssortAux, qprob, sortedList, ReusableAssort.Hybrid.ratio, advCounterI, hp]
          have hA0 : subAssort (advCounterI.phi 0) {0} (advCounterY {0}) {0} = 1/2 := hA _ (by simp [advCounterY])
          have hA1 : subAssort (advCounterI.phi 0) {0} (advCounterY {0,1}) {0} = 1/2 := hA _ (by simp [advCounterY])
          have hinner : ∀ Stil : Finset (Fin 2), ∑ i ∈ Stil, advCounterI.phi 0 Stil i * advCounterI.r 0 i = if 0 ∈ Stil then 1 else 0 := by
            intro Stil
            by_cases h : 0 ∈ Stil <;> simp [h, advCounterI]
          have hfeas : advCounterI.feas = {∅, {0}, {1}, {0,1}} := by
            rw [show advCounterI.feas = Finset.univ from rfl]; decide
          have hpow : ({0,1} : Finset (Fin 2)).powerset = {∅, {0}, {1}, {0,1}} := by decide
          have hrev : ∀ γ : ℝ, expRevAlg5One advCounterI advCounterX advCounterY γ = (1 - γ) / 2 := by
            intro γ
            unfold expRevAlg5One
            simp only [hinner]
            rw [hfeas]
            have hp0 : ({0} : Finset (Fin 2)).powerset = {∅, {0}} := by decide
            have hpe : (∅ : Finset (Fin 2)).powerset = {∅} := by decide
            rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
              Finset.sum_singleton, hp0, hpow]
            rw [Finset.sum_insert (by decide), Finset.sum_singleton]
            rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
            rw [hp0, hpe, hpow]
            have hp1 : ({1} : Finset (Fin 2)).powerset = {∅, {1}} := by decide
            rw [hp1]
            simp only [Finset.sum_insert (show (∅ : Finset (Fin 2)) ∉ ({{0}} : Finset (Finset (Fin 2))) by decide),
              Finset.sum_insert (show (∅ : Finset (Fin 2)) ∉ ({{1}} : Finset (Finset (Fin 2))) by decide),
              Finset.sum_insert (show (∅ : Finset (Fin 2)) ∉ ({{0}, {1}, {0,1}} : Finset (Finset (Fin 2))) by decide),
              Finset.sum_insert (show ({0} : Finset (Fin 2)) ∉ ({{1}, {0,1}} : Finset (Finset (Fin 2))) by decide),
              Finset.sum_insert (show ({1} : Finset (Fin 2)) ∉ ({{0,1}} : Finset (Finset (Fin 2))) by decide),
              Finset.sum_singleton]
            have hdc : (({0, 1} : Finset (Fin 2)) \ {0}).card = 1 := by decide
            simp [advCounterX, hA0, hA1, hB0, hB1, hdc]
            ring
          have hsum4 : ∀ f : Finset (Fin 2) → ℝ, ∑ S ∈ advCounterI.feas, f S = f ∅ + f {0} + f {1} + f {0,1} := by
            intro f
            rw [hfeas, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
              Finset.sum_singleton]
            ring
          have hphi : ∀ S i, advCounterI.phi 0 S i = if i = 0 ∧ (0 : Fin 2) ∈ S then 1 else 0 := fun _ _ => rfl
          have hassm : advCounterI.Assumptions := by
            refine
              { phi_empty := ?_, weak_subst := ?_, feas_nonempty := ?_, down_closed := ?_, phi_nonneg := ?_,
                phi_support := ?_, phi_sum_le := ?_, r_nonneg := ?_, one_le_c := ?_, g_nonneg := ?_,
                g_zero := ?_, g_gt := ?_, g_sum := ?_, F_nonneg := ?_, F_sum := ?_ }
            · intro z i; simp [advCounterI]
            · intro z S _ i j hji _
              simp only [advCounterI]
              by_cases hi : i = 0
              · subst hi
                by_cases h0 : (0 : Fin 2) ∈ S
                · simp [h0]
                · have : (0 : Fin 2) ∉ insert j S := by
                    simp only [Finset.mem_insert, not_or]; exact ⟨fun h => hji h.symm, h0⟩
                  simp [h0, this]
              · simp [hi]
            · exact ⟨∅, by simp [advCounterI]⟩
            · intro S _ S' _; simp [advCounterI]
            · intro z S _ i; simp only [advCounterI]; split_ifs <;> norm_num
            · intro z S _ i hi; simp only [advCounterI]
              rw [if_neg]; rintro ⟨rfl, h⟩; exact hi h
            · intro z S _
              simp only [advCounterI]
              calc ∑ i ∈ S, (if i = 0 ∧ (0 : Fin 2) ∈ S then (1 : ℝ) else 0)
                  ≤ ∑ i, (if i = 0 ∧ (0 : Fin 2) ∈ S then (1 : ℝ) else 0) :=
                    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                      (fun _ _ _ => by split_ifs <;> norm_num)
                _ ≤ 1 := by
                    rw [Fin.sum_univ_two]; by_cases h0 : (0 : Fin 2) ∈ S <;> simp [h0]
            · intro z i; simp [advCounterI]
            · intro i; simp [advCounterI]
            · intro z i d; simp only [advCounterI]; split_ifs <;> norm_num
            · intro z i; simp [advCounterI]
            · intro z i d hd; simp only [advCounterI]; rw [if_neg]; omega
            · intro z i; simp [advCounterI]
            · intro t z; simp [advCounterI]
            · intro t _; simp [advCounterI]
          have hcmin : cmin advCounterI = 100 := by simp [cmin, advCounterI]
          have hxsum : (∑ S ∈ advCounterI.feas, advCounterX S) = 1 := by
            rw [hsum4]; simp [advCounterX]; norm_num
          have hr : ∀ i, advCounterI.r 0 i = 1 := fun _ => rfl
          have hobj : advOneObj advCounterI advCounterY = 1 := by
            unfold advOneObj; rw [hsum4]; simp [advCounterY, hr]; norm_num
          have hopt : advOneOptimal advCounterI advCounterX advCounterY := by
            refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
            · intro S _; unfold advCounterX; split_ifs <;> norm_num
            · rw [hxsum]
            · intro S _ i
              rw [hphi]; unfold advCounterY advCounterX
              by_cases hi : i = 0 <;> by_cases h0 : (0 : Fin 2) ∈ S <;> simp [hi, h0]
            · intro i
              rw [hsum4]; unfold advCounterY
              fin_cases i <;> simp [advCounterI] <;> norm_num
            · intro x' y' ⟨hx0, hx1, hy, _⟩
              rw [hobj]
              unfold advOneObj
              calc ∑ S ∈ advCounterI.feas, ∑ i, advCounterI.r 0 i * y' S i
                  ≤ ∑ S ∈ advCounterI.feas, x' S := by
                    apply Finset.sum_le_sum
                    intro S hS
                    rw [Fin.sum_univ_two, hr, hr]
                    have h0 := (hy S hS 0).2
                    have h1 := (hy S hS 1).2
                    rw [hphi] at h0 h1
                    have hx := hx0 S hS
                    have : ((1 : Fin 2) = 0 ∧ (0 : Fin 2) ∈ S) = False := by simp
                    simp only [this, if_false, zero_mul] at h1
                    have h0' : y' S 0 ≤ x' S := by
                      split_ifs at h0 <;> linarith
                    linarith
                _ ≤ 1 := hx1
          have hcont : ContinuousOn (fun γ => hfun γ 100) (Set.Icc (0 : ℝ) 1) := by
            unfold hfun
            apply ContinuousOn.sub continuousOn_const
            apply ContinuousOn.mul (by fun_prop)
            apply ContinuousOn.sub continuousOn_const
            apply ContinuousOn.rexp
            apply ContinuousOn.neg
            apply ContinuousOn.div (by fun_prop) (by fun_prop)
            intro γ hγ; have := hγ.2; linarith
          obtain ⟨γm, hγm, hmin⟩ := isCompact_Icc.exists_isMinOn
            (Set.nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)) hcont
          have heps : epsStar 100 = hfun γm 100 := by
            unfold epsStar
            apply IsLeast.csInf_eq
            refine ⟨⟨γm, hγm, rfl⟩, ?_⟩
            rintro _ ⟨y, hy, rfl⟩
            exact isMinOn_iff.mp hmin y hy
          have hle : ∀ γ ∈ Set.Icc (0 : ℝ) 1, epsStar 100 ≤ hfun γ 100 := by
            intro γ hγ; rw [heps]; exact isMinOn_iff.mp hmin γ hγ
          have hfive : hfun (1/5) 100 < 1/2 := by
            unfold hfun
            have he : -((1/5 : ℝ) ^ 2 * 100 / (2 - 1/5)) = -(20/9) := by norm_num
            rw [he]
            have hexp : Real.exp (-(20/9)) ≤ 9/29 := by
              rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
              have := Real.add_one_le_exp (20/9 : ℝ)
              norm_num at this ⊢; linarith
            nlinarith
          have heps_lt : epsStar 100 < 1/2 :=
            lt_of_le_of_lt (hle (1/5) ⟨by norm_num, by norm_num⟩) hfive
          refine ⟨hassm, hcmin, hopt, hxsum, hobj, fun γ _ => hrev γ, ⟨γm, hγm, heps.symm⟩, ?_⟩
          rintro γ ⟨hγ, _⟩
          rw [hrev, hobj, mul_one]
          have := hγ.1
          linarith
