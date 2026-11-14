-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.majority_pairwise_extension
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:50:36.240478+00:00
-- url     : https://prove2.me/submissions/360ccc2e-6168-4798-9e43-7c08da2c1751

import Mathlib
noncomputable section
open scoped Classical BigOperators

private def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

private theorem maj_eq_of_two (a b c t : Bool) (h : (a = t ∧ b = t) ∨ (a = t ∧ c = t) ∨ (b = t ∧ c = t)) :
    maj a b c = t := by
  cases a <;> cases b <;> cases c <;> cases t <;> simp_all [maj]

private theorem majority_pairwise_extension {ι : Type} [Fintype ι] (R : Finset (ι → Bool))
    (hR : R.Nonempty) (hmajority : ∀ a b c, a ∈ R → b ∈ R → c ∈ R → (fun i => maj (a i) (b i) (c i)) ∈ R)
    (x : ι → Bool) (hpairs : ∀ i j : ι, ∃ y ∈ R, y i = x i ∧ y j = x j) : x ∈ R := by
  classical
  have hpatch : ∀ n : ℕ, ∀ S : Finset ι, S.card = n →
      ∃ y ∈ R, ∀ i ∈ S, y i = x i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hcard
      by_cases h0 : S = ∅
      · subst S
        obtain ⟨y,hy⟩ := hR
        exact ⟨y,hy,by simp⟩
      · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
        obtain ⟨a,ha⟩ := hne
        by_cases hsmall : S.card ≤ 1
        · obtain ⟨y,hy,hya,_⟩ := hpairs a a
          refine ⟨y,hy,?_⟩
          intro i hi
          have hi' : i = a := (Finset.card_le_one_iff.mp hsmall) hi ha
          simpa [hi'] using hya
        · by_cases htwo : S.card ≤ 2
          · have hlt : 1 < S.card := by omega
            obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hlt
            obtain ⟨y,hy,hyu,hyv⟩ := hpairs u v
            refine ⟨y,hy,?_⟩
            intro i hi
            by_cases hiu : i = u
            · simpa [hiu] using hyu
            · by_cases hiv : i = v
              · simpa [hiv] using hyv
              · have : 2 < S.card := Finset.two_lt_card.mpr ⟨u,hu,v,hv,i,hi,huv,Ne.symm hiu,Ne.symm hiv⟩
                omega
          · have hlt : 2 < S.card := by omega
            obtain ⟨u,hu,v,hv,w,hw,huv,huw,hvw⟩ := Finset.two_lt_card.mp hlt
            have hsm (z : ι) (hz : z ∈ S) : (S.erase z).card < n := by
              rw [Finset.card_erase_of_mem hz, hcard]
              omega
            obtain ⟨a',ha',hA⟩ := ih _ (hsm u hu) (S.erase u) rfl
            obtain ⟨b',hb',hB⟩ := ih _ (hsm v hv) (S.erase v) rfl
            obtain ⟨c',hc',hC⟩ := ih _ (hsm w hw) (S.erase w) rfl
            refine ⟨(fun i => maj (a' i) (b' i) (c' i)), hmajority a' b' c' ha' hb' hc', ?_⟩
            intro i hi
            apply maj_eq_of_two
            by_cases hiu : i = u
            · right; right
              exact ⟨hB i (Finset.mem_erase.mpr ⟨by intro h; exact huv (hiu.symm.trans h),hi⟩),
                hC i (Finset.mem_erase.mpr ⟨by intro h; exact huw (hiu.symm.trans h),hi⟩)⟩
            · by_cases hiv : i = v
              · right; left
                exact ⟨hA i (Finset.mem_erase.mpr ⟨hiu,hi⟩),
                  hC i (Finset.mem_erase.mpr ⟨by intro h; exact hvw (hiv.symm.trans h),hi⟩)⟩
              · left
                exact ⟨hA i (Finset.mem_erase.mpr ⟨hiu,hi⟩), hB i (Finset.mem_erase.mpr ⟨hiv,hi⟩)⟩
  obtain ⟨y,hy,heq⟩ := hpatch (Fintype.card ι) Finset.univ (by simp)
  have : y = x := by funext i; exact heq i (Finset.mem_univ _)
  simpa [this] using hy


theorem solution {ι : Type} [Fintype ι] (R : Finset (ι → Bool))
    (hR : R.Nonempty) (hmajority : ∀ a b c, a ∈ R → b ∈ R → c ∈ R →
      (fun i => (a i && b i) || (a i && c i) || (b i && c i)) ∈ R)
    (x : ι → Bool) (hpairs : ∀ i j : ι, ∃ y ∈ R, y i = x i ∧ y j = x j) : x ∈ R := by
  apply majority_pairwise_extension R hR _ x hpairs
  simpa only [maj] using hmajority
