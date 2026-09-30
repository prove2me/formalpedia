-- Prove2me | solution 1 for SP4RankProfiles.rank_nine_raw_profiles
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T04:02:35.63629+00:00
-- url     : https://prove2.me/submissions/3ecb0d6b-09c5-4a48-9d7d-87c81f1be412

import Definitions.Def_SP4RankProfiles

set_option autoImplicit false

open SP4RankProfiles

namespace SP4RankProfiles

private theorem mass_add (r s : ℤ →₀ ℕ) : mass (r + s) = mass r + mass s := by
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private theorem mass_single (a : ℤ) (n : ℕ) : mass (Finsupp.single a n) = n := by
  simp [mass]

private theorem eq_of_le_mass_eq {r s : ℤ →₀ ℕ} (hle : r ≤ s)
    (hmass : mass r = mass s) : r = s := by
  classical
  let S := r.support ∪ s.support
  have hr : mass r = ∑ i ∈ S, r i :=
    Finsupp.sum_of_support_subset r Finset.subset_union_left _ (by simp)
  have hs : mass s = ∑ i ∈ S, s i :=
    Finsupp.sum_of_support_subset s Finset.subset_union_right _ (by simp)
  rw [hr, hs] at hmass
  have he := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ S) => hle i)).mp hmass
  ext i
  by_cases hi : i ∈ S
  · exact he i hi
  · have hir : i ∉ r.support := by intro h; exact hi (Finset.mem_union_left _ h)
    have his : i ∉ s.support := by intro h; exact hi (Finset.mem_union_right _ h)
    simp [Finsupp.notMem_support_iff.mp hir, Finsupp.notMem_support_iff.mp his]

private theorem five_le {r : ℤ →₀ ℕ} {g h : ℤ}
    (hh : 0 < h) (hg : h < g) (hsym : ∀ a, r (-a) = r a)
    (hc : 0 < r 0) (hrg : 2 ≤ r g) (hrh : 2 ≤ r h) : five g h ≤ r := by
  intro a
  have hg0 : g ≠ 0 := by omega
  have hh0 : h ≠ 0 := by omega
  have hgh : g ≠ h := by omega
  have hgnh : g ≠ -h := by omega
  have hgn : -g ≠ g := by omega
  have hhn : -h ≠ h := by omega
  have hngh : -g ≠ h := by omega
  by_cases hag : a = -g
  · subst a
    simpa [five, Finsupp.single_apply, hg0, hh0, hgh, hgnh, hgn, hhn, hngh,
      hsym] using hrg
  by_cases hah : a = -h
  · subst a
    simpa [five, Finsupp.single_apply, hg0, hh0, hgh, hgnh, hgn, hhn, hngh,
      hsym] using hrh
  by_cases ha0 : a = 0
  · subst a
    simpa [five, Finsupp.single_apply, hg0, hh0] using Nat.succ_le_of_lt hc
  by_cases hap : a = h
  · subst a
    simpa [five, Finsupp.single_apply, hg0, hh0, hgh, hgnh, hgn, hhn, hngh] using hrh
  by_cases haq : a = g
  · subst a
    simpa [five, Finsupp.single_apply, hg0, hh0, hgh, hgnh, hgn, hhn, hngh] using hrg
  simp [five, Finsupp.single_apply, Ne.symm hag, Ne.symm hah, Ne.symm ha0,
    Ne.symm hap, Ne.symm haq]

end SP4RankProfiles

theorem solution (r : ℤ →₀ ℕ)
    (htotal : mass r = 9) (hsym : ∀ a, r (-a) = r a)
    (hcenter : 0 < r 0) (heven : ∀ a, a ≠ 0 → Even (r a))
    (hnontrivial : ∃ a, a ≠ 0 ∧ 0 < r a) :
    (∃ g : ℤ, 0 < g ∧ r = three g 2 5) ∨
    (∃ g : ℤ, 0 < g ∧ r = three g 4 1) ∨
    (∃ g h : ℤ, 0 < h ∧ h < g ∧ r = five g h) := by
  classical
  have hpos : ∃ g : ℤ, 0 < g ∧ 0 < r g := by
    obtain ⟨a, ha, hr⟩ := hnontrivial
    by_cases hap : 0 < a
    · exact ⟨a, hap, hr⟩
    · exact ⟨-a, by omega, by simpa [hsym] using hr⟩
  obtain ⟨g, hg, hrg⟩ := hpos
  have htwo : ∀ a : ℤ, 0 < a → 0 < r a → 2 ≤ r a := by
    intro a ha hra
    obtain ⟨k, hk⟩ := heven a (by omega)
    omega
  by_cases hsecond : ∃ h : ℤ, 0 < h ∧ h ≠ g ∧ 0 < r h
  · obtain ⟨h, hh, hne, hrh⟩ := hsecond
    have hf (u v : ℤ) (hv : 0 < v) (hu : v < u)
        (hru : 0 < r u) (hrv : 0 < r v) : r = five u v := by
      apply Eq.symm
      apply eq_of_le_mass_eq (five_le hv hu hsym hcenter
        (htwo u (by omega) hru) (htwo v hv hrv))
      simpa [five, mass_add, mass_single] using htotal.symm
    by_cases hhg : h < g
    · exact Or.inr (Or.inr ⟨g, h, hh, hhg, hf g h hh hhg hrg hrh⟩)
    · exact Or.inr (Or.inr ⟨h, g, hg, by omega, hf h g hg (by omega) hrh hrg⟩)
  · have honly : ∀ a : ℤ, a ≠ -g → a ≠ 0 → a ≠ g → r a = 0 := by
      intro a han ha0 hap
      by_contra hra
      have hra' : 0 < r a := Nat.pos_of_ne_zero hra
      by_cases ha : 0 < a
      · exact hsecond ⟨a, ha, hap, hra'⟩
      · exact hsecond ⟨-a, by omega, by omega, by simpa [hsym] using hra'⟩
    have hexact : r = three g (r g) (r 0) := by
      ext a
      by_cases ha : a = -g
      · subst a
        simp [three, Finsupp.single_apply, hsym, show g ≠ 0 by omega,
          show -g ≠ g by omega]
      by_cases hb : a = 0
      · subst a
        simp [three, Finsupp.single_apply, show g ≠ 0 by omega]
      by_cases hc : a = g
      · subst a
        simp [three, Finsupp.single_apply, show g ≠ 0 by omega,
          show -g ≠ g by omega]
      · simp [three, Finsupp.single_apply, Ne.symm ha, Ne.symm hb, Ne.symm hc,
          honly a ha hb hc]
    have hm : r g + r 0 + r g = 9 := by
      have := congrArg mass hexact
      simpa [htotal, three, mass_add, mass_single] using this.symm
    obtain ⟨k, hk⟩ := heven g (by omega)
    have hcases : (r g = 2 ∧ r 0 = 5) ∨ (r g = 4 ∧ r 0 = 1) := by omega
    rcases hcases with ⟨h2, h5⟩ | ⟨h4, h1⟩
    · exact Or.inl ⟨g, hg, by simpa [h2, h5] using hexact⟩
    · exact Or.inr (Or.inl ⟨g, hg, by simpa [h4, h1] using hexact⟩)


#print axioms solution
