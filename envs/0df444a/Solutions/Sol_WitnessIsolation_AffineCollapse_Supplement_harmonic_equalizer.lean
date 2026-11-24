-- Prove2me | solution 1 for WitnessIsolation.AffineCollapse.Supplement.harmonic_equalizer
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:09:17.585812+00:00
-- url     : https://prove2.me/submissions/0515b8d4-e481-483e-beeb-59755ff6d70a

import Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_harmonic

set_option autoImplicit false
noncomputable section

open WitnessIsolation.AffineCollapse
open WitnessIsolation.AffineCollapse.Supplement

/-- The harmonic mass as a function of the size only. -/
private def hmk (M k : ℕ) : ℝ :=
  if k = 0 then 0 else 1 / ((k : ℝ) * (harmonic M : ℝ) * (Nat.choose M k : ℝ))

private lemma harmonicMass_eq (M : ℕ) (A : Finset (Fin M)) :
    harmonicMass M A = hmk M A.card := rfl

private lemma choose_swap (n r j : ℕ) (hr : r ≤ n) :
    (n - r).choose j * n.choose r = n.choose j * (n - j).choose r := by
  by_cases hj : j ≤ n - r
  · have h1 := Nat.choose_mul (n := n) (k := n - r) (s := j) hj
    rw [Nat.choose_symm hr] at h1
    have h2 : (n - j).choose (n - r - j) = (n - j).choose r :=
      Nat.choose_symm_of_eq_add (by omega)
    rw [h2] at h1
    rw [mul_comm]
    exact h1
  · push Not at hj
    rw [Nat.choose_eq_zero_of_lt hj, zero_mul]
    by_cases hjn : j ≤ n
    · rw [Nat.choose_eq_zero_of_lt (by omega : n - j < r), mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega : n < j), zero_mul]

private lemma hockey_aux (n r : ℕ) :
    ∑ i ∈ Finset.range (n + 1), i.choose r = (n + 1).choose (r + 1) := by
  induction n with
  | zero =>
    rcases r with _ | r
    · simp
    · simp only [zero_add, Finset.sum_range_one]
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' (n + 1) r]
    ring

private lemma hockey (n r : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (n - j).choose r = (n + 1).choose (r + 1) := by
  have h := Finset.sum_range_reflect (fun i => i.choose r) (n + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h, hockey_aux]

private lemma key_sum (n r : ℕ) (hr : r ≤ n) (H : ℝ) (hH : 0 < H) :
    ((r : ℝ) + 1) * ∑ j ∈ Finset.range (n - r + 1),
      ((n - r).choose j : ℝ) * (1 / (((j : ℝ) + 1) * H * ((n + 1).choose (j + 1) : ℝ))) =
      1 / H := by
  set F : ℕ → ℝ := fun j =>
    ((n - r).choose j : ℝ) * (1 / (((j : ℝ) + 1) * H * ((n + 1).choose (j + 1) : ℝ))) with hF
  have hsub : ∑ j ∈ Finset.range (n - r + 1), F j = ∑ j ∈ Finset.range (n + 1), F j := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro j hj hj'
    simp only [Finset.mem_range] at hj hj'
    simp only [hF]
    rw [Nat.choose_eq_zero_of_lt (by omega : n - r < j)]
    simp
  have hc2 : (0 : ℝ) < n.choose r := by exact_mod_cast Nat.choose_pos hr
  have hterm : ∀ j ∈ Finset.range (n + 1),
      F j = ((n - j).choose r : ℝ) / (((n : ℝ) + 1) * H * (n.choose r : ℝ)) := by
    intro j hj
    have hj : j ≤ n := by simp only [Finset.mem_range] at hj; omega
    have hc1 : (0 : ℝ) < (n + 1).choose (j + 1) := by exact_mod_cast Nat.choose_pos (by omega)
    have e1' : ((n - r).choose j : ℝ) * (n.choose r) = (n.choose j) * ((n - j).choose r) := by
      exact_mod_cast choose_swap n r j hr
    have e2' : ((n : ℝ) + 1) * (n.choose j) = ((n + 1).choose (j + 1)) * ((j : ℝ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n j
    simp only [hF]
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination H * ((n : ℝ) + 1) * e1' + H * ((n - j).choose r : ℝ) * e2'
  rw [hsub, Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hsum : ∑ j ∈ Finset.range (n + 1), ((n - j).choose r : ℝ) = (n + 1).choose (r + 1) := by
    exact_mod_cast hockey n r
  rw [hsum]
  have e3 : ((n : ℝ) + 1) * (n.choose r) = ((n + 1).choose (r + 1)) * ((r : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n r
  rw [← mul_div_assoc, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-H) * e3

theorem solution (M : ℕ) (hM : 1 ≤ M) :
    ∃ μ : Law (Finset (Fin M)),
      (∀ A, μ.mass A = harmonicMass M A) ∧
      ∀ T : Finset (Fin M), T.Nonempty →
        μ.prob (fun A => (A ∩ T).card = 1) = 1 / (harmonic M : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  have hH : (0 : ℝ) < (harmonic (n + 1) : ℝ) := by
    exact_mod_cast harmonic_pos (by omega)
  have hnonneg : ∀ A, 0 ≤ harmonicMass (n + 1) A := by
    intro A
    rw [harmonicMass_eq, hmk]
    split_ifs
    · exact le_refl _
    · positivity
  have htotal : ∑ A, harmonicMass (n + 1) A = 1 := by
    simp only [harmonicMass_eq]
    rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card (fun k => hmk (n + 1) k),
      Finset.card_univ, Fintype.card_fin, Finset.sum_range_succ']
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (n + 1).choose (i + 1) • hmk (n + 1) (i + 1) =
          ((i : ℝ) + 1)⁻¹ / (harmonic (n + 1) : ℝ) := by
      intro i hi
      have hi : i ≤ n := by simp only [Finset.mem_range] at hi; omega
      have hc : (0 : ℝ) < (n + 1).choose (i + 1) := by exact_mod_cast Nat.choose_pos (by omega)
      rw [hmk, if_neg (by omega), nsmul_eq_mul]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
    simp only [hmk, if_pos, smul_zero, add_zero]
    have : (harmonic (n + 1) : ℝ) = ∑ i ∈ Finset.range (n + 1), ((i : ℝ) + 1)⁻¹ := by
      simp [harmonic]
    rw [← this]
    exact div_self hH.ne'
  refine ⟨⟨harmonicMass (n + 1), hnonneg, htotal⟩, fun _ => rfl, ?_⟩
  intro T hT
  unfold Law.prob Law.expect
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hbij : ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (n + 1)) => (A ∩ T).card = 1),
      harmonicMass (n + 1) A =
      ∑ p ∈ T ×ˢ Tᶜ.powerset, hmk (n + 1) (p.2.card + 1) := by
    symm
    apply Finset.sum_nbij (fun p => insert p.1 p.2)
    · rintro ⟨x, B⟩ hp
      simp only [Finset.mem_product, Finset.mem_powerset] at hp
      obtain ⟨hx, hB⟩ := hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Finset.insert_inter_of_mem hx]
      have : B ∩ T = ∅ := by
        ext y
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
        intro hy hyT
        exact (Finset.mem_compl.mp (hB hy)) hyT
      rw [this]
      rfl
    · rintro ⟨x, B⟩ hp ⟨x', B'⟩ hp' he
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powerset] at hp hp'
      simp only at he
      have hdis : ∀ C : Finset (Fin (n + 1)), C ⊆ Tᶜ → C \ T = C := by
        intro C hC
        ext y
        simp only [Finset.mem_sdiff, and_iff_left_iff_imp]
        intro hy
        exact Finset.mem_compl.mp (hC hy)
      have hBB : B = B' := by
        have := congrArg (· \ T) he
        simp only [Finset.insert_sdiff_of_mem _ hp.1, Finset.insert_sdiff_of_mem _ hp'.1,
          hdis B hp.2, hdis B' hp'.2] at this
        exact this
      have hxx : x = x' := by
        have hx : x ∈ insert x' B' := he ▸ Finset.mem_insert_self x B
        rcases Finset.mem_insert.mp hx with h | h
        · exact h
        · exact absurd hp.1 (Finset.mem_compl.mp (hp'.2 h))
      rw [hxx, hBB]
    · intro A hA
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hA
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hA
      have hxA : x ∈ A ∩ T := hx ▸ Finset.mem_singleton_self x
      refine ⟨(x, A \ T), ?_, ?_⟩
      · simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powerset]
        refine ⟨(Finset.mem_inter.mp hxA).2, ?_⟩
        intro y hy
        exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hy).2
      · simp only
        ext y
        simp only [Finset.mem_insert, Finset.mem_sdiff]
        constructor
        · rintro (rfl | ⟨h, _⟩)
          · exact (Finset.mem_inter.mp hxA).1
          · exact h
        · intro hy
          by_cases hyT : y ∈ T
          · left
            have : y ∈ A ∩ T := Finset.mem_inter.mpr ⟨hy, hyT⟩
            rw [hx] at this
            exact Finset.mem_singleton.mp this
          · right; exact ⟨hy, hyT⟩
    · rintro ⟨x, B⟩ hp
      simp only [Finset.mem_product, Finset.mem_powerset] at hp
      have hxB : x ∉ B := fun h => (Finset.mem_compl.mp (hp.2 h)) hp.1
      rw [harmonicMass_eq, Finset.card_insert_of_notMem hxB]
  rw [hbij, Finset.sum_product]
  simp only []
  rw [Finset.sum_const, nsmul_eq_mul,
    Finset.sum_powerset_apply_card (fun k => hmk (n + 1) (k + 1))]
  obtain ⟨r, hr⟩ : ∃ r, T.card = r + 1 := ⟨T.card - 1, by
    have := Finset.card_pos.mpr hT; omega⟩
  have hrn : r ≤ n := by
    have := Finset.card_le_univ T
    rw [Fintype.card_fin] at this
    omega
  have hc : Tᶜ.card = n - r := by
    rw [Finset.card_compl, Fintype.card_fin, hr]; omega
  rw [hc, hr]
  have := key_sum n r hrn _ hH
  convert this using 2
  · push_cast; ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [nsmul_eq_mul, hmk, if_neg (by omega)]
    push_cast
    ring
