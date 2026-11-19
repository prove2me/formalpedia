-- Prove2me | solution 1 for OfflineCMC.Minimax.varshamov_gilbert
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:23:53.891638+00:00
-- url     : https://prove2.me/submissions/06d8cdcf-b5bc-4892-9405-17df59008d8c

import Mathlib

open Real Finset

/-- entropy bound: Σ_{j ≤ αm} C(m,j) ≤ 2^{m h(α)} -/
lemma ent_bound (m : ℕ) (α : ℝ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    ∑ j ∈ (range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : ℝ) ≤ α * m), (m.choose j : ℝ) ≤
      (2 : ℝ) ^ ((m : ℝ) * (Real.binEntropy α / Real.log 2)) := by
  have h1α : 0 < 1 - α := by linarith
  set l : ℝ := α / (1 - α) with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one h1α]; linarith
  have hP : 0 < l ^ (α * m) := Real.rpow_pos_of_pos hl0 _
  have hterm : ∀ j ∈ (range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : ℝ) ≤ α * m),
      (m.choose j : ℝ) ≤ (m.choose j : ℝ) * l ^ j / l ^ (α * m) := by
    intro j hj
    have hj' : (j : ℝ) ≤ α * m := (mem_filter.mp hj).2
    have hpow : l ^ (α * m) ≤ l ^ j := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge hl0 hl1 hj'
    rw [le_div_iff₀ hP]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  calc ∑ j ∈ (range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : ℝ) ≤ α * m), (m.choose j : ℝ)
      ≤ ∑ j ∈ (range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : ℝ) ≤ α * m), (m.choose j : ℝ) * l ^ j / l ^ (α * m) :=
        sum_le_sum hterm
    _ ≤ ∑ j ∈ range (m + 1), (m.choose j : ℝ) * l ^ j / l ^ (α * m) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => by positivity)
    _ = (1 + l) ^ m / l ^ (α * m) := by
        rw [← sum_div, show (1 + l) = l + 1 by ring, add_pow]
        congr 1; apply sum_congr rfl; intro j _; simp only [one_pow]; ring
    _ = _ := by
        have hb : 1 + l = (1 - α)⁻¹ := by rw [hl]; field_simp; ring
        rw [hb, Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos hl0,
          ← Real.exp_log (by positivity : (0:ℝ) < (1 - α)⁻¹ ^ m), Real.log_pow, Real.log_inv,
          ← Real.exp_sub]
        congr 1
        have hlog : Real.log l = Real.log α - Real.log (1 - α) := by
          rw [hl, Real.log_div hα.ne' h1α.ne']
        rw [hlog, Real.binEntropy]
        have h2 : Real.log 2 ≠ 0 := by positivity
        field_simp
        simp only [one_div, Real.log_inv] at *
        ring

lemma h_eighth : Real.binEntropy (1 / 8) / Real.log 2 ≤ 7 / 8 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hl2, Real.binEntropy]
  have e1 : Real.log (1 / 8) = -(3 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have e2 : Real.log (1 - 1 / 8) = Real.log 7 - 3 * Real.log 2 := by
    rw [show (1:ℝ) - 1 / 8 = 7 / 2 ^ 3 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  rw [Real.log_inv, Real.log_inv, e1, e2]
  -- 17 log 2 ≤ 7 log 7
  have h : 17 * Real.log 2 ≤ 7 * Real.log 7 := by
    have a := Real.log_pow (2:ℝ) 17
    have b := Real.log_pow (7:ℝ) 7
    push_cast at a b
    rw [← a, ← b]
    exact Real.log_le_log (by norm_num) (by norm_num)
  nlinarith

lemma units_int_eq_of_ne {a b c : ℤˣ} (hab : a ≠ c) (hbc : b ≠ c) : a = b := by
  rcases Int.units_eq_one_or a with ha | ha <;> rcases Int.units_eq_one_or b with hb | hb <;>
    rcases Int.units_eq_one_or c with hc | hc <;> simp_all

theorem solution (d : ℕ) (hd : Even d) (hd2 : 2 ≤ d) :
    ∃ S : Finset (Fin (d / 2) → ℤˣ), (2 : ℝ) ^ ((d : ℝ) / 16) ≤ (S.card : ℝ) ∧
      ∀ σ ∈ S, ∀ σ' ∈ S, σ ≠ σ' →
        (d : ℝ) / 16 ≤ ((Finset.univ.filter (fun i => σ i ≠ σ' i)).card : ℝ) := by
  classical
  set m := d / 2 with hm
  have hdm : (d : ℝ) = 2 * m := by
    obtain ⟨k, hk⟩ := hd
    have : m = k := by omega
    rw [this, hk]; push_cast; ring
  set r : ℝ := (d : ℝ) / 16 with hr
  have hd2' : (2:ℝ) ≤ d := by exact_mod_cast hd2
  have hr0 : 0 < r := by rw [hr]; linarith
  let dist : (Fin m → ℤˣ) → (Fin m → ℤˣ) → ℝ :=
    fun x y => ((Finset.univ.filter (fun i => x i ≠ y i)).card : ℝ)
  have hdist_symm : ∀ x y, dist x y = dist y x := by
    intro x y; simp only [dist]; congr 2; ext i; simp [ne_comm]
  have hdist_self : ∀ x, dist x x = 0 := by intro x; simp [dist]
  let Good : Finset (Fin m → ℤˣ) → Prop := fun S => ∀ σ ∈ S, ∀ σ' ∈ S, σ ≠ σ' → r ≤ dist σ σ'
  obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Finset (Fin m → ℤˣ))).filter Good) Finset.card
    ⟨∅, by simp [Good]⟩
  have hSgood : Good S := (Finset.mem_filter.mp hSmem).2
  -- covering
  have hcover : ∀ x, ∃ s ∈ S, dist x s < r := by
    intro x
    by_contra hcon
    push Not at hcon
    have hxS : x ∉ S := by
      intro hx; have := hcon x hx; rw [hdist_self] at this; linarith
    have hgood' : Good (insert x S) := by
      intro σ hσ σ' hσ' hne
      rcases Finset.mem_insert.mp hσ with rfl | hσS <;> rcases Finset.mem_insert.mp hσ' with rfl | hσ'S
      · exact absurd rfl hne
      · exact hcon σ' hσ'S
      · rw [hdist_symm]; exact hcon σ hσS
      · exact hSgood σ hσS σ' hσ'S hne
    have := hSmax (insert x S) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood'⟩)
    rw [Finset.card_insert_of_notMem hxS] at this
    omega
  -- ball bound
  set Bn : ℝ := ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : ℝ) ≤ (1/8 : ℝ) * m),
    (m.choose j : ℝ) with hBn
  have hball : ∀ s : Fin m → ℤˣ, ((Finset.univ.filter (fun x => dist x s < r)).card : ℝ) ≤ Bn := by
    intro s
    set T := ((Finset.range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : ℝ) ≤ (1/8 : ℝ) * m)).biUnion
      (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin m))) with hT
    have hinj : ((Finset.univ.filter (fun x => dist x s < r)).card) ≤ T.card := by
      apply Finset.card_le_card_of_injOn (fun x => Finset.univ.filter (fun i => x i ≠ s i))
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
        simp only [hT, Finset.coe_biUnion, Finset.coe_filter, Finset.mem_range, Set.mem_iUnion,
          Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and,
          exists_prop]
        refine ⟨_, ⟨?_, ?_⟩, rfl⟩
        · have := Finset.card_le_univ (Finset.univ.filter (fun i => x i ≠ s i))
          simp only [Fintype.card_fin] at this; omega
        · have hx' : ((Finset.univ.filter (fun i => x i ≠ s i)).card : ℝ) < r := hx
          rw [hr, hdm] at hx'; linarith
      · intro x _ y _ hxy
        funext i
        have hi := congrArg (fun D => i ∈ D) hxy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at hi
        by_cases hxi : x i = s i
        · have : y i = s i := by by_contra h; exact absurd hxi (hi.mpr h)
          rw [hxi, this]
        · exact units_int_eq_of_ne hxi (fun h => hxi (by_contra fun h' => (hi.mp h') h))
    calc ((Finset.univ.filter (fun x => dist x s < r)).card : ℝ) ≤ T.card := by exact_mod_cast hinj
      _ ≤ ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : ℝ) ≤ (1/8 : ℝ) * m),
            ((Finset.powersetCard j (Finset.univ : Finset (Fin m))).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = Bn := by
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- counting
  have hcount : (2 : ℝ) ^ m ≤ S.card * Bn := by
    have hsub : (Finset.univ : Finset (Fin m → ℤˣ)) ⊆
        S.biUnion (fun s => Finset.univ.filter (fun x => dist x s < r)) := by
      intro x _
      obtain ⟨s, hs, hxs⟩ := hcover x
      exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxs⟩⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := S) (t := fun s => Finset.univ.filter (fun x => dist x s < r))
    have hcard : (Finset.univ : Finset (Fin m → ℤˣ)).card = 2 ^ m := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_units_int, Fintype.card_fin]
    calc (2 : ℝ) ^ m = ((Finset.univ : Finset (Fin m → ℤˣ)).card : ℝ) := by rw [hcard]; push_cast; ring
      _ ≤ ∑ s ∈ S, ((Finset.univ.filter (fun x => dist x s < r)).card : ℝ) := by
          exact_mod_cast h1.trans h2
      _ ≤ ∑ _s ∈ S, Bn := Finset.sum_le_sum (fun s _ => hball s)
      _ = S.card * Bn := by rw [Finset.sum_const, nsmul_eq_mul]
  have hB : Bn ≤ (2 : ℝ) ^ ((7/8 : ℝ) * m) := by
    refine (ent_bound m (1/8) (by norm_num) (by norm_num)).trans ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := h_eighth
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  refine ⟨S, ?_, fun σ hσ σ' hσ' hne => hSgood σ hσ σ' hσ' hne⟩
  have hBpos : 0 < (2 : ℝ) ^ ((7/8 : ℝ) * m) := by positivity
  have hsplit : (2 : ℝ) ^ m = (2 : ℝ) ^ ((d : ℝ) / 16) * (2 : ℝ) ^ ((7/8 : ℝ) * m) := by
    rw [← Real.rpow_add (by norm_num), hdm, ← Real.rpow_natCast]; congr 1; ring
  have hS0 : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
  have : (2 : ℝ) ^ ((d : ℝ) / 16) * (2 : ℝ) ^ ((7/8 : ℝ) * m) ≤ S.card * (2 : ℝ) ^ ((7/8 : ℝ) * m) := by
    rw [← hsplit]; exact hcount.trans (mul_le_mul_of_nonneg_left hB hS0)
  exact le_of_mul_le_mul_right this hBpos
