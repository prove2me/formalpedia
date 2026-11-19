-- Prove2me | solution 1 for QAOAE3Lin2.General.eq_31
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:18:08.815751+00:00
-- url     : https://prove2.me/submissions/32b16c4e-bcfe-493f-8ca0-3bd9e8bf0a0f

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

open QAOAE3Lin2.General

private lemma spin_sq {n : ℕ} (x : QAlgorithms.Qubits n) (q : Fin n) : spin x q * spin x q = 1 := by
  simp only [spin]
  cases x q <;> norm_num

private lemma avgZ_const {n : ℕ} (c : ℝ) : avgZ (fun _ : QAlgorithms.Qubits n => c) = c := by
  simp only [avgZ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (QAlgorithms.Qubits n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

private lemma avgZ_add {n : ℕ} (f g : QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => f x + g x) = avgZ f + avgZ g := by
  simp only [avgZ, Finset.sum_add_distrib, mul_add]

private lemma avgZ_smul {n : ℕ} (c : ℝ) (f : QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => c * f x) = c * avgZ f := by
  simp only [avgZ, ← Finset.mul_sum]
  ring

private lemma avgZ_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, avgZ (f j) := by
  simp only [avgZ, Finset.sum_comm (s := Finset.univ) (t := s), Finset.mul_sum]

private lemma prod_spin_symmDiff {n : ℕ} (A B : Finset (Fin n)) (x : QAlgorithms.Qubits n) :
    (∏ q ∈ A, spin x q) * (∏ q ∈ B, spin x q) = ∏ q ∈ symmDiff A B, spin x q := by
  have hA : A = (A \ B) ∪ (A ∩ B) := by ext q; simp [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hB : B = (B \ A) ∪ (A ∩ B) := by ext q; simp [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hdA : Disjoint (A \ B) (A ∩ B) := Finset.disjoint_left.mpr fun q h1 h2 =>
    (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2
  have hdB : Disjoint (B \ A) (A ∩ B) := Finset.disjoint_left.mpr fun q h1 h2 =>
    (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).1
  have hAB : symmDiff A B = (A \ B) ∪ (B \ A) := by
    ext q; simp [Finset.mem_symmDiff, Finset.mem_sdiff]
  have hdAB : Disjoint (A \ B) (B \ A) := Finset.disjoint_left.mpr fun q h1 h2 =>
    (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
  have hAB_prod : (∏ q ∈ A, spin x q) * (∏ q ∈ B, spin x q) =
      (∏ q ∈ (A \ B) ∪ (A ∩ B), spin x q) * (∏ q ∈ (B \ A) ∪ (A ∩ B), spin x q) := by
    rw [← hA, ← hB]
  rw [hAB_prod, Finset.prod_union hdA, Finset.prod_union hdB]
  have hsq : (∏ q ∈ A ∩ B, spin x q) * (∏ q ∈ A ∩ B, spin x q) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun q _ => spin_sq x q
  calc ((∏ q ∈ A \ B, spin x q) * ∏ q ∈ A ∩ B, spin x q) *
        ((∏ q ∈ B \ A, spin x q) * ∏ q ∈ A ∩ B, spin x q)
      = (∏ q ∈ A \ B, spin x q) * (∏ q ∈ B \ A, spin x q) *
          ((∏ q ∈ A ∩ B, spin x q) * ∏ q ∈ A ∩ B, spin x q) := by ring
    _ = (∏ q ∈ A \ B, spin x q) * (∏ q ∈ B \ A, spin x q) := by rw [hsq, mul_one]
    _ = ∏ q ∈ symmDiff A B, spin x q := by rw [hAB, Finset.prod_union hdAB]

private lemma avgZ_prod_spin {n : ℕ} (T : Finset (Fin n)) :
    avgZ (fun x => ∏ q ∈ T, spin x q) = if T = ∅ then 1 else 0 := by
  by_cases hT : T = ∅
  · subst hT
    simp only [Finset.prod_empty, ↓reduceIte]
    exact avgZ_const 1
  · simp only [if_neg hT]
    obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    let flip : QAlgorithms.Qubits n → QAlgorithms.Qubits n := fun x q =>
      if q = q₀ then !(x q₀) else x q
    have hflip_inv : Function.Involutive flip := by
      intro x; ext q
      by_cases h : q = q₀ <;> simp [flip, h]
    have hflip_neg : ∀ x : QAlgorithms.Qubits n,
        (∏ q ∈ T, spin (flip x) q) = -(∏ q ∈ T, spin x q) := by
      intro x
      rw [← Finset.mul_prod_erase T _ hq₀, ← Finset.mul_prod_erase T _ hq₀]
      have h0 : spin (flip x) q₀ = -spin x q₀ := by
        simp only [spin, flip, ↓reduceIte]
        cases x q₀ <;> norm_num
      have hrest : ∏ q ∈ T.erase q₀, spin (flip x) q = ∏ q ∈ T.erase q₀, spin x q := by
        refine Finset.prod_congr rfl fun q hq => ?_
        have hne : q ≠ q₀ := (Finset.mem_erase.mp hq).1
        simp [spin, flip, hne]
      rw [h0, hrest, neg_mul]
    have hsum_eq : ∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin (flip x) q) =
        ∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin x q) :=
      Fintype.sum_equiv hflip_inv.toPerm _ _ fun _ => rfl
    have hsum_neg : ∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin (flip x) q) =
        -∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin x q) := by
      simp_rw [hflip_neg, Finset.sum_neg_distrib]
    have hsum0 : ∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin x q) = 0 := by linarith
    simp [avgZ, hsum0]

private lemma avgZ_prod_spin_mul {n : ℕ} (A B : Finset (Fin n)) :
    avgZ (fun x => (∏ q ∈ A, spin x q) * (∏ q ∈ B, spin x q)) = if A = B then 1 else 0 := by
  simp_rw [prod_spin_symmDiff, avgZ_prod_spin]
  by_cases h : A = B
  · subst h; simp
  · have hs : symmDiff A B ≠ ∅ := by
      intro heq
      exact h (Finset.symmDiff_eq_empty.mp heq)
    simp [h, hs]

private def tripleSet {n : ℕ} (t : Fin n × Fin n × Fin n) : Finset (Fin n) :=
  {t.1, t.2.1, t.2.2}

private lemma mem_tripleSet_iff {n : ℕ} (t : Fin n × Fin n × Fin n) (v : Fin n) :
    v ∈ tripleSet t ↔ onTriple t v := by
  simp [tripleSet, onTriple, Finset.mem_insert, Finset.mem_singleton]

private lemma tripleSet_inj {n : ℕ} (t₁ t₂ : Fin n × Fin n × Fin n)
    (ht₁ : t₁.1 < t₁.2.1 ∧ t₁.2.1 < t₁.2.2)
    (ht₂ : t₂.1 < t₂.2.1 ∧ t₂.2.1 < t₂.2.2)
    (heq : tripleSet t₁ = tripleSet t₂) : t₁ = t₂ := by
  have h12 : ∀ v, v ∈ tripleSet t₁ ↔ v ∈ tripleSet t₂ := fun v => by rw [heq]
  have ha1 : t₁.1 ∈ tripleSet t₂ := (h12 t₁.1).mp (by simp [tripleSet])
  have hb1 : t₂.1 ∈ tripleSet t₁ := (h12 t₂.1).mpr (by simp [tripleSet])
  have ha1_le : t₂.1 ≤ t₁.1 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at ha1
    rcases ha1 with h | h | h <;> omega
  have hb1_le : t₁.1 ≤ t₂.1 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at hb1
    rcases hb1 with h | h | h <;> omega
  have hfst : t₁.1 = t₂.1 := le_antisymm hb1_le ha1_le
  have ha2 : t₁.2.1 ∈ tripleSet t₂ := (h12 t₁.2.1).mp (by simp [tripleSet])
  have hb2 : t₂.2.1 ∈ tripleSet t₁ := (h12 t₂.2.1).mpr (by simp [tripleSet])
  have ha2_le : t₂.2.1 ≤ t₁.2.1 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at ha2
    rcases ha2 with h | h | h <;> omega
  have hb2_le : t₁.2.1 ≤ t₂.2.1 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at hb2
    rcases hb2 with h | h | h <;> omega
  have hsnd : t₁.2.1 = t₂.2.1 := le_antisymm hb2_le ha2_le
  have ha3 : t₁.2.2 ∈ tripleSet t₂ := (h12 t₁.2.2).mp (by simp [tripleSet])
  have hb3 : t₂.2.2 ∈ tripleSet t₁ := (h12 t₂.2.2).mpr (by simp [tripleSet])
  have ha3_eq : t₁.2.2 = t₂.2.2 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at ha3 hb3
    rcases ha3 with h | h | h <;> rcases hb3 with g | g | g <;> omega
  ext <;> simp [hfst, hsnd, ha3_eq]

private lemma prod_tripleSet_mul_spin {n : ℕ} (t : Fin n × Fin n × Fin n)
    (ht : t.1 < t.2.1 ∧ t.2.1 < t.2.2) (v : Fin n) (hv : onTriple t v) (x : QAlgorithms.Qubits n) :
    spin x t.1 * spin x t.2.1 * spin x t.2.2 * spin x v =
      ∏ q ∈ (tripleSet t).erase v, spin x q := by
  have h12 : t.1 ≠ t.2.1 := ne_of_lt ht.1
  have h13 : t.1 ≠ t.2.2 := ne_of_lt (ht.1.trans ht.2)
  have h23 : t.2.1 ≠ t.2.2 := ne_of_lt ht.2
  have hprod : ∏ q ∈ tripleSet t, spin x q = spin x t.1 * spin x t.2.1 * spin x t.2.2 := by
    rw [tripleSet, Finset.prod_insert (by simp [h12, h13]), Finset.prod_insert (by simp [h23]),
      Finset.prod_singleton]
    ring
  have hv_mem : v ∈ tripleSet t := (mem_tripleSet_iff t v).mpr hv
  rw [← hprod, ← Finset.mul_prod_erase (tripleSet t) _ hv_mem]
  calc (spin x v * ∏ q ∈ (tripleSet t).erase v, spin x q) * spin x v
      = (spin x v * spin x v) * ∏ q ∈ (tripleSet t).erase v, spin x q := by ring
    _ = ∏ q ∈ (tripleSet t).erase v, spin x q := by rw [spin_sq, one_mul]

private lemma roleBit_onTriple {n : ℕ} (t : Fin n × Fin n × Fin n) (r : Fin 3) :
    onTriple t (roleBit t r) := by
  fin_cases r <;> simp [roleBit, onTriple]

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (htri : IsTripleFamily tri) (hocc : BoundedOccurrence tri D) (i : Fin m) (r : Fin 3) :
    avgZ (fun x => cPoly tri rhs i r x ^ 2) = (termCount tri i r : ℝ) ∧
      termCount tri i r ≤ D := by
  let v := roleBit (tri i) r
  let S : Finset (Fin m) := Finset.univ.filter (fun j => sharesOnly tri i j r)
  have hcard : S.card = termCount tri i r := by
    simp only [termCount, S]
  have hcPoly : ∀ x, cPoly tri rhs i r x =
      ∑ j ∈ S, sgn rhs j * ∏ q ∈ (tripleSet (tri j)).erase v, spin x q := by
    intro x
    simp only [cPoly, Finset.sum_filter, S]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rw [prod_tripleSet_mul_spin (tri j) (htri.1 j) v hj.2.1 x]
    · rfl
  have hpart1 : avgZ (fun x => cPoly tri rhs i r x ^ 2) = (termCount tri i r : ℝ) := by
    have hsq : ∀ x, cPoly tri rhs i r x ^ 2 =
        ∑ j₁ ∈ S, ∑ j₂ ∈ S,
          (sgn rhs j₁ * sgn rhs j₂) *
            ((∏ q ∈ (tripleSet (tri j₁)).erase v, spin x q) *
              (∏ q ∈ (tripleSet (tri j₂)).erase v, spin x q)) := by
      intro x
      rw [hcPoly x, sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₂ _ => ?_
      ring
    simp_rw [hsq, avgZ_sum, avgZ_smul, avgZ_prod_spin_mul]
    rw [← hcard]
    have hdiag : ∀ j₁ ∈ S,
        (∑ j₂ ∈ S, (sgn rhs j₁ * sgn rhs j₂) *
          if (tripleSet (tri j₁)).erase v = (tripleSet (tri j₂)).erase v then (1 : ℝ) else 0) = 1 := by
      intro j₁ hj₁
      have hv₁ : v ∈ tripleSet (tri j₁) :=
        (mem_tripleSet_iff (tri j₁) v).mpr (Finset.mem_filter.mp hj₁).2.2.1
      have huniq : ∀ j₂ ∈ S,
          ((tripleSet (tri j₁)).erase v = (tripleSet (tri j₂)).erase v) ↔ j₁ = j₂ := by
        intro j₂ hj₂
        constructor
        · intro heq
          have hv₂ : v ∈ tripleSet (tri j₂) :=
            (mem_tripleSet_iff (tri j₂) v).mpr (Finset.mem_filter.mp hj₂).2.2.1
          have hset : tripleSet (tri j₁) = tripleSet (tri j₂) := by
            rw [← Finset.insert_erase hv₁, ← Finset.insert_erase hv₂, heq]
          exact htri.2 (tripleSet_inj (tri j₁) (tri j₂) (htri.1 j₁) (htri.1 j₂) hset)
        · rintro rfl; rfl
      have hterm : ∀ j₂ ∈ S,
          (sgn rhs j₁ * sgn rhs j₂) *
            (if (tripleSet (tri j₁)).erase v = (tripleSet (tri j₂)).erase v then (1 : ℝ) else 0) =
          if j₂ = j₁ then 1 else 0 := by
        intro j₂ hj₂
        simp_rw [huniq j₂ hj₂]
        by_cases heq : j₂ = j₁
        · subst heq
          simp only [↓reduceIte, mul_one]
          simp only [sgn]
          cases rhs j₂ <;> norm_num
        · have heq' : j₁ ≠ j₂ := Ne.symm heq
          simp [heq, heq']
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hj₁]
    rw [Finset.sum_congr rfl hdiag, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine ⟨hpart1, ?_⟩
  let A : Finset (Fin m) := Finset.univ.filter (fun j => onTriple (tri j) v)
  have hiA : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ i, roleBit_onTriple (tri i) r⟩
  have hsub : S ⊆ A.erase i := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact Finset.mem_erase.mpr ⟨hj'.1, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj'.2.1⟩⟩
  have hA_le : A.card ≤ D + 1 := by
    simpa [A] using hocc v
  have hS_le : S.card ≤ A.card - 1 := by
    calc S.card ≤ (A.erase i).card := Finset.card_le_card hsub
      _ = A.card - 1 := Finset.card_erase_of_mem hiA
  rw [← hcard]
  omega
