-- Prove2me | solution 1 for ProcureAssort.Hotelling.Supplement.theorem_H_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:45:12.688499+00:00
-- url     : https://prove2.me/submissions/6bbb87a6-5399-4224-8a57-3e1df2322f5c

import Definitions.Def_ProcureAssort_Hotelling_Supplement_CommonHotelling

open ProcureAssort
open ProcureAssort.Hotelling
open ProcureAssort.Hotelling.Supplement

theorem solution (n : ℕ) (hn : 2 ≤ n) (S : Finset ℝ) (f : ℝ → ℝ)
    (hTypes : ValidTypes (fun _ : Fin n => S) (fun _ => f))
    (hReg : Regular (fun _ : Fin n => S) (fun _ => f)) (delta : ℝ) (hdelta : 0 < delta) :
    optDecLin (fun _ : Fin n => S) (fun _ => f) (hotGCS (equiLoc n) delta) (simplex n) =
      optCent (fun _ : Fin n => S) (fun _ => f) (hotGCS (equiLoc n) delta) (simplex n) ∧
    ValuesWellDefined (fun _ : Fin n => S) (fun _ => f) (hotGCS (equiLoc n) delta) := by
      classical
      have hA1 : ∀ (ℓ : Fin n → ℝ) (_ : StrictMono ℓ) (_ : ∀ i, 0 ≤ ℓ i) (_ : ∀ i, ℓ i ≤ 1) (v : Fin n → ℝ),
       ∃ (Q : Finset (Fin n)) (B : ℕ → ℝ),
        (∀ i, i ∈ Q ↔ ∀ j, j ≠ i → v i < v j + delta * |ℓ i - ℓ j|) ∧
        (∀ m : ℕ, (∀ j ∈ Q, m ≤ j.val) → B m = 0) ∧
        (∀ m : ℕ, (∀ j ∈ Q, j.val < m) → Q.Nonempty → B m = 1) ∧
        (∀ (m : ℕ) (p r : Fin n), p ∈ Q → r ∈ Q → p.val < m → m ≤ r.val → (∀ j ∈ Q, j ≤ p ∨ r ≤ j) →
            B m = (ℓ p + ℓ r)/2 + (v r - v p)/(2*delta)) ∧
        (∀ i : Fin n, i ∉ Q → B (i.val+1) = B i.val) ∧
        (∀ i : Fin n, i ∈ Q → B i.val < B (i.val+1)) ∧ B 0 = 0 ∧ B n = 1 ∧
        (∀ i : Fin n, i ∈ Q → ∀ u, B i.val ≤ u → u ≤ B (i.val+1) → ∀ j, v i + delta * |u - ℓ i| ≤ v j + delta * |u - ℓ j|) := by
        clear hTypes hReg
        intro ℓ hℓ hℓ0 hℓ1 v
        classical
        set Q : Finset (Fin n) := Finset.univ.filter (fun i => ∀ j, j ≠ i → v i < v j + delta * |ℓ i - ℓ j|) with hQdef
        have hQ : ∀ i, i ∈ Q ↔ ∀ j, j ≠ i → v i < v j + delta * |ℓ i - ℓ j| := by
          intro i; simp [hQdef]
        let B' : Finset (Fin n) → Finset (Fin n) → ℝ := fun L R =>
          if hL : L.Nonempty then (if hR : R.Nonempty then
            (ℓ (L.max' hL) + ℓ (R.min' hR))/2 + (v (R.min' hR) - v (L.max' hL))/(2*delta) else 1) else 0
        obtain ⟨LL, hLL⟩ : ∃ LL : ℕ → Finset (Fin n), ∀ m j, j ∈ LL m ↔ j ∈ Q ∧ j.val < m :=
          ⟨fun m => Q.filter (fun j => j.val < m), fun m j => Finset.mem_filter⟩
        obtain ⟨RR, hRR⟩ : ∃ RR : ℕ → Finset (Fin n), ∀ m j, j ∈ RR m ↔ j ∈ Q ∧ m ≤ j.val :=
          ⟨fun m => Q.filter (fun j => m ≤ j.val), fun m j => Finset.mem_filter⟩
        let B : ℕ → ℝ := fun m => B' (LL m) (RR m)
        have hdom : ∀ j, ∃ k ∈ Q, v k + delta * |ℓ j - ℓ k| ≤ v j := by
          intro j
          obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image
            (Finset.univ.filter (fun k => v k + delta * |ℓ j - ℓ k| ≤ v j)) v ⟨j, by simp⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hmin
          refine ⟨k, ?_, hk⟩
          rw [hQ]
          intro m hm
          by_contra hcon
          push Not at hcon
          have hpos : 0 < delta * |ℓ k - ℓ m| :=
            mul_pos hdelta (abs_pos.mpr (sub_ne_zero.mpr (fun h => hm (hℓ.injective h).symm)))
          have htri : delta * |ℓ j - ℓ m| ≤ delta * |ℓ j - ℓ k| + delta * |ℓ k - ℓ m| := by
            rw [← mul_add]; exact mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) hdelta.le
          have := hmin m (by linarith)
          linarith
        have hQne : Q.Nonempty := by
          obtain ⟨k, hk, _⟩ := hdom ⟨0, by omega⟩
          exact ⟨k, hk⟩
        have s0 : ∀ m : ℕ, (∀ j ∈ Q, m ≤ j.val) → B m = 0 := by
          intro m h
          have : ¬ (LL m).Nonempty := by
            rintro ⟨j, hj⟩
            rw [hLL] at hj
            have := h j hj.1; omega
          simp only [B, B']; rw [dif_neg this]
        have s1 : ∀ m : ℕ, (∀ j ∈ Q, j.val < m) → Q.Nonempty → B m = 1 := by
          intro m h ⟨p, hp⟩
          have h1 : (LL m).Nonempty := ⟨p, (hLL m p).mpr ⟨hp, h p hp⟩⟩
          have h2 : ¬ (RR m).Nonempty := by
            rintro ⟨j, hj⟩
            rw [hRR] at hj
            have := h j hj.1; omega
          simp only [B, B']; rw [dif_pos h1, dif_neg h2]
        have hmaxA : ∀ (A : Finset (Fin n)) (p : Fin n) (h : A.Nonempty), p ∈ A → (∀ y ∈ A, y ≤ p) → A.max' h = p :=
          fun A p h hp hA => le_antisymm (A.max'_le h p hA) (A.le_max' p hp)
        have hminA : ∀ (A : Finset (Fin n)) (p : Fin n) (h : A.Nonempty), p ∈ A → (∀ y ∈ A, p ≤ y) → A.min' h = p :=
          fun A p h hp hA => le_antisymm (A.min'_le p hp) (A.le_min' h p hA)
        have s2 : ∀ (m : ℕ) (p r : Fin n), p ∈ Q → r ∈ Q → p.val < m → m ≤ r.val → (∀ j ∈ Q, j ≤ p ∨ r ≤ j) →
              B m = (ℓ p + ℓ r)/2 + (v r - v p)/(2*delta) := by
          intro m p r hp hr hpm hmr hno
          have hp' : p ∈ LL m := (hLL m p).mpr ⟨hp, hpm⟩
          have hr' : r ∈ RR m := (hRR m r).mpr ⟨hr, hmr⟩
          have g1 : ∀ y ∈ LL m, y ≤ p := by
            intro y hy
            rw [hLL] at hy
            rcases hno y hy.1 with h | h
            · exact h
            · have := Fin.le_def.mp h; omega
          have g2 : ∀ y ∈ RR m, r ≤ y := by
            intro y hy
            rw [hRR] at hy
            rcases hno y hy.1 with h | h
            · have := Fin.le_def.mp h; omega
            · exact h
          simp only [B, B']
          have n1 : (LL m).Nonempty := ⟨p, hp'⟩
          have n2 : (RR m).Nonempty := ⟨r, hr'⟩
          rw [dif_pos n1, dif_pos n2, hmaxA _ p _ hp' g1, hminA _ r _ hr' g2]
        have hnot : ∀ i : Fin n, i ∉ Q → B (i.val+1) = B i.val := by
          intro i hi
          have e1 : LL (i.val + 1) = LL i.val := by
            ext j
            rw [hLL, hLL]
            refine and_congr_right (fun hj => ?_)
            have : j.val ≠ i.val := fun h => hi (Fin.ext h ▸ hj)
            omega
          have e2 : RR (i.val + 1) = RR i.val := by
            ext j
            rw [hRR, hRR]
            refine and_congr_right (fun hj => ?_)
            have : j.val ≠ i.val := fun h => hi (Fin.ext h ▸ hj)
            omega
          simp only [B]; rw [e1, e2]
        -- right neighbour
        have hright : ∀ i ∈ Q, ((∀ j ∈ Q, j ≤ i) ∧ B (i.val+1) = 1) ∨
            ∃ r ∈ Q, i < r ∧ (∀ j ∈ Q, j ≤ i ∨ r ≤ j) ∧ B (i.val+1) = (ℓ i + ℓ r)/2 + (v r - v i)/(2*delta) := by
          intro i hi
          by_cases h : (Q.filter (fun j => i < j)).Nonempty
          · right
            have hm := Finset.min'_mem _ h
            have hmin : ∀ j ∈ Q, i < j → (Q.filter (fun j => i < j)).min' h ≤ j := fun j hj hij =>
              Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hj, hij⟩)
            generalize (Q.filter (fun j => i < j)).min' h = r at hm hmin
            rw [Finset.mem_filter] at hm
            have hno : ∀ j ∈ Q, j ≤ i ∨ r ≤ j := fun j hj => by
              rcases le_or_gt j i with h | h
              · exact Or.inl h
              · exact Or.inr (hmin j hj h)
            refine ⟨r, hm.1, hm.2, hno, s2 _ i r hi hm.1 (by omega) ?_ hno⟩
            have := Fin.lt_def.mp hm.2; omega
          · left
            have hall : ∀ j ∈ Q, j ≤ i := fun j hj => by
              by_contra hc
              exact h ⟨j, Finset.mem_filter.mpr ⟨hj, not_le.mp hc⟩⟩
            exact ⟨hall, s1 _ (fun j hj => by have := Fin.le_def.mp (hall j hj); omega) hQne⟩
        have hleft : ∀ i ∈ Q, ((∀ j ∈ Q, i ≤ j) ∧ B i.val = 0) ∨
            ∃ p ∈ Q, p < i ∧ (∀ j ∈ Q, j ≤ p ∨ i ≤ j) ∧ B i.val = (ℓ p + ℓ i)/2 + (v i - v p)/(2*delta) := by
          intro i hi
          by_cases h : (Q.filter (fun j => j < i)).Nonempty
          · right
            have hm := Finset.max'_mem _ h
            have hmax : ∀ j ∈ Q, j < i → j ≤ (Q.filter (fun j => j < i)).max' h := fun j hj hij =>
              Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hj, hij⟩)
            generalize (Q.filter (fun j => j < i)).max' h = r at hm hmax
            rw [Finset.mem_filter] at hm
            have hno : ∀ j ∈ Q, j ≤ r ∨ i ≤ j := fun j hj => by
              rcases le_or_gt i j with h | h
              · exact Or.inr h
              · exact Or.inl (hmax j hj h)
            exact ⟨r, hm.1, hm.2, hno, s2 _ r i hm.1 hi (Fin.lt_def.mp hm.2) le_rfl hno⟩
          · left
            have hall : ∀ j ∈ Q, i ≤ j := fun j hj => by
              by_contra hc
              exact h ⟨j, Finset.mem_filter.mpr ⟨hj, not_le.mp hc⟩⟩
            exact ⟨hall, s0 _ (fun j hj => Fin.le_def.mp (hall j hj))⟩
        have hgap : ∀ i ∈ Q, ∀ j, i < j → v i - v j < delta * (ℓ j - ℓ i) := by
          intro i hi j hij
          have h1 := (hQ i).mp hi j (ne_of_gt hij)
          have h2 := hℓ hij
          rw [abs_sub_comm, abs_of_pos (by linarith)] at h1
          linarith
        have hgap' : ∀ i ∈ Q, ∀ j, j < i → v i - v j < delta * (ℓ i - ℓ j) := by
          intro i hi j hij
          have h1 := (hQ i).mp hi j (ne_of_lt hij)
          have h2 := hℓ hij
          rw [abs_of_pos (by linarith)] at h1
          linarith
        have hR' : ∀ i ∈ Q, B (i.val+1) = 1 ∨ ℓ i < B (i.val+1) := by
          intro i hi
          rcases hright i hi with ⟨_, h⟩ | ⟨r, hr, hir, _, h⟩
          · exact Or.inl h
          · right
            rw [h]
            have := hgap i hi r hir
            have h3 : (v i - v r)/(2*delta) < (ℓ r - ℓ i)/2 := by
              rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
            have h4 : (v r - v i)/(2*delta) = -((v i - v r)/(2*delta)) := by ring
            linarith
        have hL' : ∀ i ∈ Q, B i.val = 0 ∨ B i.val < ℓ i := by
          intro i hi
          rcases hleft i hi with ⟨_, h⟩ | ⟨r, hr, hir, _, h⟩
          · exact Or.inl h
          · right
            rw [h]
            have := hgap' i hi r hir
            have h3 : (v i - v r)/(2*delta) < (ℓ i - ℓ r)/2 := by
              rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
            linarith
        refine ⟨Q, B, hQ, s0, s1, s2, hnot, ?_, s0 0 (fun j _ => Nat.zero_le _), s1 n (fun j _ => j.2) hQne, ?_⟩
        · intro i hi
          have a1 := hℓ0 i
          have a2 := hℓ1 i
          rcases hR' i hi with h | h <;> rcases hL' i hi with h' | h' <;> linarith
        · intro i hi u hu1 hu2
          have hkey : ∀ j ∈ Q, v i + delta * |u - ℓ i| ≤ v j + delta * |u - ℓ j| := by
            intro j hj
            rcases lt_trichotomy i j with hij | hij | hij
            · rcases hright i hi with ⟨h, _⟩ | ⟨r, hr, hir, hno, h⟩
              · exact absurd (h j hj) (not_le.mpr hij)
              · have hrj : r ≤ j := by
                  rcases hno j hj with h | h
                  · exact absurd h (not_le.mpr hij)
                  · exact h
                have h5 : v r - v j ≤ delta * (ℓ j - ℓ r) := by
                  rcases hrj.lt_or_eq with h | h
                  · exact (hgap r hr j h).le
                  · rw [h]; simp
                have h6 : 2 * delta * u ≤ delta * (ℓ i + ℓ r) + (v r - v i) := by
                  have : 2 * delta * u ≤ 2 * delta * ((ℓ i + ℓ r)/2 + (v r - v i)/(2*delta)) :=
                    mul_le_mul_of_nonneg_left (by rw [← h]; exact hu2) (by positivity)
                  have e : 2 * delta * ((ℓ i + ℓ r)/2 + (v r - v i)/(2*delta)) = delta * (ℓ i + ℓ r) + (v r - v i) := by
                    field_simp
                  linarith
                have h7 : delta * (ℓ j - u) ≤ delta * |u - ℓ j| :=
                  mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact le_abs_self _) hdelta.le
                have h8 := hgap i hi j hij
                rcases le_total (ℓ i) u with hc | hc
                · rw [abs_of_nonneg (by linarith : 0 ≤ u - ℓ i)]
                  linarith
                · rw [abs_of_nonpos (by linarith : u - ℓ i ≤ 0)]
                  linarith
            · rw [hij]
            · rcases hleft i hi with ⟨h, _⟩ | ⟨r, hr, hir, hno, h⟩
              · exact absurd (h j hj) (not_le.mpr hij)
              · have hrj : j ≤ r := by
                  rcases hno j hj with h | h
                  · exact h
                  · exact absurd h (not_le.mpr hij)
                have h5 : v r - v j ≤ delta * (ℓ r - ℓ j) := by
                  rcases hrj.lt_or_eq with h | h
                  · exact (hgap' r hr j h).le
                  · rw [h]; simp
                have h6 : delta * (ℓ r + ℓ i) + (v i - v r) ≤ 2 * delta * u := by
                  have : 2 * delta * ((ℓ r + ℓ i)/2 + (v i - v r)/(2*delta)) ≤ 2 * delta * u :=
                    mul_le_mul_of_nonneg_left (by rw [← h]; exact hu1) (by positivity)
                  have e : 2 * delta * ((ℓ r + ℓ i)/2 + (v i - v r)/(2*delta)) = delta * (ℓ r + ℓ i) + (v i - v r) := by
                    field_simp
                  linarith
                have h7 : delta * (u - ℓ j) ≤ delta * |u - ℓ j| :=
                  mul_le_mul_of_nonneg_left (le_abs_self _) hdelta.le
                have h8 := hgap' i hi j hij
                rcases le_total (ℓ i) u with hc | hc
                · rw [abs_of_nonneg (by linarith : 0 ≤ u - ℓ i)]
                  linarith
                · rw [abs_of_nonpos (by linarith : u - ℓ i ≤ 0)]
                  linarith
          intro j
          obtain ⟨k, hk, hkj⟩ := hdom j
          have h1 := hkey k hk
          have h2 : delta * |u - ℓ k| ≤ delta * |u - ℓ j| + delta * |ℓ j - ℓ k| := by
            rw [← mul_add]; exact mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) hdelta.le
          linarith
      have hA2 : ∀ (ℓ : Fin n → ℝ) (v : Fin n → ℝ)
       (Q : Finset (Fin n)) (B : ℕ → ℝ) (_ : B 0 = 0) (_ : B n = 1)
       (_ : ∀ i : Fin n, i ∉ Q → B (i.val+1) = B i.val)
       (_ : ∀ i : Fin n, i ∈ Q → B i.val < B (i.val+1))
       (_ : ∀ i : Fin n, i ∈ Q → ∀ u, B i.val ≤ u → u ≤ B (i.val+1) → ∀ j, v i + delta * |u - ℓ i| ≤ v j + delta * |u - ℓ j|),
       (fun i : Fin n => B (i.val+1) - B i.val) ∈ simplex n ∧ ∀ y ∈ simplex n, CS (hotGCS ℓ delta) y v ≤ CS (hotGCS ℓ delta) (fun i : Fin n => B (i.val+1) - B i.val) v := by
        clear hTypes hReg hA1
        intro ℓ v Q B hB0 hBn hnot hin hkey
        classical
        have hBmono : ∀ i : Fin n, B i.val ≤ B (i.val+1) := by
          intro i
          by_cases h : i ∈ Q
          · exact (hin i h).le
          · exact (hnot i h).ge
        have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
        let h : ℝ → ℝ := fun u => Finset.univ.inf' hne (fun j : Fin n => v j + delta * |u - ℓ j|)
        have hhc : Continuous h := by
          refine Continuous.finset_inf'_apply hne (fun j _ => ?_)
          fun_prop
        have hhle : ∀ u j, h u ≤ v j + delta * |u - ℓ j| := fun u j =>
          Finset.inf'_le (fun j : Fin n => v j + delta * |u - ℓ j|) (Finset.mem_univ j)
        have hheq : ∀ u i, (∀ j, v i + delta * |u - ℓ i| ≤ v j + delta * |u - ℓ j|) → h u = v i + delta * |u - ℓ i| := by
          intro u i hi
          exact le_antisymm (hhle u i) (Finset.le_inf' hne _ (fun j _ => hi j))
        -- CS formula
        have hform : ∀ (P : ℕ → ℝ) (y : Fin n → ℝ), P 0 = 0 → (∀ i : Fin n, y i = P (i.val+1) - P i.val) →
            CS (hotGCS ℓ delta) y v = - ∑ i : Fin n, ∫ u in (P i.val)..(P (i.val+1)), (v i + delta * |u - ℓ i|) := by
          intro P y hP0 hy
          have hsum : ∀ m : ℕ, m ≤ n → ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < m), y k = P m := by
            intro m hm
            induction m with
            | zero => simp [hP0]
            | succ m ih =>
              have e : Finset.univ.filter (fun k : Fin n => k.val < m+1) =
                  insert (⟨m, by omega⟩ : Fin n) (Finset.univ.filter (fun k : Fin n => k.val < m)) := by
                ext k
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
                omega
              rw [e, Finset.sum_insert (by simp), ih (by omega), hy]
              simp
          have e1 : ∀ i : Fin n, ∑ k ∈ Finset.univ.filter (· < i), y k = P i.val := fun i => hsum i.val i.2.le
          have e2 : ∀ i : Fin n, ∑ k ∈ Finset.univ.filter (· ≤ i), y k = P (i.val+1) := by
            intro i
            rw [← hsum (i.val+1) i.2]
            apply Finset.sum_congr _ (fun _ _ => rfl)
            ext k
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]; omega
          unfold CS hotGCS
          simp only [e1, e2]
          rw [Finset.mul_sum, sub_eq_add_neg, ← neg_add, ← Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
            intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hy i, smul_eq_mul]
          ring
        have hadj : ∀ P : ℕ → ℝ, P 0 = 0 → P n = 1 →
            ∑ i : Fin n, ∫ u in (P i.val)..(P (i.val+1)), h u = ∫ u in (0:ℝ)..1, h u := by
          intro P h0 h1
          rw [Fin.sum_univ_eq_sum_range (fun i => ∫ u in (P i)..(P (i+1)), h u) n,
            intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hhc.intervalIntegrable _ _), h0, h1]
        refine ⟨⟨fun i => sub_nonneg.mpr (hBmono i), ?_⟩, ?_⟩
        · rw [Fin.sum_univ_eq_sum_range (fun i => B (i+1) - B i) n, Finset.sum_range_sub, hB0, hBn, sub_zero]
        · intro y hy
          rw [hform B _ hB0 (fun i => rfl)]
          let P : ℕ → ℝ := fun m => ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < m), y k
          have hP0 : P 0 = 0 := by simp [P]
          have hPn : P n = 1 := by
            simp only [P]
            rw [Finset.filter_true_of_mem (fun k _ => k.2)]
            exact hy.2
          have hPs : ∀ i : Fin n, y i = P (i.val+1) - P i.val := by
            intro i
            have e : Finset.univ.filter (fun k : Fin n => k.val < i.val+1) =
                  insert i (Finset.univ.filter (fun k : Fin n => k.val < i.val)) := by
                ext k
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
                omega
            simp only [P]
            rw [e, Finset.sum_insert (by simp)]
            ring
          rw [hform P y hP0 hPs]
          have h1 : ∑ i : Fin n, ∫ u in (B i.val)..(B (i.val+1)), (v i + delta * |u - ℓ i|) = ∫ u in (0:ℝ)..1, h u := by
            rw [← hadj B hB0 hBn]
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i ∈ Q
            · apply intervalIntegral.integral_congr
              intro u hu
              rw [Set.uIcc_of_le (hBmono i)] at hu
              exact (hheq u i (hkey i hi u hu.1 hu.2)).symm
            · rw [hnot i hi]; simp
          have h2 : ∫ u in (0:ℝ)..1, h u ≤ ∑ i : Fin n, ∫ u in (P i.val)..(P (i.val+1)), (v i + delta * |u - ℓ i|) := by
            rw [← hadj P hP0 hPn]
            apply Finset.sum_le_sum
            intro i _
            apply intervalIntegral.integral_mono_on
            · have := hy.1 i
              rw [hPs i] at this; linarith
            · exact hhc.intervalIntegrable _ _
            · apply Continuous.intervalIntegrable; fun_prop
            · intro u _; exact hhle u i
          linarith
      have hA3 : ∀ v : Fin n → ℝ, ∃ x : Fin n → ℝ, x ∈ simplex n ∧
        (∀ y ∈ simplex n, CS (hotGCS (equiLoc n) delta) y v ≤ CS (hotGCS (equiLoc n) delta) x v) ∧
        (∀ i j, j ≠ i → v j + delta / (n-1:ℕ) * |(i.val:ℝ) - j.val| ≤ v i → x i = 0) ∧
        (∀ i, (∀ j, j ≠ i → v i < v j + delta / (n-1:ℕ) * |(i.val:ℝ) - j.val|) → 0 < x i) ∧
        ((∀ i j, v i - v j < delta / (n-1:ℕ)) → ∀ i, x i = ∑ j : Fin n, if (j.val = i.val + 1 ∨ i.val = j.val + 1) then
            (v j - v i + delta / (n-1:ℕ)) / (2 * delta) else 0) ∧
        (∀ (k : Fin n) (c : ℝ), (∀ j, j ≠ k → v j = c) → c + delta / (n-1:ℕ) ≤ v k → x k = 0 ∧
          ∀ i, i ≠ k → x i = (∑ j : Fin n, if (j.val = i.val + 1 ∨ i.val = j.val + 1) then
            (1 + (if j = k then 1 else 0)) / (2 * ((n-1:ℕ):ℝ)) else 0)) := by
        clear hTypes hReg
        have A1 := hA1
        have A2 := hA2
        clear hA1 hA2
        classical
        intro v
        have hN : (0:ℝ) < ((n-1:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < n-1)
        set N : ℝ := ((n-1:ℕ):ℝ) with hNdef
        have hNn : ∀ m : ℕ, m + 1 = n → (m:ℝ) = N := by
          intro m hm; rw [hNdef]; congr 1; omega
        have hmono : StrictMono (equiLoc n) := by
          intro i j hij
          unfold equiLoc
          apply div_lt_div_of_pos_right _ hN
          exact_mod_cast hij
        obtain ⟨Q, B, hQ, s0, s1, s2, hnot, hin, hB0, hBn, hkey⟩ := A1 (equiLoc n) hmono
          (fun i => by unfold equiLoc; positivity)
          (fun i => by
            unfold equiLoc; rw [div_le_one hN, hNdef]; exact_mod_cast (by omega : i.val ≤ n-1)) v
        obtain ⟨hsimp, hopt⟩ := A2 (equiLoc n) v Q B hB0 hBn hnot hin hkey
        have hdist : ∀ i j : Fin n, delta * |equiLoc n i - equiLoc n j| = delta / N * |(i.val:ℝ) - j.val| := by
          intro i j
          unfold equiLoc
          rw [← sub_div, abs_div, abs_of_pos hN]
          ring
        have hQ' : ∀ i, i ∈ Q ↔ ∀ j, j ≠ i → v i < v j + delta / N * |(i.val:ℝ) - j.val| := by
          intro i; rw [hQ]; simp only [hdist]
        -- sum over the two neighbours
        have hnb : ∀ (i : Fin n) (g : Fin n → ℝ), (∑ j : Fin n, if (j.val = i.val + 1 ∨ i.val = j.val + 1) then g j else 0)
            = (if h : i.val + 1 < n then g ⟨i.val+1, h⟩ else 0) + (if h : 0 < i.val then g ⟨i.val - 1, by omega⟩ else 0) := by
          intro i g
          have e : ∀ j : Fin n, (if (j.val = i.val + 1 ∨ i.val = j.val + 1) then g j else 0) =
              (if j.val = i.val + 1 then g j else 0) + (if i.val = j.val + 1 then g j else 0) := by
            intro j
            by_cases h1 : j.val = i.val + 1
            · have h2 : ¬ i.val = j.val + 1 := by omega
              rw [if_pos (Or.inl h1), if_pos h1, if_neg h2, add_zero]
            · simp [h1]
          rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib]
          congr 1
          · split_ifs with h
            · rw [Finset.sum_eq_single (⟨i.val+1, h⟩ : Fin n)]
              · simp
              · intro j _ hj
                rw [if_neg (fun h' => hj (Fin.ext h'))]
              · simp
            · apply Finset.sum_eq_zero
              intro j _
              rw [if_neg (by omega)]
          · split_ifs with h
            · rw [Finset.sum_eq_single (⟨i.val-1, by omega⟩ : Fin n)]
              · rw [if_pos (by simp; omega)]
              · intro j _ hj
                rw [if_neg (fun h' => hj (Fin.ext (by simp; omega)))]
              · simp
            · apply Finset.sum_eq_zero
              intro j _
              rw [if_neg (by omega)]
        have habs : ∀ i j : Fin n, j ≠ i → 1 ≤ |(i.val:ℝ) - j.val| := by
          intro i j hij
          have : (i.val:ℤ) - j.val ≠ 0 := by
            intro h; exact hij (Fin.ext (by omega))
          have h2 := Int.one_le_abs this
          exact_mod_cast h2
        refine ⟨_, hsimp, hopt, ?_, ?_, ?_, ?_⟩
        · intro i j hj h
          have : i ∉ Q := by
            rw [hQ']; push Not; exact ⟨j, hj, h⟩
          simp [hnot i this]
        · intro i h
          exact sub_pos.mpr (hin i ((hQ' i).mpr h))
        · intro hall i
          have hd : 0 < delta / N := by positivity
          have hQall : ∀ j, j ∈ Q := by
            intro j
            rw [hQ']
            intro k hk
            have := hall j k
            have := mul_le_mul_of_nonneg_left (habs j k hk) hd.le
            linarith
          have hmid : ∀ (m : ℕ) (h : m + 1 < n), B (m+1) = ((m:ℝ) + (m+1))/(2*N) + (v ⟨m+1, h⟩ - v ⟨m, by omega⟩)/(2*delta) := by
            intro m h
            rw [s2 (m+1) ⟨m, by omega⟩ ⟨m+1, h⟩ (hQall _) (hQall _) (by simp) (by simp)
              (fun j _ => by simp only [Fin.le_def]; omega)]
            unfold equiLoc
            simp only [← hNdef]
            push_cast
            field_simp
          rw [hnb i (fun j => (v j - v i + delta / N) / (2 * delta))]
          have hl : B i.val = (if h : 0 < i.val then (i.val:ℝ)/N + -((v ⟨i.val - 1, by omega⟩ - v i + delta / N) / (2 * delta)) else (i.val:ℝ)/N) := by
            split_ifs with h
            · have := hmid (i.val - 1) (by omega)
              have e : i.val - 1 + 1 = i.val := by omega
              have e2 : ((i.val - 1 : ℕ):ℝ) = (i.val:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
              simp only [e, e2] at this
              rw [this]
              simp only [Fin.eta]
              field_simp
              ring
            · have : i.val = 0 := by omega
              rw [this, hB0]; simp
          have hr : B (i.val+1) = (if h : i.val + 1 < n then (i.val:ℝ)/N + ((v ⟨i.val + 1, by omega⟩ - v i + delta / N) / (2 * delta)) else (i.val:ℝ)/N) := by
            split_ifs with h
            · rw [hmid i.val h]
              simp only [Fin.eta]
              field_simp
              ring
            · have h2 : i.val + 1 = n := by omega
              rw [h2, hBn, hNn _ h2, div_self hN.ne']
          rw [hl, hr]
          split_ifs <;> ring
        · intro k c hc hk
          have hd : 0 < delta / N := by positivity
          have hkQ : k ∉ Q := by
            obtain ⟨j, hj, hj2⟩ : ∃ j : Fin n, j ≠ k ∧ |(k.val:ℝ) - j.val| = 1 := by
              by_cases h : k.val = 0
              · exact ⟨⟨1, by omega⟩, by simp [Fin.ext_iff, h], by simp [h]⟩
              · refine ⟨⟨k.val - 1, by omega⟩, by simp [Fin.ext_iff]; omega, ?_⟩
                have e2 : ((k.val - 1 : ℕ):ℝ) = (k.val:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
                simp [e2]
            rw [hQ']
            push Not
            exact ⟨j, hj, by rw [hj2, hc j hj]; linarith⟩
          have hQall : ∀ j, j ≠ k → j ∈ Q := by
            intro j hj
            rw [hQ']
            intro m hm
            have h1 := mul_le_mul_of_nonneg_left (habs j m hm) hd.le
            rw [hc j hj]
            by_cases hmk : m = k
            · rw [hmk] at h1 ⊢; linarith
            · rw [hc m hmk]; linarith
          have hBk : B k.val = k.val / N := by
            by_cases h : k.val = 0
            · rw [h, hB0]; simp
            · by_cases h2 : k.val + 1 < n
              · rw [s2 k.val ⟨k.val - 1, by omega⟩ ⟨k.val + 1, h2⟩ (hQall _ (by simp [Fin.ext_iff]; omega))
                  (hQall _ (by simp [Fin.ext_iff])) (by simp; omega) (by simp) ?_]
                · rw [hc ⟨k.val - 1, _⟩ (by simp [Fin.ext_iff]; omega), hc ⟨k.val + 1, h2⟩ (by simp [Fin.ext_iff])]
                  have e2 : ((k.val - 1 : ℕ):ℝ) = (k.val:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
                  unfold equiLoc
                  simp only [e2, ← hNdef]
                  push_cast
                  field_simp
                  ring
                · intro j hj
                  have : j ≠ k := fun h => hkQ (h ▸ hj)
                  have : j.val ≠ k.val := fun h => this (Fin.ext h)
                  simp only [Fin.le_def]; omega
              · rw [s1 k.val ?_ ⟨⟨k.val - 1, by omega⟩, hQall _ (by simp [Fin.ext_iff]; omega)⟩]
                · rw [hNn k.val (by omega), div_self hN.ne']
                · intro j hj
                  have : j ≠ k := fun h => hkQ (h ▸ hj)
                  have : j.val ≠ k.val := fun h => this (Fin.ext h)
                  omega
          have hBk1 : B (k.val+1) = k.val / N := by rw [hnot k hkQ, hBk]
          have hmid : ∀ (m : ℕ) (h : m + 1 < n), m ≠ k.val → m + 1 ≠ k.val → B (m+1) = ((m:ℝ) + (m+1))/(2*N) := by
            intro m h h1 h2
            rw [s2 (m+1) ⟨m, by omega⟩ ⟨m+1, h⟩ (hQall _ (by simp [Fin.ext_iff, h1])) (hQall _ (by simp [Fin.ext_iff, h2])) (by simp) (by simp)
              (fun j _ => by simp only [Fin.le_def]; omega), hc ⟨m, _⟩ (by simp [Fin.ext_iff, h1]), hc ⟨m+1, h⟩ (by simp [Fin.ext_iff, h2])]
            unfold equiLoc
            simp only [← hNdef]
            push_cast
            field_simp
            ring
          refine ⟨by simp only [hBk, hBk1, sub_self], ?_⟩
          intro i hi
          have hik : i.val ≠ k.val := fun h => hi (Fin.ext h)
          rw [hnb i (fun j => (1 + (if j = k then 1 else 0)) / (2 * N))]
          have hl : B i.val = (if h : 0 < i.val then (i.val:ℝ)/N + -((1 + (if (⟨i.val - 1, by omega⟩ : Fin n) = k then 1 else 0)) / (2 * N)) else (i.val:ℝ)/N) := by
            split_ifs with h h3
            · have h4 : i.val = k.val + 1 := by rw [← h3]; simp; omega
              rw [h4, hBk1]
              push_cast
              field_simp
              ring
            · have h4 : i.val - 1 ≠ k.val := fun h' => h3 (Fin.ext h')
              have := hmid (i.val - 1) (by omega) h4 (by omega)
              have e : i.val - 1 + 1 = i.val := by omega
              have e2 : ((i.val - 1 : ℕ):ℝ) = (i.val:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
              simp only [e, e2] at this
              rw [this]
              field_simp
              ring
            · have : i.val = 0 := by omega
              rw [this, hB0]; simp
          have hr : B (i.val+1) = (if h : i.val + 1 < n then (i.val:ℝ)/N + ((1 + (if (⟨i.val + 1, h⟩ : Fin n) = k then 1 else 0)) / (2 * N)) else (i.val:ℝ)/N) := by
            split_ifs with h h3
            · have h4 : i.val + 1 = k.val := by rw [← h3]
              rw [h4, hBk, ← h4]
              push_cast
              field_simp
              ring
            · have h4 : i.val + 1 ≠ k.val := fun h' => h3 (Fin.ext h')
              rw [hmid i.val h hik h4]
              field_simp
              ring
            · have h2 : i.val + 1 = n := by omega
              rw [h2, hBn, hNn _ h2, div_self hN.ne']
          rw [hl, hr]
          by_cases c1 : i.val + 1 < n <;> by_cases c2 : 0 < i.val <;> simp only [c1, c2, dif_pos, dif_neg, not_false_eq_true] <;> ring
      clear hA1 hA2
      have hB1 : ∀ (V : ℝ → ℝ) (xs : Profile (fun _ : Fin n => S) → Fin n → ℝ)   (hX0 : ∀ θ : Profile (fun _ : Fin n => S), ∀ i j, j ≠ i → V (θ j) + delta / (n-1:ℕ) * |(i.val:ℝ) - j.val| ≤ V (θ i) → xs θ i = 0)   (hXp : ∀ θ : Profile (fun _ : Fin n => S), ∀ i, (∀ j, j ≠ i → V (θ i) < V (θ j) + delta / (n-1:ℕ) * |(i.val:ℝ) - j.val|) → 0 < xs θ i)   (hXE : ∀ θ : Profile (fun _ : Fin n => S), (∀ i j, V (θ i) - V (θ j) < delta / (n-1:ℕ)) → ∀ i, xs θ i = ∑ j : Fin n, if (j.val = i.val + 1 ∨ i.val = j.val + 1) then         (V (θ j) - V (θ i) + delta / (n-1:ℕ)) / (2 * delta) else 0)   (hXK : ∀ θ : Profile (fun _ : Fin n => S), (∀ (k : Fin n) (c : ℝ), (∀ j, j ≠ k → V (θ j) = c) → c + delta / (n-1:ℕ) ≤ V (θ k) → xs θ k = 0 ∧       ∀ i, i ≠ k → xs θ i = (∑ j : Fin n, if (j.val = i.val + 1 ∨ i.val = j.val + 1) then         (1 + (if j = k then 1 else 0)) / (2 * ((n-1:ℕ):ℝ)) else 0)))   (beta : Fin n → ℝ → ℝ)   (hbeta : ∀ θ : Profile (fun _ : Fin n => S), ∑ i, beta i (θ i) * xs θ i = 0),
       ∀ c ∈ S, ∀ b ∈ S, (V c ≤ V b) → ∑ i, beta i c * interim (fun _ => f) (fun θ : Profile (fun _ : Fin n => S) => xs θ i) i b = 0 := by
        clear hTypes hReg hA3
        intro V xs hX0 hXp hXE hXK beta hbeta
        classical
        have hN : (0:ℝ) < ((n-1:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < n-1)
        set N : ℝ := ((n-1:ℕ):ℝ) with hNdef
        have hd : 0 < delta / N := by positivity
        set d : ℝ := delta / N with hddef
        have hnb : ∀ (i : Fin n) (g : Fin n → ℝ), (∑ j : Fin n, if (j.val = i.val + 1 ∨ i.val = j.val + 1) then g j else 0)
            = (if h : i.val + 1 < n then g ⟨i.val+1, h⟩ else 0) + (if h : 0 < i.val then g ⟨i.val - 1, by omega⟩ else 0) := by
          intro i g
          have e : ∀ j : Fin n, (if (j.val = i.val + 1 ∨ i.val = j.val + 1) then g j else 0) =
              (if j.val = i.val + 1 then g j else 0) + (if i.val = j.val + 1 then g j else 0) := by
            intro j
            by_cases h1 : j.val = i.val + 1
            · have h2 : ¬ i.val = j.val + 1 := by omega
              rw [if_pos (Or.inl h1), if_pos h1, if_neg h2, add_zero]
            · simp [h1]
          rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib]
          congr 1
          · split_ifs with h
            · rw [Finset.sum_eq_single (⟨i.val+1, h⟩ : Fin n)]
              · simp
              · intro j _ hj
                rw [if_neg (fun h' => hj (Fin.ext h'))]
              · simp
            · apply Finset.sum_eq_zero
              intro j _
              rw [if_neg (by omega)]
          · split_ifs with h
            · rw [Finset.sum_eq_single (⟨i.val-1, by omega⟩ : Fin n)]
              · rw [if_pos (by simp; omega)]
              · intro j _ hj
                rw [if_neg (fun h' => hj (Fin.ext (by simp; omega)))]
              · simp
            · apply Finset.sum_eq_zero
              intro j _
              rw [if_neg (by omega)]
        let w : Fin n → ℝ := fun i => ∑ j : Fin n, if (j.val = i.val + 1 ∨ i.val = j.val + 1) then 1 else 0
        have hwsum : ∀ c ∈ S, ∑ i, beta i c * w i = 0 := by
          intro c hc
          have h := hbeta (fun _ => ⟨c, hc⟩)
          have h2 := hXE (fun _ => ⟨c, hc⟩) (by intro i j; simpa using hd)
          have h3 : ∀ i : Fin n, beta i c * xs (fun _ => ⟨c, hc⟩) i = beta i c * w i * (1 / (2 * N)) := by
            intro i
            rw [h2 i, mul_assoc]
            congr 1
            simp only [w]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs
            · simp only [sub_self, zero_add, hddef]; field_simp
            · simp
          simp only [h3] at h
          rw [← Finset.sum_mul] at h
          rcases mul_eq_zero.mp h with h | h
          · exact h
          · have : (0:ℝ) < 1 / (2 * N) := by positivity
            linarith
        have hB1 : ∀ c ∈ S, ∀ M ∈ S, V c + d ≤ V M → ∀ i, beta i c = 0 := by
          intro c hc M hM hcM
          have hk : ∀ k : Fin n, (∑ j : Fin n, if (j.val = k.val + 1 ∨ k.val = j.val + 1) then (beta j c - beta k c) else 0) = 0 := by
            intro k
            let θ : Profile (fun _ : Fin n => S) := Function.update (fun _ => (⟨c, hc⟩ : ↥S)) k ⟨M, hM⟩
            have hθk : (θ k : ℝ) = M := by simp [θ]
            have hθj : ∀ j, j ≠ k → (θ j : ℝ) = c := by intro j hj; simp [θ, Function.update_of_ne hj]
            obtain ⟨h1, h2⟩ := hXK θ k (V c) (fun j hj => by rw [hθj j hj]) (by rw [hθk]; exact hcM)
            have h := hbeta θ
            have h3 : ∀ i : Fin n, beta i (θ i) * xs θ i = (beta i c * (w i + (if (k.val = i.val + 1 ∨ i.val = k.val + 1) then 1 else 0))
                - (if i = k then beta k c * w k else 0)) * (1 / (2 * N)) := by
              intro i
              by_cases hi : i = k
              · subst hi
                rw [h1]
                simp
              · rw [h2 i hi, hθj i hi, if_neg hi, sub_zero, mul_assoc]
                congr 1
                have : (if (k.val = i.val + 1 ∨ i.val = k.val + 1) then (1:ℝ) else 0) =
                    ∑ j : Fin n, if j = k then (if (j.val = i.val + 1 ∨ i.val = j.val + 1) then (1:ℝ) else 0) else 0 := by
                  rw [Finset.sum_ite_eq']; simp
                rw [this]
                simp only [w]
                rw [← Finset.sum_add_distrib, Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro j _
                split_ifs <;> ring
            simp only [h3] at h
            rw [← Finset.sum_mul] at h
            have h4 : (0:ℝ) < 1 / (2 * N) := by positivity
            have h5 := (mul_eq_zero.mp h).resolve_right h4.ne'
            rw [Finset.sum_sub_distrib, Finset.sum_ite_eq'] at h5
            simp only [Finset.mem_univ, if_true, mul_add, Finset.sum_add_distrib] at h5
            rw [hwsum c hc] at h5
            have h6 : (∑ j : Fin n, if (j.val = k.val + 1 ∨ k.val = j.val + 1) then (beta j c - beta k c) else 0) =
                (∑ i : Fin n, beta i c * (if (k.val = i.val + 1 ∨ i.val = k.val + 1) then 1 else 0)) - beta k c * w k := by
              simp only [w]
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro j _
              by_cases hj : (j.val = k.val + 1 ∨ k.val = j.val + 1)
              · rw [if_pos hj, if_pos (by omega), if_pos hj]; ring
              · rw [if_neg hj, if_neg (by omega), if_neg hj]; ring
            rw [h6]; linarith
          have hconst : ∀ m : ℕ, ∀ h : m < n, beta ⟨m, h⟩ c = beta ⟨0, by omega⟩ c ∧ ∀ h' : m + 1 < n, beta ⟨m+1, h'⟩ c = beta ⟨0, by omega⟩ c := by
            intro m
            induction m with
            | zero =>
              intro h
              refine ⟨rfl, fun h' => ?_⟩
              have := hk ⟨0, h⟩
              rw [hnb] at this
              simp only [dif_pos h', lt_irrefl, dif_neg, not_false_eq_true, add_zero, zero_add] at this ⊢
              linarith
            | succ m ih =>
              intro h
              obtain ⟨i1, i2⟩ := ih (by omega)
              refine ⟨i2 h, fun h' => ?_⟩
              have := hk ⟨m+1, h⟩
              rw [hnb (⟨m+1, h⟩ : Fin n) (fun j => beta j c - beta ⟨m+1, h⟩ c)] at this
              simp only [dif_pos h', Nat.succ_pos, dif_pos, Nat.add_sub_cancel] at this
              rw [i1, i2 h] at this
              linarith
          have hall : ∀ i : Fin n, beta i c = beta ⟨0, by omega⟩ c := fun i => (hconst i.val i.2).1
          have hs := hwsum c hc
          rw [Finset.sum_congr rfl (fun i _ => by rw [hall i] : ∀ i ∈ Finset.univ, beta i c * w i = beta ⟨0, by omega⟩ c * w i), ← Finset.mul_sum] at hs
          have hwpos : 0 < ∑ i, w i := by
            apply Finset.sum_pos'
            · intro i _; exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
            · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
              have hw0 := hnb (⟨0, by omega⟩ : Fin n) (fun _ => (1:ℝ))
              have h01 : 0 + 1 < n := by omega
              rw [dif_pos h01, dif_neg (lt_irrefl _)] at hw0
              show (0:ℝ) < ∑ j : Fin n, if (j.val = (⟨0, by omega⟩ : Fin n).val + 1 ∨ (⟨0, by omega⟩ : Fin n).val = j.val + 1) then 1 else 0
              rw [hw0]; norm_num
          intro i
          rw [hall i]
          exact (mul_eq_zero.mp hs).resolve_right hwpos.ne'
        have hB2 : ∀ (e : Fin n ≃ Fin n), (∀ i j, |((e i).val:ℝ) - (e j).val| = |(i.val:ℝ) - j.val|) →
            ∀ a ∈ S, ∀ c ∈ S, V a < V c → (∀ i, beta i a = 0) →
            ∀ m : ℕ, ∀ h : m < n, V c < V a + d * (N - m) → beta (e ⟨m, h⟩) c = 0 := by
          intro e he a ha c hc hac ha0 m
          induction m using Nat.strong_induction_on with
          | _ m ih =>
            intro h hm
            set t : ℝ := (V c - V a) / d with ht
            have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
            have htd : t * d = V c - V a := by rw [ht]; field_simp
            set q : ℕ := ⌊t⌋₊ with hq
            have hq1 : (q:ℝ) ≤ t := Nat.floor_le ht0
            have hq2 : t < q + 1 := Nat.lt_floor_add_one t
            have hqm : m + q + 1 < n := by
              have h1 : t < N - m := by
                rw [ht, div_lt_iff₀ hd]; linarith
              have h2 : (q:ℝ) + m < N := by linarith
              rw [hNdef] at h2
              have h3 : q + m < n - 1 := by exact_mod_cast h2
              omega
            let θ : Profile (fun _ : Fin n => S) := fun k => if (e.symm k).val ≤ m + q then ⟨c, hc⟩ else ⟨a, ha⟩
            have hθ1 : ∀ k : Fin n, k.val ≤ m + q → (θ (e k) : ℝ) = c := by
              intro k hk; simp [θ, hk]
            have hθ2 : ∀ k : Fin n, ¬ k.val ≤ m + q → (θ (e k) : ℝ) = a := by
              intro k hk; simp [θ, hk]
            have hs := hbeta θ
            rw [← Equiv.sum_comp e, Finset.sum_eq_single (⟨m, h⟩ : Fin n)] at hs
            · rw [hθ1 ⟨m, h⟩ (by simp)] at hs
              refine (mul_eq_zero.mp hs).resolve_right (ne_of_gt (hXp θ _ ?_))
              intro j hj
              obtain ⟨j', rfl⟩ := e.surjective j
              have hj' : j' ≠ ⟨m, h⟩ := fun hh => hj (by rw [hh])
              rw [he, hθ1 ⟨m, h⟩ (by simp)]
              by_cases hjq : j'.val ≤ m + q
              · rw [hθ1 j' hjq]
                have : 0 < |(((⟨m, h⟩ : Fin n).val:ℝ)) - j'.val| := by
                  rw [abs_pos, sub_ne_zero]
                  intro hh
                  exact hj' (Fin.ext (by exact_mod_cast hh.symm))
                have := mul_pos hd this
                linarith
              · rw [hθ2 j' hjq]
                have h5 : (m:ℝ) + q + 1 ≤ j'.val := by exact_mod_cast (by omega : m + q + 1 ≤ j'.val)
                have h6 : t < |(((⟨m, h⟩ : Fin n).val:ℝ)) - j'.val| := by
                  rw [abs_sub_comm]
                  refine lt_of_lt_of_le ?_ (le_abs_self _)
                  simp only; linarith
                have := mul_lt_mul_of_pos_left h6 hd
                linarith
            · intro k _ hk
              have hkm : k.val ≠ m := fun hh => hk (Fin.ext hh)
              rcases lt_trichotomy k.val m with h1 | h1 | h1
              · rw [hθ1 k (by omega)]
                have := ih k.val h1 k.2 (by
                  have : (k.val:ℝ) ≤ m := by exact_mod_cast h1.le
                  have := mul_le_mul_of_nonneg_left this hd.le
                  linarith)
                simp only [Fin.eta] at this
                rw [this, zero_mul]
              · exact absurd h1 hkm
              · by_cases hkq : k.val ≤ m + q
                · have : xs θ (e k) = 0 := by
                    apply hX0 θ (e k) (e ⟨m+q+1, hqm⟩)
                    · intro hh
                      have := congrArg Fin.val (e.injective hh)
                      simp only at this; omega
                    · rw [he, hθ1 k hkq, hθ2 ⟨m+q+1, hqm⟩ (by simp)]
                      have h5 : |((k.val:ℝ)) - ((⟨m+q+1, hqm⟩ : Fin n).val : ℝ)| ≤ q := by
                        have h6 : (m:ℝ) + 1 ≤ k.val := by exact_mod_cast h1
                        have h7 : (k.val:ℝ) ≤ m + q := by exact_mod_cast hkq
                        rw [abs_le]
                        simp only
                        push_cast
                        constructor <;> linarith
                      have := mul_le_mul_of_nonneg_left (h5.trans hq1) hd.le
                      linarith
                  rw [this, mul_zero]
                · rw [hθ2 k hkq, ha0, zero_mul]
            · simp
        have hB2' : ∀ a ∈ S, ∀ c ∈ S, V a < V c → (∀ i, beta i a = 0) →
            ∀ i j : Fin n, V c < V a + d * |(i.val:ℝ) - j.val| → beta i c = 0 := by
          intro a ha c hc hac ha0 i j hij
          have hNn : N = (n:ℝ) - 1 := by rw [hNdef, Nat.cast_sub (by omega)]; simp
          rcases le_total i.val j.val with h | h
          · have := hB2 (Equiv.refl _) (fun _ _ => rfl) a ha c hc hac ha0 i.val i.2 (by
              have h1 : (i.val:ℝ) ≤ j.val := by exact_mod_cast h
              have h2 : (j.val:ℝ) + 1 ≤ n := by exact_mod_cast j.2
              rw [abs_of_nonpos (by linarith)] at hij
              have := mul_le_mul_of_nonneg_left (by linarith : -((i.val:ℝ) - j.val) ≤ N - i.val) hd.le
              linarith)
            simpa using this
          · have hr : ∀ k : Fin n, ((Fin.revPerm k).val : ℝ) = N - k.val := by
              intro k
              rw [Fin.revPerm_apply, Fin.val_rev, Nat.cast_sub (by omega), hNn]; push_cast; ring
            have := hB2 Fin.revPerm (fun x y => by rw [hr, hr, abs_sub_comm]; congr 1; ring) a ha c hc hac ha0 (Fin.revPerm i).val (Fin.revPerm i).2 (by
              have h1 : (j.val:ℝ) ≤ i.val := by exact_mod_cast h
              have h2 : (0:ℝ) ≤ j.val := Nat.cast_nonneg _
              rw [abs_of_nonneg (by linarith)] at hij
              rw [hr]
              have := mul_le_mul_of_nonneg_left (by linarith : ((i.val:ℝ) - j.val) ≤ N - (N - i.val)) hd.le
              linarith)
            have e : Fin.revPerm (⟨(Fin.revPerm i).val, (Fin.revPerm i).2⟩ : Fin n) = i := by
              rw [Fin.eta, Fin.revPerm_apply, Fin.revPerm_apply, Fin.rev_rev]
            rw [e] at this
            exact this
        intro c hc b hb hcb
        by_cases hctop : ∃ M ∈ S, V c + d ≤ V M
        · obtain ⟨M, hM, hcM⟩ := hctop
          exact Finset.sum_eq_zero (fun i _ => by rw [hB1 c hc M hM hcM i, zero_mul])
        · push Not at hctop
          let top : Profile (fun _ : Fin n => S) → Prop := fun θ => ∀ j : Fin n, ∀ M ∈ S, V M < V (θ j) + d
          let E : Fin n → Fin n → ℝ := fun i j => ∑ θ : Profile (fun _ : Fin n => S),
            if (θ i : ℝ) = b then probOthers (fun _ => f) i θ * (if top θ then (V (θ j) - V b + d) / (2 * delta) else 0) else 0
          have hEsymm : ∀ i j i' j' : Fin n, i ≠ j → i' ≠ j' → E i j = E i' j' := by
            intro i j i' j' hij hij'
            obtain ⟨σ, hσi, hσj⟩ : ∃ σ : Equiv.Perm (Fin n), σ i' = i ∧ σ j' = j := by
              refine ⟨Equiv.swap (Equiv.swap i i' j') j * Equiv.swap i i', ?_, ?_⟩
              · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
                apply Equiv.swap_apply_of_ne_of_ne _ hij
                intro h
                have : Equiv.swap i i' i' = Equiv.swap i i' j' := by rw [Equiv.swap_apply_right]; exact h
                exact hij' ((Equiv.swap i i').injective this)
              · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
            let Φ : Profile (fun _ : Fin n => S) ≃ Profile (fun _ : Fin n => S) :=
              (σ.symm.arrowCongr (Equiv.refl ↥S) : (Fin n → ↥S) ≃ (Fin n → ↥S))
            have hΦ : ∀ θ k, Φ θ k = θ (σ k) := fun θ k => rfl
            simp only [E]
            rw [← Equiv.sum_comp Φ (fun θ => if (θ i' : ℝ) = b then probOthers (fun _ => f) i' θ * (if top θ then (V (θ j') - V b + d) / (2 * delta) else 0) else 0)]
            apply Finset.sum_congr rfl
            intro θ _
            have ht : top (Φ θ) ↔ top θ := by
              constructor
              · intro h k
                have := h (σ.symm k)
                rw [hΦ, Equiv.apply_symm_apply] at this
                exact this
              · intro h k
                exact h (σ k)
            have hp : probOthers (fun _ => f) i' (Φ θ) = probOthers (fun _ => f) i θ := by
              unfold probOthers
              apply Finset.prod_equiv σ
              · intro k
                simp only [Finset.mem_erase, Finset.mem_univ, and_true]
                rw [← hσi, not_iff_not, σ.injective.eq_iff]
              · intro k _; rw [hΦ]
            rw [hΦ, hΦ, hσi, hσj, hp]
            simp only [ht]
          have hXi : ∀ i, beta i c ≠ 0 → interim (fun _ => f) (fun θ : Profile (fun _ : Fin n => S) => xs θ i) i b =
              ∑ j : Fin n, if (j.val = i.val + 1 ∨ i.val = j.val + 1) then E i j else 0 := by
            intro i hi
            have hx : ∀ θ : Profile (fun _ : Fin n => S), (θ i : ℝ) = b → xs θ i =
                ∑ j : Fin n, if (j.val = i.val + 1 ∨ i.val = j.val + 1) then (if top θ then (V (θ j) - V b + d) / (2 * delta) else 0) else 0 := by
              intro θ hθ
              by_cases ht : top θ
              · rw [hXE θ (fun k l => by have := ht l (θ k) (θ k).2; linarith) i, hθ]
                simp only [if_pos ht]
              · simp only [if_neg ht, ite_self, Finset.sum_const_zero]
                simp only [top] at ht
                push Not at ht
                obtain ⟨j, M, hM, hjM⟩ := ht
                have h0 := hB1 (θ j) (θ j).2 M hM hjM
                have hcM := hctop M hM
                have hlt : V (θ j) < V c := by linarith
                have hge : ¬ V c < V (θ j) + d * |(i.val:ℝ) - j.val| := fun h =>
                  hi (hB2' (θ j) (θ j).2 c hc hlt h0 i j h)
                apply hX0 θ i j
                · rintro rfl
                  rw [hθ] at hlt; linarith
                · rw [hθ]; linarith
            unfold interim
            have : ∀ θ : Profile (fun _ : Fin n => S), (if (θ i : ℝ) = b then probOthers (fun _ => f) i θ * xs θ i else 0) =
                ∑ j : Fin n, if (j.val = i.val + 1 ∨ i.val = j.val + 1) then (if (θ i : ℝ) = b then probOthers (fun _ => f) i θ * (if top θ then (V (θ j) - V b + d) / (2 * delta) else 0) else 0) else 0 := by
              intro θ
              by_cases hθ : (θ i : ℝ) = b
              · simp only [if_pos hθ]
                rw [hx θ hθ, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                split_ifs <;> simp
              · simp only [if_neg hθ, ite_self, Finset.sum_const_zero]
            rw [Finset.sum_congr rfl (fun θ _ => this θ), Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs
            · rfl
            · simp
          set Z : ℝ := E ⟨0, by omega⟩ ⟨1, by omega⟩ with hZ
          have hfin : ∀ i, beta i c * interim (fun _ => f) (fun θ : Profile (fun _ : Fin n => S) => xs θ i) i b = beta i c * w i * Z := by
            intro i
            by_cases hi : beta i c = 0
            · rw [hi]; simp
            · rw [hXi i hi, mul_assoc]
              congr 1
              simp only [w]
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              split_ifs with h
              · rw [one_mul, hZ]
                apply hEsymm
                · intro hh; rw [hh] at h; omega
                · simp [Fin.ext_iff]
              · simp
          rw [Finset.sum_congr rfl (fun i _ => hfin i), ← Finset.sum_mul, hwsum c hc, zero_mul]
      obtain ⟨hne, hpos, hfpos, hsum⟩ := hTypes
      have hS : S.Nonempty := hne ⟨0, by omega⟩
      have hSpos : ∀ c ∈ S, 0 < c := hpos ⟨0, by omega⟩
      have hfS : ∀ c ∈ S, 0 < f c := hfpos ⟨0, by omega⟩
      have hsumS : ∑ c ∈ S, f c = 1 := hsum ⟨0, by omega⟩
      have hprob : ∀ θ : Profile (fun _ : Fin n => S), 0 ≤ prob (fun _ => f) θ := by
        intro θ
        unfold prob
        exact Finset.prod_nonneg (fun j _ => (hfS _ (θ j).2).le)
      have hprobO : ∀ (i : Fin n) (θ : Profile (fun _ : Fin n => S)),
          0 ≤ probOthers (fun _ => f) i θ := by
        intro i θ
        unfold probOthers
        exact Finset.prod_nonneg (fun j _ => (hfS _ (θ j).2).le)
      have hE : ∀ (i : Fin n) (g : Profile (fun _ : Fin n => S) → ℝ),
          expect (fun _ => f) g = ∑ c ∈ S, f c * interim (fun _ => f) g i c := by
        intro i g
        unfold expect interim
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro θ _
        have h1 : prob (fun _ => f) θ = f (θ i) * probOthers (fun _ => f) i θ := by
          unfold prob probOthers
          exact (Finset.mul_prod_erase Finset.univ (fun j => f (θ j : ℝ)) (Finset.mem_univ i)).symm
        rw [h1]
        have h2 : ∀ c ∈ S, (f c * if (θ i : ℝ) = c then probOthers (fun _ => f) i θ * g θ else 0)
            = if (θ i : ℝ) = c then f (θ i) * probOthers (fun _ => f) i θ * g θ else 0 := by
          intro c _
          split_ifs with h
          · rw [h]; ring
          · simp
        rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq S (θ i : ℝ)]
        simp [(θ i).2]
      have hDC : {r | ∃ (q : Profile (fun _ : Fin n => S) → Finset (Fin n))
            (p x : Profile (fun _ : Fin n => S) → Fin n → ℝ),
            IsDecLinFeasible (fun _ => f) (hotGCS (equiLoc n) delta) (simplex n) q p x ∧
            r = decLinObj (fun _ => f) (hotGCS (equiLoc n) delta) p x} ⊆
          {r | ∃ x t : Profile (fun _ : Fin n => S) → Fin n → ℝ,
            IsCentFeasible (fun _ => f) (simplex n) x t ∧
            r = centObj (fun _ => f) (hotGCS (equiLoc n) delta) x t} := by
        rintro r ⟨q, p, x, ⟨hc, _⟩, rfl⟩
        exact ⟨x, fun θ i => p θ i * x θ i, hc, rfl⟩
      have hpred : ∀ i : Fin n, ∀ c ∈ S, ∀ c' ∈ S, c < c' → (∀ b ∈ S, c < b → c' ≤ b) →
          pred (fun _ : Fin n => S) i c' = c := by
        intro i c hc c' hc' hlt hmin
        have hne : (S.filter (· < c')).Nonempty := ⟨c, by simp [hc, hlt]⟩
        unfold pred
        rw [dif_pos hne]
        apply le_antisymm
        · by_contra hcon
          push Not at hcon
          have hm := Finset.max'_mem _ hne
          simp only [Finset.mem_filter] at hm
          have := hmin _ hm.1 hcon
          linarith [hm.2]
        · exact Finset.le_max' _ c (by simp [hc, hlt])
      have hswap : ∀ (i : Fin n) (X : ℝ → ℝ), ∑ c ∈ S, f c * ∑ b ∈ S.filter (c < ·), (b - pred (fun _ : Fin n => S) i b) * X b
          = ∑ b ∈ S, cdfF (fun _ : Fin n => S) (fun _ => f) i (pred (fun _ : Fin n => S) i b) *
              (b - pred (fun _ : Fin n => S) i b) * X b := by
        intro i X
        simp_rw [Finset.sum_filter, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hne : (S.filter (· < b)).Nonempty
        · have hcdf : cdfF (fun _ : Fin n => S) (fun _ => f) i (pred (fun _ : Fin n => S) i b)
              = ∑ c ∈ S, if c < b then f c else 0 := by
            unfold cdfF
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro c hc
            have hm := Finset.max'_mem _ hne
            simp only [Finset.mem_filter] at hm
            have e : (c ≤ pred (fun _ : Fin n => S) i b) ↔ c < b := by
              unfold pred
              rw [dif_pos hne]
              constructor
              · intro h; linarith [hm.2]
              · intro h; exact Finset.le_max' _ c (by simp [hc, h])
            simp only [e]
          rw [hcdf, Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro c _
          split_ifs <;> ring
        · have hp : pred (fun _ : Fin n => S) i b = b := by unfold pred; rw [dif_neg hne]
          rw [hp]
          simp
      have hMy : ∀ x t : Profile (fun _ : Fin n => S) → Fin n → ℝ,
          IsCentFeasible (fun _ => f) (simplex n) x t → ∀ i : Fin n,
          expect (fun _ => f) (fun θ => virtualCost (fun _ : Fin n => S) (fun _ => f) i (θ i) * x θ i)
            ≤ expect (fun _ => f) (fun θ => t θ i) := by
        intro x t hft i
        obtain ⟨hIC, hIR, _⟩ := hft
        set T : ℝ → ℝ := fun c => interim (fun _ => f) (fun θ => t θ i) i c with hT
        set X : ℝ → ℝ := fun c => interim (fun _ => f) (fun θ => x θ i) i c with hX
        have hU : ∀ b a : ℝ, utility (fun _ => f) x t i b a = T b - a * X b := by
          intro b a
          simp only [utility, interim, hT, hX, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro θ _
          split_ifs <;> ring
        have hIC' : ∀ a ∈ S, ∀ b ∈ S, T b - a * X b ≤ T a - a * X a := by
          intro a ha b hb
          have := hIC i a ha b hb
          rwa [hU, hU] at this
        have hIR' : ∀ a ∈ S, 0 ≤ T a - a * X a := by
          intro a ha
          have := hIR i a ha
          rwa [hU] at this
        have hInd : ∀ k : ℕ, ∀ c ∈ S, (S.filter (c < ·)).card = k →
            ∑ b ∈ S.filter (c < ·), (b - pred (fun _ : Fin n => S) i b) * X b ≤ T c - c * X c := by
          intro k
          induction k using Nat.strong_induction_on with
          | _ k ih =>
            intro c hc hk
            by_cases hne : (S.filter (c < ·)).Nonempty
            · set c' := (S.filter (c < ·)).min' hne with hc'def
              have hc'm := Finset.min'_mem _ hne
              rw [← hc'def] at hc'm
              simp only [Finset.mem_filter] at hc'm
              have hmin : ∀ b ∈ S, c < b → c' ≤ b := fun b hb hcb =>
                Finset.min'_le _ b (by simp [hb, hcb])
              have hp := hpred i c hc c' hc'm.1 hc'm.2 hmin
              have hins : S.filter (c < ·) = insert c' (S.filter (c' < ·)) := by
                ext b
                simp only [Finset.mem_filter, Finset.mem_insert]
                constructor
                · rintro ⟨hb, hcb⟩
                  rcases (hmin b hb hcb).lt_or_eq with h | h
                  · exact Or.inr ⟨hb, h⟩
                  · exact Or.inl h.symm
                · rintro (h | ⟨hb, h⟩)
                  · subst h; exact hc'm
                  · exact ⟨hb, lt_trans hc'm.2 h⟩
              have hnot : c' ∉ S.filter (c' < ·) := by simp
              have hcard : (S.filter (c' < ·)).card < k := by
                rw [← hk, hins, Finset.card_insert_of_notMem hnot]; omega
              have h1 := ih _ hcard c' hc'm.1 rfl
              rw [hins, Finset.sum_insert hnot, hp]
              have h2 := hIC' c hc c' hc'm.1
              linarith
            · rw [Finset.not_nonempty_iff_eq_empty] at hne
              rw [hne, Finset.sum_empty]
              exact hIR' c hc
        have hsumU : ∑ c ∈ S, f c * ∑ b ∈ S.filter (c < ·), (b - pred (fun _ : Fin n => S) i b) * X b
            ≤ ∑ c ∈ S, f c * (T c - c * X c) :=
          Finset.sum_le_sum (fun c hc => mul_le_mul_of_nonneg_left (hInd _ c hc rfl) (hfS c hc).le)
        have hvx : ∀ c ∈ S, f c * interim (fun _ => f)
              (fun θ => virtualCost (fun _ : Fin n => S) (fun _ => f) i (θ i) * x θ i) i c
            = f c * c * X c + cdfF (fun _ : Fin n => S) (fun _ => f) i (pred (fun _ : Fin n => S) i c) *
                (c - pred (fun _ : Fin n => S) i c) * X c := by
          intro c hc
          have h1 : interim (fun _ => f)
              (fun θ => virtualCost (fun _ : Fin n => S) (fun _ => f) i (θ i) * x θ i) i c
              = virtualCost (fun _ : Fin n => S) (fun _ => f) i c * X c := by
            simp only [interim, hX, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro θ _
            split_ifs with h
            · rw [h]; ring
            · simp
          rw [h1]
          unfold virtualCost
          have hf := (hfS c hc).ne'
          field_simp
        rw [hE i, hE i, Finset.sum_congr rfl hvx, Finset.sum_add_distrib, ← hswap i X]
        have h3 : ∑ c ∈ S, f c * (T c - c * X c) = ∑ c ∈ S, f c * T c - ∑ c ∈ S, f c * c * X c := by
          rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro c _; ring
        have : ∑ c ∈ S, f c * interim (fun _ => f) (fun θ => t θ i) i c = ∑ c ∈ S, f c * T c := rfl
        rw [this]
        linarith
      have hCentUB : ∀ x t : Profile (fun _ : Fin n => S) → Fin n → ℝ,
          IsCentFeasible (fun _ => f) (simplex n) x t →
          centObj (fun _ => f) (hotGCS (equiLoc n) delta) x t ≤
            expect (fun _ => f) (fun θ => hotGCS (equiLoc n) delta (x θ) -
              ∑ i, virtualCost (fun _ : Fin n => S) (fun _ => f) i (θ i) * x θ i) := by
        intro x t hft
        have hlin : ∀ g : Fin n → Profile (fun _ : Fin n => S) → ℝ,
            expect (fun _ => f) (fun θ => hotGCS (equiLoc n) delta (x θ) - ∑ i, g i θ) =
              expect (fun _ => f) (fun θ => hotGCS (equiLoc n) delta (x θ)) -
                ∑ i, expect (fun _ => f) (g i) := by
          intro g
          unfold expect
          simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
          rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
        unfold centObj
        rw [hlin (fun i θ => t θ i),
          hlin (fun i θ => virtualCost (fun _ : Fin n => S) (fun _ => f) i (θ i) * x θ i)]
        have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hMy x t hft i)
        linarith
      let i0 : Fin n := ⟨0, by omega⟩
      set V : ℝ → ℝ := virtualCost (fun _ : Fin n => S) (fun _ => f) i0 with hVdef
      set pr : ℝ → ℝ := pred (fun _ : Fin n => S) i0 with hprdef
      have hVi : ∀ i : Fin n, virtualCost (fun _ : Fin n => S) (fun _ => f) i = V := fun i => rfl
      have hVmono : ∀ a ∈ S, ∀ b ∈ S, a < b → V a < V b := fun a ha b hb hab => hReg i0 ha hb hab
      have hA := fun θ : Profile (fun _ : Fin n => S) => hA3 (fun i => V (θ i))
      choose xs hsx hopt hX0 hXp hXE hXK using hA
      have hCore := hB1 V xs hX0 hXp hXE hXK
      set Xs : Fin n → ℝ → ℝ := fun i c => interim (fun _ => f) (fun θ : Profile (fun _ : Fin n => S) => xs θ i) i c with hXs
      set Ts : Fin n → ℝ → ℝ := fun i c => c * Xs i c +
          ∑ b ∈ S.filter (c < ·), (b - pr b) * Xs i b with hTs
      have hprob' : ∀ (i : Fin n) (θ : Profile (fun _ : Fin n => S)),
          prob (fun _ => f) θ = f (θ i) * probOthers (fun _ => f) i θ := by
        intro i θ
        unfold prob probOthers
        exact (Finset.mul_prod_erase Finset.univ (fun j => f (θ j : ℝ)) (Finset.mem_univ i)).symm
      have hprobpos : ∀ θ : Profile (fun _ : Fin n => S), 0 < prob (fun _ => f) θ := by
        intro θ
        unfold prob
        exact Finset.prod_pos (fun j _ => hfS _ (θ j).2)
      have hk : ∃ k : Profile (fun _ : Fin n => S) → ℝ, ∀ i : Fin n, ∀ c ∈ S,
          interim (fun _ => f) (fun θ : Profile (fun _ : Fin n => S) => (V (θ i) + k θ) * xs θ i) i c = Ts i c := by
        let Mx : Matrix (Fin n × ↥S) (Profile (fun _ : Fin n => S)) ℝ := Matrix.of (fun p θ =>
          if θ p.1 = p.2 then probOthers (fun _ => f) p.1 θ * xs θ p.1 else 0)
        let τ : Fin n × ↥S → ℝ := fun p => Ts p.1 p.2 - V p.2 * Xs p.1 p.2
        have hmem : τ ∈ LinearMap.range (Matrix.mulVecLin Mx) := by
          by_contra hnot
          obtain ⟨φ, hφ1, hφ2⟩ := Submodule.exists_le_ker_of_notMem hnot
          apply hφ1
          let g : Fin n × ↥S → ℝ := fun p => φ (fun q => if p = q then 1 else 0)
          have hφ : ∀ z : Fin n × ↥S → ℝ, φ z = ∑ i : Fin n, ∑ s : ↥S, z (i, s) * g (i, s) := by
            intro z
            rw [LinearMap.pi_apply_eq_sum_univ φ z, Fintype.sum_prod_type]
            rfl
          let beta : Fin n → ℝ → ℝ := fun i c => if h : c ∈ S then g (i, ⟨c, h⟩) / f c else 0
          have hbetag : ∀ (i : Fin n) (s : ↥S), g (i, s) = f s * beta i s := by
            intro i s
            have := (hfS s s.2).ne'
            simp only [beta]
            rw [dif_pos s.2]
            field_simp
          have hb0 : ∀ θ : Profile (fun _ : Fin n => S), ∑ i, beta i (θ i) * xs θ i = 0 := by
            intro θ
            have h1 : φ (Matrix.mulVecLin Mx (Pi.single θ 1)) = 0 :=
              hφ2 ⟨Pi.single θ 1, rfl⟩
            rw [hφ, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
            have h2 : ∀ i : Fin n, ∑ s : ↥S, Mx (i, s) θ * g (i, s) = prob (fun _ => f) θ * (beta i (θ i) * xs θ i) := by
              intro i
              have h3 : ∀ s : ↥S, Mx (i, s) θ * g (i, s) =
                  if θ i = s then probOthers (fun _ => f) i θ * xs θ i * g (i, s) else 0 := by
                intro s
                simp only [Mx, Matrix.of_apply]
                split_ifs <;> simp
              rw [Finset.sum_congr rfl (fun s _ => h3 s), Finset.sum_ite_eq]
              rw [if_pos (Finset.mem_univ _), hbetag, hprob' i]
              ring
            have h1' : ∑ i : Fin n, ∑ s : ↥S, Mx (i, s) θ * g (i, s) = 0 := h1
            rw [Finset.sum_congr rfl (fun i _ => h2 i), ← Finset.mul_sum] at h1'
            exact (mul_eq_zero.mp h1').resolve_left (hprobpos θ).ne'
          have hC := hCore beta hb0
          rw [hφ, Finset.sum_comm]
          apply Finset.sum_eq_zero
          intro s _
          have h4 : ∀ i : Fin n, τ (i, s) * g (i, s) = f s * (((s:ℝ) - V s) * (beta i s * Xs i s) +
              ∑ b ∈ S.filter ((s:ℝ) < ·), (b - pr b) * (beta i s * Xs i b)) := by
            intro i
            rw [hbetag]
            have e : ∑ b ∈ S.filter ((s:ℝ) < ·), (b - pr b) * (beta i s * Xs i b) =
                beta i s * ∑ b ∈ S.filter ((s:ℝ) < ·), (b - pr b) * Xs i b := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
            rw [e]
            simp only [τ, hTs]
            ring
          rw [Finset.sum_congr rfl (fun i _ => h4 i), ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
            hC s s.2 s s.2 le_rfl, Finset.sum_comm]
          have h5 : ∑ b ∈ S.filter ((s:ℝ) < ·), ∑ i : Fin n, (b - pr b) * (beta i s * Xs i b) = 0 := by
            apply Finset.sum_eq_zero
            intro b hb
            rw [Finset.mem_filter] at hb
            rw [← Finset.mul_sum, hC s s.2 b hb.1 (hVmono s s.2 b hb.1 hb.2).le, mul_zero]
          rw [h5]; ring
        obtain ⟨k, hk⟩ := hmem
        refine ⟨k, fun i c hc => ?_⟩
        have h1 := congrFun hk (i, ⟨c, hc⟩)
        have h2 : interim (fun _ => f) (fun θ : Profile (fun _ : Fin n => S) => (V (θ i) + k θ) * xs θ i) i c =
            V c * Xs i c + Matrix.mulVecLin Mx k (i, ⟨c, hc⟩) := by
          rw [Matrix.mulVecLin_apply]
          simp only [Matrix.mulVec, dotProduct, hXs, interim]
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro θ _
          simp only [Mx, Matrix.of_apply]
          by_cases h : (θ i : ℝ) = c
          · have h' : θ i = (⟨c, hc⟩ : ↥S) := Subtype.ext h
            rw [if_pos h, if_pos h, if_pos h', h]; ring
          · have h' : ¬ θ i = (⟨c, hc⟩ : ↥S) := fun hh => h (congrArg Subtype.val hh)
            rw [if_neg h, if_neg h, if_neg h']; ring
        rw [h2, h1]
        simp only [τ]
        ring
      obtain ⟨k, hkT⟩ := hk
      have hpl : ∀ b, pr b ≤ b := by
        intro b
        rw [hprdef]
        unfold pred
        split_ifs with hne'
        · exact ((Finset.mem_filter.mp (Finset.max'_mem _ hne')).2).le
        · exact le_rfl
      have hXsnn : ∀ i c, 0 ≤ Xs i c := by
        intro i c
        simp only [hXs, interim]
        refine Finset.sum_nonneg (fun θ _ => ?_)
        split_ifs
        · exact mul_nonneg (hprobO i θ) ((hsx θ).1 i)
        · exact le_rfl
      have hICs : ∀ i, ∀ a ∈ S, ∀ b ∈ S, Ts i b - a * Xs i b ≤ Ts i a - a * Xs i a := by
        intro i
        have hmono : ∀ c ∈ S, ∀ c' ∈ S, c ≤ c' → Xs i c' ≤ Xs i c := by
          intro c hc c' hc' hcc
          rcases eq_or_lt_of_le hcc with h | h
          · rw [h]
          have hpt : ∀ θ : Profile (fun _ : Fin n => S), (θ i : ℝ) = c →
              xs (Function.update θ i ⟨c', hc'⟩) i ≤ xs θ i := by
            intro θ hθ
            set θ' : Profile (fun _ : Fin n => S) := Function.update θ i ⟨c', hc'⟩ with hθ'
            have h1 := hopt θ (xs θ') (hsx θ')
            have h2 := hopt θ' (xs θ) (hsx θ)
            have hvj : ∀ j, j ≠ i → V (θ' j) = V (θ j) := by
              intro j hj; simp [θ', Function.update_of_ne hj]
            have hvi : V (θ i) < V (θ' i) := by
              simp only [θ', Function.update_self, hθ]
              exact hVmono c hc c' hc' h
            have key : ∀ y : Fin n → ℝ, ∑ j, V (θ' j) * y j - ∑ j, V (θ j) * y j =
                (V (θ' i) - V (θ i)) * y i := by
              intro y
              rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
              · ring
              · intro j _ hj; rw [hvj j hj]; ring
              · simp
            have k1 := key (xs θ)
            have k2 := key (xs θ')
            simp only [CS] at h1 h2
            refine le_of_mul_le_mul_left ?_ (sub_pos.mpr hvi)
            linarith
          let ea : ↥S := ⟨c, hc⟩
          let eb : ↥S := ⟨c', hc'⟩
          let σ : Profile (fun _ : Fin n => S) ≃ Profile (fun _ : Fin n => S) := Equiv.piCongrRight
            (fun j => if j = i then Equiv.swap ea eb else Equiv.refl _)
          have hσi : ∀ θ : Profile (fun _ : Fin n => S), σ θ i = Equiv.swap ea eb (θ i) := by
            intro θ; simp [σ]
          have hσj : ∀ θ : Profile (fun _ : Fin n => S), ∀ j, j ≠ i → σ θ j = θ j := by
            intro θ j hj; simp [σ, hj]
          simp only [hXs, interim]
          rw [← Equiv.sum_comp σ]
          refine Finset.sum_le_sum (fun θ _ => ?_)
          by_cases hθ : (θ i : ℝ) = c
          · have hθe : θ i = ea := Subtype.ext hθ
            have hσθ : σ θ = Function.update θ i eb := by
              funext j
              by_cases hj : j = i
              · subst hj; rw [hσi, Function.update_self, hθe, Equiv.swap_apply_left]
              · rw [hσj θ j hj, Function.update_of_ne hj]
            have hpo : probOthers (fun _ => f) i (Function.update θ i eb) = probOthers (fun _ => f) i θ := by
              unfold probOthers
              refine Finset.prod_congr rfl (fun j hj => ?_)
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
            rw [hσθ, if_pos (by simp [eb]), if_pos hθ, hpo]
            exact mul_le_mul_of_nonneg_left (hpt θ hθ) (hprobO i θ)
          · rw [if_neg hθ, if_neg]
            intro hc2
            apply hθ
            have : σ θ i = eb := Subtype.ext hc2
            rw [hσi, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at this
            rw [this]
        have htele : ∀ b ∈ S, ∀ m : ℕ, ∀ a ∈ S, a ≤ b →
            (S.filter (fun b' => a < b' ∧ b' ≤ b)).card = m →
            ∑ b' ∈ S.filter (fun b' => a < b' ∧ b' ≤ b), (b' - pr b') = b - a := by
          intro b hb m
          induction m using Nat.strong_induction_on with
          | _ m ih =>
            intro a ha hab hm
            rcases eq_or_lt_of_le hab with h | h
            · subst h
              rw [sub_self]
              refine Finset.sum_eq_zero (fun b' hb' => ?_)
              obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hb'
              linarith
            · have hS' : (S.filter (a < ·)).Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, h⟩⟩
              set c' := (S.filter (a < ·)).min' hS' with hc'def
              obtain ⟨hc'Θ, hac'⟩ := Finset.mem_filter.mp (Finset.min'_mem (S.filter (a < ·)) hS')
              have hmin : ∀ x ∈ S, a < x → c' ≤ x := fun x hx hax =>
                Finset.min'_le _ x (Finset.mem_filter.mpr ⟨hx, hax⟩)
              have hc'b : c' ≤ b := hmin b hb h
              have hmem : c' ∈ S.filter (fun b' => a < b' ∧ b' ≤ b) :=
                Finset.mem_filter.mpr ⟨hc'Θ, hac', hc'b⟩
              have herase : (S.filter (fun b' => a < b' ∧ b' ≤ b)).erase c' =
                  S.filter (fun b' => c' < b' ∧ b' ≤ b) := by
                ext x
                simp only [Finset.mem_erase, Finset.mem_filter]
                constructor
                · rintro ⟨hne, hx, hax, hxb⟩
                  exact ⟨hx, lt_of_le_of_ne (hmin x hx hax) (Ne.symm hne), hxb⟩
                · rintro ⟨hx, hcx, hxb⟩
                  exact ⟨ne_of_gt hcx, hx, lt_trans hac' hcx, hxb⟩
              have hcard' : (S.filter (fun b' => c' < b' ∧ b' ≤ b)).card < m := by
                rw [← herase, Finset.card_erase_of_mem hmem, ← hm]
                exact Nat.sub_lt (Finset.card_pos.mpr ⟨c', hmem⟩) one_pos
              rw [← Finset.add_sum_erase _ _ hmem, herase, ih _ hcard' c' hc'Θ hc'b rfl,
                (show pr c' = a from hpred i0 a ha c' hc'Θ hac' hmin)]
              ring
        have hsplitS : ∀ a b, a ≤ b →
            ∑ b' ∈ S.filter (a < ·), (b' - pr b') * Xs i b' =
              ∑ b' ∈ S.filter (fun b' => a < b' ∧ b' ≤ b), (b' - pr b') * Xs i b' +
              ∑ b' ∈ S.filter (b < ·), (b' - pr b') * Xs i b' := by
          intro a b hab
          rw [← Finset.sum_filter_add_sum_filter_not (S.filter (a < ·)) (· ≤ b),
            Finset.filter_filter, Finset.filter_filter]
          congr 2
          · ext x; simp only [Finset.mem_filter, not_le]
            constructor
            · rintro ⟨hx, -, hbx⟩; exact ⟨hx, hbx⟩
            · rintro ⟨hx, hbx⟩; exact ⟨hx, lt_of_le_of_lt hab hbx, hbx⟩
        intro a ha b hb
        simp only [hTs]
        rcases le_total a b with hab | hab
        · rw [hsplitS a b hab]
          have hT := htele b hb _ a ha hab rfl
          have : (b - a) * Xs i b ≤
              ∑ b' ∈ S.filter (fun b' => a < b' ∧ b' ≤ b), (b' - pr b') * Xs i b' := by
            rw [← hT, Finset.sum_mul]
            refine Finset.sum_le_sum (fun x hx => ?_)
            obtain ⟨hx, -, hxb⟩ := Finset.mem_filter.mp hx
            exact mul_le_mul_of_nonneg_left (hmono x hx b hb hxb) (by linarith [hpl x])
          linarith
        · rw [hsplitS b a hab]
          have hT := htele a ha _ b hb hab rfl
          have : ∑ b' ∈ S.filter (fun b' => b < b' ∧ b' ≤ a), (b' - pr b') * Xs i b'
              ≤ (a - b) * Xs i b := by
            rw [← hT, Finset.sum_mul]
            refine Finset.sum_le_sum (fun x hx => ?_)
            obtain ⟨hx, hbx, -⟩ := Finset.mem_filter.mp hx
            exact mul_le_mul_of_nonneg_left (hmono b hb x hx hbx.le) (by linarith [hpl x])
          linarith
      have hut : ∀ i a b, b ∈ S → utility (fun _ => f) xs (fun θ i => (V (θ i) + k θ) * xs θ i) i b a =
          Ts i b - a * Xs i b := by
        intro i a b hb
        rw [← hkT i b hb]
        simp only [utility, interim, hXs]
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro θ _
        split_ifs <;> ring
      have hTnn : ∀ i c, 0 ≤ ∑ b ∈ S.filter (c < ·), (b - pr b) * Xs i b := by
        intro i c
        exact Finset.sum_nonneg (fun b _ => mul_nonneg (by linarith [hpl b]) (hXsnn i b))
      have hfeasC : IsCentFeasible (fun _ => f) (simplex n) xs (fun θ i => (V (θ i) + k θ) * xs θ i) := by
        refine ⟨?_, ?_, hsx⟩
        · intro i a ha b hb
          rw [hut i a b hb, hut i a a ha]
          exact hICs i a ha b hb
        · intro i a ha
          rw [hut i a a ha]
          simp only [hTs, add_sub_cancel_left]
          exact hTnn i a
      have hCSk : ∀ θ (y : Fin n → ℝ), y ∈ simplex n → CS (hotGCS (equiLoc n) delta) y (fun i => V (θ i) + k θ) =
          CS (hotGCS (equiLoc n) delta) y (fun i => V (θ i)) - k θ := by
        intro θ y hy
        simp only [CS, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hy.2]
        ring
      have hfeasD : IsDecLinFeasible (fun _ => f) (hotGCS (equiLoc n) delta) (simplex n) (fun _ => Finset.univ)
          (fun θ i => V (θ i) + k θ) xs := by
        refine ⟨hfeasC, fun θ => ⟨hsx θ, by simp, fun z hz _ => ?_⟩⟩
        rw [hCSk θ z hz, hCSk θ (xs θ) (hsx θ)]
        linarith [hopt θ z hz]
      -- expected transfers equal expected virtual costs
      have hTV : ∀ i : Fin n, expect (fun _ => f) (fun θ : Profile (fun _ : Fin n => S) => (V (θ i) + k θ) * xs θ i) =
          expect (fun _ => f) (fun θ : Profile (fun _ : Fin n => S) => V (θ i) * xs θ i) := by
        intro i
        rw [hE i, hE i]
        have e1 : ∀ c ∈ S, f c * interim (fun _ => f) (fun θ : Profile (fun _ : Fin n => S) => (V (θ i) + k θ) * xs θ i) i c =
            f c * c * Xs i c + f c * ∑ b ∈ S.filter (c < ·), (b - pr b) * Xs i b := by
          intro c hc
          rw [hkT i c hc]
          simp only [hTs]; ring
        have e2 : ∀ c ∈ S, f c * interim (fun _ => f) (fun θ : Profile (fun _ : Fin n => S) => V (θ i) * xs θ i) i c =
            f c * c * Xs i c + cdfF (fun _ : Fin n => S) (fun _ => f) i0 (pr c) * (c - pr c) * Xs i c := by
          intro c hc
          have h1 : interim (fun _ => f) (fun θ : Profile (fun _ : Fin n => S) => V (θ i) * xs θ i) i c = V c * Xs i c := by
            simp only [interim, hXs, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro θ _
            split_ifs with h
            · rw [h]; ring
            · simp
          have hf := (hfS c hc).ne'
          have h2 : V c = c + cdfF (fun _ : Fin n => S) (fun _ => f) i0 (pr c) / f c * (c - pr c) := rfl
          rw [h1, h2]
          field_simp
        rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_add_distrib, Finset.sum_add_distrib]
        congr 1
        exact hswap i0 (Xs i)
      have hlin : ∀ (z : Profile (fun _ : Fin n => S) → Fin n → ℝ) (g : Fin n → Profile (fun _ : Fin n => S) → ℝ),
          expect (fun _ => f) (fun θ => hotGCS (equiLoc n) delta (z θ) - ∑ i, g i θ) =
            expect (fun _ => f) (fun θ => hotGCS (equiLoc n) delta (z θ)) -
              ∑ i, expect (fun _ => f) (g i) := by
        intro z g
        unfold expect
        simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      have hval : decLinObj (fun _ => f) (hotGCS (equiLoc n) delta) (fun θ i => V (θ i) + k θ) xs =
          expect (fun _ => f) (fun θ : Profile (fun _ : Fin n => S) => hotGCS (equiLoc n) delta (xs θ) - ∑ i, V (θ i) * xs θ i) := by
        unfold decLinObj CS
        rw [hlin xs (fun i θ => (V (θ i) + k θ) * xs θ i), hlin xs (fun i θ => V (θ i) * xs θ i)]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => hTV i)
      have hub : ∀ r ∈ {r | ∃ x t : Profile (fun _ : Fin n => S) → Fin n → ℝ,
            IsCentFeasible (fun _ => f) (simplex n) x t ∧
            r = centObj (fun _ => f) (hotGCS (equiLoc n) delta) x t},
          r ≤ decLinObj (fun _ => f) (hotGCS (equiLoc n) delta) (fun θ i => V (θ i) + k θ) xs := by
        rintro r ⟨x, t, hft, rfl⟩
        refine (hCentUB x t hft).trans ?_
        rw [hval]
        unfold expect
        apply Finset.sum_le_sum
        intro θ _
        exact mul_le_mul_of_nonneg_left (hopt θ (x θ) (hft.2.2 θ)) (hprob θ)
      have hCbddA : BddAbove {r | ∃ x t : Profile (fun _ : Fin n => S) → Fin n → ℝ,
            IsCentFeasible (fun _ => f) (simplex n) x t ∧
            r = centObj (fun _ => f) (hotGCS (equiLoc n) delta) x t} := ⟨_, hub⟩
      have hDne : {r | ∃ (q : Profile (fun _ : Fin n => S) → Finset (Fin n))
            (p x : Profile (fun _ : Fin n => S) → Fin n → ℝ),
            IsDecLinFeasible (fun _ => f) (hotGCS (equiLoc n) delta) (simplex n) q p x ∧
            r = decLinObj (fun _ => f) (hotGCS (equiLoc n) delta) p x}.Nonempty := ⟨_, _, _, _, hfeasD, rfl⟩
      exact ⟨le_antisymm (csSup_le_csSup hCbddA hDne hDC)
        ((csSup_le (hDne.mono hDC) hub).trans (le_csSup (hCbddA.mono hDC) ⟨_, _, _, hfeasD, rfl⟩)),
        hDne.mono hDC, hCbddA, hDne, hCbddA.mono hDC⟩
