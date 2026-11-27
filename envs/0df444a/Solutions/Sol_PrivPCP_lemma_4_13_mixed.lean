-- Prove2me | solution 1 for PrivPCP.lemma_4_13_mixed
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:35:14.493864+00:00
-- url     : https://prove2.me/submissions/2d07db7c-9040-4ede-96f9-3fbf82edaea4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PrivPCP_gridQ
import Theorems.Thm_PrivPCP_lemma_4_13_mixed_closure


namespace PrivPCP.GD

open Classical MvPolynomial

variable {F : Type} [Field F]

lemma le_degreeOf_of_mem {R : MvPolynomial (Fin 2) F} {e : Fin 2 →₀ ℕ} (he : e ∈ R.support)
    (j : Fin 2) : e j ≤ R.degreeOf j :=
  (degreeOf_le_iff.mp le_rfl) e he

noncomputable def rowP (α : F) (P : MvPolynomial (Fin 2) F) : Polynomial F :=
  aeval (![Polynomial.C α, Polynomial.X] : Fin 2 → Polynomial F) P
noncomputable def colP (β : F) (P : MvPolynomial (Fin 2) F) : Polynomial F :=
  aeval (![Polynomial.X, Polynomial.C β] : Fin 2 → Polynomial F) P

lemma fin2_eq (z : Fin 2 → F) : ![z 0, z 1] = z := by funext i; fin_cases i <;> rfl

lemma eval_aeval_gen (f : Fin 2 → Polynomial F) (t : F) (P : MvPolynomial (Fin 2) F) :
    (aeval f P).eval t = eval (fun i => (f i).eval t) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, Polynomial.eval_mul, hp, map_mul, aeval_X, eval_X]

lemma eval_rowP (α y : F) (P : MvPolynomial (Fin 2) F) : (rowP α P).eval y = eval ![α, y] P := by
  unfold rowP; rw [eval_aeval_gen]; congr 2; funext i; fin_cases i <;> simp

lemma eval_colP (β x : F) (P : MvPolynomial (Fin 2) F) : (colP β P).eval x = eval ![x, β] P := by
  unfold colP; rw [eval_aeval_gen]; congr 2; funext i; fin_cases i <;> simp

lemma natDegree_aeval_le (f : Fin 2 → Polynomial F) (j : Fin 2) (hf : f j = Polynomial.X)
    (hc : ∀ l, l ≠ j → (f l).natDegree = 0) (P : MvPolynomial (Fin 2) F) :
    (aeval f P).natDegree ≤ P.degreeOf j := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ l, ((f l) ^ m l : Polynomial F).natDegree
      ≤ ∑ l, if l = j then m l else 0 := by
        refine Finset.sum_le_sum fun l _ => ?_
        refine (Polynomial.natDegree_pow_le).trans ?_
        split_ifs with h
        · subst h; rw [hf]; have := Polynomial.natDegree_X_le (R := F); nlinarith
        · rw [hc l h]; simp
    _ = m j := by simp
    _ ≤ P.degreeOf j := le_degreeOf_of_mem hm j

lemma natDegree_rowP (α : F) (P : MvPolynomial (Fin 2) F) : (rowP α P).natDegree ≤ P.degreeOf 1 :=
  natDegree_aeval_le _ 1 (by simp) (fun l hl => by fin_cases l <;> simp_all) P

lemma natDegree_colP (β : F) (P : MvPolynomial (Fin 2) F) : (colP β P).natDegree ≤ P.degreeOf 0 :=
  natDegree_aeval_le _ 0 (by simp) (fun l hl => by fin_cases l <;> simp_all) P

lemma rowP_mul (α : F) (P Q : MvPolynomial (Fin 2) F) : rowP α (P * Q) = rowP α P * rowP α Q := by
  unfold rowP; rw [map_mul]
lemma colP_mul (β : F) (P Q : MvPolynomial (Fin 2) F) : colP β (P * Q) = colP β P * colP β Q := by
  unfold colP; rw [map_mul]

lemma card_le_roots (p : Polynomial F) (hp : p ≠ 0) (s : Finset F) (hs : ∀ x ∈ s, p.eval x = 0) :
    s.card ≤ p.natDegree := by
  have h1 : s ⊆ p.roots.toFinset := by
    intro x hx; rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]; exact hs x hx
  exact (Finset.card_le_card h1).trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p))

lemma card_nonzero_ge (p : Polynomial F) (hp : p ≠ 0) (s : Finset F) :
    s.card ≤ (s.filter fun x => p.eval x ≠ 0).card + p.natDegree := by
  have := card_le_roots p hp (s.filter fun x => p.eval x = 0) (fun x hx => (Finset.mem_filter.1 hx).2)
  have h2 := Finset.card_filter_add_card_filter_not (s := s) (fun x => p.eval x ≠ 0)
  simp only [not_not] at h2
  omega

lemma aeval_pure0 (D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 1 = 0) {A : Type} [CommRing A]
    [Algebra F A] (f g : Fin 2 → A) (h0 : f 0 = g 0) : aeval f D = aeval g D := by
  conv_lhs => rw [D.as_sum]
  conv_rhs => rw [D.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  congr 1
  refine Finsupp.prod_congr fun i hi => ?_
  have : i = 0 := by
    fin_cases i
    · rfl
    · exfalso; rw [Finsupp.mem_support_iff] at hi
      have := le_degreeOf_of_mem hm 1; exact hi (Nat.le_zero.1 (hD ▸ this))
  subst this; rw [h0]

lemma aeval_pure1 (D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 0 = 0) {A : Type} [CommRing A]
    [Algebra F A] (f g : Fin 2 → A) (h1 : f 1 = g 1) : aeval f D = aeval g D := by
  conv_lhs => rw [D.as_sum]
  conv_rhs => rw [D.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  congr 1
  refine Finsupp.prod_congr fun i hi => ?_
  have : i = 1 := by
    fin_cases i
    · exfalso; rw [Finsupp.mem_support_iff] at hi
      have := le_degreeOf_of_mem hm 0; exact hi (Nat.le_zero.1 (hD ▸ this))
    · rfl
  subst this; rw [h1]

lemma aeval_X0_colP (D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 1 = 0) (β : F) :
    Polynomial.aeval (X 0 : MvPolynomial (Fin 2) F) (colP β D) = D := by
  unfold colP
  rw [← AlgHom.comp_apply, comp_aeval]
  conv_rhs => rw [← aeval_X_left_apply D]
  exact aeval_pure0 D hD _ _ (by simp)

lemma aeval_X1_rowP (D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 0 = 0) (α : F) :
    Polynomial.aeval (X 1 : MvPolynomial (Fin 2) F) (rowP α D) = D := by
  unfold rowP
  rw [← AlgHom.comp_apply, comp_aeval]
  conv_rhs => rw [← aeval_X_left_apply D]
  exact aeval_pure1 D hD _ _ (by simp)

end PrivPCP.GD


namespace PrivPCP.Fact33Aux

open MvPolynomial

variable {F : Type} [Field F] {k : ℕ}

lemma degreeOf_monomial_le' (s : Fin k →₀ ℕ) (c : F) (j : Fin k) :
    (monomial s c : MvPolynomial (Fin k) F).degreeOf j ≤ s j := by
  rw [degreeOf_le_iff]
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]

lemma degreeOf_aeval_X_le (i j : Fin k) (p : Polynomial F) :
    (Polynomial.aeval (X i : MvPolynomial (Fin k) F) p).degreeOf j ≤
      if j = i then p.natDegree else 0 := by
  rw [Polynomial.aeval_eq_sum_range]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun n hn => ?_)
  rw [MvPolynomial.smul_eq_C_mul]
  refine (degreeOf_C_mul_le _ _ _).trans ?_
  split_ifs with h
  · subst h
    rw [degreeOf_X_self_pow]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  · rw [degreeOf_X_pow_of_ne _ h]

lemma le_degreeOf_of_mem {R : MvPolynomial (Fin k) F} {e : Fin k →₀ ℕ} (he : e ∈ R.support)
    (j : Fin k) : e j ≤ R.degreeOf j :=
  (degreeOf_le_iff.mp le_rfl) e he

/-- quotient of division by `Z(X_i)` -/
noncomputable def divQ (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F) :
    MvPolynomial (Fin k) F :=
  ∑ e ∈ R.support, monomial (Finsupp.update e i 0) (R.coeff e) *
    Polynomial.aeval (X i) (Polynomial.X ^ (e i) /ₘ Z)

/-- remainder of division by `Z(X_i)` -/
noncomputable def divR (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F) :
    MvPolynomial (Fin k) F :=
  ∑ e ∈ R.support, monomial (Finsupp.update e i 0) (R.coeff e) *
    Polynomial.aeval (X i) (Polynomial.X ^ (e i) %ₘ Z)

lemma div_eq (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F) :
    R = Polynomial.aeval (X i) Z * divQ i Z R + divR i Z R := by
  conv_lhs => rw [as_sum R]
  unfold divQ divR
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h1 : (monomial e (R.coeff e) : MvPolynomial (Fin k) F) =
      monomial (Finsupp.update e i 0) (R.coeff e) * X i ^ (e i) := by
    have hs : Finsupp.update e i 0 + Finsupp.single i (e i) = e := by
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Finsupp.update_apply, hj, Finsupp.single_apply, Ne.symm hj]
    rw [X_pow_eq_monomial, monomial_mul, mul_one, hs]
  have h2 : (X i : MvPolynomial (Fin k) F) ^ (e i) =
      Polynomial.aeval (X i) (Polynomial.X ^ (e i) %ₘ Z + Z * (Polynomial.X ^ (e i) /ₘ Z)) := by
    rw [Polynomial.modByMonic_add_div]; simp
  rw [h1, h2, map_add, map_mul]
  ring

lemma divQ_degreeOf (i : Fin k) (Z : Polynomial F) (hZ : Z.Monic) (R : MvPolynomial (Fin k) F)
    (j : Fin k) :
    (divQ i Z R).degreeOf j ≤ if j = i then R.degreeOf i - Z.natDegree else R.degreeOf j := by
  unfold divQ
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add (degreeOf_monomial_le' _ _ _) (degreeOf_aeval_X_le _ _ _)).trans ?_
  split_ifs with h
  · subst h
    have h0 : (Finsupp.update e j 0) j = 0 := by simp
    rw [h0, zero_add]
    rw [Polynomial.natDegree_divByMonic _ hZ, Polynomial.natDegree_X_pow]
    exact Nat.sub_le_sub_right (le_degreeOf_of_mem he j) _
  · simp only [Finsupp.update_apply, h, if_false, add_zero]
    exact le_degreeOf_of_mem he j

lemma divR_degreeOf_ne (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F)
    (j : Fin k) (hj : j ≠ i) : (divR i Z R).degreeOf j ≤ R.degreeOf j := by
  unfold divR
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add (degreeOf_monomial_le' _ _ _) (degreeOf_aeval_X_le _ _ _)).trans ?_
  simp only [Finsupp.update_apply, hj, if_false, add_zero]
  exact le_degreeOf_of_mem he j

lemma divR_degreeOf_self (i : Fin k) (Z : Polynomial F) (hZ : Z.Monic) (hZ1 : Z ≠ 1)
    (R : MvPolynomial (Fin k) F) : (divR i Z R).degreeOf i < Z.natDegree := by
  have hpos : 0 < Z.natDegree := by
    rcases Nat.eq_zero_or_pos Z.natDegree with h | h
    · exact absurd (Polynomial.eq_one_of_monic_natDegree_zero hZ h) hZ1
    · exact h
  have : (divR i Z R).degreeOf i ≤ Z.natDegree - 1 := by
    unfold divR
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
    refine (degreeOf_mul_le _ _ _).trans ?_
    refine (add_le_add (degreeOf_monomial_le' _ _ _) (degreeOf_aeval_X_le _ _ _)).trans ?_
    have h0 : (Finsupp.update e i 0) i = 0 := by simp
    simp only [h0, if_true, zero_add]
    have := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ (e i)) hZ hZ1
    omega
  omega

end PrivPCP.Fact33Aux


namespace PrivPCP.GD

open Classical MvPolynomial PrivPCP.Fact33Aux

variable {F : Type} [Field F]

lemma eval_aeval_X' (p : Polynomial F) (l : Fin 2) (z : Fin 2 → F) :
    eval z (Polynomial.aeval (X l : MvPolynomial (Fin 2) F) p) = p.eval (z l) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

noncomputable def lbas (B : Finset F) (β : F) : Polynomial F := Lagrange.basis B id β

lemma eval_lbas (B : Finset F) (β b : F) (hβ : β ∈ B) (hb : b ∈ B) :
    (lbas B β).eval b = if β = b then 1 else 0 := by
  unfold lbas
  split_ifs with h
  · subst h
    have := Lagrange.eval_basis_self (v := (id : F → F)) (Set.injOn_id _) hβ
    simpa using this
  · have := Lagrange.eval_basis_of_ne (v := (id : F → F)) (s := B) h hb
    simpa using this

lemma natDegree_lbas (B : Finset F) (β : F) (hβ : β ∈ B) : (lbas B β).natDegree < B.card := by
  unfold lbas
  rw [Lagrange.natDegree_basis (Set.injOn_id _) hβ]
  have : 0 < B.card := Finset.card_pos.mpr ⟨β, hβ⟩
  omega

noncomputable def interpY (B : Finset F) (G : MvPolynomial (Fin 2) F) : MvPolynomial (Fin 2) F :=
  ∑ β ∈ B, Polynomial.aeval (X 0 : MvPolynomial (Fin 2) F) (colP β G) *
    Polynomial.aeval (X 1 : MvPolynomial (Fin 2) F) (lbas B β)

noncomputable def interpX (A : Finset F) (G : MvPolynomial (Fin 2) F) : MvPolynomial (Fin 2) F :=
  ∑ α ∈ A, Polynomial.aeval (X 0 : MvPolynomial (Fin 2) F) (lbas A α) *
    Polynomial.aeval (X 1 : MvPolynomial (Fin 2) F) (rowP α G)

lemma interpY_deg0 (B : Finset F) (G : MvPolynomial (Fin 2) F) : (interpY B G).degreeOf 0 ≤ G.degreeOf 0 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun β _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_aeval_X_le (0 : Fin 2) (0 : Fin 2) (colP β G)
  have h2 := degreeOf_aeval_X_le (1 : Fin 2) (0 : Fin 2) (lbas B β)
  rw [if_pos rfl] at h1
  rw [if_neg (show (0 : Fin 2) ≠ 1 by decide)] at h2
  have := natDegree_colP β G
  exact (add_le_add h1 h2).trans (by omega)

lemma interpY_deg1 (B : Finset F) (G : MvPolynomial (Fin 2) F) (hB : 0 < B.card) :
    (interpY B G).degreeOf 1 ≤ B.card - 1 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun β hβ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_aeval_X_le (0 : Fin 2) (1 : Fin 2) (colP β G)
  have h2 := degreeOf_aeval_X_le (1 : Fin 2) (1 : Fin 2) (lbas B β)
  rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h1
  rw [if_pos rfl] at h2
  have := natDegree_lbas B β hβ
  exact (add_le_add h1 h2).trans (by omega)

lemma interpX_deg1 (A : Finset F) (G : MvPolynomial (Fin 2) F) : (interpX A G).degreeOf 1 ≤ G.degreeOf 1 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun α _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_aeval_X_le (0 : Fin 2) (1 : Fin 2) (lbas A α)
  have h2 := degreeOf_aeval_X_le (1 : Fin 2) (1 : Fin 2) (rowP α G)
  rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h1
  rw [if_pos rfl] at h2
  have := natDegree_rowP α G
  exact (add_le_add h1 h2).trans (by omega)

lemma interpX_deg0 (A : Finset F) (G : MvPolynomial (Fin 2) F) (hA : 0 < A.card) :
    (interpX A G).degreeOf 0 ≤ A.card - 1 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun α hα => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_aeval_X_le (0 : Fin 2) (0 : Fin 2) (lbas A α)
  have h2 := degreeOf_aeval_X_le (1 : Fin 2) (0 : Fin 2) (rowP α G)
  rw [if_pos rfl] at h1
  rw [if_neg (show (0 : Fin 2) ≠ 1 by decide)] at h2
  have := natDegree_lbas A α hα
  exact (add_le_add h1 h2).trans (by omega)

lemma eq_on_grid (A B : Finset F) (P Q : MvPolynomial (Fin 2) F)
    (hP0 : P.degreeOf 0 < A.card) (hP1 : P.degreeOf 1 < B.card)
    (hQ0 : Q.degreeOf 0 < A.card) (hQ1 : Q.degreeOf 1 < B.card)
    (h : ∀ a ∈ A, ∀ b ∈ B, eval ![a, b] P = eval ![a, b] Q) : P = Q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_eval_zero_at_prod_finset _ ![A, B]
  · intro l; fin_cases l
    · exact lt_of_le_of_lt (degreeOf_sub_le _ _ _) (max_lt hP0 hQ0)
    · exact lt_of_le_of_lt (degreeOf_sub_le _ _ _) (max_lt hP1 hQ1)
  · intro x hx
    have hx0 : x 0 ∈ A := by simpa using hx 0
    have hx1 : x 1 ∈ B := by simpa using hx 1
    rw [map_sub, ← fin2_eq x, h _ hx0 _ hx1, sub_self]

lemma interpY_eq (A B : Finset F) (G : MvPolynomial (Fin 2) F) (hGA : G.degreeOf 0 < A.card)
    (hGB : G.degreeOf 1 < B.card) : interpY B G = G := by
  have hB : 0 < B.card := by omega
  apply eq_on_grid A B _ _ (lt_of_le_of_lt (interpY_deg0 B G) hGA)
    (lt_of_le_of_lt (interpY_deg1 B G hB) (by omega)) hGA hGB
  intro a _ b hb
  unfold interpY
  rw [map_sum, Finset.sum_eq_single b]
  · rw [map_mul, eval_aeval_X', eval_aeval_X']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [eval_lbas B _ _ hb hb, if_pos rfl, mul_one, eval_colP]
  · intro β hβ hne
    rw [map_mul, eval_aeval_X', eval_aeval_X']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [eval_lbas B _ _ hβ hb, if_neg hne, mul_zero]
  · intro h; exact absurd hb h

lemma interpX_eq (A B : Finset F) (G : MvPolynomial (Fin 2) F) (hGA : G.degreeOf 0 < A.card)
    (hGB : G.degreeOf 1 < B.card) : interpX A G = G := by
  have hA : 0 < A.card := by omega
  apply eq_on_grid A B _ _ (lt_of_le_of_lt (interpX_deg0 A G hA) (by omega))
    (lt_of_le_of_lt (interpX_deg1 A G) hGB) hGA hGB
  intro a ha b _
  unfold interpX
  rw [map_sum, Finset.sum_eq_single a]
  · rw [map_mul, eval_aeval_X', eval_aeval_X']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [eval_lbas A _ _ ha ha, if_pos rfl, one_mul, eval_rowP]
  · intro α hα hne
    rw [map_mul, eval_aeval_X', eval_aeval_X']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [eval_lbas A _ _ hα ha, if_neg hne, zero_mul]
  · intro h; exact absurd ha h

lemma int_div_col (G D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 1 = 0) (A B : Finset F)
    (hGA : G.degreeOf 0 < A.card) (hGB : G.degreeOf 1 < B.card)
    (h : ∀ β ∈ B, colP β D ∣ colP β G) : D ∣ G := by
  rw [← interpY_eq A B G hGA hGB]
  unfold interpY
  refine Finset.dvd_sum fun β hβ => ?_
  obtain ⟨R, hR⟩ := h β hβ
  rw [hR, map_mul, aeval_X0_colP D hD, mul_assoc]
  exact dvd_mul_right _ _

lemma int_div_row (G V : MvPolynomial (Fin 2) F) (hV : V.degreeOf 0 = 0) (A B : Finset F)
    (hGA : G.degreeOf 0 < A.card) (hGB : G.degreeOf 1 < B.card)
    (h : ∀ α ∈ A, rowP α V ∣ rowP α G) : V ∣ G := by
  rw [← interpX_eq A B G hGA hGB]
  unfold interpX
  refine Finset.dvd_sum fun α hα => ?_
  obtain ⟨R, hR⟩ := h α hα
  rw [hR, map_mul, aeval_X1_rowP V hV, ← mul_assoc, mul_comm _ V, mul_assoc]
  exact dvd_mul_right _ _

end PrivPCP.GD


namespace PrivPCP.GD

open Classical MvPolynomial

variable {F : Type} [Field F]


lemma degreeOf_unit {u : MvPolynomial (Fin 2) F} (hu : IsUnit u) (i : Fin 2) : u.degreeOf i = 0 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have := degreeOf_mul_eq (n := i) hu0 hv0
  rw [hv, ← C_1, degreeOf_C] at this
  omega

lemma not_isUnit_lin (α : F) (i : Fin 2) : ¬ IsUnit (X i - C α : MvPolynomial (Fin 2) F) := by
  intro h
  have h2 := h.map (eval (fun _ => α))
  simp at h2

lemma rowP_ne_zero_of_irred (G : MvPolynomial (Fin 2) F) (hG : Irreducible G) (h1 : 0 < G.degreeOf 1)
    (A B : Finset F) (hA : G.degreeOf 0 < A.card) (hB : G.degreeOf 1 < B.card) (α : F) :
    rowP α G ≠ 0 := by
  intro h0
  set D : MvPolynomial (Fin 2) F := X 0 - C α
  have hD1 : D.degreeOf 1 = 0 := by
    have : D.degreeOf 1 ≤ max ((X 0 : MvPolynomial (Fin 2) F).degreeOf 1) ((C α : MvPolynomial (Fin 2) F).degreeOf 1) :=
      degreeOf_sub_le _ _ _
    rw [degreeOf_X, degreeOf_C, if_neg (by decide)] at this
    omega
  have hDG : D ∣ G := by
    apply int_div_col G D hD1 A B hA hB
    intro β _
    have : colP β D = Polynomial.X - Polynomial.C α := by simp [D, colP]
    rw [this, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, eval_colP, ← eval_rowP, h0,
      Polynomial.eval_zero]
  obtain ⟨u, hu⟩ := hDG
  rcases hG.isUnit_or_isUnit hu with hD | hu'
  · exact not_isUnit_lin α 0 hD
  · have hD0 : D ≠ 0 := by rintro hD; rw [hD, zero_mul] at hu; exact hG.ne_zero hu
    have := degreeOf_mul_eq (n := (1 : Fin 2)) hD0 hu'.ne_zero
    rw [← hu, hD1, degreeOf_unit hu'] at this
    omega

lemma colP_ne_zero_of_irred (G : MvPolynomial (Fin 2) F) (hG : Irreducible G) (h0 : 0 < G.degreeOf 0)
    (A B : Finset F) (hA : G.degreeOf 0 < A.card) (hB : G.degreeOf 1 < B.card) (β : F) :
    colP β G ≠ 0 := by
  intro hc
  set D : MvPolynomial (Fin 2) F := X 1 - C β
  have hD0' : D.degreeOf 0 = 0 := by
    have : D.degreeOf 0 ≤ max ((X 1 : MvPolynomial (Fin 2) F).degreeOf 0) ((C β : MvPolynomial (Fin 2) F).degreeOf 0) :=
      degreeOf_sub_le _ _ _
    rw [degreeOf_X, degreeOf_C, if_neg (by decide)] at this
    omega
  have hDG : D ∣ G := by
    apply int_div_row G D hD0' A B hA hB
    intro α _
    have : rowP α D = Polynomial.X - Polynomial.C β := by simp [D, rowP]
    rw [this, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, eval_rowP, ← eval_colP, hc,
      Polynomial.eval_zero]
  obtain ⟨u, hu⟩ := hDG
  rcases hG.isUnit_or_isUnit hu with hD | hu'
  · exact not_isUnit_lin β 1 hD
  · have hD0 : D ≠ 0 := by rintro hD; rw [hD, zero_mul] at hu; exact hG.ne_zero hu
    have := degreeOf_mul_eq (n := (0 : Fin 2)) hD0 hu'.ne_zero
    rw [← hu, hD0', degreeOf_unit hu'] at this
    omega

/-- a polynomial without mixed irreducible factors splits as `U(X) V(Y)` -/
lemma pure_split (E : MvPolynomial (Fin 2) F) (hE : E ≠ 0)
    (h : ∀ G, Irreducible G → G ∣ E → G.degreeOf 0 = 0 ∨ G.degreeOf 1 = 0) :
    ∃ U V : MvPolynomial (Fin 2) F, E = U * V ∧ U.degreeOf 1 = 0 ∧ V.degreeOf 0 = 0 := by
  induction E using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hE
  | h₂ x hx => exact ⟨x, 1, (mul_one x).symm, degreeOf_unit hx 1, by rw [← C_1, degreeOf_C]⟩
  | h₃ a p ha hp ih =>
    obtain ⟨U, V, rfl, hU, hV⟩ := ih ha (fun G hG hGa => h G hG (dvd_mul_of_dvd_right hGa p))
    have hp0 : p ≠ 0 := hp.ne_zero
    rcases h p hp.irreducible (dvd_mul_right p _) with h0 | h1
    · refine ⟨U, p * V, by ring, hU, ?_⟩
      have := degreeOf_mul_le (0 : Fin 2) p V
      omega
    · refine ⟨p * U, V, by ring, ?_, hV⟩
      have := degreeOf_mul_le (1 : Fin 2) p U
      omega

def Rows (A : Finset F) (E P : MvPolynomial (Fin 2) F) : Prop :=
  ∀ α ∈ A, ∃ R : Polynomial F, rowP α P = rowP α E * R
def Cols (B : Finset F) (E P : MvPolynomial (Fin 2) F) : Prop :=
  ∀ β ∈ B, ∃ R : Polynomial F, colP β P = colP β E * R

theorem div_main (A B : Finset F) (k1 k2 : ℕ) (τ : ℝ)
    (hτ : ∀ e : ℕ, (e : ℝ) ≤ τ → k1 + e < A.card ∧ k2 + e < B.card)
    (Hmix : ∀ E P : MvPolynomial (Fin 2) F, E ≠ 0 → (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤ τ →
      P.degreeOf 0 < k1 + E.degreeOf 0 → P.degreeOf 1 < k2 + E.degreeOf 1 → Rows A E P →
      Cols B E P → ∀ G, Irreducible G → G ∣ E → 0 < G.degreeOf 0 → 0 < G.degreeOf 1 → G ∣ P) :
    ∀ n, ∀ E P : MvPolynomial (Fin 2) F, E.degreeOf 0 + E.degreeOf 1 = n → E ≠ 0 →
      (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤ τ →
      P.degreeOf 0 < k1 + E.degreeOf 0 → P.degreeOf 1 < k2 + E.degreeOf 1 → Rows A E P →
      Cols B E P → E ∣ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E P hn hE hτE hPX hPY hR hC
  have hA0 := (hτ _ (le_trans (le_max_left _ _) hτE)).1
  have hB1 := (hτ _ (le_trans (le_max_right _ _) hτE)).2
  by_cases hP : P = 0
  · rw [hP]; exact dvd_zero E
  by_cases hmix : ∃ G, Irreducible G ∧ G ∣ E ∧ 0 < G.degreeOf 0 ∧ 0 < G.degreeOf 1
  · obtain ⟨G, hG, hGE, hG0, hG1⟩ := hmix
    have hGP := Hmix E P hE hτE hPX hPY hR hC G hG hGE hG0 hG1
    obtain ⟨E', rfl⟩ := hGE
    obtain ⟨P', rfl⟩ := hGP
    have hGn : G ≠ 0 := hG.ne_zero
    have hE' : E' ≠ 0 := right_ne_zero_of_mul hE
    have hP' : P' ≠ 0 := right_ne_zero_of_mul hP
    have dE0 := degreeOf_mul_eq (n := (0 : Fin 2)) hGn hE'
    have dE1 := degreeOf_mul_eq (n := (1 : Fin 2)) hGn hE'
    have dP0 := degreeOf_mul_eq (n := (0 : Fin 2)) hGn hP'
    have dP1 := degreeOf_mul_eq (n := (1 : Fin 2)) hGn hP'
    have hrowG : ∀ α, rowP α G ≠ 0 := rowP_ne_zero_of_irred G hG hG1 A B (by omega) (by omega)
    have hcolG : ∀ β, colP β G ≠ 0 := colP_ne_zero_of_irred G hG hG0 A B (by omega) (by omega)
    have hR' : Rows A E' P' := by
      intro α hα
      obtain ⟨R, hR⟩ := hR α hα
      refine ⟨R, ?_⟩
      rw [rowP_mul, rowP_mul, mul_assoc] at hR
      exact mul_left_cancel₀ (hrowG α) hR
    have hC' : Cols B E' P' := by
      intro β hβ
      obtain ⟨R, hR⟩ := hC β hβ
      refine ⟨R, ?_⟩
      rw [colP_mul, colP_mul, mul_assoc] at hR
      exact mul_left_cancel₀ (hcolG β) hR
    have hτ' : (max (E'.degreeOf 0) (E'.degreeOf 1) : ℝ) ≤ τ := by
      refine le_trans ?_ hτE
      rw [dE0, dE1]
      push_cast
      exact max_le_max (by linarith) (by linarith)
    have := ih (E'.degreeOf 0 + E'.degreeOf 1) (by omega) E' P' rfl hE' hτ' (by omega) (by omega)
      hR' hC'
    exact mul_dvd_mul_left G this
  · push Not at hmix
    obtain ⟨U, V, rfl, hU, hV⟩ := pure_split E hE (fun G hG hGE => by
      by_cases h0 : G.degreeOf 0 = 0
      · exact Or.inl h0
      · right; have := hmix G hG hGE (by omega); omega)
    have hU0 : U ≠ 0 := left_ne_zero_of_mul hE
    have hV0 : V ≠ 0 := right_ne_zero_of_mul hE
    have d0 := degreeOf_mul_eq (n := (0 : Fin 2)) hU0 hV0
    have d1 := degreeOf_mul_eq (n := (1 : Fin 2)) hU0 hV0
    have hVP : V ∣ P := by
      apply int_div_row P V hV A B (by omega) (by omega)
      intro α hα
      obtain ⟨R, hR⟩ := hR α hα
      rw [rowP_mul] at hR
      exact ⟨rowP α U * R, by rw [hR]; ring⟩
    obtain ⟨P1, rfl⟩ := hVP
    have hP1 : P1 ≠ 0 := right_ne_zero_of_mul hP
    have e0 := degreeOf_mul_eq (n := (0 : Fin 2)) hV0 hP1
    have e1 := degreeOf_mul_eq (n := (1 : Fin 2)) hV0 hP1
    set v := rowP 0 V with hvdef
    have hv : v ≠ 0 := by
      intro h0; apply hV0; rw [← aeval_X1_rowP V hV 0, ← hvdef, h0, map_zero]
    set Bg := B.filter fun β => v.eval β ≠ 0 with hBg
    have hcard : B.card ≤ Bg.card + v.natDegree := card_nonzero_ge v hv B
    have hvd : v.natDegree ≤ V.degreeOf 1 := natDegree_rowP 0 V
    have hcolV : ∀ β ∈ Bg, colP β V ≠ 0 := by
      intro β hβ h0
      have := (Finset.mem_filter.1 hβ).2
      apply this
      rw [hvdef, eval_rowP, ← eval_colP, h0, Polynomial.eval_zero]
    have hUP : U ∣ P1 := by
      apply int_div_col P1 U hU A Bg (by omega) (by omega)
      intro β hβ
      obtain ⟨C, hC'⟩ := hC β (Finset.mem_filter.1 hβ).1
      rw [colP_mul, colP_mul] at hC'
      exact ⟨C, mul_left_cancel₀ (hcolV β hβ) (by rw [hC']; ring)⟩
    obtain ⟨Q, rfl⟩ := hUP
    exact ⟨Q, by ring⟩

end PrivPCP.GD


namespace PrivPCP.GD

open Classical MvPolynomial

variable {q : ℕ} [Fact q.Prime]

local notation "K" => AlgebraicClosure (ZMod q)

lemma iota_inj : Function.Injective (algebraMap (ZMod q) K) := (algebraMap (ZMod q) K).injective

lemma fixed_mem_range (c : K) (hc : c ^ q = c) : c ∈ Set.range (algebraMap (ZMod q) K) := by
  by_contra hn
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  set p : Polynomial K := Polynomial.X ^ q - Polynomial.X
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq1
  have hpd : p.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
  set s : Finset K := insert c (Finset.univ.image (algebraMap (ZMod q) K))
  have hcard : s.card = q + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ iota_inj, Finset.card_univ,
      ZMod.card]
    intro hm; rw [Finset.mem_image] at hm
    obtain ⟨a, -, ha⟩ := hm; exact hn ⟨a, ha⟩
  have := card_le_roots p hp0 s (by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_image] at hx
    simp only [p, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rcases hx with rfl | ⟨a, -, rfl⟩
    · rw [hc, sub_self]
    · rw [← map_pow, ZMod.pow_card, sub_self])
  omega

lemma frob_iota (a : ZMod q) : (algebraMap (ZMod q) K a) ^ q = algebraMap (ZMod q) K a := by
  rw [← map_pow, ZMod.pow_card]

/-- divisibility descends from `𝔽̄_q` to `𝔽_q` -/
theorem dvd_descent (E P : MvPolynomial (Fin 2) (ZMod q)) (hE : E ≠ 0)
    (h : map (algebraMap (ZMod q) K) E ∣ map (algebraMap (ZMod q) K) P) : E ∣ P := by
  set ι := algebraMap (ZMod q) K
  obtain ⟨Q', hQ'⟩ := h
  haveI : CharP K q := charP_of_injective_algebraMap iota_inj q
  haveI : ExpChar K q := ExpChar.prime (Fact.out)
  set φ := frobenius K q
  have hφι : φ.comp ι = ι := by
    ext a; simp only [RingHom.comp_apply, φ, frobenius_def]; exact frob_iota a
  have hmapφ : ∀ R : MvPolynomial (Fin 2) (ZMod q), map φ (map ι R) = map ι R := by
    intro R; rw [map_map, hφι]
  have hE' : map ι E ≠ 0 := by
    intro h0; apply hE; apply map_injective ι iota_inj; rw [h0, map_zero]
  have hfix : map φ Q' = Q' := by
    have := congrArg (map φ) hQ'
    rw [hmapφ, map_mul, hmapφ, hQ'] at this
    exact (mul_left_cancel₀ hE' this).symm
  have hcoef : ((Q'.coeffs : Set K)) ⊆ Set.range ι := by
    intro c hc
    obtain ⟨m, hm, rfl⟩ := mem_coeffs_iff.1 hc
    apply fixed_mem_range
    have := congrArg (coeff m) hfix
    rw [coeff_map] at this
    simpa [φ, frobenius_def] using this
  obtain ⟨Q, rfl⟩ := mem_range_map_iff_coeffs_subset.2 hcoef
  refine ⟨Q, map_injective ι iota_inj ?_⟩
  rw [hQ', map_mul]

lemma degreeOf_map_iota (P : MvPolynomial (Fin 2) (ZMod q)) (i : Fin 2) :
    (map (algebraMap (ZMod q) K) P).degreeOf i = P.degreeOf i := by
  unfold degreeOf
  rw [degrees_map_of_injective _ iota_inj]

lemma rowP_map (α : ZMod q) (P : MvPolynomial (Fin 2) (ZMod q)) :
    rowP (algebraMap (ZMod q) K α) (map (algebraMap (ZMod q) K) P) =
      Polynomial.map (algebraMap (ZMod q) K) (rowP α P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowP]
  | add p r hp hr => simp only [map_add, rowP] at hp hr ⊢; rw [hp, hr, Polynomial.map_add]
  | mul_X p i hp =>
    simp only [map_mul, rowP] at hp ⊢
    rw [hp, Polynomial.map_mul]
    congr 1
    fin_cases i <;> simp

lemma colP_map (β : ZMod q) (P : MvPolynomial (Fin 2) (ZMod q)) :
    colP (algebraMap (ZMod q) K β) (map (algebraMap (ZMod q) K) P) =
      Polynomial.map (algebraMap (ZMod q) K) (colP β P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [colP]
  | add p r hp hr => simp only [map_add, colP] at hp hr ⊢; rw [hp, hr, Polynomial.map_add]
  | mul_X p i hp =>
    simp only [map_mul, colP] at hp ⊢
    rw [hp, Polynomial.map_mul]
    congr 1
    fin_cases i <;> simp

end PrivPCP.GD


namespace PrivPCP.GD

lemma tau_le (c1 h n1 n2 : ℝ) (hc1 : 0 < c1) (hc1' : c1 ≤ 1 / 2) (hh : 0 ≤ h) (hn1 : 0 < n1)
    (hn2 : 0 < n2) (hh1 : h ≤ n1) (hh2 : h ≤ n2) : c1 * h ^ 3 / (n1 * n2) ≤ h / 2 := by
  have hN : 0 < n1 * n2 := mul_pos hn1 hn2
  rw [div_le_iff₀ hN]
  have hhN : h * h ≤ n1 * n2 := mul_le_mul hh1 hh2 hh hn1.le
  have e1 : h ^ 3 = h * (h * h) := by ring
  rw [e1]
  have a := mul_le_mul_of_nonneg_left hhN hh
  have b : c1 * (h * (h * h)) ≤ (1 / 2) * (h * (h * h)) :=
    mul_le_mul_of_nonneg_right hc1' (by positivity)
  nlinarith

end PrivPCP.GD

open PrivPCP PrivPCP.GD Classical MvPolynomial in
theorem solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (q : ℕ) [Fact q.Prime] (S₁ S₂ : Subgroup (ZMod q)ˣ),
      Nat.Coprime (Nat.card S₁) (Nat.card S₂) →
      ∀ k₁ k₂ : ℕ, k₁ < Nat.card S₁ → k₂ < Nat.card S₂ →
      ∀ E P : MvPolynomial (Fin 2) (ZMod q), E ≠ 0 →
        (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤
          c₀ * ((min (Nat.card S₁ - k₁) (Nat.card S₂ - k₂) : ℕ) : ℝ) ^ 3 / ((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) →
        P.degreeOf 0 < k₁ + E.degreeOf 0 →
        P.degreeOf 1 < k₂ + E.degreeOf 1 →
        (∀ α ∈ S₁, ∃ R : Polynomial (ZMod q),
          MvPolynomial.aeval (![Polynomial.C (α : ZMod q), Polynomial.X] : Fin 2 → Polynomial (ZMod q)) P =
            MvPolynomial.aeval (![Polynomial.C (α : ZMod q), Polynomial.X] : Fin 2 → Polynomial (ZMod q)) E * R) →
        (∀ β ∈ S₂, ∃ Cβ : Polynomial (ZMod q),
          MvPolynomial.aeval (![Polynomial.X, Polynomial.C (β : ZMod q)] : Fin 2 → Polynomial (ZMod q)) P =
            MvPolynomial.aeval (![Polynomial.X, Polynomial.C (β : ZMod q)] : Fin 2 → Polynomial (ZMod q)) E * Cβ) →
        ∀ F : MvPolynomial (Fin 2) (ZMod q), Irreducible F → F ∣ E →
          0 < F.degreeOf 0 → 0 < F.degreeOf 1 → F ∣ P := by
  obtain ⟨c0, hc0, Hc⟩ := PrivPCP.lemma_4_13_mixed_closure
  have hc1 : 0 < min c0 (1 / 2) := lt_min hc0 (by norm_num)
  refine ⟨min c0 (1 / 2), hc1, ?_⟩
  intro q _ S₁ S₂ hcop k₁ k₂ hk1n hk2n E P hE hmax hPX hPY hrow hcol F hF hFE hF0 hF1
  refine dvd_trans hFE ?_
  have hc1' : min c0 (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hc10 : min c0 (1 / 2) ≤ c0 := min_le_left _ _
  set ι := algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) with hιdef
  set A : Finset (AlgebraicClosure (ZMod q)) :=
    (Finset.univ : Finset S₁).image (fun u : S₁ => ι ((u : (ZMod q)ˣ) : ZMod q)) with hAdef
  set B : Finset (AlgebraicClosure (ZMod q)) :=
    (Finset.univ : Finset S₂).image (fun u : S₂ => ι ((u : (ZMod q)ˣ) : ZMod q)) with hBdef
  have hinj : ∀ (S : Subgroup (ZMod q)ˣ), Function.Injective (fun u : S => ι ((u : (ZMod q)ˣ) : ZMod q)) := by
    intro S u v h
    exact Subtype.ext (Units.ext (iota_inj h))
  have hA : A.card = Nat.card S₁ := by
    rw [hAdef, Finset.card_image_of_injective _ (hinj S₁), Finset.card_univ, Nat.card_eq_fintype_card]
  have hB : B.card = Nat.card S₂ := by
    rw [hBdef, Finset.card_image_of_injective _ (hinj S₂), Finset.card_univ, Nat.card_eq_fintype_card]
  set n1 := Nat.card S₁ with hn1
  set n2 := Nat.card S₂ with hn2
  set h := min (n1 - k₁) (n2 - k₂) with hhdef
  set τ : ℝ := min c0 (1 / 2) * (h : ℝ) ^ 3 / ((n1 * n2 : ℕ) : ℝ) with hτdef
  have hhn1 : h ≤ n1 := (Nat.min_le_left _ _).trans (Nat.sub_le _ _)
  have hhn2 : h ≤ n2 := (Nat.min_le_right _ _).trans (Nat.sub_le _ _)
  have hh1 : h ≤ n1 - k₁ := Nat.min_le_left _ _
  have hh2 : h ≤ n2 - k₂ := Nat.min_le_right _ _
  have hhpos : 1 ≤ h := by omega
  have hτh : τ ≤ (h : ℝ) / 2 := by
    rw [hτdef]; push_cast
    exact tau_le _ _ _ _ hc1 hc1' (by positivity) (by exact_mod_cast (show 0 < n1 by omega))
      (by exact_mod_cast (show 0 < n2 by omega)) (by exact_mod_cast hhn1) (by exact_mod_cast hhn2)
  have hτ : ∀ e : ℕ, (e : ℝ) ≤ τ → k₁ + e < A.card ∧ k₂ + e < B.card := by
    intro e he
    have h1 : (e : ℝ) < h := by
      have : (1 : ℝ) ≤ h := by exact_mod_cast hhpos
      linarith
    have : e < h := by exact_mod_cast h1
    rw [hA, hB]; omega
  have hτc0 : τ ≤ c0 * (h : ℝ) ^ 3 / ((n1 * n2 : ℕ) : ℝ) := by
    rw [hτdef]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hc10 (by positivity)
  have Hmix : ∀ E P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q)), E ≠ 0 →
      (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤ τ →
      P.degreeOf 0 < k₁ + E.degreeOf 0 → P.degreeOf 1 < k₂ + E.degreeOf 1 → Rows A E P →
      Cols B E P → ∀ G, Irreducible G → G ∣ E → 0 < G.degreeOf 0 → 0 < G.degreeOf 1 → G ∣ P := by
    intro E P hE hm hPX hPY hR hC
    exact Hc q S₁ S₂ hcop k₁ k₂ hk1n hk2n E P hE (hm.trans hτc0) hPX hPY
      (fun α hα => hR _ (Finset.mem_image.2 ⟨⟨α, hα⟩, Finset.mem_univ _, rfl⟩))
      (fun β hβ => hC _ (Finset.mem_image.2 ⟨⟨β, hβ⟩, Finset.mem_univ _, rfl⟩))
  have hE' : map ι E ≠ 0 := by
    intro h0; apply hE; apply map_injective ι iota_inj; rw [h0, map_zero]
  have hR' : Rows A (map ι E) (map ι P) := by
    intro a ha
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨R, hR⟩ := hrow u.1 u.2
    refine ⟨Polynomial.map ι R, ?_⟩
    rw [rowP_map, rowP_map, ← Polynomial.map_mul]
    exact congrArg (Polynomial.map ι) hR
  have hC' : Cols B (map ι E) (map ι P) := by
    intro b hb
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨R, hR⟩ := hcol u.1 u.2
    refine ⟨Polynomial.map ι R, ?_⟩
    rw [colP_map, colP_map, ← Polynomial.map_mul]
    exact congrArg (Polynomial.map ι) hR
  have hmax' : (max ((map ι E).degreeOf 0) ((map ι E).degreeOf 1) : ℝ) ≤ τ := by
    rw [degreeOf_map_iota, degreeOf_map_iota]; exact hmax
  have hdiv := div_main A B k₁ k₂ τ hτ Hmix _ (map ι E) (map ι P) rfl hE' hmax'
    (by rw [degreeOf_map_iota, degreeOf_map_iota]; exact hPX)
    (by rw [degreeOf_map_iota, degreeOf_map_iota]; exact hPY) hR' hC'
  exact dvd_descent E P hE hdiv


