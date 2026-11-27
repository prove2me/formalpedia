-- Prove2me | solution 1 for PrivPCP.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:23:18.823578+00:00
-- url     : https://prove2.me/submissions/f75be7b8-3daf-416c-afd6-3b90e8a29455

import Mathlib
import Definitions.Def_PrivPCP_rsNested
import Definitions.Def_PrivPCP_certLaw


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


namespace PrivPCP.Fact33Full

open PrivPCP MvPolynomial PrivPCP.Fact33Aux

theorem fact33 {F : Type} [Field F] [Fintype F] {k : ℕ} (H : Fin k → Finset F) (a : Fin k → ℕ)
    (ha : ∀ i, (H i).card ≤ a i) (R : MvPolynomial (Fin k) F) (hR : ∀ i, R.degreeOf i ≤ a i) :
    (∀ x : Fin k → F, (∀ i, x i ∈ H i) → MvPolynomial.eval x R = 0) ↔
      ∃ Q : Fin k → MvPolynomial (Fin k) F, (∀ i, Q i ∈ gridQ H a i) ∧
        R = ∑ i, gridZ H i * Q i := by
  classical
  constructor
  swap
  · rintro ⟨Q, -, rfl⟩ x hx
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, gridZ, map_prod]
    rw [Finset.prod_eq_zero (hx i) (by simp), zero_mul]
  intro hvan
  -- the univariate vanishing polynomials
  let Zp : Fin k → Polynomial F := fun i => ∏ c ∈ H i, (Polynomial.X - Polynomial.C c)
  have hZmon : ∀ i, (Zp i).Monic := fun i => Polynomial.monic_prod_of_monic _ _
    (fun c _ => Polynomial.monic_X_sub_C c)
  have hZdeg : ∀ i, (Zp i).natDegree = (H i).card := by
    intro i
    simp only [Zp]
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C c)]
    simp
  have hZev : ∀ i, Polynomial.aeval (X i : MvPolynomial (Fin k) F) (Zp i) = gridZ H i := by
    intro i
    simp only [Zp, gridZ, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      MvPolynomial.algebraMap_eq]
  -- the empty case
  by_cases hemp : ∃ i, H i = ∅
  · obtain ⟨i₀, hi₀⟩ := hemp
    refine ⟨Pi.single i₀ R, ?_, ?_⟩
    · intro i
      by_cases hi : i = i₀
      · subst hi
        refine ⟨?_, ?_⟩
        · simp [hi₀, hR]
        · intro j _; simpa using hR j
      · refine ⟨?_, ?_⟩ <;> simp [Pi.single_apply, hi]
    · rw [Finset.sum_eq_single i₀]
      · simp [gridZ, hi₀]
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
  push Not at hemp
  have hne : ∀ i, (H i).Nonempty := hemp
  have hZ1 : ∀ i, Zp i ≠ 1 := by
    intro i h
    have := hZdeg i
    rw [h, Polynomial.natDegree_one] at this
    exact (Finset.card_pos.mpr (hne i)).ne' this.symm
  -- invariant: after processing variables `< j`
  have key : ∀ j : ℕ, j ≤ k → ∃ Q : Fin k → MvPolynomial (Fin k) F,
      (∀ i, Q i ∈ gridQ H a i) ∧
      (∀ i : Fin k, (R - ∑ i, gridZ H i * Q i).degreeOf i ≤
        if i.val < j then (H i).card - 1 else a i) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨0, fun i => ⟨by simp, fun j _ => by simp⟩, fun i => ?_⟩
      simpa using hR i
    | succ j ih =>
      intro hj
      obtain ⟨Q, hQ, hRem⟩ := ih (Nat.le_of_succ_le hj)
      set i₀ : Fin k := ⟨j, hj⟩
      set Rem := R - ∑ i, gridZ H i * Q i
      refine ⟨Q + Pi.single i₀ (divQ i₀ (Zp i₀) Rem), ?_, ?_⟩
      · intro i
        have hdq := divQ_degreeOf i₀ (Zp i₀) (hZmon i₀) Rem
        by_cases hi : i = i₀
        · subst hi
          have hr := hRem i₀
          simp only [i₀, lt_irrefl, if_false] at hr
          refine ⟨?_, ?_⟩
          · simp only [Pi.add_apply, Pi.single_eq_same]
            refine (degreeOf_add_le _ _ _).trans (max_le (hQ _).1 ?_)
            refine (hdq _).trans ?_
            simp only [if_true, hZdeg]
            exact Nat.sub_le_sub_right hr _
          · intro j' hj'
            simp only [Pi.add_apply, Pi.single_eq_same]
            refine (degreeOf_add_le _ _ _).trans (max_le ((hQ _).2 j' hj') ?_)
            refine (hdq j').trans ?_
            simp only [hj', if_false]
            refine (hRem j').trans ?_
            split_ifs
            · have := ha j'; omega
            · exact le_rfl
        · simp only [Pi.add_apply, Pi.single_eq_of_ne hi, add_zero]
          exact hQ i
      · intro i
        have hsplit : R - ∑ i, gridZ H i * ((Q + Pi.single i₀ (divQ i₀ (Zp i₀) Rem) : Fin k → MvPolynomial (Fin k) F) i) =
            divR i₀ (Zp i₀) Rem := by
          have hd := div_eq i₀ (Zp i₀) Rem
          rw [hZev] at hd
          simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
          have hs : ∑ x, gridZ H x *
              (Pi.single i₀ (divQ i₀ (Zp i₀) Rem) : Fin k → MvPolynomial (Fin k) F) x =
              gridZ H i₀ * divQ i₀ (Zp i₀) Rem := by
            rw [Finset.sum_eq_single i₀ (fun b _ hb => by simp [Pi.single_apply, hb])
              (by simp), Pi.single_eq_same]
          rw [hs]
          have : Rem = R - ∑ i, gridZ H i * Q i := rfl
          rw [← sub_sub, ← this]
          rw [sub_eq_iff_eq_add]; rw [add_comm]; exact hd
        rw [hsplit]
        by_cases hi : i = i₀
        · subst hi
          have := divR_degreeOf_self i₀ (Zp i₀) (hZmon i₀) (hZ1 i₀) Rem
          rw [hZdeg] at this
          have hlt : (i₀ : Fin k).val < j + 1 := Nat.lt_succ_self j
          rw [if_pos hlt]
          omega
        · refine (divR_degreeOf_ne i₀ (Zp i₀) Rem i hi).trans ?_
          refine (hRem i).trans ?_
          have hiv : i.val ≠ j := fun h => hi (Fin.ext h)
          by_cases hlt : i.val < j
          · simp [hlt, Nat.lt_succ_of_lt hlt]
          · have : ¬ i.val < j + 1 := by omega
            simp [hlt, this]
  obtain ⟨Q, hQ, hRem⟩ := key k le_rfl
  refine ⟨Q, hQ, ?_⟩
  have h0 : R - ∑ i, gridZ H i * Q i = 0 := by
    apply eq_zero_of_eval_zero_at_prod_finset _ H
    · intro i
      have := hRem i
      simp only [i.isLt, if_true] at this
      have := Finset.card_pos.mpr (hne i)
      omega
    · intro x hx
      rw [map_sub, hvan x hx, map_sum, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_mul, gridZ, map_prod, Finset.prod_eq_zero (hx i) (by simp), zero_mul]
  exact sub_eq_zero.mp h0



end PrivPCP.Fact33Full


namespace PrivPCP.L62Aux

open MvPolynomial PrivPCP.Fact33Aux Classical

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

/-- univariate restriction of `R` to the `j`-line through `x` -/
noncomputable def lineRestr (R : MvPolynomial (Fin k) F) (j : Fin k) (x : Fin k → F) :
    Polynomial F :=
  aeval (fun l => if l = j then Polynomial.X else Polynomial.C (x l)) R

lemma eval_lineRestr (R : MvPolynomial (Fin k) F) (j : Fin k) (x : Fin k → F) (t : F) :
    (lineRestr R j x).eval t = eval (Function.update x j t) R := by
  unfold lineRestr
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul, aeval_X, eval_X]
    congr 1
    by_cases h : i = j
    · subst h; simp
    · simp [h, Function.update_of_ne h]

lemma natDegree_lineRestr (R : MvPolynomial (Fin k) F) (j : Fin k) (x : Fin k → F) :
    (lineRestr R j x).natDegree ≤ R.degreeOf j := by
  unfold lineRestr
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ l, ((if l = j then Polynomial.X else Polynomial.C (x l)) ^ m l : Polynomial F).natDegree
      ≤ ∑ l, if l = j then m l else 0 := by
        refine Finset.sum_le_sum fun l _ => ?_
        refine (Polynomial.natDegree_pow_le).trans ?_
        split_ifs with h
        · have := Polynomial.natDegree_X_le (R := F); nlinarith
        · simp
    _ = m j := by simp
    _ ≤ R.degreeOf j := le_degreeOf_of_mem hm j

lemma lineRestr_mul (R R' : MvPolynomial (Fin k) F) (j : Fin k) (x : Fin k → F) :
    lineRestr (R * R') j x = lineRestr R j x * lineRestr R' j x := by
  unfold lineRestr; rw [map_mul]

lemma cardS (S : Fin k → Finset F) (j : Fin k) :
    Fintype.card ↥((S j : Finset F) : Set F) = (S j).card := by simp

/-- the grid point as a point of `F^k` -/
def gpt (S : Fin k → Finset F) (x : Grid S) : Fin k → F := fun l => (x l : F)

lemma evGrid_eq (S : Fin k → Finset F) (P : MvPolynomial (Fin k) F) (x : Grid S) :
    evGrid S P x = eval (gpt S x) P := rfl

/-- Lagrange basis polynomial on the side `S j` -/
noncomputable def lb (S : Fin k → Finset F) (j : Fin k) (t : ↥((S j : Finset F) : Set F)) :
    Polynomial F :=
  Lagrange.basis (Finset.univ : Finset ↥((S j : Finset F) : Set F)) Subtype.val t

lemma injOn_val (S : Fin k → Finset F) (j : Fin k) :
    Set.InjOn (Subtype.val : ↥((S j : Finset F) : Set F) → F)
      ((Finset.univ : Finset ↥((S j : Finset F) : Set F)) : Set _) :=
  Subtype.val_injective.injOn

lemma eval_lb (S : Fin k → Finset F) (j : Fin k) (t t' : ↥((S j : Finset F) : Set F)) :
    (lb S j t).eval (t' : F) = if t = t' then 1 else 0 := by
  unfold lb
  split_ifs with h
  · subst h; exact Lagrange.eval_basis_self (injOn_val S j) (Finset.mem_univ _)
  · exact Lagrange.eval_basis_of_ne h (Finset.mem_univ _)

lemma natDegree_lb (S : Fin k → Finset F) (j : Fin k) (t : ↥((S j : Finset F) : Set F)) :
    (lb S j t).natDegree < (S j).card := by
  unfold lb
  rw [Lagrange.natDegree_basis (injOn_val S j) (Finset.mem_univ _)]
  have : 0 < (Finset.univ : Finset ↥((S j : Finset F) : Set F)).card :=
    Finset.card_pos.mpr ⟨t, Finset.mem_univ _⟩
  rw [Finset.card_univ, cardS] at this ⊢
  omega

/-- interpolant of the `j`-line of `w` through `y` -/
noncomputable def lineInterp (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k) (y : Grid S) :
    Polynomial F :=
  Lagrange.interpolate (Finset.univ : Finset ↥((S j : Finset F) : Set F)) Subtype.val
    (fun t => w (Function.update y j t))

lemma eval_lineInterp (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k) (y : Grid S)
    (t : ↥((S j : Finset F) : Set F)) :
    (lineInterp S w j y).eval (t : F) = w (Function.update y j t) :=
  Lagrange.eval_interpolate_at_node _ (injOn_val S j) (Finset.mem_univ _)

/-- if the line is a polynomial of small degree, the interpolant equals it -/
lemma lineInterp_eq (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k) (y : Grid S)
    (p : Polynomial F) (hp : p.degree < (S j).card)
    (hev : ∀ t : ↥((S j : Finset F) : Set F), p.eval (t : F) = w (Function.update y j t)) :
    lineInterp S w j y = p := by
  symm
  apply Lagrange.eq_interpolate_of_eval_eq _ (injOn_val S j)
  · rw [Finset.card_univ, cardS]; exact hp
  · intro t _; exact hev t

/-- the regrouped Lagrange interpolant along direction `j` -/
noncomputable def Pj (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k)
    (t0 : ↥((S j : Finset F) : Set F)) : MvPolynomial (Fin k) F :=
  ∑ y ∈ Finset.univ.filter (fun y : Grid S => y j = t0),
    (∏ l ∈ Finset.univ.erase j, Polynomial.aeval (X l) (lb S l (y l))) *
      Polynomial.aeval (X j) (lineInterp S w j y)

lemma eval_aeval_X (p : Polynomial F) (l : Fin k) (z : Fin k → F) :
    eval z (Polynomial.aeval (X l : MvPolynomial (Fin k) F) p) = p.eval (z l) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

lemma eval_Pj (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k)
    (t0 : ↥((S j : Finset F) : Set F)) (x : Grid S) (c : F) :
    eval (Function.update (gpt S x) j c) (Pj S w j t0) =
      (lineInterp S w j (Function.update x j t0)).eval c := by
  unfold Pj
  rw [map_sum]
  rw [Finset.sum_eq_single (Function.update x j t0)]
  · rw [map_mul, eval_aeval_X, map_prod, Function.update_self]
    rw [Finset.prod_eq_one, one_mul]
    intro l hl
    have hlj : l ≠ j := Finset.ne_of_mem_erase hl
    rw [eval_aeval_X, Function.update_of_ne hlj, Function.update_of_ne hlj]
    unfold gpt
    rw [eval_lb, if_pos rfl]
  · intro y hy hne
    rw [Finset.mem_filter] at hy
    have : ∃ l, l ≠ j ∧ y l ≠ x l := by
      by_contra hcon
      push Not at hcon
      apply hne
      funext l
      by_cases hl : l = j
      · subst hl; rw [Function.update_self, hy.2]
      · rw [Function.update_of_ne hl]; exact hcon l hl
    obtain ⟨l, hlj, hl⟩ := this
    rw [map_mul, map_prod]
    rw [Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨hlj, Finset.mem_univ _⟩), zero_mul]
    rw [eval_aeval_X, Function.update_of_ne hlj]
    unfold gpt
    rw [eval_lb, if_neg hl]
  · intro h
    exfalso; apply h
    simp

lemma evGrid_Pj (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k)
    (t0 : ↥((S j : Finset F) : Set F)) : evGrid S (Pj S w j t0) = w := by
  funext x
  rw [evGrid_eq]
  have : gpt S x = Function.update (gpt S x) j (x j : F) := by simp [gpt]
  rw [this, eval_Pj, eval_lineInterp]
  congr 1
  funext l
  by_cases hl : l = j
  · subst hl; simp [gpt]
  · simp [Function.update_of_ne hl]

end PrivPCP.L62Aux


namespace PrivPCP.L62Aux

open MvPolynomial PrivPCP.Fact33Aux Classical

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

lemma degreeOf_prod_aeval_le (S : Fin k → Finset F) (j l : Fin k) (y : Grid S) :
    (∏ m ∈ Finset.univ.erase j, Polynomial.aeval (X m : MvPolynomial (Fin k) F) (lb S m (y m))).degreeOf l
      ≤ if l = j then 0 else (S l).card - 1 := by
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc ∑ m ∈ Finset.univ.erase j,
        (Polynomial.aeval (X m : MvPolynomial (Fin k) F) (lb S m (y m))).degreeOf l
      ≤ ∑ m ∈ Finset.univ.erase j, if l = m then (S l).card - 1 else 0 := by
        refine Finset.sum_le_sum fun m _ => (degreeOf_aeval_X_le m l _).trans ?_
        split_ifs with h
        · subst h; have := natDegree_lb S l (y l); omega
        · exact le_rfl
    _ = if l = j then 0 else (S l).card - 1 := by
        rw [Finset.sum_ite_eq]
        by_cases h : l = j
        · subst h; simp
        · simp [h]

lemma degreeOf_Pj_ne (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k)
    (t0 : ↥((S j : Finset F) : Set F)) (l : Fin k) (hl : l ≠ j) :
    (Pj S w j t0).degreeOf l ≤ (S l).card - 1 := by
  unfold Pj
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun y _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_prod_aeval_le S j l y
  rw [if_neg hl] at h1
  have h2 := degreeOf_aeval_X_le j l (lineInterp S w j y)
  rw [if_neg hl] at h2
  omega

lemma degreeOf_Pj_self (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k)
    (t0 : ↥((S j : Finset F) : Set F)) (d : ℕ) (hd : ∀ y, (lineInterp S w j y).natDegree ≤ d) :
    (Pj S w j t0).degreeOf j ≤ d := by
  unfold Pj
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun y _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_prod_aeval_le S j j y
  rw [if_pos rfl] at h1
  have h2 := degreeOf_aeval_X_le j j (lineInterp S w j y)
  rw [if_pos rfl] at h2
  have := hd y
  omega

lemma gpt_mk (S : Fin k → Finset F) (x : Fin k → F) (hx : ∀ l, x l ∈ S l) :
    gpt S (fun l => ⟨x l, hx l⟩ : Grid S) = x := rfl

lemma eq_of_evGrid_eq (S : Fin k → Finset F) (P1 P2 : MvPolynomial (Fin k) F)
    (h1 : ∀ l, P1.degreeOf l < (S l).card) (h2 : ∀ l, P2.degreeOf l < (S l).card)
    (he : evGrid S P1 = evGrid S P2) : P1 = P2 := by
  rw [← sub_eq_zero]
  apply eq_zero_of_eval_zero_at_prod_finset _ S
  · intro l
    exact lt_of_le_of_lt (degreeOf_sub_le _ _ _) (max_lt (h1 l) (h2 l))
  · intro x hx
    have := congrFun he (fun l => ⟨x l, hx l⟩)
    rw [evGrid_eq, evGrid_eq, gpt_mk] at this
    rw [map_sub, this, sub_self]

/-- a line of a tensor-RS word -/
lemma line_mem_rs (S : Fin k → Finset F) (a : Fin k → ℕ) (w : Grid S → F)
    (hw : w ∈ tensorCode (fun l => GoodQLTC.rsCode ((S l : Finset F) : Set F) (a l + 1)))
    (j : Fin k) (y : Grid S) :
    ∃ p : Polynomial F, p.degree < a j + 1 ∧
      ∀ t : ↥((S j : Finset F) : Set F), p.eval (t : F) = w (Function.update y j t) := by
  have hw' := (Submodule.mem_iInf _).1 hw j
  simp only [GoodQLTC.axisCode, Submodule.mem_iInf, Submodule.mem_comap] at hw'
  obtain ⟨p, hp, hpe⟩ := hw' y
  refine ⟨p, Polynomial.mem_degreeLT.1 hp, fun t => ?_⟩
  have := congrFun hpe t
  simpa [GoodQLTC.evalOn] using this

/-- full Lagrange interpolant -/
noncomputable def P0 (S : Fin k → Finset F) (w : Grid S → F) : MvPolynomial (Fin k) F :=
  ∑ x : Grid S, C (w x) * ∏ l, Polynomial.aeval (X l) (lb S l (x l))

lemma evGrid_P0 (S : Fin k → Finset F) (w : Grid S → F) : evGrid S (P0 S w) = w := by
  funext x
  rw [evGrid_eq]
  unfold P0
  rw [map_sum, Finset.sum_eq_single x]
  · rw [map_mul, eval_C, map_prod]
    rw [Finset.prod_eq_one, mul_one]
    intro l _
    rw [eval_aeval_X]; unfold gpt; rw [eval_lb, if_pos rfl]
  · intro y _ hne
    obtain ⟨l, hl⟩ : ∃ l, y l ≠ x l := by
      by_contra h; push Not at h; exact hne (funext h)
    rw [map_mul, map_prod, Finset.prod_eq_zero (i := l) (Finset.mem_univ _), mul_zero]
    rw [eval_aeval_X]; unfold gpt; rw [eval_lb, if_neg hl]
  · simp

lemma degreeOf_P0 (S : Fin k → Finset F) (w : Grid S → F) (hS : ∀ l, 0 < (S l).card) (l : Fin k) :
    (P0 S w).degreeOf l < (S l).card := by
  have : (P0 S w).degreeOf l ≤ (S l).card - 1 := by
    unfold P0
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun y _ => ?_)
    refine (degreeOf_C_mul_le _ _ _).trans ?_
    refine (degreeOf_prod_le _ _ _).trans ?_
    calc ∑ m, (Polynomial.aeval (X m : MvPolynomial (Fin k) F) (lb S m (y m))).degreeOf l
        ≤ ∑ m, if l = m then (S l).card - 1 else 0 := by
          refine Finset.sum_le_sum fun m _ => (degreeOf_aeval_X_le m l _).trans ?_
          split_ifs with h
          · subst h; have := natDegree_lb S l (y l); omega
          · exact le_rfl
      _ = (S l).card - 1 := by simp
  have := hS l
  omega

/-- **Interpolation of tensor Reed–Solomon words** -/
theorem interp (S : Fin k → Finset F) (a : Fin k → ℕ) (ha : ∀ l, a l < (S l).card)
    (w : Grid S → F)
    (hw : w ∈ tensorCode (fun l => GoodQLTC.rsCode ((S l : Finset F) : Set F) (a l + 1))) :
    (∀ l, (P0 S w).degreeOf l ≤ a l) ∧ evGrid S (P0 S w) = w ∧
      ∀ j (t0 : ↥((S j : Finset F) : Set F)), P0 S w = Pj S w j t0 := by
  have hS : ∀ l, 0 < (S l).card := fun l => by have := ha l; omega
  have heq : ∀ j (t0 : ↥((S j : Finset F) : Set F)), P0 S w = Pj S w j t0 := by
    intro j t0
    apply eq_of_evGrid_eq S
    · exact degreeOf_P0 S w hS
    · intro l
      by_cases hl : l = j
      · subst hl
        refine lt_of_le_of_lt (degreeOf_Pj_self S w l t0 (a l) fun y => ?_) (ha l)
        obtain ⟨p, hp, hpe⟩ := line_mem_rs S a w hw l y
        rw [lineInterp_eq S w l y p (lt_of_lt_of_le hp (by exact_mod_cast ha l)) hpe]
        by_cases hp0 : p = 0
        · simp [hp0]
        · have h' := (Polynomial.natDegree_lt_iff_degree_lt hp0).2 (by exact_mod_cast hp)
          omega
      · have := degreeOf_Pj_ne S w j t0 l hl
        have := hS l
        omega
    · rw [evGrid_P0, evGrid_Pj]
  refine ⟨fun l => ?_, evGrid_P0 S w, heq⟩
  obtain ⟨t0, ht0'⟩ := Finset.card_pos.mp (hS l)
  have ht0 : t0 ∈ ((S l : Finset F) : Set F) := by simpa using ht0'
  rw [heq l ⟨t0, ht0⟩]
  refine degreeOf_Pj_self S w l _ (a l) fun y => ?_
  obtain ⟨p, hp, hpe⟩ := line_mem_rs S a w hw l y
  rw [lineInterp_eq S w l y p (lt_of_lt_of_le hp (by exact_mod_cast ha l)) hpe]
  by_cases hp0 : p = 0
  · simp [hp0]
  · have h' := (Polynomial.natDegree_lt_iff_degree_lt hp0).2 (by exact_mod_cast hp)
    omega

end PrivPCP.L62Aux


namespace PrivPCP.L62Aux

open MvPolynomial PrivPCP.Fact33Aux Classical

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

/-- the certificate space as a submodule of polynomials -/
def gridQsub (H : Fin k → Finset F) (a : Fin k → ℕ) (i : Fin k) :
    Submodule F (MvPolynomial (Fin k) F) where
  carrier := gridQ H a i
  add_mem' := by
    intro p q hp hq
    refine ⟨(degreeOf_add_le _ _ _).trans (max_le hp.1 hq.1), fun j hj =>
      (degreeOf_add_le _ _ _).trans (max_le (hp.2 j hj) (hq.2 j hj))⟩
  zero_mem' := ⟨by simp, fun j _ => by simp⟩
  smul_mem' := by
    intro c p hp
    rw [smul_eq_C_mul]
    exact ⟨(degreeOf_C_mul_le _ _ _).trans hp.1, fun j hj => (degreeOf_C_mul_le _ _ _).trans (hp.2 j hj)⟩

/-- evaluation on the grid as a linear map -/
noncomputable def evLin (S : Fin k → Finset F) : MvPolynomial (Fin k) F →ₗ[F] (Grid S → F) where
  toFun := evGrid S
  map_add' p q := by funext x; simp [evGrid]
  map_smul' c p := by funext x; simp [evGrid]

/-- `E_i` in certificate form: `{ev(Z_i Q) : Q ∈ Q_i(a)}` -/
noncomputable def Ecert (S H : Fin k → Finset F) (a : Fin k → ℕ) (i : Fin k) :
    Submodule F (Grid S → F) :=
  (gridQsub H a i).map ((evLin S).comp (LinearMap.mulLeft F (gridZ H i)))

lemma mem_Ecert (S H : Fin k → Finset F) (a : Fin k → ℕ) (i : Fin k) (w : Grid S → F) :
    w ∈ Ecert S H a i ↔ ∃ Q ∈ gridQ H a i, evGrid S (gridZ H i * Q) = w := by
  simp [Ecert, evLin, gridQsub]
  rfl

lemma degreeOf_gridZ_ne (H : Fin k → Finset F) (i l : Fin k) (hl : l ≠ i) :
    (gridZ H i).degreeOf l = 0 := by
  unfold gridZ
  apply Nat.eq_zero_of_le_zero
  refine (degreeOf_prod_le _ _ _).trans ?_
  refine (Finset.sum_le_sum fun c _ => (degreeOf_sub_le _ _ _).trans
    (max_le (by rw [degreeOf_X_of_ne hl]) (by rw [degreeOf_C]))).trans ?_
  simp

lemma degreeOf_gridZ_self (H : Fin k → Finset F) (i : Fin k) :
    (gridZ H i).degreeOf i ≤ (H i).card := by
  unfold gridZ
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc ∑ c ∈ H i, (X i - C c : MvPolynomial (Fin k) F).degreeOf i ≤ ∑ _c ∈ H i, 1 := by
        refine Finset.sum_le_sum fun c _ => (degreeOf_sub_le _ _ _).trans (max_le ?_ (by simp))
        rw [degreeOf_X_self]
    _ = (H i).card := by simp

lemma mem_rsCode_of (Sl : Finset F) (d : ℕ) (line : ↥((Sl : Finset F) : Set F) → F)
    (p : Polynomial F) (hp : p.natDegree ≤ d)
    (hev : ∀ t : ↥((Sl : Finset F) : Set F), p.eval (t : F) = line t) :
    line ∈ GoodQLTC.rsCode ((Sl : Finset F) : Set F) (d + 1) := by
  refine ⟨p, ?_, ?_⟩
  · rw [SetLike.mem_coe, Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)
  · funext t; simp [GoodQLTC.evalOn, hev]

lemma mem_vanishCode_of (Sl Hl : Finset F) (d : ℕ) (line : ↥((Sl : Finset F) : Set F) → F)
    (p : Polynomial F) (hp : p.natDegree ≤ d) (hv : ∀ c ∈ Hl, p.eval c = 0)
    (hev : ∀ t : ↥((Sl : Finset F) : Set F), p.eval (t : F) = line t) :
    line ∈ vanishCode Sl Hl d := by
  refine ⟨p, ⟨?_, ?_⟩, ?_⟩
  · rw [SetLike.mem_coe, Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, Polynomial.leval_apply]
    exact hv
  · funext t; simp [GoodQLTC.evalOn, hev]

lemma of_mem_vanishCode (Sl Hl : Finset F) (d : ℕ) (line : ↥((Sl : Finset F) : Set F) → F)
    (h : line ∈ vanishCode Sl Hl d) :
    ∃ p : Polynomial F, p.degree < d + 1 ∧ (∀ c ∈ Hl, p.eval c = 0) ∧
      ∀ t : ↥((Sl : Finset F) : Set F), p.eval (t : F) = line t := by
  obtain ⟨p, ⟨hp1, hp2⟩, hpe⟩ := h
  refine ⟨p, Polynomial.mem_degreeLT.1 hp1, ?_, fun t => ?_⟩
  · simpa only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, Polynomial.leval_apply]
      using hp2
  · have := congrFun hpe t; simpa [GoodQLTC.evalOn] using this

lemma vanishCode_le (Sl Hl : Finset F) (d : ℕ) :
    vanishCode Sl Hl d ≤ GoodQLTC.rsCode ((Sl : Finset F) : Set F) (d + 1) :=
  Submodule.map_mono inf_le_left

lemma line_eval (S : Fin k → Finset F) (R : MvPolynomial (Fin k) F) (l : Fin k) (y : Grid S)
    (t : ↥((S l : Finset F) : Set F)) :
    evGrid S R (Function.update y l t) = (lineRestr R l (gpt S y)).eval (t : F) := by
  rw [eval_lineRestr, evGrid_eq]
  congr 2
  funext m
  by_cases h : m = l
  · subst h; simp [gpt]
  · simp [gpt, Function.update_of_ne h]

lemma mem_axisCode_iff' {ι : Type} [DecidableEq ι] {Ω : ι → Type}
    (C : ∀ i, Submodule F (Ω i → F)) (i : ι) (x : (∀ i, Ω i) → F) :
    x ∈ GoodQLTC.axisCode C i ↔ ∀ b : (∀ i, Ω i), (fun t => x (Function.update b i t)) ∈ C i := by
  simp only [GoodQLTC.axisCode, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.funLeft_apply]
  exact Iff.rfl

theorem Ecert_le (S H : Fin k → Finset F) (a : Fin k → ℕ) (ha : ∀ i, (H i).card ≤ a i)
    (i : Fin k) :
    Ecert S H a i ≤ (rsNested S H a).E i := by
  intro w hw
  rw [mem_Ecert] at hw
  obtain ⟨Q, hQ, rfl⟩ := hw
  unfold NestedCodes.E tensorCode
  rw [Submodule.mem_iInf]
  intro l
  rw [mem_axisCode_iff']
  intro y
  by_cases hl : l = i
  · subst hl
    rw [Function.update_self]
    refine mem_vanishCode_of _ _ _ _ (lineRestr (gridZ H l * Q) l (gpt S y)) ?_ ?_
      (fun t => (line_eval S _ l y t).symm)
    · refine (natDegree_lineRestr _ _ _).trans ((degreeOf_mul_le _ _ _).trans ?_)
      have := degreeOf_gridZ_self H l
      have := hQ.1
      have := ha l
      omega
    · intro c hc
      rw [eval_lineRestr, map_mul, gridZ, map_prod, Finset.prod_eq_zero hc (by simp), zero_mul]
  · rw [Function.update_of_ne hl]
    refine mem_rsCode_of _ _ _ (lineRestr (gridZ H i * Q) l (gpt S y)) ?_
      (fun t => (line_eval S _ l y t).symm)
    refine (natDegree_lineRestr _ _ _).trans ((degreeOf_mul_le _ _ _).trans ?_)
    rw [degreeOf_gridZ_ne H i l hl, zero_add]
    exact hQ.2 l hl

theorem le_Ecert (S H : Fin k → Finset F) (a : Fin k → ℕ)
    (hSH : ∀ i, 1 ≤ (H i).card ∧ Disjoint (H i) (S i) ∧ (H i).card ≤ a i ∧ a i < (S i).card)
    (i : Fin k) : (rsNested S H a).E i ≤ Ecert S H a i := by
  intro w hw
  have hlines : ∀ l (y : Grid S), (fun t => w (Function.update y l t)) ∈
      Function.update (rsNested S H a).V i ((rsNested S H a).K i) l := by
    intro l y
    have := (Submodule.mem_iInf _).1 hw l
    exact (mem_axisCode_iff' _ l w).1 this y
  have hwV : w ∈ tensorCode (fun l => GoodQLTC.rsCode ((S l : Finset F) : Set F) (a l + 1)) := by
    unfold tensorCode
    rw [Submodule.mem_iInf]
    intro l
    rw [mem_axisCode_iff']
    intro y
    have := hlines l y
    by_cases hl : l = i
    · subst hl
      rw [Function.update_self] at this
      exact vanishCode_le _ _ _ this
    · rw [Function.update_of_ne hl] at this
      exact this
  have ha : ∀ l, a l < (S l).card := fun l => (hSH l).2.2.2
  obtain ⟨hdeg, hev, hPj⟩ := interp S a ha w hwV
  set P := P0 S w
  let Zp : Polynomial F := ∏ c ∈ H i, (Polynomial.X - Polynomial.C c)
  have hZmon : Zp.Monic := Polynomial.monic_prod_of_monic _ _
    (fun c _ => Polynomial.monic_X_sub_C c)
  have hZdeg : Zp.natDegree = (H i).card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C c)]
    simp
  have hZev : Polynomial.aeval (X i : MvPolynomial (Fin k) F) Zp = gridZ H i := by
    simp only [Zp, gridZ, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      MvPolynomial.algebraMap_eq]
  have hZ1 : Zp ≠ 1 := by
    intro h; have := hZdeg; rw [h, Polynomial.natDegree_one] at this; have := (hSH i).1; omega
  have hdiv := div_eq i Zp P
  rw [hZev] at hdiv
  -- the remainder vanishes
  obtain ⟨t0, ht0'⟩ := Finset.card_pos.mp (show 0 < (S i).card by have := ha i; omega)
  have ht0 : t0 ∈ ((S i : Finset F) : Set F) := by simpa using ht0'
  have hrem : divR i Zp P = 0 := by
    apply eq_zero_of_eval_zero_at_prod_finset _ (fun l => if l = i then H i else S l)
    · intro l
      by_cases hl : l = i
      · subst hl
        simp only [if_true]
        have := divR_degreeOf_self l Zp hZmon hZ1 P
        rwa [hZdeg] at this
      · simp only [hl, if_false]
        exact lt_of_le_of_lt ((divR_degreeOf_ne i Zp P l hl).trans (hdeg l)) (ha l)
    · intro z hz
      have hzi : z i ∈ H i := by simpa using hz i
      have hzl : ∀ l, l ≠ i → z l ∈ S l := fun l hl => by simpa [hl] using hz l
      let x : Grid S := fun l => ⟨if l = i then t0 else z l, by
        by_cases h : l = i
        · subst h; simpa using ht0'
        · simpa [h] using hzl l h⟩
      have hzx : z = Function.update (gpt S x) i (z i) := by
        funext l
        by_cases h : l = i
        · subst h; simp
        · simp [Function.update_of_ne h, gpt, x, h]
      have hPz : eval z P = 0 := by
        rw [hPj i ⟨t0, ht0⟩, hzx, eval_Pj]
        have hK := hlines i (Function.update x i ⟨t0, ht0⟩)
        rw [Function.update_self] at hK
        obtain ⟨p, hp, hpv, hpe⟩ := of_mem_vanishCode _ _ _ _ hK
        rw [lineInterp_eq S w i _ p (lt_of_lt_of_le hp (by exact_mod_cast ha i)) hpe]
        exact hpv _ hzi
      have hZz : eval z (gridZ H i) = 0 := by
        rw [gridZ, map_prod]
        exact Finset.prod_eq_zero hzi (by simp)
      have := congrArg (eval z) hdiv
      rw [map_add, map_mul, hZz, zero_mul, zero_add, hPz] at this
      exact this.symm
  rw [hrem, add_zero] at hdiv
  rw [mem_Ecert]
  refine ⟨divQ i Zp P, ⟨?_, fun l hl => ?_⟩, ?_⟩
  · have := divQ_degreeOf i Zp hZmon P i
    rw [if_pos rfl, hZdeg] at this
    exact this.trans (Nat.sub_le_sub_right (hdeg i) _)
  · have := divQ_degreeOf i Zp hZmon P l
    rw [if_neg hl] at this
    exact this.trans (hdeg l)
  · rw [← hdiv]; exact hev

end PrivPCP.L62Aux


namespace PrivPCP.L62Aux

open Classical

variable {F : Type} [Field F] [Fintype F]

/-- fibers of a linear functional over a translation-invariant set are equinumerous -/
lemma fiber_card_mul {V : Type} [AddCommGroup V] [Module F V] (A : Finset V) (φ : V →ₗ[F] F)
    (n0 : V) (hφ : φ n0 = 1) (hA : ∀ x ∈ A, ∀ t : F, x + t • n0 ∈ A) (b : F) :
    (A.filter (fun x => φ x = b)).card * Fintype.card F = A.card := by
  have heq : ∀ b', (A.filter (fun x => φ x = b')).card = (A.filter (fun x => φ x = b)).card := by
    intro b'
    refine Finset.card_nbij' (fun x => x + (b - b') • n0) (fun x => x + (b' - b) • n0) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
      refine ⟨hA x hx.1 _, ?_⟩
      rw [map_add, map_smul, hφ, hx.2, smul_eq_mul, mul_one]; ring
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
      refine ⟨hA x hx.1 _, ?_⟩
      rw [map_add, map_smul, hφ, hx.2, smul_eq_mul, mul_one]; ring
    · intro x _
      simp only
      rw [add_assoc, ← add_smul]; simp
    · intro x _
      simp only
      rw [add_assoc, ← add_smul]; simp
  have hA' : A.card = ∑ b' ∈ (Finset.univ : Finset F), (A.filter (fun x => φ x = b')).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [hA', Finset.sum_congr rfl fun b' _ => heq b', Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_comm]

/-- the dot product with a fixed vector as a linear functional -/
def dotL {J : Type} [Fintype J] (w : J → F) : (J → F) →ₗ[F] F where
  toFun θ := θ ⬝ᵥ w
  map_add' x y := add_dotProduct x y w
  map_smul' c x := by simp [smul_dotProduct]

lemma card_ker_dot {J : Type} [Fintype J] (w : J → F) (hw : w ≠ 0) :
    (Finset.univ.filter (fun θ : J → F => θ ⬝ᵥ w = 0)).card * Fintype.card F =
      Fintype.card F ^ Fintype.card J := by
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h; push Not at h; exact hw (funext h)
  have := fiber_card_mul Finset.univ (dotL w) (Pi.single j (w j)⁻¹)
    (by simp [dotL, single_dotProduct, hj]) (fun _ _ _ => Finset.mem_univ _) 0
  rw [Finset.card_univ, Fintype.card_fun] at this
  have h2 : (Finset.univ.filter fun θ : J → F => θ ⬝ᵥ w = 0) =
      Finset.univ.filter fun x => dotL w x = 0 := by
    ext θ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  rw [h2]; exact this

lemma map_apply_toReal {α β : Type} [Fintype α] (μ : PMF α) (f : α → β) (b : β) :
    ((μ.map f) b).toReal = ∑ a, if b = f a then (μ a).toReal else 0 := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  · intro a _; split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top

lemma sum_toReal {α : Type} [Fintype α] (μ : PMF α) : ∑ a, (μ a).toReal = 1 := by
  have h := PMF.tsum_coe μ
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top μ a), h]
  simp

/-- the key identity behind the Radon inversion -/
lemma radon_identity {J : Type} [Fintype J] (μ : PMF (J → F)) (v : J → F) :
    (∑ θ : J → F, ((μ.map (fun u => θ ⬝ᵥ u)) (θ ⬝ᵥ v)).toReal) * Fintype.card F =
      (Fintype.card F : ℝ) ^ Fintype.card J +
        (μ v).toReal * ((Fintype.card F : ℝ) ^ (Fintype.card J + 1) -
          (Fintype.card F : ℝ) ^ Fintype.card J) := by
  simp_rw [map_apply_toReal]
  rw [Finset.sum_comm]
  have hcount : ∀ u : J → F, (∑ θ : J → F, if θ ⬝ᵥ v = θ ⬝ᵥ u then (μ u).toReal else 0) *
      Fintype.card F = (μ u).toReal * ((Fintype.card F : ℝ) ^ Fintype.card J +
        if u = v then (Fintype.card F : ℝ) ^ (Fintype.card J + 1) -
          (Fintype.card F : ℝ) ^ Fintype.card J else 0) := by
    intro u
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases huv : u = v
    · subst huv
      simp [Fintype.card_fun]
      ring
    · simp only [huv, if_false, add_zero]
      have hw : u - v ≠ 0 := sub_ne_zero.mpr huv
      have h := card_ker_dot (u - v) hw
      have hfilt : (Finset.univ.filter fun θ : J → F => θ ⬝ᵥ v = θ ⬝ᵥ u) =
          Finset.univ.filter (fun θ : J → F => θ ⬝ᵥ (u - v) = 0) := by
        ext θ; simp [dotProduct_sub, sub_eq_zero, eq_comm]
      rw [hfilt]
      have h' : ((Finset.univ.filter (fun θ : J → F => θ ⬝ᵥ (u - v) = 0)).card : ℝ) *
          Fintype.card F = (Fintype.card F : ℝ) ^ Fintype.card J := by exact_mod_cast h
      calc ((Finset.univ.filter (fun θ : J → F => θ ⬝ᵥ (u - v) = 0)).card : ℝ) * (μ u).toReal *
            Fintype.card F = (μ u).toReal * (((Finset.univ.filter
              (fun θ : J → F => θ ⬝ᵥ (u - v) = 0)).card : ℝ) * Fintype.card F) := by ring
        _ = _ := by rw [h']
  rw [Finset.sum_mul, Finset.sum_congr rfl fun u _ => hcount u]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_toReal, one_mul]
  rw [Finset.sum_eq_single v (fun u _ hu => by simp [hu]) (by simp)]
  simp

/-- **Radon inversion**: a law on `F^J` is determined by the laws of its linear functionals -/
theorem radon {J : Type} [Fintype J] (μ ν : PMF (J → F))
    (h : ∀ θ : J → F, μ.map (fun u => θ ⬝ᵥ u) = ν.map (fun u => θ ⬝ᵥ u)) : μ = ν := by
  ext v
  have h1 := radon_identity μ v
  have h2 := radon_identity ν v
  simp_rw [h] at h1
  rw [h1] at h2
  have hq : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ (Fintype.card J + 1) -
      (Fintype.card F : ℝ) ^ Fintype.card J := by
    rw [sub_pos]; exact pow_lt_pow_right₀ hq (Nat.lt_succ_self _)
  have : (μ v).toReal = (ν v).toReal := by
    have := add_left_cancel h2
    exact mul_right_cancel₀ hpos.ne' this
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).1 this

/-- uniform law on a translation-invariant set pushed through a nonconstant affine functional -/
theorem uniform_map_affine {V : Type} [AddCommGroup V] [Module F V] (A : Finset V) (hA0 : A.Nonempty)
    (φ : V →ₗ[F] F) (c : F) (n0 : V) (hφ : φ n0 = 1) (hA : ∀ x ∈ A, ∀ t : F, x + t • n0 ∈ A) :
    (PMF.uniformOfFinset A hA0).map (fun x => c + φ x) = PMF.uniformOfFintype F := by
  ext b
  rw [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_eq_sum (s := A)]
  · have hfib := fiber_card_mul A φ n0 hφ hA (b - c)
    have hsum : ∑ x ∈ A, (if b = c + φ x then (PMF.uniformOfFinset A hA0) x else 0) =
        ∑ x ∈ A.filter (fun x => φ x = b - c), (A.card : ENNReal)⁻¹ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [PMF.uniformOfFinset_apply_of_mem hA0 hx]
      congr 1
      apply propext
      constructor <;> intro h <;> linear_combination -h
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    have hA : (A.card : ENNReal) = ((A.filter (fun x => φ x = b - c)).card : ENNReal) *
        Fintype.card F := by exact_mod_cast hfib.symm
    rw [hA, ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp))]
    have hne : ((A.filter (fun x => φ x = b - c)).card : ENNReal) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hA
      have : A.card = 0 := by exact_mod_cast hA
      exact (Finset.card_ne_zero.mpr hA0) this
    rw [← mul_assoc, ENNReal.mul_inv_cancel hne (by simp), one_mul]
  · intro x hx
    rw [PMF.uniformOfFinset_apply_of_notMem hA0 hx]; simp

end PrivPCP.L62Aux


namespace PrivPCP.L62Aux

open MvPolynomial PrivPCP.Fact33Aux Classical

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

/-- factorization of a functional through a linear map -/
lemma exists_factor {U V : Type} [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
    (f : U →ₗ[F] V) (ψ : U →ₗ[F] F) (h : LinearMap.ker f ≤ LinearMap.ker ψ) :
    ∃ ℓ : V →ₗ[F] F, ∀ y, ℓ (f y) = ψ y := by
  let fbar := (LinearMap.ker f).liftQ f le_rfl
  have hinj : LinearMap.ker fbar = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  obtain ⟨inv, hinv⟩ := LinearMap.exists_leftInverse_of_injective fbar hinj
  refine ⟨((LinearMap.ker f).liftQ ψ h).comp inv, fun y => ?_⟩
  have : inv (f y) = (LinearMap.ker f).mkQ y := by
    have := congrArg (fun g => g ((LinearMap.ker f).mkQ y)) hinv
    simpa [fbar] using this
  simp [this]

/-- a functional is a dot product -/
lemma functional_eq_dot {Ω : Type} [Fintype Ω] (ℓ : (Ω → F) →ₗ[F] F) (v : Ω → F) :
    ℓ v = (fun x => ℓ (Pi.single x 1)) ⬝ᵥ v := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  congr 2
  funext y
  simp [Pi.single_apply, eq_comm]

lemma sum_subtype_dite {Ω : Type} [Fintype Ω] (s : Finset Ω) (f : ↥s → F) :
    ∑ x : ↥s, f x = ∑ x, if h : x ∈ s then f ⟨x, h⟩ else 0 := by
  rw [← Finset.sum_subset (Finset.subset_univ s)]
  · rw [← Finset.sum_attach s]
    refine (Finset.sum_bij (fun y _ => y) (by simp) (by simp) (fun y _ => ⟨y, by simp⟩) ?_)
    intro y _; simp [y.2]
  · intro x _ hx; simp [hx]

/-- the grid vector of `Z_i` -/
noncomputable def zv (S H : Fin k → Finset F) (i : Fin k) : Grid S → F := evGrid S (gridZ H i)

lemma zv_ne (S H : Fin k → Finset F) (i : Fin k) (hd : Disjoint (H i) (S i)) (x : Grid S) :
    zv S H i x ≠ 0 := by
  unfold zv
  rw [evGrid_eq, gridZ, map_prod, Finset.prod_ne_zero_iff]
  intro c hc
  simp only [map_sub, eval_X, eval_C, gpt]
  intro h
  have hx : (x i : F) ∈ S i := by simpa using (x i).2
  rw [sub_eq_zero] at h
  exact Finset.disjoint_left.1 hd hc (h ▸ hx)

lemma evGrid_mul (S : Fin k → Finset F) (P Q : MvPolynomial (Fin k) F) :
    evGrid S (P * Q) = evGrid S P * evGrid S Q := by
  funext x; simp [evGrid]

lemma evGrid_sum (S : Fin k → Finset F) (P : Fin k → MvPolynomial (Fin k) F) :
    evGrid S (∑ i, P i) = ∑ i, evGrid S (P i) := by
  funext x; simp [evGrid]

/-- certificate values -/
noncomputable def Vc (S H : Fin k → Finset F) (a : Fin k → ℕ) (i : Fin k) :
    Submodule F (Grid S → F) :=
  (gridQsub H a i).map (evLin S)

lemma mem_certSet_iff (S H : Fin k → Finset F) (a : Fin k → ℕ) (g : Grid S → F)
    (Qs : Fin k → (Grid S → F)) :
    Qs ∈ certSet S H a g ↔ (∀ i, Qs i ∈ Vc S H a i) ∧ g = ∑ i, zv S H i * Qs i := by
  constructor
  · rintro ⟨Q, hQ, hQs, hg⟩
    refine ⟨fun i => ⟨Q i, hQ i, (hQs i).symm⟩, ?_⟩
    rw [hg, evGrid_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [evGrid_mul, hQs i]; rfl
  · rintro ⟨hV, hg⟩
    choose Q hQ hQe using hV
    refine ⟨Q, hQ, fun i => (hQe i).symm, ?_⟩
    rw [hg, evGrid_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [evGrid_mul]
    show zv S H i * Qs i = evGrid S (gridZ H i) * evGrid S (Q i)
    rw [← hQe i]; rfl

lemma mem_Ecert_iff' (S H : Fin k → Finset F) (a : Fin k → ℕ) (i : Fin k) (y : Grid S → F) :
    y ∈ Ecert S H a i ↔ ∃ v ∈ Vc S H a i, y = zv S H i * v := by
  rw [mem_Ecert]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact ⟨evGrid S Q, ⟨Q, hQ, rfl⟩, by rw [evGrid_mul]; rfl⟩
  · rintro ⟨v, ⟨Q, hQ, rfl⟩, rfl⟩
    exact ⟨Q, hQ, by rw [evGrid_mul]; rfl⟩

lemma certSet_nonempty (S H : Fin k → Finset F) (a : Fin k → ℕ)
    (ha : ∀ i, (H i).card ≤ a i) (g : Grid S → F) (hg : g ∈ zaEval S H a) :
    (certSet S H a g).Nonempty := by
  obtain ⟨R, ⟨hRdeg, hRvan⟩, rfl⟩ := hg
  obtain ⟨Q, hQ, hRQ⟩ := (PrivPCP.Fact33Full.fact33 H a ha R hRdeg).1 hRvan
  exact ⟨fun i => evGrid S (Q i), Q, hQ, fun i => rfl, by rw [hRQ]⟩

end PrivPCP.L62Aux


namespace PrivPCP.L62Aux

open MvPolynomial PrivPCP.Fact33Aux Classical

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

lemma bind_eq_of_support {α β : Type} (p : PMF α) (f : α → PMF β) (c : PMF β)
    (h : ∀ a ∈ p.support, f a = c) : p.bind f = c := by
  ext b
  rw [PMF.bind_apply]
  have : ∀ a, p a * f a b = p a * c b := by
    intro a
    by_cases ha : a ∈ p.support
    · rw [h a ha]
    · rw [PMF.mem_support_iff, not_not] at ha; simp [ha]
  simp_rw [this]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma bind_congr_support {α β : Type} (p : PMF α) (f f' : α → PMF β)
    (h : ∀ a ∈ p.support, f a = f' a) : p.bind f = p.bind f' := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  congr 1
  funext a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [PMF.mem_support_iff, not_not] at ha; simp [ha]

lemma map_eq_pure_of_support {α β : Type} (p : PMF α) (f : α → β) (c : β)
    (h : ∀ a ∈ p.support, f a = c) : p.map f = PMF.pure c := by
  rw [PMF.map]
  exact bind_eq_of_support _ _ _ fun a ha => by rw [Function.comp_apply, h a ha]

lemma distTo_le {α : Type} [Fintype α] (x y : α → F) (E : Submodule F (α → F)) (hy : y ∈ E) :
    distTo x E ≤ GoodQLTC.supportCard (x - y) :=
  Nat.sInf_le ⟨y, hy, rfl⟩

lemma exists_distTo {α : Type} [Fintype α] (x : α → F) (E : Submodule F (α → F)) :
    ∃ y ∈ E, GoodQLTC.supportCard (x - y) = distTo x E :=
  Nat.sInf_mem (s := {d | ∃ y ∈ E, GoodQLTC.supportCard (x - y) = d}) ⟨_, 0, E.zero_mem, rfl⟩

lemma supportCard_le_of {α : Type} [Fintype α] (x : α → F) (T : Finset α)
    (h : ∀ a, x a ≠ 0 → a ∈ T) : GoodQLTC.supportCard x ≤ T.card := by
  unfold GoodQLTC.supportCard
  exact Finset.card_le_card fun a ha => h a (by simpa using ha)

end PrivPCP.L62Aux

open PrivPCP PrivPCP.L62Aux MvPolynomial Classical

theorem solution {F : Type} [Field F] [Fintype F] {k : ℕ} (hk : 2 ≤ k) (S H : Fin k → Finset F)
    (a : Fin k → ℕ)
    (hSH : ∀ i, 1 ≤ (H i).card ∧ Disjoint (H i) (S i) ∧ (H i).card ≤ a i ∧ a i < (S i).card)
    (C : ℝ) (hC : ∀ M : Grid S → F,
      (distTo M (rsNested S H a).Dbig : ℝ) ≤ C * ∑ i, (distTo M ((rsNested S H a).D i) : ℝ))
    {Msg : Type} (G : Msg → PMF (Grid S → F)) (hG : ∀ m, ∀ g ∈ (G m).support, g ∈ zaEval S H a)
    (s : ℕ) (hpriv : ∀ T : Finset (Grid S), T.card ≤ s → ∀ m m',
      (G m).map (fun g (x : T) => g x) = (G m').map (fun g (x : T) => g x))
    (TG : Finset (Grid S)) (T : Fin k → Finset (Grid S))
    (hT : (TG.card : ℝ) + C * ∑ i, ((T i).card : ℝ) ≤ s) (m m' : Msg) :
    (jointCertLaw S H a (G m)).map (fun p => ((fun x : TG => p.1 x), fun i (x : T i) => p.2 i x)) =
      (jointCertLaw S H a (G m')).map (fun p => ((fun x : TG => p.1 x), fun i (x : T i) => p.2 i x)) := by
  -- abbreviations
  have haH : ∀ i, (H i).card ≤ a i := fun i => (hSH i).2.2.1
  have hEq : ∀ i, Ecert S H a i = (rsNested S H a).E i := fun i =>
    le_antisymm (Ecert_le S H a haH i) (le_Ecert S H a hSH i)
  -- the flattened view
  let viewJ : (Grid S → F) × (Fin k → (Grid S → F)) → (((↥TG) ⊕ (Σ i, ↥(T i))) → F) :=
    fun p => Sum.elim (fun x => p.1 x) (fun q => p.2 q.1 q.2)
  let eW : (((↥TG) ⊕ (Σ i, ↥(T i))) → F) → (↥TG → F) × (∀ i, ↥(T i) → F) :=
    fun u => (fun x => u (Sum.inl x), fun i x => u (Sum.inr ⟨i, x⟩))
  have hview : (fun p : (Grid S → F) × (Fin k → (Grid S → F)) =>
      ((fun x : TG => p.1 x), fun i (x : T i) => p.2 i x)) = eW ∘ viewJ := rfl
  rw [hview, ← PMF.map_comp, ← PMF.map_comp]
  congr 1
  apply radon
  intro θ
  rw [PMF.map_comp, PMF.map_comp]
  -- the coefficient vectors
  let muv : Grid S → F := fun x => if h : x ∈ TG then θ (Sum.inl ⟨x, h⟩) else 0
  let lamv : Fin k → Grid S → F := fun i x => if h : x ∈ T i then θ (Sum.inr ⟨i, ⟨x, h⟩⟩) else 0
  have hθ : ∀ p : (Grid S → F) × (Fin k → (Grid S → F)),
      θ ⬝ᵥ viewJ p = muv ⬝ᵥ p.1 + ∑ i, lamv i ⬝ᵥ p.2 i := by
    intro p
    simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_sigma, viewJ, Sum.elim_inl,
      Sum.elim_inr]
    congr 1
    · rw [sum_subtype_dite]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [muv]; split_ifs <;> simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_subtype_dite]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [lamv]; split_ifs <;> simp
  let φL : (Fin k → (Grid S → F)) →ₗ[F] F :=
    { toFun := fun Qs => ∑ i, lamv i ⬝ᵥ Qs i
      map_add' := by intro x y; simp [dotProduct_add, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [dotProduct_smul, Finset.mul_sum] }
  -- the law of the functional
  have hlaw : ∀ m0, (jointCertLaw S H a (G m0)).map (fun p => θ ⬝ᵥ viewJ p) =
      (G m0).bind (fun g => (certLaw S H a g).map (fun Qs => muv ⬝ᵥ g + φL Qs)) := by
    intro m0
    unfold jointCertLaw
    rw [PMF.map_bind]
    congr 1
    funext g
    rw [PMF.map_comp]
    congr 1
    funext Qs
    simp only [Function.comp_apply, hθ]
    rfl
  have hfun : (fun p => θ ⬝ᵥ viewJ p) = (fun p => θ ⬝ᵥ viewJ p) := rfl
  show (jointCertLaw S H a (G m)).map ((fun u => θ ⬝ᵥ u) ∘ viewJ) =
    (jointCertLaw S H a (G m')).map ((fun u => θ ⬝ᵥ u) ∘ viewJ)
  have e1 : ((fun u => θ ⬝ᵥ u) ∘ viewJ) = (fun p => θ ⬝ᵥ viewJ p) := rfl
  rw [e1, hlaw m, hlaw m']
  -- nonempty certificate sets on the support
  have hne : ∀ m0, ∀ g ∈ (G m0).support, (certSet S H a g).toFinset.Nonempty := by
    intro m0 g hg
    rw [Set.toFinset_nonempty]
    exact certSet_nonempty S H a haH g (hG m0 g hg)
  by_cases hcase : ∃ n0, (∀ i, n0 i ∈ Vc S H a i) ∧ ∑ i, zv S H i * n0 i = 0 ∧ φL n0 ≠ 0
  · -- the functional is nonconstant on certificates: uniform
    obtain ⟨n0, hn0V, hn0s, hn0φ⟩ := hcase
    set n1 := (φL n0)⁻¹ • n0 with hn1
    have hn1φ : φL n1 = 1 := by rw [hn1, map_smul, smul_eq_mul, inv_mul_cancel₀ hn0φ]
    have hunif : ∀ m0, ∀ g ∈ (G m0).support,
        (certLaw S H a g).map (fun Qs => muv ⬝ᵥ g + φL Qs) = PMF.uniformOfFintype F := by
      intro m0 g hg
      unfold certLaw
      rw [dif_pos (hne m0 g hg)]
      refine uniform_map_affine _ _ φL _ n1 hn1φ ?_
      intro x hx t
      rw [Set.mem_toFinset, mem_certSet_iff] at hx ⊢
      refine ⟨fun i => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, hn1]
        exact Submodule.add_mem _ (hx.1 i) (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hn0V i)))
      · rw [hx.2]
        simp only [Pi.add_apply, Pi.smul_apply, hn1, mul_add, Finset.sum_add_distrib]
        have : ∑ i, zv S H i * (t • (φL n0)⁻¹ • n0 i) = (t * (φL n0)⁻¹) • ∑ i, zv S H i * n0 i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_smul, mul_smul_comm, mul_smul_comm]
        rw [this, hn0s, smul_zero, add_zero]
    rw [bind_eq_of_support _ _ _ (hunif m), bind_eq_of_support _ _ _ (hunif m')]
  · -- the functional is constant on certificates: reduce to a view of `G`
    push Not at hcase
    -- C is nonnegative
    have hS0 : ∀ l, 0 < (S l).card := fun l => by have := (hSH l).2.2.2; omega
    let x0 : Grid S := fun l => ⟨(Finset.card_pos.mp (hS0 l)).choose, by
      simpa using (Finset.card_pos.mp (hS0 l)).choose_spec⟩
    have hCnn : 0 ≤ C := by
      by_contra hneg
      push Not at hneg
      let i0 : Fin k := ⟨0, by omega⟩
      let M : Grid S → F := Pi.single x0 1
      have hzE : zv S H i0 ∈ (rsNested S H a).E i0 := by
        rw [← hEq, mem_Ecert]
        exact ⟨1, ⟨by simp, fun j _ => by simp⟩, by rw [mul_one]; rfl⟩
      have hMD : M ∉ (rsNested S H a).D i0 := by
        intro hM
        have := hM _ hzE
        simp only [M, dotProduct_single, mul_one] at this
        exact zv_ne S H i0 (hSH i0).2.1 x0 this
      have hd1 : 1 ≤ distTo M ((rsNested S H a).D i0) := by
        by_contra h0
        push Not at h0
        obtain ⟨y, hy, hyc⟩ := exists_distTo M ((rsNested S H a).D i0)
        rw [Nat.lt_one_iff.mp h0] at hyc
        unfold GoodQLTC.supportCard at hyc
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hyc
        have : M = y := by
          funext x; have := hyc (Finset.mem_univ x); rw [Pi.sub_apply, not_not, sub_eq_zero] at this
          exact this
        exact hMD (this ▸ hy)
      have hsum : (1 : ℝ) ≤ ∑ i, (distTo M ((rsNested S H a).D i) : ℝ) := by
        calc (1 : ℝ) ≤ (distTo M ((rsNested S H a).D i0) : ℝ) := by exact_mod_cast hd1
          _ ≤ _ := Finset.single_le_sum (f := fun i => (distTo M ((rsNested S H a).D i) : ℝ))
              (fun i _ => by positivity) (Finset.mem_univ i0)
      have := hC M
      have : C * ∑ i, (distTo M ((rsNested S H a).D i) : ℝ) < 0 := by nlinarith
      have : (0 : ℝ) ≤ distTo M (rsNested S H a).Dbig := by positivity
      linarith
    -- the functional on the product of the `E_i`
    let α : Fin k → Grid S → F := fun i x => lamv i x / zv S H i x
    have hαz : ∀ i v, lamv i ⬝ᵥ v = α i ⬝ᵥ (zv S H i * v) := by
      intro i v
      simp only [dotProduct, Pi.mul_apply, α]
      refine Finset.sum_congr rfl fun x _ => ?_
      have := zv_ne S H i (hSH i).2.1 x
      field_simp
    let P : Submodule F (Fin k → (Grid S → F)) := Submodule.pi Set.univ (fun i => Ecert S H a i)
    let fsum : P →ₗ[F] (Grid S → F) :=
      { toFun := fun Y => ∑ i, Y.1 i
        map_add' := by intro x y; simp [Finset.sum_add_distrib]
        map_smul' := by intro c x; simp [Finset.smul_sum] }
    let ψ : P →ₗ[F] F :=
      { toFun := fun Y => ∑ i, α i ⬝ᵥ Y.1 i
        map_add' := by intro x y; simp [dotProduct_add, Finset.sum_add_distrib]
        map_smul' := by intro c x; simp [dotProduct_smul, Finset.mul_sum] }
    have hker : LinearMap.ker fsum ≤ LinearMap.ker ψ := by
      intro Y hY
      rw [LinearMap.mem_ker] at hY ⊢
      have hYi : ∀ i, ∃ v ∈ Vc S H a i, Y.1 i = zv S H i * v := fun i =>
        (mem_Ecert_iff' S H a i _).1 (Y.2 i (Set.mem_univ i))
      choose v hv hYv using hYi
      have h0 := hcase v hv (by
        have : ∑ i, Y.1 i = 0 := hY
        rw [← this]; exact Finset.sum_congr rfl fun i _ => (hYv i).symm)
      show ∑ i, α i ⬝ᵥ Y.1 i = 0
      rw [← h0]
      show _ = ∑ i, lamv i ⬝ᵥ v i
      exact Finset.sum_congr rfl fun i _ => by rw [hYv i, hαz]
    obtain ⟨ℓ, hℓ⟩ := exists_factor fsum ψ hker
    let L0 : Grid S → F := fun x => ℓ (Pi.single x 1)
    have hL0 : ∀ v, ℓ v = L0 ⬝ᵥ v := fun v => by
      convert functional_eq_dot ℓ v using 2
      funext x; simp only [L0]; congr; exact Subsingleton.elim _ _
    have hL0D : ∀ i, L0 - α i ∈ (rsNested S H a).D i := by
      intro i y hy
      rw [← hEq] at hy
      have hYP : (Pi.single i y : Fin k → (Grid S → F)) ∈ P := by
        intro j _
        by_cases hj : j = i
        · subst hj; simpa using hy
        · simp [Pi.single_apply, hj]
      have := hℓ ⟨_, hYP⟩
      simp only [fsum, ψ, LinearMap.coe_mk, AddHom.coe_mk] at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
        Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)] at this
      simp only [Pi.single_eq_same] at this
      rw [hL0] at this
      rw [dotProduct_sub, dotProduct_comm y L0, dotProduct_comm y (α i), this, sub_self]
    -- distance bound
    have hdist : ∀ i, (distTo L0 ((rsNested S H a).D i) : ℝ) ≤ (T i).card := by
      intro i
      have h1 := distTo_le L0 _ _ (hL0D i)
      rw [sub_sub_cancel] at h1
      have h2 := supportCard_le_of (α i) (T i) (fun x hx => by
        by_contra hxT
        apply hx
        simp [α, lamv, hxT])
      exact_mod_cast h1.trans h2
    obtain ⟨d, hd, hdc⟩ := exists_distTo L0 (rsNested S H a).Dbig
    set L := L0 - d with hLdef
    have hLwt : (GoodQLTC.supportCard L : ℝ) ≤ C * ∑ i, ((T i).card : ℝ) := by
      rw [hLdef, hdc]
      refine (hC L0).trans ?_
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hdist i) hCnn
    -- the functional on certificates
    have hcert : ∀ g, ∀ Qs ∈ certSet S H a g, φL Qs = L ⬝ᵥ g := by
      intro g Qs hQs
      rw [mem_certSet_iff] at hQs
      obtain ⟨hV, hg⟩ := hQs
      have hy : ∀ i, zv S H i * Qs i ∈ (rsNested S H a).E i := by
        intro i; rw [← hEq, mem_Ecert_iff']; exact ⟨Qs i, hV i, rfl⟩
      show ∑ i, lamv i ⬝ᵥ Qs i = L ⬝ᵥ g
      rw [hg, dotProduct_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hαz]
      have h1 := hL0D i _ (hy i)
      have h2 : (zv S H i * Qs i) ⬝ᵥ d = 0 :=
        hd _ (Submodule.mem_iSup_of_mem i (hy i))
      rw [dotProduct_sub] at h1
      rw [hLdef, sub_dotProduct, dotProduct_comm d, h2, sub_zero, dotProduct_comm L0,
        dotProduct_comm (α i)]
      exact (sub_eq_zero.mp h1).symm
    have hpure : ∀ m0, ∀ g ∈ (G m0).support,
        (certLaw S H a g).map (fun Qs => muv ⬝ᵥ g + φL Qs) = PMF.pure ((muv + L) ⬝ᵥ g) := by
      intro m0 g hg
      unfold certLaw
      rw [dif_pos (hne m0 g hg)]
      apply map_eq_pure_of_support
      intro Qs hQs
      rw [PMF.mem_support_uniformOfFinset_iff, Set.mem_toFinset] at hQs
      rw [hcert g Qs hQs, add_dotProduct]
    rw [bind_congr_support _ _ _ (hpure m), bind_congr_support _ _ _ (hpure m')]
    rw [show (fun g => PMF.pure ((muv + L) ⬝ᵥ g)) = PMF.pure ∘ (fun g => (muv + L) ⬝ᵥ g) from rfl,
      PMF.bind_pure_comp, PMF.bind_pure_comp]
    set T0 : Finset (Grid S) := Finset.univ.filter (fun x => (muv + L) x ≠ 0) with hT0
    have hfac : (fun g : Grid S → F => (muv + L) ⬝ᵥ g) =
        (fun r : ↥T0 → F => ∑ x : ↥T0, (muv + L) x * r x) ∘ (fun g (x : ↥T0) => g x) := by
      funext g
      simp only [Function.comp_apply, dotProduct]
      rw [sum_subtype_dite T0 (fun x => (muv + L) x * g x)]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ T0
      · rw [dif_pos hx]
      · rw [dif_neg hx]
        simp only [hT0, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
        rw [hx, zero_mul]
    have hcard : T0.card ≤ s := by
      have h1 : T0 ⊆ TG ∪ Finset.univ.filter (fun x => L x ≠ 0) := by
        intro x hx
        simp only [hT0, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply] at hx
        rw [Finset.mem_union, Finset.mem_filter]
        by_contra hcon
        push Not at hcon
        apply hx
        have : muv x = 0 := by simp [muv, hcon.1]
        rw [this, hcon.2 (Finset.mem_univ _), add_zero]
      have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
      have h3 : (Finset.univ.filter (fun x => L x ≠ 0)).card = GoodQLTC.supportCard L := by
        unfold GoodQLTC.supportCard; rfl
      rw [h3] at h2
      have : (T0.card : ℝ) ≤ s := by
        calc (T0.card : ℝ) ≤ TG.card + GoodQLTC.supportCard L := by exact_mod_cast h2
          _ ≤ TG.card + C * ∑ i, ((T i).card : ℝ) := by linarith
          _ ≤ s := hT
      exact_mod_cast this
    rw [hfac, ← PMF.map_comp, ← PMF.map_comp, hpriv T0 hcard m m']


