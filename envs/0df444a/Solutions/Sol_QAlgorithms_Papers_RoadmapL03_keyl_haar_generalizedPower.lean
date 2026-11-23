-- Prove2me | solution 1 for QAlgorithms.Papers.RoadmapL03.keyl_haar_generalizedPower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T11:28:05.141213+00:00
-- url     : https://prove2.me/submissions/8445a295-38c3-404f-a15e-2d16ab2c0736

import Mathlib
import Definitions.Def_QAlgorithms_Defs_KeylTomography


/-! Layer 2 for 29dded7d: the tableau combinatorics behind von Neumann's lemma and the
orthogonality of Young symmetrizers of different shapes, via the column-sum statistic. -/

set_option autoImplicit false

open QAlgorithms QAlgorithms.Schur

noncomputable section

namespace KWS29

variable {d n : ℕ}

/-- `card` distinct naturals sum to at least `0 + 1 + ... + (card-1)`, with equality only for the range. -/
lemma range_sum_aux (A : Finset ℕ) :
    ∑ k ∈ Finset.range A.card, k ≤ ∑ a ∈ A, a ∧
    (∑ a ∈ A, a ≤ ∑ k ∈ Finset.range A.card, k → A = Finset.range A.card) := by
  induction A using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hcard : s.card ≤ a := by
      have hsub : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (ha x hx)
      simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem has, Finset.sum_insert has, Finset.sum_range_succ]
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨by omega, fun hle => ?_⟩
    have h1 : a = s.card := by omega
    have h2 : s = Finset.range s.card := ih2 (by omega)
    rw [h1, Finset.range_add_one, ← h2]

/-- Row and column of the cell numbered `i`. -/
def rowOf (lam : Partition d n) (i : Fin n) : ℕ := ((cellNumbering lam).symm i).val.1
def colOf (lam : Partition d n) (i : Fin n) : ℕ := ((cellNumbering lam).symm i).val.2

lemma cell_eq (lam : Partition d n) (i : Fin n) :
    ((cellNumbering lam).symm i).val = (rowOf lam i, colOf lam i) := rfl

lemma rowcol_inj (lam : Partition d n) {i j : Fin n} (hr : rowOf lam i = rowOf lam j)
    (hc : colOf lam i = colOf lam j) : i = j := by
  apply (cellNumbering lam).symm.injective
  apply Subtype.ext
  rw [cell_eq, cell_eq, hr, hc]

lemma mem_cells (lam : Partition d n) (i : Fin n) : (rowOf lam i, colOf lam i) ∈ lam.val := by
  rw [← cell_eq]; exact ((cellNumbering lam).symm i).property

/-- The fibre of row `r`. -/
def rowFib (lam : Partition d n) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => rowOf lam i = r

lemma image_col_rowFib (lam : Partition d n) (r : ℕ) :
    (rowFib lam r).image (colOf lam) = Finset.range (lam.val.rowLen r) := by
  ext j
  simp only [Finset.mem_image, rowFib, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have := mem_cells lam i
    rw [hi] at this
    exact (YoungDiagram.mem_iff_lt_rowLen).1 this
  · intro hj
    have hm : (r, j) ∈ lam.val := (YoungDiagram.mem_iff_lt_rowLen).2 hj
    refine ⟨cellNumbering lam ⟨(r, j), hm⟩, ?_, ?_⟩
    · simp [rowOf]
    · simp [colOf]

lemma card_rowFib (lam : Partition d n) (r : ℕ) :
    (rowFib lam r).card = lam.val.rowLen r := by
  rw [← Finset.card_range (lam.val.rowLen r), ← image_col_rowFib, Finset.card_image_of_injOn]
  intro i hi j hj hc
  simp only [rowFib, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
  exact rowcol_inj lam (hi.trans hj.symm) hc

/-- Key inequality: if `i ↦ (row_lam i, col_mu (psi i))` is injective, then the column-sum statistic
of `lam` is at most that of `mu`, and with equality every such pair is a cell of `lam`. -/
theorem key_ineq (lam mu : Partition d n) (psi : Equiv.Perm (Fin n))
    (hinj : ∀ i j, rowOf lam i = rowOf lam j → colOf mu (psi i) = colOf mu (psi j) → i = j) :
    ∑ i, colOf lam i ≤ ∑ i, colOf mu i ∧
    (∑ i, colOf mu i ≤ ∑ i, colOf lam i → ∀ i, (rowOf lam i, colOf mu (psi i)) ∈ lam.val) := by
  classical
  have hre : ∑ i, colOf mu i = ∑ i, colOf mu (psi i) :=
    (Equiv.sum_comp psi (colOf mu)).symm
  set t : Finset ℕ := Finset.univ.image (rowOf lam) with ht
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin n)), rowOf lam i ∈ t := fun i _ =>
    Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hsplit : ∀ f : Fin n → ℕ, ∑ i, f i = ∑ r ∈ t, ∑ i ∈ rowFib lam r, f i := by
    intro f
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    rfl
  -- per-row statement
  have hrow : ∀ r, ∑ i ∈ rowFib lam r, colOf lam i ≤ ∑ i ∈ rowFib lam r, colOf mu (psi i) ∧
      (∑ i ∈ rowFib lam r, colOf mu (psi i) ≤ ∑ i ∈ rowFib lam r, colOf lam i →
        ∀ i ∈ rowFib lam r, colOf mu (psi i) < lam.val.rowLen r) := by
    intro r
    have hinjA : Set.InjOn (fun i => colOf mu (psi i)) (rowFib lam r) := by
      intro i hi j hj hc
      simp only [rowFib, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
      exact hinj i j (hi.trans hj.symm) hc
    have hinjB : Set.InjOn (colOf lam) (rowFib lam r) := by
      intro i hi j hj hc
      simp only [rowFib, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
      exact rowcol_inj lam (hi.trans hj.symm) hc
    set A := (rowFib lam r).image (fun i => colOf mu (psi i)) with hA
    have hAcard : A.card = lam.val.rowLen r := by
      rw [hA, Finset.card_image_of_injOn hinjA, card_rowFib]
    have hAsum : ∑ a ∈ A, a = ∑ i ∈ rowFib lam r, colOf mu (psi i) :=
      Finset.sum_image hinjA
    have hBsum : ∑ i ∈ rowFib lam r, colOf lam i = ∑ k ∈ Finset.range (lam.val.rowLen r), k := by
      rw [← image_col_rowFib, Finset.sum_image hinjB]
    obtain ⟨h1, h2⟩ := range_sum_aux A
    rw [hAcard] at h1 h2
    refine ⟨by rw [hBsum, ← hAsum]; exact h1, fun hle i hi => ?_⟩
    have hAeq := h2 (by rw [hAsum, ← hBsum]; exact hle)
    have hmem : colOf mu (psi i) ∈ A := Finset.mem_image_of_mem _ hi
    rw [hAeq] at hmem
    exact Finset.mem_range.1 hmem
  have hle : ∑ i, colOf lam i ≤ ∑ i, colOf mu i := by
    rw [hre, hsplit, hsplit (fun i => colOf mu (psi i))]
    exact Finset.sum_le_sum fun r _ => (hrow r).1
  refine ⟨hle, fun hge i => ?_⟩
  have heq : ∑ r ∈ t, ∑ i ∈ rowFib lam r, colOf lam i =
      ∑ r ∈ t, ∑ i ∈ rowFib lam r, colOf mu (psi i) := by
    rw [← hsplit, ← hsplit (fun i => colOf mu (psi i)), ← hre]
    exact le_antisymm hle hge
  have hall := (Finset.sum_eq_sum_iff_of_le (fun r _ => (hrow r).1)).1 heq
  have hr := (hrow (rowOf lam i)).2 (le_of_eq (hall _ (hmaps i (Finset.mem_univ i))).symm) i
    (by simp [rowFib])
  exact (YoungDiagram.mem_iff_lt_rowLen).2 hr

/-! ## Layer 3: von Neumann's lemma in the group algebra -/

abbrev GA (n : ℕ) := MonoidAlgebra ℂ (Equiv.Perm (Fin n))

lemma mem_R (lam : Partition d n) (p : Equiv.Perm (Fin n)) :
    p ∈ rowPermutations lam ↔ ∀ i, rowOf lam (p i) = rowOf lam i := by
  unfold rowPermutations
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

lemma mem_C (lam : Partition d n) (p : Equiv.Perm (Fin n)) :
    p ∈ columnPermutations lam ↔ ∀ i, colOf lam (p i) = colOf lam i := by
  unfold columnPermutations
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

lemma one_mem_R (lam : Partition d n) : (1 : Equiv.Perm (Fin n)) ∈ rowPermutations lam := by
  rw [mem_R]; intro i; rfl

lemma one_mem_C (lam : Partition d n) : (1 : Equiv.Perm (Fin n)) ∈ columnPermutations lam := by
  rw [mem_C]; intro i; rfl

lemma R_mul {lam : Partition d n} {p q : Equiv.Perm (Fin n)} (hp : p ∈ rowPermutations lam)
    (hq : q ∈ rowPermutations lam) : p * q ∈ rowPermutations lam := by
  rw [mem_R] at *
  intro i
  simp only [Equiv.Perm.mul_apply]
  rw [hp, hq]

lemma C_mul {lam : Partition d n} {p q : Equiv.Perm (Fin n)} (hp : p ∈ columnPermutations lam)
    (hq : q ∈ columnPermutations lam) : p * q ∈ columnPermutations lam := by
  rw [mem_C] at *
  intro i
  simp only [Equiv.Perm.mul_apply]
  rw [hp, hq]

lemma R_inv {lam : Partition d n} {p : Equiv.Perm (Fin n)} (hp : p ∈ rowPermutations lam) :
    p⁻¹ ∈ rowPermutations lam := by
  rw [mem_R] at *
  intro i
  have h := hp (p⁻¹ i)
  rw [show p (p⁻¹ i) = i by simp] at h
  exact h.symm

lemma C_inv {lam : Partition d n} {p : Equiv.Perm (Fin n)} (hp : p ∈ columnPermutations lam) :
    p⁻¹ ∈ columnPermutations lam := by
  rw [mem_C] at *
  intro i
  have h := hp (p⁻¹ i)
  rw [show p (p⁻¹ i) = i by simp] at h
  exact h.symm

lemma swap_mem_R (lam : Partition d n) {i j : Fin n} (h : rowOf lam i = rowOf lam j) :
    Equiv.swap i j ∈ rowPermutations lam := by
  rw [mem_R]
  intro k
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

lemma swap_mem_C (lam : Partition d n) {i j : Fin n} (h : colOf lam i = colOf lam j) :
    Equiv.swap i j ∈ columnPermutations lam := by
  rw [mem_C]
  intro k
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

lemma RC_inter {lam : Partition d n} {p : Equiv.Perm (Fin n)} (hR : p ∈ rowPermutations lam)
    (hC : p ∈ columnPermutations lam) : p = 1 := by
  rw [mem_R] at hR
  rw [mem_C] at hC
  apply Equiv.ext
  intro i
  exact rowcol_inj lam (hR i) (hC i)

/-- Combinatorial von Neumann lemma. -/
theorem vn_comb (lam : Partition d n) (g : Equiv.Perm (Fin n)) :
    (∃ p ∈ rowPermutations lam, ∃ q ∈ columnPermutations lam, g = p * q) ∨
    (∃ i j, i ≠ j ∧ rowOf lam i = rowOf lam j ∧ colOf lam (g⁻¹ i) = colOf lam (g⁻¹ j)) := by
  classical
  by_cases hinj : ∀ i j, rowOf lam i = rowOf lam j → colOf lam (g⁻¹ i) = colOf lam (g⁻¹ j) → i = j
  · left
    have hmem := (key_ineq lam lam g⁻¹ hinj).2 le_rfl
    let s : Fin n → Fin n := fun i =>
      cellNumbering lam ⟨(rowOf lam i, colOf lam (g⁻¹ i)), hmem i⟩
    have hs_row : ∀ i, rowOf lam (s i) = rowOf lam i := by
      intro i; simp [s, rowOf]
    have hs_col : ∀ i, colOf lam (s i) = colOf lam (g⁻¹ i) := by
      intro i; simp [s, colOf]
    have hs_inj : Function.Injective s := by
      intro i j hij
      apply hinj i j
      · rw [← hs_row i, ← hs_row j, hij]
      · rw [← hs_col i, ← hs_col j, hij]
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective s (Finite.injective_iff_bijective.mp hs_inj)
    have hσR : σ ∈ rowPermutations lam := (mem_R lam σ).2 hs_row
    have hqC : g⁻¹ * σ⁻¹ ∈ columnPermutations lam := by
      rw [mem_C]
      intro k
      simp only [Equiv.Perm.mul_apply]
      have h1 := hs_col (σ⁻¹ k)
      have h2 : s (σ⁻¹ k) = k := by
        have h3 : σ (σ⁻¹ k) = k := by simp
        exact h3
      rw [h2] at h1
      exact h1.symm
    exact ⟨σ⁻¹, R_inv hσR, (g⁻¹ * σ⁻¹)⁻¹, C_inv hqC, by group⟩
  · right
    push Not at hinj
    obtain ⟨i, j, h1, h2, h3⟩ := hinj
    exact ⟨i, j, h3, h1, h2⟩

/-- Signs as complex numbers. -/
def sgn (x : Equiv.Perm (Fin n)) : ℂ := (((Equiv.Perm.sign x : ℤˣ) : ℤ) : ℂ)

lemma sgn_mul (x y : Equiv.Perm (Fin n)) : sgn (x * y) = sgn x * sgn y := by
  simp [sgn, Equiv.Perm.sign_mul]

lemma sgn_self (x : Equiv.Perm (Fin n)) : sgn x * sgn x = 1 := by
  unfold sgn
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

/-- Row symmetrizer and column antisymmetrizer. -/
noncomputable def Aelt (lam : Partition d n) : GA n :=
  ∑ p ∈ rowPermutations lam, MonoidAlgebra.single p (1 : ℂ)

noncomputable def Belt (lam : Partition d n) : GA n :=
  ∑ q ∈ columnPermutations lam, MonoidAlgebra.single q (sgn q)

noncomputable def youngElt (lam : Partition d n) : GA n :=
  ∑ a ∈ rowPermutations lam, ∑ b ∈ columnPermutations lam,
    MonoidAlgebra.single (a * b) ((((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ))

lemma youngElt_eq (lam : Partition d n) : youngElt lam = Aelt lam * Belt lam := by
  unfold youngElt Aelt Belt
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [MonoidAlgebra.single_mul_single, one_mul, sgn]

lemma A_mul_single {lam : Partition d n} {p : Equiv.Perm (Fin n)} (hp : p ∈ rowPermutations lam) :
    Aelt lam * MonoidAlgebra.single p (1 : ℂ) = Aelt lam := by
  unfold Aelt
  rw [Finset.sum_mul]
  simp only [MonoidAlgebra.single_mul_single, one_mul]
  exact Finset.sum_nbij' (fun x => x * p) (fun y => y * p⁻¹)
    (fun x hx => R_mul hx hp) (fun y hy => R_mul hy (R_inv hp))
    (fun x _ => by simp) (fun y _ => by simp) (fun x _ => rfl)

lemma single_mul_B {lam : Partition d n} {q : Equiv.Perm (Fin n)}
    (hq : q ∈ columnPermutations lam) :
    MonoidAlgebra.single q (1 : ℂ) * Belt lam = sgn q • Belt lam := by
  unfold Belt
  rw [Finset.mul_sum, Finset.smul_sum]
  simp only [MonoidAlgebra.single_mul_single, one_mul, MonoidAlgebra.smul_single']
  exact Finset.sum_nbij' (fun x => q * x) (fun y => q⁻¹ * y)
    (fun x hx => C_mul hq hx) (fun y hy => C_mul (C_inv hq) hy)
    (fun x _ => by simp) (fun y _ => by simp)
    (fun x _ => by congr 1; rw [sgn_mul, ← mul_assoc, sgn_self, one_mul])

lemma A_single_B_zero (lam mu : Partition d n) (g : Equiv.Perm (Fin n)) {i j : Fin n}
    (hij : i ≠ j) (hr : rowOf lam i = rowOf lam j) (hc : colOf mu (g⁻¹ i) = colOf mu (g⁻¹ j)) :
    Aelt lam * MonoidAlgebra.single g (1 : ℂ) * Belt mu = 0 := by
  set X := Aelt lam * MonoidAlgebra.single g (1 : ℂ) * Belt mu with hXdef
  have ht : Equiv.swap i j ∈ rowPermutations lam := swap_mem_R lam hr
  have ht' : Equiv.swap (g⁻¹ i) (g⁻¹ j) ∈ columnPermutations mu := swap_mem_C mu hc
  have hne : g⁻¹ i ≠ g⁻¹ j := fun h => hij (g⁻¹.injective h)
  have hsg : sgn (Equiv.swap (g⁻¹ i) (g⁻¹ j)) = -1 := by
    simp [sgn, hij]
  have hconj : Equiv.swap i j * g = g * Equiv.swap (g⁻¹ i) (g⁻¹ j) := by
    rw [Equiv.swap_apply_apply, inv_inv]
    group
  have hs : MonoidAlgebra.single (Equiv.swap i j) (1 : ℂ) * MonoidAlgebra.single g 1 =
      MonoidAlgebra.single g 1 * MonoidAlgebra.single (Equiv.swap (g⁻¹ i) (g⁻¹ j)) 1 := by
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, hconj]
  have hX : X = -X := by
    calc X = Aelt lam * MonoidAlgebra.single (Equiv.swap i j) 1 * MonoidAlgebra.single g 1 *
          Belt mu := by rw [A_mul_single ht]
      _ = Aelt lam * (MonoidAlgebra.single g 1 *
          (MonoidAlgebra.single (Equiv.swap (g⁻¹ i) (g⁻¹ j)) 1 * Belt mu)) := by
          rw [mul_assoc (Aelt lam), hs]; simp only [mul_assoc]
      _ = -X := by rw [single_mul_B ht', hsg, hXdef]; simp [mul_assoc]
  have h2 : (2 : ℂ) • X = 0 := by
    rw [two_smul]; nth_rewrite 1 [hX]; exact neg_add_cancel _
  have h3 := congrArg (fun Y => (2 : ℂ)⁻¹ • Y) h2
  simp only [smul_smul, smul_zero] at h3
  rw [inv_mul_cancel₀ two_ne_zero, one_smul] at h3
  exact h3

lemma A_single_B (lam : Partition d n) (g : Equiv.Perm (Fin n)) :
    ∃ α : ℂ, Aelt lam * MonoidAlgebra.single g (1 : ℂ) * Belt lam = α • (Aelt lam * Belt lam) := by
  rcases vn_comb lam g with ⟨p, hp, q, hq, rfl⟩ | ⟨i, j, hij, hr, hc⟩
  · refine ⟨sgn q, ?_⟩
    have hpq : MonoidAlgebra.single (p * q) (1 : ℂ) =
        MonoidAlgebra.single p 1 * MonoidAlgebra.single q 1 := by
      rw [MonoidAlgebra.single_mul_single, mul_one]
    rw [hpq, ← mul_assoc, A_mul_single hp, mul_assoc, single_mul_B hq, mul_smul_comm]
  · exact ⟨0, by rw [A_single_B_zero lam lam g hij hr hc, zero_smul]⟩

lemma AxB (lam : Partition d n) (x : GA n) :
    ∃ α : ℂ, Aelt lam * x * Belt lam = α • (Aelt lam * Belt lam) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    rw [show MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g = MonoidAlgebra.single g 1 from rfl]
    exact A_single_B lam g
  | add f g hf hg =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    exact ⟨a + b, by rw [mul_add, add_mul, ha, hb, add_smul]⟩
  | smul r f hf =>
    obtain ⟨a, ha⟩ := hf
    exact ⟨r * a, by rw [mul_smul_comm, smul_mul_assoc, ha, smul_smul]⟩

/-- (K1) `c x c ∈ ℂ c`. -/
theorem cxc (lam : Partition d n) (x : GA n) :
    ∃ α : ℂ, youngElt lam * x * youngElt lam = α • youngElt lam := by
  obtain ⟨α, h⟩ := AxB lam (Belt lam * x * Aelt lam)
  refine ⟨α, ?_⟩
  rw [youngElt_eq, ← h]
  simp only [mul_assoc]

/-! Left regular representation and `c^2 = k c` with `k ≠ 0`. -/

lemma lr_one : leftRegular (1 : Equiv.Perm (Fin n)) = 1 := by
  ext g h
  simp [leftRegular, Matrix.one_apply]

lemma lr_mul (p q : Equiv.Perm (Fin n)) : leftRegular (p * q) = leftRegular p * leftRegular q := by
  ext g h
  simp only [leftRegular, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_assoc]

noncomputable def Lm (n : ℕ) :
    Equiv.Perm (Fin n) →* Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ where
  toFun := leftRegular
  map_one' := lr_one
  map_mul' := lr_mul

noncomputable def LR (n : ℕ) : GA n →ₐ[ℂ] Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ :=
  MonoidAlgebra.lift ℂ _ _ (Lm n)

lemma LR_single (p : Equiv.Perm (Fin n)) (c : ℂ) :
    LR n (MonoidAlgebra.single p c) = c • leftRegular p := by
  simp [LR]
  rfl

lemma lr_trace (s : Equiv.Perm (Fin n)) :
    (leftRegular s).trace = if s = 1 then (n.factorial : ℂ) else 0 := by
  unfold Matrix.trace
  simp only [Matrix.diag, leftRegular, Matrix.of_apply]
  by_cases hs : s = 1
  · subst hs; simp [Fintype.card_perm]
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun g _ => if_neg ?_
    intro h
    apply hs
    have h' := congrArg (· * g⁻¹) h
    simpa using h'.symm

lemma trace_LR_young (lam : Partition d n) : (LR n (youngElt lam)).trace = (n.factorial : ℂ) := by
  unfold youngElt
  simp only [map_sum, LR_single, Matrix.trace_sum, Matrix.trace_smul, lr_trace, smul_eq_mul]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp
    · intro b _ hb1
      rw [one_mul, if_neg hb1, mul_zero]
    · intro h; exact absurd (one_mem_C lam) h
  · intro a ha ha1
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [if_neg, mul_zero]
    intro hab
    apply ha1
    have h1 : a⁻¹ = b := inv_eq_of_mul_eq_one_right hab
    have hb' : a⁻¹ ∈ columnPermutations lam := h1 ▸ hb
    exact inv_eq_one.mp (RC_inter (R_inv ha) hb')
  · intro h; exact absurd (one_mem_R lam) h

/-- (K0) `c^2 = k c` with `k ≠ 0`. -/
theorem young_sq (lam : Partition d n) :
    ∃ k : ℂ, k ≠ 0 ∧ youngElt lam * youngElt lam = k • youngElt lam := by
  obtain ⟨k, hk⟩ := cxc lam 1
  rw [mul_one] at hk
  refine ⟨k, ?_, hk⟩
  rintro rfl
  rw [zero_smul] at hk
  have hnil : IsNilpotent (LR n (youngElt lam)) :=
    ⟨2, by rw [pow_two, ← map_mul, hk, map_zero]⟩
  have h1 := Matrix.isNilpotent_trace_of_isNilpotent hnil
  rw [trace_LR_young] at h1
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) h1.eq_zero

/-! ## Layer 4: orthogonality of Young symmetrizers of different shapes -/

lemma col_card_of_inj (lam : Partition d n) (ψ : Fin n → ℕ × ℕ) (hinj : Function.Injective ψ)
    (hmem : ∀ i, ψ i ∈ lam.val) (j : ℕ) :
    lam.val.colLen j = (Finset.univ.filter fun i => (ψ i).2 = j).card := by
  classical
  have hsub : Finset.univ.image ψ ⊆ lam.val.cells := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hc
    exact (YoungDiagram.mem_cells _).2 (hmem i)
  have hcard : lam.val.cells.card ≤ (Finset.univ.image ψ).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    exact le_of_eq lam.property.1
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  rw [YoungDiagram.colLen_eq_card, ← Finset.card_image_of_injective _ hinj]
  congr 1
  ext c
  rw [YoungDiagram.mem_col_iff, Finset.mem_image]
  constructor
  · rintro ⟨hc, rfl⟩
    have hc' : c ∈ Finset.univ.image ψ := by rw [heq]; exact (YoungDiagram.mem_cells _).2 hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hc'
    exact ⟨i, by simp, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨hmem i, hi⟩

lemma colLen_mu (mu : Partition d n) (j : ℕ) :
    mu.val.colLen j = (Finset.univ.filter fun k => colOf mu k = j).card :=
  col_card_of_inj mu (fun k => (rowOf mu k, colOf mu k))
    (fun a b h => rowcol_inj mu (congrArg Prod.fst h) (congrArg Prod.snd h)) (mem_cells mu) j

/-- (K2) Two letters in one `lam`-row and one `mu`-column unless `lam = mu`, when the column-sum
statistic of `mu` does not exceed that of `lam`. -/
theorem shape_orth (lam mu : Partition d n) (hne : lam ≠ mu)
    (hle : ∑ i, colOf mu i ≤ ∑ i, colOf lam i) (g : Equiv.Perm (Fin n)) :
    Aelt lam * MonoidAlgebra.single g (1 : ℂ) * Belt mu = 0 := by
  classical
  by_cases hinj : ∀ i j, rowOf lam i = rowOf lam j → colOf mu (g⁻¹ i) = colOf mu (g⁻¹ j) → i = j
  · exfalso
    apply hne
    have hmem := (key_ineq lam mu g⁻¹ hinj).2 hle
    have hφ : Function.Injective (fun i => (rowOf lam i, colOf mu (g⁻¹ i))) := by
      intro a b h
      simp only [Prod.mk.injEq] at h
      exact hinj a b h.1 h.2
    have hcol : ∀ j, lam.val.colLen j = mu.val.colLen j := by
      intro j
      rw [col_card_of_inj lam _ hφ hmem j, colLen_mu mu j]
      exact Finset.card_nbij' (fun i => g⁻¹ i) (fun k => g k)
        (by intro a ha; simpa using ha) (by intro a ha; simpa using ha)
        (by intro a _; simp) (by intro a _; simp)
    apply Subtype.ext
    apply YoungDiagram.ext
    apply Finset.ext
    rintro ⟨r, j⟩
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen,
      YoungDiagram.mem_iff_lt_colLen, hcol j]
  · push Not at hinj
    obtain ⟨i, j, h1, h2, h3⟩ := hinj
    exact A_single_B_zero lam mu g h3 h1 h2

lemma A_x_B_zero (lam mu : Partition d n) (hne : lam ≠ mu)
    (hle : ∑ i, colOf mu i ≤ ∑ i, colOf lam i) (x : GA n) : Aelt lam * x * Belt mu = 0 := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    rw [show MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g = MonoidAlgebra.single g 1 from rfl]
    exact shape_orth lam mu hne hle g
  | add f g hf hg => rw [mul_add, add_mul, hf, hg, add_zero]
  | smul r f hf => rw [mul_smul_comm, smul_mul_assoc, hf, smul_zero]

theorem young_orth (lam mu : Partition d n) (hne : lam ≠ mu)
    (hle : ∑ i, colOf mu i ≤ ∑ i, colOf lam i) (y : GA n) :
    youngElt lam * y * youngElt mu = 0 := by
  rw [youngElt_eq, youngElt_eq]
  have h := A_x_B_zero lam mu hne hle (Belt lam * y * Aelt mu)
  calc Aelt lam * Belt lam * y * (Aelt mu * Belt mu)
      = Aelt lam * (Belt lam * y * Aelt mu) * Belt mu := by simp only [mul_assoc]
    _ = 0 := h


/-! ## Layer 5a: the conjugation sum `W = ∑ h c h⁻¹` is central, `W c = k^2 c`, `W W = k^2 W`. -/

abbrev og (g : Equiv.Perm (Fin n)) : GA n := MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g

lemma og_mul (g h : Equiv.Perm (Fin n)) : og (g * h) = og g * og h := map_mul _ g h

lemma og_one : og (1 : Equiv.Perm (Fin n)) = 1 := map_one _

lemma og_inv_mul (g : Equiv.Perm (Fin n)) : og g⁻¹ * og g = 1 := by
  rw [← og_mul, inv_mul_cancel, og_one]

/-- Trace of the left regular representation: `tau x = n! * x(1)`. -/
noncomputable def tau (x : GA n) : ℂ := (LR n x).trace

lemma tau_add (x y : GA n) : tau (x + y) = tau x + tau y := by
  simp only [tau, map_add, Matrix.trace_add]

lemma tau_smul (r : ℂ) (x : GA n) : tau (r • x) = r * tau x := by
  simp only [tau, map_smul, Matrix.trace_smul, smul_eq_mul]

lemma tau_comm (x y : GA n) : tau (x * y) = tau (y * x) := by
  simp only [tau, map_mul]
  exact Matrix.trace_mul_comm _ _

lemma tau_og (g : Equiv.Perm (Fin n)) : tau (og g) = if g = 1 then (n.factorial : ℂ) else 0 := by
  show (LR n (MonoidAlgebra.single g 1)).trace = _
  rw [LR_single, one_smul, lr_trace]

lemma tau_young (lam : Partition d n) : tau (youngElt lam) = (n.factorial : ℂ) :=
  trace_LR_young lam

lemma young_ne_zero (lam : Partition d n) : youngElt lam ≠ 0 := by
  intro h
  have h1 := tau_young lam
  rw [h, tau, map_zero, Matrix.trace_zero] at h1
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) h1.symm

/-- Fourier expansion: `∑_h tau(x h) h⁻¹ = n! x`. -/
lemma expand (x : GA n) :
    ∑ h : Equiv.Perm (Fin n), tau (x * og h) • og h⁻¹ = (n.factorial : ℂ) • x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    show ∑ h : Equiv.Perm (Fin n), tau (og g * og h) • og h⁻¹ = (n.factorial : ℂ) • og g
    rw [Finset.sum_eq_single g⁻¹]
    · rw [← og_mul, mul_inv_cancel, tau_og, if_pos rfl, inv_inv]
    · intro b _ hb
      rw [← og_mul, tau_og, if_neg, zero_smul]
      intro h
      exact hb (eq_inv_of_mul_eq_one_right h)
    · intro h; exact absurd (Finset.mem_univ _) h
  | add x y hx hy =>
    simp only [add_mul, tau_add, add_smul, Finset.sum_add_distrib, hx, hy, smul_add]
  | smul r x hx =>
    simp only [smul_mul_assoc, tau_smul, mul_smul, ← Finset.smul_sum, hx]
    rw [smul_comm]

/-- The conjugation sum of the Young symmetrizer. -/
noncomputable def Wc (lam : Partition d n) : GA n :=
  ∑ h : Equiv.Perm (Fin n), og h * youngElt lam * og h⁻¹

lemma Wc_og (lam : Partition d n) (g : Equiv.Perm (Fin n)) : og g * Wc lam = Wc lam * og g := by
  unfold Wc
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => ?_)
  simp only [Equiv.coe_mulLeft]
  rw [mul_inv_rev, og_mul, og_mul]
  simp only [mul_assoc]
  rw [og_inv_mul, mul_one]

lemma Wc_comm (lam : Partition d n) (x : GA n) : x * Wc lam = Wc lam * x := by
  induction x using MonoidAlgebra.induction_on with
  | of g => exact Wc_og lam g
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

/-- `∑_h tau(c h) α(h) = n! k^2` where `c h⁻¹ c = α(h) c`. -/
lemma sum_tau_alpha (lam : Partition d n) {k : ℂ}
    (hk : youngElt lam * youngElt lam = k • youngElt lam) (α : Equiv.Perm (Fin n) → ℂ)
    (hα : ∀ h, youngElt lam * og h⁻¹ * youngElt lam = α h • youngElt lam) :
    ∑ h : Equiv.Perm (Fin n), tau (youngElt lam * og h) * α h = (n.factorial : ℂ) * (k * k) := by
  apply smul_left_injective ℂ (young_ne_zero lam)
  show (∑ h : Equiv.Perm (Fin n), tau (youngElt lam * og h) * α h) • youngElt lam =
    ((n.factorial : ℂ) * (k * k)) • youngElt lam
  have e1 : youngElt lam * (∑ h : Equiv.Perm (Fin n), tau (youngElt lam * og h) • og h⁻¹) *
      youngElt lam = ((n.factorial : ℂ) * (k * k)) • youngElt lam := by
    rw [expand, mul_smul_comm, smul_mul_assoc, hk, smul_mul_assoc, hk, smul_smul, smul_smul,
      mul_assoc]
  rw [← e1, Finset.mul_sum, Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, hα h, smul_smul]

/-- (K2) `W c = k^2 c`. -/
theorem Wc_young (lam : Partition d n) {k : ℂ} (hk0 : k ≠ 0)
    (hk : youngElt lam * youngElt lam = k • youngElt lam) :
    Wc lam * youngElt lam = (k * k) • youngElt lam := by
  obtain ⟨γ, hγ⟩ := cxc lam (Wc lam)
  have hβ : Wc lam * youngElt lam = (k⁻¹ * γ) • youngElt lam := by
    have h2 : youngElt lam * Wc lam * youngElt lam = k • (Wc lam * youngElt lam) := by
      rw [Wc_comm, mul_assoc, hk, mul_smul_comm]
    rw [hγ] at h2
    rw [mul_smul, h2, smul_smul, inv_mul_cancel₀ hk0, one_smul]
  choose α hα using fun h : Equiv.Perm (Fin n) => cxc lam (og h⁻¹)
  have hS := sum_tau_alpha lam hk α hα
  have hT : tau (Wc lam * youngElt lam) = (n.factorial : ℂ) * (k * k) := by
    rw [← hS]
    unfold Wc
    rw [Finset.sum_mul]
    simp only [tau, map_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    show tau (og h * youngElt lam * og h⁻¹ * youngElt lam) = tau (youngElt lam * og h) * α h
    rw [mul_assoc, mul_assoc, tau_comm, ← mul_assoc, hα h, smul_mul_assoc, tau_smul,
      mul_comm (α h)]
  rw [hβ, tau_smul, tau_young] at hT
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hb : k⁻¹ * γ = k * k := by
    have := hT
    rw [mul_comm] at this
    exact mul_left_cancel₀ hf this
  rw [hβ, hb]

/-- (K3) `W W = k^2 W`. -/
theorem Wc_sq (lam : Partition d n) {k : ℂ} (hk0 : k ≠ 0)
    (hk : youngElt lam * youngElt lam = k • youngElt lam) :
    Wc lam * Wc lam = (k * k) • Wc lam := by
  have hW : Wc lam = ∑ h : Equiv.Perm (Fin n), og h * youngElt lam * og h⁻¹ := rfl
  nth_rewrite 2 [hW]
  rw [Finset.mul_sum]
  conv_rhs => rw [hW]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← mul_assoc, ← mul_assoc, ← Wc_og, mul_assoc (og h), Wc_young lam hk0 hk, mul_smul_comm,
    smul_mul_assoc]

/-- (K4) different shapes: `W_lam W_mu = 0`. -/
lemma Wc_orth_le (lam mu : Partition d n) (hne : lam ≠ mu)
    (hle : ∑ i, colOf mu i ≤ ∑ i, colOf lam i) : Wc lam * Wc mu = 0 := by
  unfold Wc
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun g _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun h _ => ?_
  have := young_orth lam mu hne hle (og g⁻¹ * og h)
  calc og g * youngElt lam * og g⁻¹ * (og h * youngElt mu * og h⁻¹)
      = og g * (youngElt lam * (og g⁻¹ * og h) * youngElt mu) * og h⁻¹ := by
        simp only [mul_assoc]
    _ = 0 := by rw [this, mul_zero, zero_mul]

theorem Wc_orth (lam mu : Partition d n) (hne : lam ≠ mu) : Wc lam * Wc mu = 0 := by
  rcases le_total (∑ i, colOf mu i) (∑ i, colOf lam i) with hle | hle
  · exact Wc_orth_le lam mu hne hle
  · rw [Wc_comm]
    exact Wc_orth_le mu lam (Ne.symm hne) hle

end KWS29

end

-- ===== layers from 29dded7d_c5.lean (namespace KWS29P) =====

/-! Layer 2 for 29dded7d: the tableau combinatorics behind von Neumann's lemma and the
orthogonality of Young symmetrizers of different shapes, via the column-sum statistic. -/

set_option autoImplicit false

open QAlgorithms QAlgorithms.Schur
open scoped Matrix

noncomputable section

namespace KWS29P

variable {d n : ℕ}
abbrev GA (n : ℕ) := MonoidAlgebra ℂ (Equiv.Perm (Fin n))
noncomputable def youngElt (lam : Partition d n) : GA n :=
  ∑ a ∈ rowPermutations lam, ∑ b ∈ columnPermutations lam,
    MonoidAlgebra.single (a * b) ((((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ))

lemma lr_one : leftRegular (1 : Equiv.Perm (Fin n)) = 1 := by
  ext g h
  simp [leftRegular, Matrix.one_apply]

lemma lr_mul (p q : Equiv.Perm (Fin n)) : leftRegular (p * q) = leftRegular p * leftRegular q := by
  ext g h
  simp only [leftRegular, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_assoc]

noncomputable def Lm (n : ℕ) :
    Equiv.Perm (Fin n) →* Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ where
  toFun := leftRegular
  map_one' := lr_one
  map_mul' := lr_mul

noncomputable def LR (n : ℕ) : GA n →ₐ[ℂ] Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ :=
  MonoidAlgebra.lift ℂ _ _ (Lm n)

lemma LR_single (p : Equiv.Perm (Fin n)) (c : ℂ) :
    LR n (MonoidAlgebra.single p c) = c • leftRegular p := by
  simp [LR]
  rfl

lemma lr_trace (s : Equiv.Perm (Fin n)) :
    (leftRegular s).trace = if s = 1 then (n.factorial : ℂ) else 0 := by
  unfold Matrix.trace
  simp only [Matrix.diag, leftRegular, Matrix.of_apply]
  by_cases hs : s = 1
  · subst hs; simp [Fintype.card_perm]
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun g _ => if_neg ?_
    intro h
    apply hs
    have h' := congrArg (· * g⁻¹) h
    simpa using h'.symm

abbrev og (g : Equiv.Perm (Fin n)) : GA n := MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g

lemma og_mul (g h : Equiv.Perm (Fin n)) : og (g * h) = og g * og h := map_mul _ g h

lemma og_one : og (1 : Equiv.Perm (Fin n)) = 1 := map_one _

lemma og_inv_mul (g : Equiv.Perm (Fin n)) : og g⁻¹ * og g = 1 := by
  rw [← og_mul, inv_mul_cancel, og_one]

/-- Trace of the left regular representation: `tau x = n! * x(1)`. -/
noncomputable def tau (x : GA n) : ℂ := (LR n x).trace

lemma tau_add (x y : GA n) : tau (x + y) = tau x + tau y := by
  simp only [tau, map_add, Matrix.trace_add]

lemma tau_smul (r : ℂ) (x : GA n) : tau (r • x) = r * tau x := by
  simp only [tau, map_smul, Matrix.trace_smul, smul_eq_mul]

lemma tau_comm (x y : GA n) : tau (x * y) = tau (y * x) := by
  simp only [tau, map_mul]
  exact Matrix.trace_mul_comm _ _

lemma tau_og (g : Equiv.Perm (Fin n)) : tau (og g) = if g = 1 then (n.factorial : ℂ) else 0 := by
  show (LR n (MonoidAlgebra.single g 1)).trace = _
  rw [LR_single, one_smul, lr_trace]

/-- Fourier expansion: `∑_h tau(x h) h⁻¹ = n! x`. -/
lemma expand (x : GA n) :
    ∑ h : Equiv.Perm (Fin n), tau (x * og h) • og h⁻¹ = (n.factorial : ℂ) • x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    show ∑ h : Equiv.Perm (Fin n), tau (og g * og h) • og h⁻¹ = (n.factorial : ℂ) • og g
    rw [Finset.sum_eq_single g⁻¹]
    · rw [← og_mul, mul_inv_cancel, tau_og, if_pos rfl, inv_inv]
    · intro b _ hb
      rw [← og_mul, tau_og, if_neg, zero_smul]
      intro h
      exact hb (eq_inv_of_mul_eq_one_right h)
    · intro h; exact absurd (Finset.mem_univ _) h
  | add x y hx hy =>
    simp only [add_mul, tau_add, add_smul, Finset.sum_add_distrib, hx, hy, smul_add]
  | smul r x hx =>
    simp only [smul_mul_assoc, tau_smul, mul_smul, ← Finset.smul_sum, hx]
    rw [smul_comm]

lemma tau_sum {ι : Type} (s : Finset ι) (f : ι → GA n) : tau (∑ i ∈ s, f i) = ∑ i ∈ s, tau (f i) := by
  simp only [tau, map_sum, Matrix.trace_sum]

lemma tau_og_single (x y : Equiv.Perm (Fin n)) (r : ℂ) :
    tau (og x * MonoidAlgebra.single y r) = if x * y = 1 then r * (n.factorial : ℂ) else 0 := by
  show tau (MonoidAlgebra.single x 1 * MonoidAlgebra.single y r) = _
  rw [MonoidAlgebra.single_mul_single, one_mul]
  unfold tau
  rw [LR_single, Matrix.trace_smul, lr_trace, smul_eq_mul]
  split_ifs <;> simp

/-- Matrix of right multiplication by `x` on the regular basis: column `h` is `h * x`. -/
noncomputable def RR (x : GA n) : Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ :=
  Matrix.of fun g h => (n.factorial : ℂ)⁻¹ * tau (og g⁻¹ * og h * x)

lemma youngRightOperator_eq (lam : Partition d n) : youngRightOperator lam = RR (youngElt lam) := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  ext g h
  simp only [youngRightOperator, RR, Matrix.of_apply, youngElt, Finset.mul_sum, tau_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← og_mul, tau_og_single]
  have hiff : g⁻¹ * h * (a * b) = 1 ↔ g = h * a * b := by
    rw [mul_assoc, inv_mul_eq_one, ← mul_assoc]
  by_cases H : g = h * a * b
  · rw [if_pos H, if_pos (hiff.2 H)]
    field_simp
  · rw [if_neg H, if_neg (fun H' => H (hiff.1 H')), mul_zero]

lemma RR_mul (x y : GA n) : RR x * RR y = RR (y * x) := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  ext g h
  have key := congrArg (fun z => tau (z * (og h * y))) (expand (x * og g⁻¹))
  simp only [Finset.sum_mul, tau_sum, smul_mul_assoc, tau_smul] at key
  simp only [RR, Matrix.mul_apply, Matrix.of_apply]
  have e1 : ∀ m : Equiv.Perm (Fin n), tau (og g⁻¹ * og m * x) = tau (x * og g⁻¹ * og m) :=
    fun m => by rw [tau_comm, mul_assoc x]
  have e2 : ∀ m : Equiv.Perm (Fin n), tau (og m⁻¹ * og h * y) = tau (og m⁻¹ * (og h * y)) :=
    fun m => by rw [mul_assoc]
  have e3 : tau (og g⁻¹ * og h * (y * x)) = tau (x * og g⁻¹ * (og h * y)) := by
    rw [tau_comm, mul_assoc, tau_comm]; simp only [mul_assoc]
  have e4 : ∀ a b : ℂ, (n.factorial : ℂ)⁻¹ * a * ((n.factorial : ℂ)⁻¹ * b) =
      ((n.factorial : ℂ)⁻¹ * (n.factorial : ℂ)⁻¹) * (a * b) := fun a b => by ring
  simp only [e1, e2, e3, e4]
  rw [← Finset.mul_sum, key]
  field_simp

lemma trace_lr_RR (p : Equiv.Perm (Fin n)) (x : GA n) :
    (leftRegular p * RR x).trace =
      (n.factorial : ℂ)⁻¹ * ∑ a : Equiv.Perm (Fin n), tau (og a * x * og a⁻¹ * og p) := by
  unfold Matrix.trace
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.diag, Matrix.mul_apply, leftRegular, RR, Matrix.of_apply, ite_mul, one_mul,
    zero_mul]
  rw [Finset.sum_eq_single (p⁻¹ * a)]
  · rw [if_pos (show a = p * (p⁻¹ * a) by group), mul_inv_rev, inv_inv, og_mul]
    rw [show og a⁻¹ * og p * og a * x = (og a⁻¹ * og p) * (og a * x) by simp only [mul_assoc],
      tau_comm]
    simp only [mul_assoc]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (show b = p⁻¹ * a by rw [h, ← mul_assoc, inv_mul_cancel, one_mul])
  · intro h; exact absurd (Finset.mem_univ _) h

lemma trace_RR (x : GA n) : (RR x).trace = tau x := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h := trace_lr_RR 1 x
  rw [lr_one, one_mul] at h
  rw [h]
  have e : ∀ a : Equiv.Perm (Fin n), tau (og a * x * og a⁻¹ * og 1) = tau x := fun a => by
    rw [og_one, mul_one, tau_comm, ← mul_assoc, ← og_mul, inv_mul_cancel, og_one, one_mul]
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-! ### glue-2: the orthogonal projection onto the range of a quasi-idempotent matrix -/

section MatGlue
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def projMat (S : Submodule ℂ (EuclideanSpace ℂ ι)) : Matrix ι ι ℂ :=
  Matrix.of fun g h => inner ℂ (ket g) (S.starProjection (ket h))

lemma toEL_mul (A B : Matrix ι ι ℂ) :
    Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_mul _ _ _ A B

lemma toEL_projMat (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    Matrix.toEuclideanLin (projMat S) =
      (S.starProjection : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) := by
  apply (EuclideanSpace.basisFun ι ℂ).toBasis.ext
  intro h
  ext g
  rw [EuclideanSpace.basisFun_toBasis]
  simp [projMat, ket, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    EuclideanSpace.inner_single_left, Pi.single_apply]

lemma trace_toEL (M : Matrix ι ι ℂ) :
    LinearMap.trace ℂ _ (Matrix.toEuclideanLin M) = M.trace := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun ι ℂ).toBasis, LinearMap.toMatrix_toLin]

variable {Y : Matrix ι ι ℂ} {k : ℂ}

lemma projMat_mul (_hY : Y * Y = k • Y) :
    projMat (LinearMap.range (Matrix.toEuclideanLin Y)) * Y = Y := by
  apply Matrix.toEuclideanLin.injective
  rw [toEL_mul, toEL_projMat]
  ext1 v
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe]
  exact Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self _ v)

lemma mul_projMat (hY : Y * Y = k • Y) :
    Y * projMat (LinearMap.range (Matrix.toEuclideanLin Y)) =
      k • projMat (LinearMap.range (Matrix.toEuclideanLin Y)) := by
  apply Matrix.toEuclideanLin.injective
  rw [toEL_mul, map_smul, toEL_projMat]
  ext1 v
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
    LinearMap.smul_apply]
  obtain ⟨w, hw⟩ := Submodule.starProjection_apply_mem
    (LinearMap.range (Matrix.toEuclideanLin Y)) v
  rw [← hw]
  have := congrArg (fun M => Matrix.toEuclideanLin M w) hY
  simpa [toEL_mul] using this

lemma finrank_range (hk : k ≠ 0) (hY : Y * Y = k • Y) :
    (Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin Y)) : ℂ) = k⁻¹ * Y.trace := by
  have hP : LinearMap.IsProj (LinearMap.range (Matrix.toEuclideanLin Y))
      (Matrix.toEuclideanLin (k⁻¹ • Y)) := by
    constructor
    · intro x
      rw [map_smul]
      exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ x)
    · rintro x ⟨w, rfl⟩
      have := congrArg (fun M => Matrix.toEuclideanLin M w) hY
      simp only [toEL_mul, LinearMap.coe_comp, Function.comp_apply, map_smul,
        LinearMap.smul_apply] at this
      rw [map_smul, LinearMap.smul_apply, this, smul_smul, inv_mul_cancel₀ hk, one_smul]
  have h := hP.trace
  rw [trace_toEL, Matrix.trace_smul, smul_eq_mul] at h
  exact h.symm

lemma trace_mul_projMat (hk : k ≠ 0) (hY : Y * Y = k • Y) (M : Matrix ι ι ℂ)
    (hM : M * Y = Y * M) :
    (M * projMat (LinearMap.range (Matrix.toEuclideanLin Y))).trace = k⁻¹ * (M * Y).trace := by
  set P := projMat (LinearMap.range (Matrix.toEuclideanLin Y))
  have h2 : P = k⁻¹ • (Y * P) := by
    rw [mul_projMat hY, smul_smul, inv_mul_cancel₀ hk, one_smul]
  rw [h2, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← Matrix.mul_assoc,
    Matrix.trace_mul_cycle, Matrix.mul_assoc P, hM,
    ← Matrix.mul_assoc, projMat_mul hY, Matrix.trace_mul_comm Y M]

end MatGlue

lemma RR_smul (r : ℂ) (x : GA n) : RR (r • x) = r • RR x := by
  ext g h
  simp only [RR, Matrix.of_apply, Matrix.smul_apply, mul_smul_comm, tau_smul, smul_eq_mul]
  ring

lemma lr_RR_comm (p : Equiv.Perm (Fin n)) (x : GA n) :
    leftRegular p * RR x = RR x * leftRegular p := by
  ext g h
  simp only [Matrix.mul_apply, leftRegular, RR, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (p⁻¹ * g), Finset.sum_eq_single (p * h)]
  · rw [if_pos rfl, if_pos (show g = p * (p⁻¹ * g) by group), mul_inv_rev, inv_inv, og_mul,
      og_mul]
    simp only [mul_assoc]
  · intro b _ hb; rw [if_neg hb]
  · intro h'; exact absurd (Finset.mem_univ _) h'
  · intro b _ hb
    rw [if_neg]
    intro h'
    exact hb (show b = p⁻¹ * g by rw [h', ← mul_assoc, inv_mul_cancel, one_mul])
  · intro h'; exact absurd (Finset.mem_univ _) h'

noncomputable def Wx (x : GA n) : GA n := ∑ h : Equiv.Perm (Fin n), og h * x * og h⁻¹

lemma og_smul_single (p : Equiv.Perm (Fin n)) (c : ℂ) : MonoidAlgebra.single p c = c • og p := by
  simp [og, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single']

section Glue2
variable {x : GA n} {k : ℂ}

lemma RR_sq (hx : x * x = k • x) : RR x * RR x = k • RR x := by
  rw [RR_mul, hx, RR_smul]

lemma finrank_RR (hk : k ≠ 0) (hx : x * x = k • x) :
    (Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin (RR x))) : ℂ) = k⁻¹ * tau x := by
  rw [finrank_range hk (RR_sq hx), trace_RR]

lemma char_RR (hk : k ≠ 0) (hx : x * x = k • x) (p : Equiv.Perm (Fin n)) :
    (leftRegular p * projMat (LinearMap.range (Matrix.toEuclideanLin (RR x)))).trace =
      (k * n.factorial)⁻¹ * tau (Wx x * og p) := by
  rw [trace_mul_projMat hk (RR_sq hx) _ (lr_RR_comm p x), trace_lr_RR, Wx, Finset.sum_mul,
    tau_sum, mul_inv, mul_assoc]

end Glue2

noncomputable def isoElt (lam : Partition d n) : GA n :=
  ((Module.finrank ℂ (spechtSpace lam) : ℂ) / (n.factorial : ℂ)) •
    ∑ pi : Equiv.Perm (Fin n), MonoidAlgebra.single pi (spechtCharacter lam pi⁻¹)

lemma spechtSpace_eq (lam : Partition d n) :
    spechtSpace lam = LinearMap.range (Matrix.toEuclideanLin (RR (youngElt lam))) := by
  rw [spechtSpace, youngRightOperator_eq]

theorem finrank_specht (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ)) :
    (Module.finrank ℂ (spechtSpace lam) : ℂ) = k⁻¹ * n.factorial := by
  rw [spechtSpace_eq, finrank_RR hk hx, ht]

theorem char_specht (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam) (p : Equiv.Perm (Fin n)) :
    spechtCharacter lam p = (k * n.factorial)⁻¹ * tau (Wx (youngElt lam) * og p) := by
  rw [spechtCharacter, show spechtProjection lam = projMat (spechtSpace lam) from rfl,
    spechtSpace_eq, char_RR hk hx]

theorem isoElt_eq (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ)) :
    isoElt lam = (k * k)⁻¹ • Wx (youngElt lam) := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hre : ∑ pi : Equiv.Perm (Fin n), MonoidAlgebra.single pi (spechtCharacter lam pi⁻¹) =
      (k * n.factorial)⁻¹ • ∑ h : Equiv.Perm (Fin n), tau (Wx (youngElt lam) * og h) • og h⁻¹ := by
    rw [Finset.smul_sum]
    exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun pi => by
      rw [og_smul_single, char_specht lam hk hx, smul_smul]
      simp)
  rw [isoElt, hre, expand, finrank_specht lam hk hx ht, smul_smul, smul_smul]
  congr 1
  field_simp

lemma tp_one (d n : ℕ) : tensorPermutation d n 1 = 1 := by
  ext y x
  rfl

lemma tp_mul (d n : ℕ) (p q : Equiv.Perm (Fin n)) :
    tensorPermutation d n (p * q) = tensorPermutation d n p * tensorPermutation d n q := by
  ext y x
  simp only [tensorPermutation, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

noncomputable def Tm (d n : ℕ) :
    Equiv.Perm (Fin n) →* Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ where
  toFun := tensorPermutation d n
  map_one' := tp_one d n
  map_mul' := tp_mul d n

noncomputable def TR (d n : ℕ) : GA n →ₐ[ℂ] Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  MonoidAlgebra.lift ℂ _ _ (Tm d n)

lemma TR_single (p : Equiv.Perm (Fin n)) (c : ℂ) :
    TR d n (MonoidAlgebra.single p c) = c • tensorPermutation d n p := by
  simp [TR]
  rfl

lemma TR_youngElt (lam : Partition d n) : TR d n (youngElt lam) = tensorYoungOperator lam := by
  simp only [youngElt, tensorYoungOperator, map_sum, TR_single]

lemma TR_isoElt (lam : Partition d n) : TR d n (isoElt lam) = isotypicProjector lam := by
  simp only [isoElt, isotypicProjector, map_smul, map_sum, TR_single]

lemma tp_conjTranspose (p : Equiv.Perm (Fin n)) :
    (tensorPermutation d n p)ᴴ = tensorPermutation d n p⁻¹ := by
  ext y x
  have h : (x = y ∘ p.symm) ↔ (y = x ∘ (p⁻¹).symm) := by
    constructor
    · rintro rfl; funext i; simp [Equiv.Perm.inv_def]
    · rintro rfl; funext i; simp [Equiv.Perm.inv_def]
  simp only [tensorPermutation, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hx : x = y ∘ p.symm
  · rw [if_pos hx, if_pos (h.1 hx)]; simp
  · rw [if_neg hx, if_neg (fun h' => hx (h.2 h'))]; simp

lemma lr_conjTranspose (p : Equiv.Perm (Fin n)) : (leftRegular p)ᴴ = leftRegular p⁻¹ := by
  ext g h
  simp only [leftRegular, Matrix.conjTranspose_apply, Matrix.of_apply]
  have : (h = p * g) ↔ (g = p⁻¹ * h) := by
    constructor
    · rintro rfl; group
    · rintro rfl; group
  by_cases hx : h = p * g
  · rw [if_pos hx, if_pos (this.1 hx)]; simp
  · rw [if_neg hx, if_neg (fun h' => hx (this.2 h'))]; simp

lemma sp_conjTranspose (lam : Partition d n) : (spechtProjection lam)ᴴ = spechtProjection lam := by
  ext g h
  simp only [spechtProjection, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [← inner_conj_symm, Submodule.inner_starProjection_left_eq_right, starRingEnd_apply,
    star_star]

lemma char_star (lam : Partition d n) (p : Equiv.Perm (Fin n)) :
    star (spechtCharacter lam p) = spechtCharacter lam p⁻¹ := by
  unfold spechtCharacter
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, sp_conjTranspose,
    lr_conjTranspose, Matrix.trace_mul_comm]

lemma iso_hermitian (lam : Partition d n) : (isotypicProjector lam)ᴴ = isotypicProjector lam := by
  unfold isotypicProjector
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  have hc : star ((Module.finrank ℂ (spechtSpace lam) : ℂ) / (n.factorial : ℂ)) =
      (Module.finrank ℂ (spechtSpace lam) : ℂ) / (n.factorial : ℂ) := by
    simp [star_div₀]
  rw [hc]
  congr 1
  simp only [Matrix.conjTranspose_smul, tp_conjTranspose, char_star, inv_inv]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun p => by simp)

lemma tp_commute_piKron (p : Equiv.Perm (Fin n)) (X : Matrix (Fin d) (Fin d) ℂ) :
    Commute (tensorPermutation d n p) (piKron n X) := by
  unfold Commute SemiconjBy
  ext y x
  simp only [tensorPermutation, piKron, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul,
    zero_mul, mul_ite, mul_one, mul_zero]
  have h1 : ∀ z : Fin n → Fin d, (y = z ∘ p.symm) ↔ (z = y ∘ p) := by
    intro z; constructor
    · rintro rfl; funext i; simp
    · rintro rfl; funext i; simp
  simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Fintype.prod_equiv p _ _ (fun i => by simp)

lemma iso_commute_piKron (lam : Partition d n) (X : Matrix (Fin d) (Fin d) ℂ) :
    Commute (isotypicProjector lam) (piKron n X) := by
  unfold isotypicProjector
  refine Commute.smul_left (Commute.sum_left _ _ _ (fun p _ => ?_)) _
  exact Commute.smul_left (tp_commute_piKron p X) _


/-! ### layer top: conjuncts 3, 4, 7, 8 from the group-algebra identities -/

lemma trT_comm (a b : GA n) : (TR d n (a * b)).trace = (TR d n (b * a)).trace := by
  rw [map_mul, map_mul, Matrix.trace_mul_comm]

lemma TR_og (p : Equiv.Perm (Fin n)) : TR d n (og p) = tensorPermutation d n p := by
  rw [show og p = MonoidAlgebra.single p 1 from rfl, TR_single, one_smul]

lemma trT_young {x : GA n} {k : ℂ} (hk : k ≠ 0) (hx : x * x = k • x)
    (hcxc : ∀ y : GA n, ∃ γ : ℂ, x * y * x = γ • x)
    (ht : tau x = (n.factorial : ℂ)) (y : GA n) :
    (TR d n (y * x)).trace =
      ((Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin (TR d n x))) : ℂ) * k /
        n.factorial) * tau (y * x) := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hT : TR d n x * TR d n x = k • TR d n x := by rw [← map_mul, hx, map_smul]
  rw [finrank_range hk hT]
  obtain ⟨γ, hγ⟩ := hcxc y
  have e1 : (TR d n (y * x)).trace = k⁻¹ * (TR d n (x * y * x)).trace := by
    have h1 : (TR d n (y * x * x)).trace = k * (TR d n (y * x)).trace := by
      rw [mul_assoc, hx, mul_smul_comm, map_smul, Matrix.trace_smul, smul_eq_mul]
    rw [show x * y * x = x * (y * x) by rw [mul_assoc], trT_comm x, h1]
    field_simp
  have e2 : tau (y * x) = k⁻¹ * tau (x * y * x) := by
    have h1 : tau (y * x * x) = k * tau (y * x) := by
      rw [mul_assoc, hx, mul_smul_comm, tau_smul]
    rw [show x * y * x = x * (y * x) by rw [mul_assoc], tau_comm x, h1]
    field_simp
  rw [e1, e2, hγ, map_smul, Matrix.trace_smul, smul_eq_mul, tau_smul, ht]
  field_simp
  try ring

theorem conj8_core (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (hcxc : ∀ y : GA n, ∃ γ : ℂ, youngElt lam * y * youngElt lam = γ • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ)) (p : Equiv.Perm (Fin n)) :
    (tensorPermutation d n p * isotypicProjector lam).trace =
      (Module.finrank ℂ (schurModule lam) : ℂ) * spechtCharacter lam p := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  set c := youngElt lam with hc
  have hS : schurModule lam = LinearMap.range (Matrix.toEuclideanLin (TR d n c)) := by
    rw [schurModule, hc, TR_youngElt]
  set M := ((Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin (TR d n c))) : ℂ) * k /
        n.factorial) with hM
  have key : ∀ h : Equiv.Perm (Fin n), (TR d n (og p * (og h * c * og h⁻¹))).trace =
      M * tau (og h * c * og h⁻¹ * og p) := by
    intro h
    rw [hM]
    have a1 : (TR d n (og p * (og h * c * og h⁻¹))).trace =
        (TR d n ((og h⁻¹ * og p * og h) * c)).trace := by
      rw [show og h⁻¹ * og p * og h * c = og h⁻¹ * (og p * og h * c) by simp only [mul_assoc],
        trT_comm (og h⁻¹)]
      simp only [mul_assoc]
    rw [a1, trT_young hk hx hcxc ht,
      show og h⁻¹ * og p * og h * c = (og h⁻¹ * og p) * (og h * c) by simp only [mul_assoc],
      tau_comm]
    simp only [mul_assoc]
  have hsum : (TR d n (og p * Wx c)).trace = M * tau (Wx c * og p) := by
    rw [Wx, Finset.mul_sum, Finset.sum_mul, map_sum, Matrix.trace_sum, tau_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun h _ => key h)
  rw [← TR_isoElt, ← TR_og, ← map_mul, isoElt_eq lam hk hx ht, char_specht lam hk hx, hS,
    mul_smul_comm, map_smul, Matrix.trace_smul, smul_eq_mul, hsum, hM]
  field_simp
  try ring

theorem conj3_core (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ))
    (hW : Wx (youngElt lam) * Wx (youngElt lam) = (k * k) • Wx (youngElt lam)) :
    isotypicProjector lam * isotypicProjector lam = isotypicProjector lam := by
  rw [← TR_isoElt, ← map_mul, isoElt_eq lam hk hx ht, smul_mul_smul_comm, hW, smul_smul,
    show (k * k)⁻¹ * (k * k)⁻¹ * (k * k) = (k * k)⁻¹ by field_simp]

theorem conj4_core (lam mu : Partition d n) {k k' : ℂ} (hk : k ≠ 0) (hk' : k' ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ))
    (hx' : youngElt mu * youngElt mu = k' • youngElt mu)
    (ht' : tau (youngElt mu) = (n.factorial : ℂ))
    (hW : Wx (youngElt lam) * Wx (youngElt mu) = 0) :
    isotypicProjector lam * isotypicProjector mu = 0 := by
  rw [← TR_isoElt, ← TR_isoElt, ← map_mul, isoElt_eq lam hk hx ht, isoElt_eq mu hk' hx' ht',
    smul_mul_smul_comm, hW, smul_zero, map_zero]

theorem conj7_core (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ))
    (hW : ∀ y : GA n, y * Wx (youngElt lam) = Wx (youngElt lam) * y)
    (p : Equiv.Perm (Fin n)) :
    Commute (isotypicProjector lam) (tensorPermutation d n p) := by
  rw [← TR_isoElt, ← TR_og, isoElt_eq lam hk hx ht]
  show TR d n _ * TR d n _ = TR d n _ * TR d n _
  rw [← map_mul, ← map_mul, smul_mul_assoc, mul_smul_comm, hW]

/-! ### conj 1: the isotypic projector is nonzero (relay 5) -/

lemma hw_val (lam : Partition d n) (j : Fin n) :
    (highestWeightWord lam j).val = ((cellNumbering lam).symm j).val.1 := rfl

lemma mem_rowP {lam : Partition d n} {a : Equiv.Perm (Fin n)} (ha : a ∈ rowPermutations lam)
    (i : Fin n) :
    ((cellNumbering lam).symm (a i)).val.1 = ((cellNumbering lam).symm i).val.1 := by
  unfold rowPermutations at ha
  exact (Finset.mem_filter.mp ha).2 i

lemma mem_colP {lam : Partition d n} {b : Equiv.Perm (Fin n)} (hb : b ∈ columnPermutations lam)
    (i : Fin n) :
    ((cellNumbering lam).symm (b i)).val.2 = ((cellNumbering lam).symm i).val.2 := by
  unfold columnPermutations at hb
  exact (Finset.mem_filter.mp hb).2 i

lemma one_mem_rowP (lam : Partition d n) : (1 : Equiv.Perm (Fin n)) ∈ rowPermutations lam := by
  unfold rowPermutations
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ => rfl⟩

lemma one_mem_colP (lam : Partition d n) : (1 : Equiv.Perm (Fin n)) ∈ columnPermutations lam := by
  unfold columnPermutations
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ => rfl⟩

lemma cell_eq' {lam : Partition d n} {i j : Fin n}
    (h1 : ((cellNumbering lam).symm i).val.1 = ((cellNumbering lam).symm j).val.1)
    (h2 : ((cellNumbering lam).symm i).val.2 = ((cellNumbering lam).symm j).val.2) : i = j := by
  have : (cellNumbering lam).symm i = (cellNumbering lam).symm j := Subtype.ext (Prod.ext h1 h2)
  exact (cellNumbering lam).symm.injective this

lemma hw_fix_iff (lam : Partition d n) {a b : Equiv.Perm (Fin n)} (ha : a ∈ rowPermutations lam)
    (hb : b ∈ columnPermutations lam) :
    (highestWeightWord lam = highestWeightWord lam ∘ (a * b).symm) ↔ b = 1 := by
  constructor
  · intro h
    have hrow : ∀ j, ((cellNumbering lam).symm (b⁻¹ j)).val.1 =
        ((cellNumbering lam).symm j).val.1 := by
      intro j
      have h' := congrArg (fun f => (f (a j)).val) h
      simp only [Function.comp_apply, hw_val] at h'
      have e : (a * b).symm (a j) = b⁻¹ j := by
        show (a * b)⁻¹ (a j) = b⁻¹ j
        rw [mul_inv_rev, Equiv.Perm.mul_apply]
        exact congrArg (fun x => b⁻¹ x) (a.symm_apply_apply j)
      rw [e, mem_rowP ha] at h'
      exact h'.symm
    have hc : ∀ j, ((cellNumbering lam).symm (b⁻¹ j)).val.2 =
        ((cellNumbering lam).symm j).val.2 := by
      intro j
      have := mem_colP hb (b⁻¹ j)
      have e2 : b (b⁻¹ j) = j := b.apply_symm_apply j
      rw [e2] at this
      exact this.symm
    have hb1 : b⁻¹ = 1 := by
      ext j
      rw [cell_eq' (hrow j) (hc j)]
      rfl
    exact inv_eq_one.mp hb1
  · rintro rfl
    funext i
    apply Fin.ext
    simp only [Function.comp_apply, hw_val]
    have e : (a * 1).symm i = a⁻¹ i := by rw [mul_one]; rfl
    rw [e]
    have := mem_rowP ha (a⁻¹ i)
    have e2 : a (a⁻¹ i) = i := a.apply_symm_apply i
    rw [e2] at this
    exact this

lemma tyo_hw (lam : Partition d n) :
    tensorYoungOperator lam (highestWeightWord lam) (highestWeightWord lam) =
      ((rowPermutations lam).card : ℂ) := by
  unfold tensorYoungOperator
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.sum_eq_single_of_mem 1 (one_mem_colP lam)]
  · rw [show tensorPermutation d n (a * 1) (highestWeightWord lam) (highestWeightWord lam) = 1 from by
      simp only [tensorPermutation, Matrix.of_apply]
      exact if_pos ((hw_fix_iff lam ha (one_mem_colP lam)).mpr rfl)]
    simp
  · intro b hb hb1
    rw [show tensorPermutation d n (a * b) (highestWeightWord lam) (highestWeightWord lam) = 0 from by
      simp only [tensorPermutation, Matrix.of_apply]
      exact if_neg (fun h => hb1 ((hw_fix_iff lam ha hb).mp h))]
    simp

lemma tyo_ne_zero (lam : Partition d n) : tensorYoungOperator lam ≠ 0 := by
  intro h
  have := tyo_hw lam
  rw [h, Matrix.zero_apply] at this
  exact (Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem (one_mem_rowP lam))) this.symm

lemma finrank_schur_ne_zero (lam : Partition d n) : Module.finrank ℂ (schurModule lam) ≠ 0 := by
  intro h
  rw [Submodule.finrank_eq_zero] at h
  unfold schurModule at h
  rw [LinearMap.range_eq_bot] at h
  exact tyo_ne_zero lam ((LinearEquiv.map_eq_zero_iff Matrix.toEuclideanLin).mp h)

lemma tau_Wx (x : GA n) : tau (Wx x) = (n.factorial : ℂ) * tau x := by
  unfold Wx
  rw [tau_sum]
  have : ∀ h : Equiv.Perm (Fin n), tau (og h * x * og h⁻¹) = tau x := by
    intro h
    rw [tau_comm, ← mul_assoc, og_inv_mul, one_mul]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

theorem conj1_core (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (hcxc : ∀ y : GA n, ∃ γ : ℂ, youngElt lam * y * youngElt lam = γ • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ)) :
    isotypicProjector lam ≠ 0 := by
  intro h
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h8 := conj8_core lam hk hx hcxc ht 1
  rw [h, mul_zero, Matrix.trace_zero, char_specht lam hk hx, og_one, mul_one, tau_Wx, ht] at h8
  have hm := Nat.cast_ne_zero (R := ℂ) |>.mpr (finrank_schur_ne_zero lam)
  exact (mul_ne_zero hm (mul_ne_zero (inv_ne_zero (mul_ne_zero hk hf)) (mul_ne_zero hf hf))) h8.symm

end KWS29P


set_option autoImplicit false
open QAlgorithms QAlgorithms.Schur
open scoped Matrix

noncomputable section

namespace KeylW
open KWS29

variable {d n : ℕ}

/-- the highest weight word -/
abbrev hw (lam : Partition d n) : Fin n → Fin d := highestWeightWord lam

lemma hw_val (lam : Partition d n) (k : Fin n) : (hw lam k).val = rowOf lam k := rfl

/-- generic principal minor -/
def pmin (Z : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) : ℂ :=
  if hm : m ≤ d then (Z.submatrix (fun i : Fin m => (⟨i.val, by omega⟩ : Fin d))
    (fun i : Fin m => (⟨i.val, by omega⟩ : Fin d))).det else 1

lemma colLen_le (lam : Partition d n) (j : ℕ) : lam.val.colLen j ≤ d :=
  (lam.val.colLen_anti 0 j (Nat.zero_le j)).trans lam.property.2

lemma genPower_eq (lam : Partition d n) (Z : Matrix (Fin d) (Fin d) ℂ) :
    Tomography.keylGeneralizedPower lam Z =
      ∏ k ∈ Finset.range d, pmin Z (k+1) ^ (lam.val.rowLen k - lam.val.rowLen (k+1)) := by
  unfold Tomography.keylGeneralizedPower
  rw [Finset.prod_range (fun k => pmin Z (k+1) ^ (lam.val.rowLen k - lam.val.rowLen (k+1)))]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  unfold pmin
  rw [dif_pos (by omega)]

/-- grouping columns by their length -/
lemma prod_cols (lam : Partition d n) {M : Type*} [CommMonoid M] (g : ℕ → M) :
    ∏ j ∈ Finset.range (lam.val.rowLen 0), g (lam.val.colLen j) =
      ∏ k ∈ Finset.range d, g (k+1) ^ (lam.val.rowLen k - lam.val.rowLen (k+1)) := by
  have hmaps : ∀ j ∈ Finset.range (lam.val.rowLen 0), lam.val.colLen j - 1 ∈ Finset.range d := by
    intro j hj
    have := colLen_le lam j
    have h1 : 0 < lam.val.colLen j := by
      rw [Finset.mem_range] at hj
      have : (0, j) ∈ lam.val := YoungDiagram.mem_iff_lt_rowLen.2 hj
      exact YoungDiagram.mem_iff_lt_colLen.1 this
    rw [Finset.mem_range]; omega
  rw [← Finset.prod_fiberwise_of_maps_to hmaps]
  refine Finset.prod_congr rfl (fun k hk => ?_)
  have hfil : (Finset.range (lam.val.rowLen 0)).filter (fun j => lam.val.colLen j - 1 = k) =
      Finset.Ico (lam.val.rowLen (k+1)) (lam.val.rowLen k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    have e1 : k < lam.val.colLen j ↔ j < lam.val.rowLen k := by
      rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
    have e2 : k + 1 < lam.val.colLen j ↔ j < lam.val.rowLen (k+1) := by
      rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
    have e3 : lam.val.rowLen k ≤ lam.val.rowLen 0 := lam.val.rowLen_anti 0 k (Nat.zero_le k)
    constructor
    · rintro ⟨h1, h2⟩
      have h0 : 0 < lam.val.colLen j := by
        have : (0, j) ∈ lam.val := YoungDiagram.mem_iff_lt_rowLen.2 h1
        exact YoungDiagram.mem_iff_lt_colLen.1 this
      constructor
      · by_contra hc; push_neg at hc
        have := e2.2 hc; omega
      · exact e1.1 (by omega)
    · rintro ⟨h1, h2⟩
      have := e1.2 h2
      have h3 : ¬ (k + 1 < lam.val.colLen j) := fun h => absurd (e2.1 h) (by omega)
      exact ⟨by omega, by omega⟩
  rw [Finset.prod_congr rfl (fun j hj => by
      rw [show lam.val.colLen j = k + 1 by
        have := (Finset.mem_filter.1 hj).2
        have h0 : 0 < lam.val.colLen j := by
          have hj' := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
          have : (0, j) ∈ lam.val := YoungDiagram.mem_iff_lt_rowLen.2 hj'
          exact YoungDiagram.mem_iff_lt_colLen.1 this
        omega]),
    Finset.prod_const, hfil, Nat.card_Ico]

/-- the block matrix -/
def blkM (lam : Partition d n) (Z : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if colOf lam i = colOf lam j then Z (hw lam i) (hw lam j) else 0

lemma det_blkM (lam : Partition d n) (Z : Matrix (Fin d) (Fin d) ℂ) :
    (blkM lam Z).det = ∑ σ ∈ columnPermutations lam,
      sgn σ * ∏ i, Z (hw lam (σ i)) (hw lam i) := by
  rw [Matrix.det_apply']
  rw [← Finset.sum_subset (Finset.subset_univ (columnPermutations lam))]
  · refine Finset.sum_congr rfl (fun σ hσ => ?_)
    rw [mem_C] at hσ
    unfold sgn
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    show (if colOf lam (σ i) = colOf lam i then Z (hw lam (σ i)) (hw lam i) else 0) = _
    rw [if_pos (hσ i)]
  · intro σ _ hσ
    rw [mem_C] at hσ
    push_neg at hσ
    obtain ⟨i, hi⟩ := hσ
    apply mul_eq_zero_of_right
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    show (if colOf lam (σ i) = colOf lam i then Z (hw lam (σ i)) (hw lam i) else 0) = 0
    rw [if_neg hi]

lemma colOf_lt (lam : Partition d n) (k : Fin n) : colOf lam k < lam.val.rowLen 0 := by
  have h := mem_cells lam k
  have := YoungDiagram.mem_iff_lt_rowLen.1 h
  exact lt_of_lt_of_le this (lam.val.rowLen_anti 0 _ (Nat.zero_le _))

lemma rowOf_lt (lam : Partition d n) (k : Fin n) : rowOf lam k < lam.val.colLen (colOf lam k) :=
  YoungDiagram.mem_iff_lt_colLen.1 (mem_cells lam k)

/-- the cells of column `a`, enumerated by row -/
def colFib (lam : Partition d n) (a : ℕ) (ha : a < lam.val.rowLen 0) :
    Fin (lam.val.colLen a) ≃ {k : Fin n // colOf lam k = a} where
  toFun i := ⟨cellNumbering lam ⟨(i.val, a), YoungDiagram.mem_iff_lt_colLen.2 i.isLt⟩,
    by simp [colOf]⟩
  invFun k := ⟨rowOf lam k.1, by have := rowOf_lt lam k.1; rw [k.2] at this; exact this⟩
  left_inv i := by
    apply Fin.ext
    simp [rowOf]
  right_inv k := by
    apply Subtype.ext
    apply (cellNumbering lam).symm.injective
    apply Subtype.ext
    show ((cellNumbering lam).symm (cellNumbering lam ⟨(rowOf lam k.1, a), _⟩)).val = _
    rw [Equiv.symm_apply_apply, cell_eq, k.2]

lemma blkM_tri (lam : Partition d n) (Z : Matrix (Fin d) (Fin d) ℂ) :
    (blkM lam Z).BlockTriangular (colOf lam) := by
  intro i j hij
  show (if colOf lam i = colOf lam j then Z (hw lam i) (hw lam j) else 0) = 0
  rw [if_neg (by omega)]

lemma image_colOf (lam : Partition d n) :
    Finset.univ.image (colOf lam) = Finset.range (lam.val.rowLen 0) := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨k, rfl⟩; exact colOf_lt lam k
  · intro ha
    have hm : (0, a) ∈ lam.val := YoungDiagram.mem_iff_lt_rowLen.2 ha
    exact ⟨cellNumbering lam ⟨(0, a), hm⟩, by simp [colOf]⟩

lemma det_block (lam : Partition d n) (Z : Matrix (Fin d) (Fin d) ℂ) (a : ℕ)
    (ha : a < lam.val.rowLen 0) :
    ((blkM lam Z).toSquareBlock (colOf lam) a).det = pmin Z (lam.val.colLen a) := by
  rw [← Matrix.det_submatrix_equiv_self (colFib lam a ha)]
  unfold pmin
  rw [dif_pos (colLen_le lam a)]
  congr 1
  ext i i'
  simp only [Matrix.submatrix_apply, Matrix.toSquareBlock, Matrix.toSquareBlockProp,
    Matrix.toBlock_apply]
  show (if colOf lam ((colFib lam a ha) i).1 = colOf lam ((colFib lam a ha) i').1 then
    Z (hw lam ((colFib lam a ha) i).1) (hw lam ((colFib lam a ha) i').1) else 0) = _
  rw [if_pos (((colFib lam a ha) i).2.trans ((colFib lam a ha) i').2.symm)]
  congr 1
  · apply Fin.ext; show rowOf lam _ = _; simp [colFib, rowOf]
  · apply Fin.ext; show rowOf lam _ = _; simp [colFib, rowOf]

lemma det_blkM_eq (lam : Partition d n) (Z : Matrix (Fin d) (Fin d) ℂ) :
    (blkM lam Z).det = Tomography.keylGeneralizedPower lam Z := by
  rw [(blkM_tri lam Z).det, image_colOf, genPower_eq, ← prod_cols lam (pmin Z)]
  refine Finset.prod_congr rfl (fun a ha => ?_)
  exact det_block lam Z a (Finset.mem_range.1 ha)

/-- the wedge vector: column antisymmetrization of the highest weight word -/
def wv (lam : Partition d n) : (Fin n → Fin d) → ℂ :=
  fun y => ∑ b ∈ columnPermutations lam, sgn b * (if y = hw lam ∘ ⇑b.symm then 1 else 0)

lemma sgn_inv (b : Equiv.Perm (Fin n)) : sgn b⁻¹ = sgn b := by
  simp [sgn]

lemma star_sgn (b : Equiv.Perm (Fin n)) : star (sgn b) = sgn b := by
  unfold sgn
  rcases Int.units_eq_one_or (Equiv.Perm.sign b) with h | h <;> rw [h] <;> simp

lemma sum_C_shift (lam : Partition d n) (b : Equiv.Perm (Fin n)) (hb : b ∈ columnPermutations lam)
    (G : Equiv.Perm (Fin n) → ℂ) :
    ∑ b' ∈ columnPermutations lam, sgn b * sgn b' * G (b'⁻¹ * b) =
      ∑ c ∈ columnPermutations lam, sgn c * G c := by
  refine Finset.sum_nbij' (fun b' => b'⁻¹ * b) (fun c => b * c⁻¹)
    (fun b' hb' => C_mul (C_inv hb') hb) (fun c hc => C_mul hb (C_inv hc))
    (fun b' _ => by simp [mul_assoc]) (fun c _ => by simp [mul_assoc]) (fun b' _ => ?_)
  rw [sgn_mul, sgn_inv]; ring

lemma sum_ite_mul {α β : Type} [Fintype α] [DecidableEq α] (S : Finset β) (u : β → α)
    (c : β → ℂ) (F : α → ℂ) :
    ∑ y, (∑ b ∈ S, if y = u b then c b else 0) * F y = ∑ b ∈ S, c b * F (u b) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]

lemma mul_sum_ite {α β : Type} [Fintype α] [DecidableEq α] (S : Finset β) (u : β → α)
    (c : β → ℂ) (F : α → ℂ) :
    ∑ x, F x * (∑ b ∈ S, if x = u b then c b else 0) = ∑ b ∈ S, F (u b) * c b := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]

lemma wv_eq (lam : Partition d n) (y : Fin n → Fin d) :
    wv lam y = ∑ b ∈ columnPermutations lam, if y = hw lam ∘ ⇑b.symm then sgn b else 0 := by
  unfold wv
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs <;> simp

lemma star_wv (lam : Partition d n) (y : Fin n → Fin d) :
    star (wv lam y) = ∑ b ∈ columnPermutations lam, if y = hw lam ∘ ⇑b.symm then sgn b else 0 := by
  rw [wv_eq, star_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs <;> simp [star_sgn]

/-- the column-group function -/
def Gf (lam : Partition d n) (Z : Matrix (Fin d) (Fin d) ℂ) (c : Equiv.Perm (Fin n)) : ℂ :=
  ∏ k, Z (hw lam k) (hw lam (c k))

lemma quad_wv (lam : Partition d n) (Z : Matrix (Fin d) (Fin d) ℂ) :
    ∑ y, ∑ x, star (wv lam y) * piKron n Z y x * wv lam x =
      ((columnPermutations lam).card : ℂ) * Tomography.keylGeneralizedPower lam Z := by
  have h1 : ∑ y, ∑ x, star (wv lam y) * piKron n Z y x * wv lam x =
      ∑ b ∈ columnPermutations lam, ∑ b' ∈ columnPermutations lam, sgn b * sgn b' *
        piKron n Z (hw lam ∘ ⇑b.symm) (hw lam ∘ ⇑b'.symm) := by
    have : ∀ y, ∑ x, star (wv lam y) * piKron n Z y x * wv lam x =
        star (wv lam y) * ∑ x, piKron n Z y x * wv lam x := by
      intro y; rw [Finset.mul_sum]; simp only [mul_assoc]
    simp_rw [this, star_wv]
    rw [sum_ite_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp_rw [wv_eq]
    rw [mul_sum_ite, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    ring
  have h2 : ∀ b b' : Equiv.Perm (Fin n), piKron n Z (hw lam ∘ ⇑b.symm) (hw lam ∘ ⇑b'.symm) =
      Gf lam Z (b'⁻¹ * b) := by
    intro b b'
    simp only [piKron, Matrix.of_apply, Function.comp_apply, Gf]
    rw [← Equiv.prod_comp b]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  rw [h1]
  have h3 : ∀ b ∈ columnPermutations lam, ∑ b' ∈ columnPermutations lam, sgn b * sgn b' *
      piKron n Z (hw lam ∘ ⇑b.symm) (hw lam ∘ ⇑b'.symm) =
        ∑ c ∈ columnPermutations lam, sgn c * Gf lam Z c := by
    intro b hb
    rw [← sum_C_shift lam b hb (Gf lam Z)]
    refine Finset.sum_congr rfl (fun b' _ => by rw [h2])
  rw [Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul, ← det_blkM_eq, det_blkM]
  congr 1
  refine Finset.sum_nbij' (fun c => c⁻¹) (fun σ => σ⁻¹) (fun c hc => C_inv hc)
    (fun σ hσ => C_inv hσ) (fun c _ => by simp) (fun σ _ => by simp) (fun c _ => ?_)
  rw [sgn_inv]
  congr 1
  unfold Gf
  rw [← Equiv.prod_comp c⁻¹]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  simp

end KeylW


set_option autoImplicit false
open QAlgorithms QAlgorithms.Schur
open scoped Matrix

noncomputable section

namespace KeylW

variable {d n : ℕ}

lemma incl_excl (T : Finset (Fin n)) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => T ⊆ S),
      (-1 : ℂ) ^ (n - S.card) = if T = Finset.univ then 1 else 0 := by
  have h1 : ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => T ⊆ S),
      (-1 : ℂ) ^ (n - S.card) = ∑ W ∈ (Finset.univ \ T).powerset, (-1 : ℂ) ^ W.card := by
    refine Finset.sum_nbij' (fun S => Finset.univ \ S) (fun W => Finset.univ \ W) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      simp only [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff (le_refl _) hS.2
    · intro W hW
      simp only [Finset.mem_powerset] at hW
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      intro t ht
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro htW
      have := hW htW
      simp at this
      exact this ht
    · intro S _; simp
    · intro W _; simp
    · intro S _
      congr 1
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
  rw [h1]
  have h2 := Finset.sum_powerset_neg_one_pow_card (x := (Finset.univ \ T : Finset (Fin n)))
  have h3 : ∑ W ∈ (Finset.univ \ T).powerset, (-1 : ℂ) ^ W.card =
      ((∑ W ∈ (Finset.univ \ T).powerset, (-1 : ℤ) ^ W.card : ℤ) : ℂ) := by push_cast; rfl
  rw [h3, h2]
  have h4 : (Finset.univ \ T = ∅) ↔ T = Finset.univ := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun h => Finset.eq_univ_of_forall (fun x => h (Finset.mem_univ x)),
      fun h => h ▸ le_refl _⟩
  by_cases hT : T = Finset.univ
  · rw [if_pos (h4.2 hT), if_pos hT]; simp
  · rw [if_neg (fun h => hT (h4.1 h)), if_neg hT]; simp

/-- Ryser's inclusion–exclusion formula for the permanent -/
lemma ryser (a : Fin n → Fin n → ℂ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, (-1 : ℂ) ^ (n - S.card) * ∏ j, ∑ k ∈ S, a j k =
      ∑ σ : Equiv.Perm (Fin n), ∏ j, a j (σ j) := by
  simp_rw [Finset.prod_univ_sum, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ)
    (s' := fun f => (Finset.univ : Finset (Fin n)).powerset.filter (fun S => Finset.univ.image f ⊆ S))]
  · have : ∀ f : Fin n → Fin n,
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => Finset.univ.image f ⊆ S),
          (-1 : ℂ) ^ (n - S.card) * ∏ j, a j (f j) =
        if Function.Surjective f then ∏ j, a j (f j) else 0 := by
      intro f
      rw [← Finset.sum_mul, incl_excl]
      have : Finset.univ.image f = Finset.univ ↔ Function.Surjective f := by
        constructor
        · intro h y
          have : y ∈ Finset.univ.image f := by rw [h]; exact Finset.mem_univ y
          simpa using this
        · intro h
          exact Finset.eq_univ_of_forall (fun y => by
            obtain ⟨x, rfl⟩ := h y; exact Finset.mem_image_of_mem f (Finset.mem_univ x))
      by_cases hs : Function.Surjective f
      · rw [if_pos (this.2 hs), if_pos hs, one_mul]
      · rw [if_neg (fun h => hs (this.1 h)), if_neg hs, zero_mul]
    simp_rw [this]
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_nbij' (fun σ => ⇑σ)
      (fun f => if h : Function.Surjective f then
        Equiv.ofBijective f (Finite.surjective_iff_bijective.mp h) else 1) ?_ ?_ ?_ ?_ ?_
    · intro σ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact σ.surjective
    · intro f _; exact Finset.mem_univ _
    · intro σ _
      show (if h : _ then _ else _) = _
      rw [dif_pos σ.surjective]
      ext x; rfl
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      simp only [dif_pos hf]
      rfl
    · intro σ _; rfl
  · intro S f
    simp [Fintype.mem_piFinset, Finset.image_subset_iff]

abbrev Idx (d n : ℕ) := Fin n → Fin d

/-- the span of tensor powers -/
def powSpan (d n : ℕ) : Submodule ℂ (Matrix (Idx d n) (Idx d n) ℂ) :=
  Submodule.span ℂ (Set.range (fun X : Matrix (Fin d) (Fin d) ℂ => piKron n X))

lemma sym_mem (x y : Idx d n) :
    ∑ π : Equiv.Perm (Fin n), Matrix.single (x ∘ ⇑π) (y ∘ ⇑π) (1 : ℂ) ∈ powSpan d n := by
  have heq : ∑ π : Equiv.Perm (Fin n), Matrix.single (x ∘ ⇑π) (y ∘ ⇑π) (1 : ℂ) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, (-1 : ℂ) ^ (n - S.card) •
        piKron n (∑ k ∈ S, Matrix.single (x k) (y k) (1 : ℂ)) := by
    ext u v
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, piKron, Matrix.of_apply,
      Matrix.single_apply]
    have := ryser (fun j k => if x k = u j ∧ y k = v j then (1 : ℂ) else 0)
    rw [this]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.prod_boole]
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2⟩ j _
      exact ⟨congrFun h1 j, congrFun h2 j⟩
    · intro h
      exact ⟨funext (fun j => (h j (Finset.mem_univ j)).1), funext (fun j => (h j (Finset.mem_univ j)).2)⟩
  rw [heq]
  refine Submodule.sum_mem _ (fun S _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨_, rfl⟩

lemma tp_apply' (π : Equiv.Perm (Fin n)) (u v : Idx d n) :
    tensorPermutation d n π u v = if u = v ∘ ⇑π.symm then 1 else 0 := rfl

lemma comp_symm_iff (π : Equiv.Perm (Fin n)) (u w : Idx d n) :
    u = w ∘ ⇑π.symm ↔ w = u ∘ ⇑π := by
  constructor
  · rintro rfl; funext k; simp
  · rintro rfl; funext k; simp

lemma eq_comp_iff (π : Equiv.Perm (Fin n)) (v x : Idx d n) :
    v = x ∘ ⇑π ↔ x = v ∘ ⇑π.symm := by
  constructor
  · rintro rfl; funext k; simp
  · rintro rfl; funext k; simp

lemma comp_iff (π : Equiv.Perm (Fin n)) (u x : Idx d n) :
    x ∘ ⇑π = u ↔ x = u ∘ ⇑π.symm := by
  constructor
  · rintro rfl; funext k; simp
  · rintro rfl; funext k; simp

/-- polarization: permutation-invariant operators are combinations of tensor powers -/
theorem inv_mem (G : Matrix (Idx d n) (Idx d n) ℂ)
    (hG : ∀ π : Equiv.Perm (Fin n), tensorPermutation d n π * G = G * tensorPermutation d n π) :
    G ∈ powSpan d n := by
  have hinv0 : ∀ (π : Equiv.Perm (Fin n)) (u v : Idx d n), G (u ∘ ⇑π) v = G u (v ∘ ⇑π.symm) := by
    intro π u v
    have h := congrFun (congrFun (hG π) u) v
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (u ∘ ⇑π),
      Finset.sum_eq_single (v ∘ ⇑π.symm)] at h
    · rw [tp_apply', tp_apply', if_pos (by funext k; simp), if_pos rfl, one_mul, mul_one] at h
      exact h
    · intro b _ hb
      rw [tp_apply', if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      rw [tp_apply', if_neg (fun h => hb (by rw [h]; funext k; simp)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hinv : ∀ (π : Equiv.Perm (Fin n)) (u v : Idx d n), G (u ∘ ⇑π) (v ∘ ⇑π) = G u v := by
    intro π u v
    rw [hinv0]
    congr 1; funext k; simp
  have hπ : ∀ (π : Equiv.Perm (Fin n)) (u v : Idx d n), ∑ x : Idx d n, ∑ y : Idx d n,
      G x y * (if x ∘ ⇑π = u ∧ y ∘ ⇑π = v then 1 else 0) = G u v := by
    intro π u v
    rw [Finset.sum_eq_single (u ∘ ⇑π.symm)]
    · rw [Finset.sum_eq_single (v ∘ ⇑π.symm)]
      · rw [if_pos ⟨by funext k; simp, by funext k; simp⟩, mul_one]
        exact hinv π.symm u v
      · intro b _ hb
        rw [if_neg (fun h => hb ((comp_iff π v b).1 h.2)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      refine Finset.sum_eq_zero (fun y _ => ?_)
      rw [if_neg (fun h => hb ((comp_iff π u b).1 h.1)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hfac : (Nat.factorial n : ℂ) • G = ∑ x : Idx d n, ∑ y : Idx d n, G x y •
      ∑ π : Equiv.Perm (Fin n), Matrix.single (x ∘ ⇑π) (y ∘ ⇑π) (1 : ℂ) := by
    ext u v
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm), Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun π _ => hπ π u v), Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hn : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hG' : G = (Nat.factorial n : ℂ)⁻¹ • ((Nat.factorial n : ℂ) • G) := by
    rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [hG', hfac]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun x _ => Submodule.sum_mem _ (fun y _ =>
    Submodule.smul_mem _ _ (sym_mem x y))))

lemma comm_of_mem {T M : Matrix (Idx d n) (Idx d n) ℂ}
    (hT : ∀ X : Matrix (Fin d) (Fin d) ℂ, T * piKron n X = piKron n X * T) (hM : M ∈ powSpan d n) :
    T * M = M * T := by
  induction hM using Submodule.span_induction with
  | mem x hx => obtain ⟨X, rfl⟩ := hx; exact hT X
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, hx, hy]
  | smul c x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul, hx]

/-- the group algebra acting on tensor space -/
def actHom (d n : ℕ) : KWS29P.GA n →+* Module.End ℂ (Idx d n → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Idx d n) (Idx d n) ℂ ≃ₐ[ℂ] _).toRingEquiv.toRingHom.comp
    (KWS29P.TR d n).toRingHom

lemma actHom_apply (r : KWS29P.GA n) (v : Idx d n → ℂ) :
    actHom d n r v = (KWS29P.TR d n r) *ᵥ v := rfl

instance neZero_perm : NeZero (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
  ⟨by rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)⟩

/-- commutant theorem: an operator commuting with all tensor powers is a combination of
permutations -/
theorem commutant (T : Matrix (Idx d n) (Idx d n) ℂ)
    (hT : ∀ X : Matrix (Fin d) (Fin d) ℂ, T * piKron n X = piKron n X * T) :
    ∃ q : KWS29P.GA n, T = KWS29P.TR d n q := by
  letI : Module (KWS29P.GA n) (Idx d n → ℂ) := Module.compHom _ (actHom d n)
  have hsmul : ∀ (r : KWS29P.GA n) (v : Idx d n → ℂ), r • v = (KWS29P.TR d n r) *ᵥ v :=
    fun r v => rfl
  haveI : IsSemisimpleModule (KWS29P.GA n) (Idx d n → ℂ) := inferInstance
  -- scalar endomorphisms
  let cEnd : ℂ → Module.End (KWS29P.GA n) (Idx d n → ℂ) := fun c =>
    { toFun := fun w => c • w
      map_add' := fun a b => smul_add c a b
      map_smul' := fun r w => by
        simp only [RingHom.id_apply, hsmul, Matrix.mulVec_smul] }
  haveI : Module.Finite (Module.End (KWS29P.GA n) (Idx d n → ℂ)) (Idx d n → ℂ) := by
    refine ⟨⟨Finset.univ.image (fun x : Idx d n => (Pi.single x 1 : Idx d n → ℂ)), ?_⟩⟩
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ x : Idx d n, (cEnd (v x)) • (Pi.single x 1 : Idx d n → ℂ) := by
      ext y
      simp [cEnd, Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ (fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    simp
  -- every group-algebra-linear map commutes with T
  have hcomm : ∀ (g : Module.End (KWS29P.GA n) (Idx d n → ℂ)) (v : Idx d n → ℂ),
      T *ᵥ g v = g (T *ᵥ v) := by
    intro g v
    have hgc : ∀ (c : ℂ) (w : Idx d n → ℂ), g (c • w) = c • g w := by
      intro c w
      have h1 : c • w = (MonoidAlgebra.single (1 : Equiv.Perm (Fin n)) c) • w := by
        rw [hsmul, KWS29P.TR_single, KWS29P.tp_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      have h2 : c • g w = (MonoidAlgebra.single (1 : Equiv.Perm (Fin n)) c) • g w := by
        rw [hsmul, KWS29P.TR_single, KWS29P.tp_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [h1, map_smul, ← h2]
    let gl : (Idx d n → ℂ) →ₗ[ℂ] (Idx d n → ℂ) :=
      { toFun := g, map_add' := g.map_add, map_smul' := hgc }
    set Gm := LinearMap.toMatrix' gl with hGm
    have hGv : ∀ w, g w = Gm *ᵥ w := by
      intro w
      rw [hGm, LinearMap.toMatrix'_mulVec]; rfl
    have hGp : ∀ π : Equiv.Perm (Fin n), tensorPermutation d n π * Gm = Gm * tensorPermutation d n π := by
      intro π
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro w
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      rw [← hGv, ← hGv]
      have := g.map_smul (MonoidAlgebra.single π (1 : ℂ)) w
      rw [hsmul, hsmul, KWS29P.TR_single, one_smul] at this
      exact this.symm
    have hmem := inv_mem Gm hGp
    have hTG := comm_of_mem hT hmem
    rw [hGv, hGv, Matrix.mulVec_mulVec, hTG, ← Matrix.mulVec_mulVec]
  let f : Module.End (Module.End (KWS29P.GA n) (Idx d n → ℂ)) (Idx d n → ℂ) :=
    { toFun := fun v => T *ᵥ v
      map_add' := fun a b => Matrix.mulVec_add T a b
      map_smul' := fun g v => hcomm g v }
  obtain ⟨r, hr⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective f
  refine ⟨r, ?_⟩
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  have := congrArg (fun F => F v) hr
  simp only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply] at this
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← hsmul]
  exact this.symm

end KeylW


set_option autoImplicit false
open QAlgorithms QAlgorithms.Schur
open scoped Matrix ComplexOrder

noncomputable section

namespace KeylW

variable {d n : ℕ}

lemma eval_aeval_poly {σ : Type*} (f : σ → Polynomial ℂ) (t : ℂ) (p : MvPolynomial σ ℂ) :
    Polynomial.eval t (MvPolynomial.aeval f p) =
      MvPolynomial.eval (fun i => Polynomial.eval t (f i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- polynomials vanishing on Hermitian matrices vanish -/
lemma herm_dense (p : MvPolynomial (Fin d × Fin d) ℂ)
    (hp : ∀ H : Matrix (Fin d) (Fin d) ℂ, H.IsHermitian →
      MvPolynomial.eval (fun ij => H ij.1 ij.2) p = 0) : p = 0 := by
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  set Z : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => x (i, j) with hZ
  set A : Matrix (Fin d) (Fin d) ℂ := (1/2 : ℂ) • (Z + Zᴴ) with hA
  set B : Matrix (Fin d) (Fin d) ℂ := (-Complex.I / 2) • (Z - Zᴴ) with hB
  have hAH : Aᴴ = A := by
    rw [hA, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    rw [add_comm]; congr 1; simp
  have hBH : Bᴴ = B := by
    rw [hB, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    have : star (-Complex.I / 2) = -(-Complex.I / 2) := by
      simp [Complex.conj_I]; ring
    rw [this, neg_smul, ← smul_neg, neg_sub]
  clear_value A B
  set g : Polynomial ℂ := MvPolynomial.aeval
    (fun ij : Fin d × Fin d => Polynomial.C (A ij.1 ij.2) + Polynomial.C (B ij.1 ij.2) * Polynomial.X) p
    with hg
  have hgt : ∀ t : ℂ, Polynomial.eval t g =
      MvPolynomial.eval (fun ij => A ij.1 ij.2 + t * B ij.1 ij.2) p := by
    intro t
    rw [hg, eval_aeval_poly]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    simp_rw [mul_comm _ t]
  have hreal : ∀ r : ℝ, Polynomial.eval (r : ℂ) g = 0 := by
    intro r
    rw [hgt]
    have := hp (A + (r : ℂ) • B) (by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hAH, hBH]
      simp)
    simpa using this
  have hg0 : g = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.range (fun r : ℝ => (r : ℂ)))
    · rintro _ ⟨r, rfl⟩
      exact hreal r
    · exact Set.infinite_range_of_injective Complex.ofReal_injective
  have hx : (fun ij : Fin d × Fin d => A ij.1 ij.2 + Complex.I * B ij.1 ij.2) = x := by
    funext ij
    simp only [hA, hB, hZ, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply,
      Matrix.conjTranspose_apply, smul_eq_mul]
    have hI : Complex.I * (-Complex.I / 2) = 1/2 := by
      rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; ring
    rw [← mul_assoc, hI]
    ring
  have := hgt Complex.I
  rw [hg0, Polynomial.eval_zero, hx] at this
  exact this.symm

/-- commutator with a tensor power -/
def Ecomm (T : Matrix (Idx d n) (Idx d n) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Idx d n) (Idx d n) ℂ :=
  T * piKron n X - piKron n X * T

lemma piKron_smul' (c : ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    piKron n (c • X) = c ^ n • piKron n X := by
  ext u v
  simp only [piKron, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma Ecomm_smul (T : Matrix (Idx d n) (Idx d n) ℂ) (c : ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    Ecomm T (c • X) = c ^ n • Ecomm T X := by
  unfold Ecomm
  rw [piKron_smul', Matrix.mul_smul, Matrix.smul_mul, smul_sub]

lemma det_one_add_IH (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    IsUnit (1 + Complex.I • H).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] at hv0
  have hHv : H *ᵥ v = Complex.I • v := by
    have h1 : Complex.I • (H *ᵥ v) = -v := eq_neg_of_add_eq_zero_right hv0
    calc H *ᵥ v = (-Complex.I) • (Complex.I • (H *ᵥ v)) := by
          rw [smul_smul]; simp
      _ = Complex.I • v := by rw [h1, smul_neg, neg_smul, neg_neg]
  have hq : star v ⬝ᵥ (H *ᵥ v) = Complex.I * (star v ⬝ᵥ v) := by
    rw [hHv, dotProduct_smul, smul_eq_mul]
  have hq' : star (star v ⬝ᵥ (H *ᵥ v)) = star v ⬝ᵥ (H *ᵥ v) := by
    calc star (star v ⬝ᵥ (H *ᵥ v)) = star (H *ᵥ v) ⬝ᵥ v := (Matrix.star_dotProduct (H *ᵥ v) v).symm
      _ = (star v ᵥ* Hᴴ) ⬝ᵥ v := by rw [Matrix.star_mulVec]
      _ = star v ⬝ᵥ (Hᴴ *ᵥ v) := by rw [Matrix.dotProduct_mulVec]
      _ = star v ⬝ᵥ (H *ᵥ v) := by rw [hH.eq]
  have hss : star (star v ⬝ᵥ v) = star v ⬝ᵥ v := (Matrix.star_dotProduct v v).symm
  have key : star (Complex.I * (star v ⬝ᵥ v)) = Complex.I * (star v ⬝ᵥ v) := by
    rw [← hq]; exact hq'
  rw [star_mul', hss] at key
  have hI : star Complex.I = -Complex.I := by simp [Complex.ext_iff]
  rw [hI] at key
  have h2 : (2 * Complex.I) * (star v ⬝ᵥ v) = 0 := by linear_combination -key
  have h3 : star v ⬝ᵥ v = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exfalso; simp [Complex.ext_iff] at h
    · exact h
  exact hv (dotProduct_star_self_eq_zero.1 h3)

lemma cayley_mem (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    (1 - Complex.I • H) * (1 + Complex.I • H)⁻¹ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  have hA := det_one_add_IH H hH
  have hB : IsUnit (1 - Complex.I • H).det := by
    have := det_one_add_IH (-H) (by unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_neg, hH.eq])
    rwa [smul_neg, ← sub_eq_add_neg] at this
  have hsA : star (1 + Complex.I • H) = 1 - Complex.I • H := by
    rw [star_add, star_one, star_smul, Matrix.star_eq_conjTranspose, hH.eq, Complex.star_def,
      Complex.conj_I, neg_smul, ← sub_eq_add_neg]
  have hsB : star (1 - Complex.I • H) = 1 + Complex.I • H := by
    rw [star_sub, star_one, star_smul, Matrix.star_eq_conjTranspose, hH.eq, Complex.star_def,
      Complex.conj_I, neg_smul, sub_neg_eq_add]
  have hcomm : (1 + Complex.I • H) * (1 - Complex.I • H) = (1 - Complex.I • H) * (1 + Complex.I • H) := by
    generalize Complex.I • H = K
    noncomm_ring
  rw [Matrix.mem_unitaryGroup_iff', star_mul, Matrix.star_eq_conjTranspose (1 + Complex.I • H)⁻¹,
    Matrix.conjTranspose_nonsing_inv, ← Matrix.star_eq_conjTranspose, hsA, hsB]
  calc (1 - Complex.I • H)⁻¹ * (1 + Complex.I • H) * ((1 - Complex.I • H) * (1 + Complex.I • H)⁻¹)
      = (1 - Complex.I • H)⁻¹ * ((1 + Complex.I • H) * (1 - Complex.I • H)) * (1 + Complex.I • H)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (1 - Complex.I • H)⁻¹ * ((1 - Complex.I • H) * (1 + Complex.I • H)) * (1 + Complex.I • H)⁻¹ := by
        rw [hcomm]
    _ = 1 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul,
          Matrix.mul_nonsing_inv _ hA]

lemma adj_eq (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A.det) : A.adjugate = A.det • A⁻¹ := by
  rw [Matrix.inv_def, smul_smul]
  rw [Ring.mul_inverse_cancel A.det hA, one_smul]

lemma Ecomm_herm (T : Matrix (Idx d n) (Idx d n) ℂ)
    (hU : ∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ, T * piKron n U = piKron n U * T)
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    Ecomm T ((1 - Complex.I • H) * (1 + Complex.I • H).adjugate) = 0 := by
  rw [adj_eq _ (det_one_add_IH H hH), Matrix.mul_smul, Ecomm_smul]
  unfold Ecomm
  rw [hU _ (cayley_mem H hH), sub_self, smul_zero]

/-- generic tensor power of a square matrix -/
def pk {R : Type*} [CommRing R] (n : ℕ) (M : Matrix (Fin d) (Fin d) R) :
    Matrix (Idx d n) (Idx d n) R :=
  Matrix.of fun x y => ∏ i, M (x i) (y i)

lemma pk_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin d) (Fin d) R) :
    (pk n M).map f = pk n (M.map f) := by
  ext x y
  simp [pk, map_prod]

lemma pk_eq (M : Matrix (Fin d) (Fin d) ℂ) : pk n M = piKron n M := rfl

/-- the polynomial matrix of the Cayley numerator -/
def Xp (d : ℕ) : Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Fin d) ℂ) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

def Np (d : ℕ) : Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Fin d) ℂ) :=
  (1 - (MvPolynomial.C (σ := Fin d × Fin d) Complex.I) • Xp d) *
    (1 + (MvPolynomial.C (σ := Fin d × Fin d) Complex.I) • Xp d).adjugate

def Fp (T : Matrix (Idx d n) (Idx d n) ℂ) : Matrix (Idx d n) (Idx d n) (MvPolynomial (Fin d × Fin d) ℂ) :=
  T.map MvPolynomial.C * pk n (Np d) - pk n (Np d) * T.map MvPolynomial.C

lemma Xp_map (x : Fin d × Fin d → ℂ) :
    (Xp d).map (MvPolynomial.eval x) = Matrix.of fun i j => x (i, j) := by
  ext i j; simp [Xp]

lemma Np_map (x : Fin d × Fin d → ℂ) :
    (Np d).map (MvPolynomial.eval x) =
      (1 - Complex.I • (Matrix.of fun i j => x (i, j))) *
        (1 + Complex.I • (Matrix.of fun i j => x (i, j))).adjugate := by
  unfold Np
  rw [Matrix.map_mul]
  have h1 : (1 - (MvPolynomial.C (σ := Fin d × Fin d) Complex.I) • Xp d).map (MvPolynomial.eval x) =
      1 - Complex.I • (Matrix.of fun i j => x (i, j)) := by
    ext i j
    simp [Xp, Matrix.one_apply]
  have h2 : (1 + (MvPolynomial.C (σ := Fin d × Fin d) Complex.I) • Xp d).map (MvPolynomial.eval x) =
      1 + Complex.I • (Matrix.of fun i j => x (i, j)) := by
    ext i j
    simp [Xp, Matrix.one_apply]
  rw [h1]
  congr 1
  have := RingHom.map_adjugate (MvPolynomial.eval x)
    (1 + (MvPolynomial.C (σ := Fin d × Fin d) Complex.I) • Xp d)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, h2] at this
  exact this

lemma Fp_map (T : Matrix (Idx d n) (Idx d n) ℂ) (x : Fin d × Fin d → ℂ) :
    (Fp T).map (MvPolynomial.eval x) =
      Ecomm T ((1 - Complex.I • (Matrix.of fun i j => x (i, j))) *
        (1 + Complex.I • (Matrix.of fun i j => x (i, j))).adjugate) := by
  unfold Fp Ecomm
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, pk_map, Np_map, pk_eq]
  have : (T.map MvPolynomial.C).map (MvPolynomial.eval x) = T := by
    ext u v; simp
  rw [this]

lemma Ecomm_cayley_all (T : Matrix (Idx d n) (Idx d n) ℂ)
    (hU : ∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ, T * piKron n U = piKron n U * T)
    (Z : Matrix (Fin d) (Fin d) ℂ) :
    Ecomm T ((1 - Complex.I • Z) * (1 + Complex.I • Z).adjugate) = 0 := by
  have hF : Fp T = 0 := by
    refine Matrix.ext (fun u v => ?_)
    rw [Matrix.zero_apply]
    apply herm_dense
    intro H hH
    have h := congrFun (congrFun (Fp_map T (fun ij => H ij.1 ij.2)) u) v
    rw [Matrix.map_apply] at h
    rw [h]
    have hH' : (Matrix.of fun i j => (fun ij : Fin d × Fin d => H ij.1 ij.2) (i, j)) = H := by
      ext i j; rfl
    rw [hH', Ecomm_herm T hU H hH]
    rfl
  have h := Fp_map T (fun ij => Z ij.1 ij.2)
  rw [hF, Matrix.map_zero _ (map_zero _)] at h
  have hZ : (Matrix.of fun i j => (fun ij : Fin d × Fin d => Z ij.1 ij.2) (i, j)) = Z := by
    ext i j; rfl
  rw [hZ] at h
  exact h.symm

lemma cayley_inv (X : Matrix (Fin d) (Fin d) ℂ) (hX : IsUnit (1 + X).det) :
    ∃ (Z : Matrix (Fin d) (Fin d) ℂ) (c : ℂ), c ≠ 0 ∧
      (1 - Complex.I • Z) * (1 + Complex.I • Z).adjugate = c • X := by
  set W := 1 + X with hWdef
  have hWX : X * W⁻¹ = W⁻¹ * X := by
    have h1 : X * W = W * X := by rw [hWdef]; noncomm_ring
    calc X * W⁻¹ = W⁻¹ * (W * X) * W⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hX, Matrix.one_mul]
      _ = W⁻¹ * (X * W) * W⁻¹ := by rw [h1]
      _ = W⁻¹ * X := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]
  set Z : Matrix (Fin d) (Fin d) ℂ := (-Complex.I) • (W⁻¹ * (1 - X)) with hZ
  have hIZ : Complex.I • Z = W⁻¹ * (1 - X) := by
    rw [hZ, smul_smul]; simp
  have hone : (1 : Matrix (Fin d) (Fin d) ℂ) = W⁻¹ * (1 + X) := by
    rw [← hWdef, Matrix.nonsing_inv_mul _ hX]
  have hA : 1 + Complex.I • Z = (2 : ℂ) • W⁻¹ := by
    rw [hIZ]
    calc (1 : Matrix (Fin d) (Fin d) ℂ) + W⁻¹ * (1 - X) = W⁻¹ * (1 + X) + W⁻¹ * (1 - X) := by
          rw [← hone]
      _ = W⁻¹ * ((2 : ℂ) • 1) := by
          rw [← Matrix.mul_add]; congr 1; rw [two_smul]; abel
      _ = (2 : ℂ) • W⁻¹ := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hB : 1 - Complex.I • Z = (2 : ℂ) • (X * W⁻¹) := by
    rw [hIZ]
    calc (1 : Matrix (Fin d) (Fin d) ℂ) - W⁻¹ * (1 - X) = W⁻¹ * (1 + X) - W⁻¹ * (1 - X) := by
          rw [← hone]
      _ = W⁻¹ * ((2 : ℂ) • X) := by
          rw [← Matrix.mul_sub]; congr 1; rw [two_smul]; abel
      _ = (2 : ℂ) • (X * W⁻¹) := by rw [Matrix.mul_smul, hWX]
  set A := 1 + Complex.I • Z with hAdef
  have hAu : IsUnit A.det := by
    rw [hA, Matrix.det_smul, Matrix.det_nonsing_inv]
    refine IsUnit.mul (IsUnit.pow _ (by norm_num)) ?_
    exact (Ring.inverse_unit hX.unit) ▸ hX.unit⁻¹.isUnit
  refine ⟨Z, A.det, hAu.ne_zero, ?_⟩
  have key : ((1 - Complex.I • Z) * A.adjugate) * A = (A.det • X) * A := by
    rw [Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, hB, Matrix.smul_mul,
      hA, Matrix.mul_smul, smul_comm]
  have := congrArg (fun M => M * A⁻¹) key
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAu, Matrix.mul_one] at this
  exact this

/-- commuting with all unitary tensor powers implies commuting with all tensor powers -/
theorem comm_all (T : Matrix (Idx d n) (Idx d n) ℂ)
    (hU : ∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ, T * piKron n U = piKron n U * T)
    (X : Matrix (Fin d) (Fin d) ℂ) : T * piKron n X = piKron n X * T := by
  have hgood : ∀ Y : Matrix (Fin d) (Fin d) ℂ, IsUnit (1 + Y).det → Ecomm T Y = 0 := by
    intro Y hY
    obtain ⟨Z, c, hc, hZ⟩ := cayley_inv Y hY
    have := Ecomm_cayley_all T hU Z
    rw [hZ, Ecomm_smul] at this
    exact (smul_eq_zero.1 this).resolve_left (pow_ne_zero _ hc)
  -- find a good scaling
  set Q : Polynomial ℂ := (1 + (Polynomial.X : Polynomial ℂ) • X.map Polynomial.C).det with hQ
  have hQt : ∀ t : ℂ, Polynomial.eval t Q = (1 + t • X).det := by
    intro t
    rw [hQ, ← Polynomial.coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp [mul_comm]
  have hQne : Q ≠ 0 := by
    intro h
    have := hQt 0
    rw [h] at this
    simp at this
  have hXQ : Polynomial.X * Q ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hQne
  obtain ⟨t, ht⟩ : ∃ t : ℂ, Polynomial.eval t (Polynomial.X * Q) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hXQ
    apply Polynomial.funext
    intro t
    rw [hcon t, Polynomial.eval_zero]
  rw [Polynomial.eval_mul, Polynomial.eval_X] at ht
  have ht0 : t ≠ 0 := left_ne_zero_of_mul ht
  have hdet : IsUnit (1 + t • X).det := by
    rw [isUnit_iff_ne_zero, ← hQt]; exact right_ne_zero_of_mul ht
  have h := hgood (t • X) hdet
  rw [Ecomm_smul] at h
  have h2 := (smul_eq_zero.1 h).resolve_left (pow_ne_zero _ ht0)
  unfold Ecomm at h2
  exact sub_eq_zero.1 h2

end KeylW


set_option autoImplicit false
open QAlgorithms QAlgorithms.Schur
open scoped Matrix ComplexOrder

noncomputable section

namespace KeylW
open KWS29

variable {d n : ℕ}

abbrev tp (d n : ℕ) (π : Equiv.Perm (Fin n)) := tensorPermutation d n π

/-- row symmetrizer and column antisymmetrizer on tensor space -/
def Am (lam : Partition d n) : Matrix (Idx d n) (Idx d n) ℂ :=
  ∑ a ∈ rowPermutations lam, tp d n a

def Bm (lam : Partition d n) : Matrix (Idx d n) (Idx d n) ℂ :=
  ∑ b ∈ columnPermutations lam, sgn b • tp d n b

lemma TR_Aelt (lam : Partition d n) : KWS29P.TR d n (Aelt lam) = Am lam := by
  simp only [Aelt, Am, map_sum, KWS29P.TR_single, one_smul]

lemma TR_Belt (lam : Partition d n) : KWS29P.TR d n (Belt lam) = Bm lam := by
  simp only [Belt, Bm, map_sum, KWS29P.TR_single]

lemma youngElt_eqP (lam : Partition d n) : KWS29P.youngElt lam = Aelt lam * Belt lam := by
  rw [← youngElt_eq]; rfl

lemma Y_eq (lam : Partition d n) : tensorYoungOperator lam = Am lam * Bm lam := by
  rw [← KWS29P.TR_youngElt, youngElt_eqP, map_mul, TR_Aelt, TR_Belt]

lemma tp_transpose (π : Equiv.Perm (Fin n)) : (tp d n π)ᵀ = tp d n π⁻¹ := by
  ext y x
  simp only [Matrix.transpose_apply, tp, KeylW.tp_apply']
  have : (x = y ∘ ⇑π.symm) ↔ (y = x ∘ ⇑(π⁻¹).symm) := by
    constructor
    · rintro rfl; funext k; simp [Equiv.Perm.inv_def]
    · rintro rfl; funext k; simp [Equiv.Perm.inv_def]
  by_cases h : x = y ∘ ⇑π.symm
  · rw [if_pos h, if_pos (this.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]

lemma Am_transpose (lam : Partition d n) : (Am lam)ᵀ = Am lam := by
  unfold Am
  rw [Matrix.transpose_sum]
  simp_rw [tp_transpose]
  exact Finset.sum_nbij' (fun a => a⁻¹) (fun a => a⁻¹) (fun a ha => R_inv ha) (fun a ha => R_inv ha)
    (fun a _ => by simp) (fun a _ => by simp) (fun a _ => rfl)

lemma Bm_transpose (lam : Partition d n) : (Bm lam)ᵀ = Bm lam := by
  unfold Bm
  rw [Matrix.transpose_sum]
  simp_rw [Matrix.transpose_smul, tp_transpose]
  exact Finset.sum_nbij' (fun a => a⁻¹) (fun a => a⁻¹) (fun a ha => C_inv ha) (fun a ha => C_inv ha)
    (fun a _ => by simp) (fun a _ => by simp) (fun a _ => by rw [KeylW.sgn_inv])

/-- the transposed Young symmetrizer -/
def Yp (lam : Partition d n) : Matrix (Idx d n) (Idx d n) ℂ := Bm lam * Am lam

lemma Yp_eq (lam : Partition d n) : Yp lam = (tensorYoungOperator lam)ᵀ := by
  rw [Y_eq, Matrix.transpose_mul, Am_transpose, Bm_transpose]; rfl

lemma Y_sq (lam : Partition d n) :
    ∃ k : ℂ, k ≠ 0 ∧ tensorYoungOperator lam * tensorYoungOperator lam = k • tensorYoungOperator lam := by
  obtain ⟨k, hk, h⟩ := young_sq lam
  refine ⟨k, hk, ?_⟩
  have h' : KWS29P.youngElt lam * KWS29P.youngElt lam = k • KWS29P.youngElt lam := h
  rw [← KWS29P.TR_youngElt, ← map_mul, h', map_smul]

lemma TR_transpose (q : KWS29P.GA n) : ∃ q' : KWS29P.GA n, (KWS29P.TR d n q)ᵀ = KWS29P.TR d n q' := by
  induction q using MonoidAlgebra.induction_on with
  | of g =>
    refine ⟨MonoidAlgebra.of ℂ _ g⁻¹, ?_⟩
    rw [show MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g = MonoidAlgebra.single g 1 from rfl,
      show MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g⁻¹ = MonoidAlgebra.single g⁻¹ 1 from rfl,
      KWS29P.TR_single, KWS29P.TR_single, one_smul, one_smul]
    exact tp_transpose g
  | add f g hf hg =>
    obtain ⟨f', hf'⟩ := hf
    obtain ⟨g', hg'⟩ := hg
    exact ⟨f' + g', by rw [map_add, Matrix.transpose_add, hf', hg', map_add]⟩
  | smul r f hf =>
    obtain ⟨f', hf'⟩ := hf
    exact ⟨r • f', by rw [map_smul, Matrix.transpose_smul, hf', map_smul]⟩

lemma vN_Yp (lam : Partition d n) (q : KWS29P.GA n) :
    ∃ α : ℂ, Yp lam * KWS29P.TR d n q * Yp lam = α • Yp lam := by
  obtain ⟨q', hq'⟩ := TR_transpose (d := d) q
  obtain ⟨α, hα⟩ := cxc lam q'
  refine ⟨α, ?_⟩
  have hα' : KWS29P.youngElt lam * q' * KWS29P.youngElt lam = α • KWS29P.youngElt lam := hα
  have h1 : tensorYoungOperator lam * (KWS29P.TR d n q)ᵀ * tensorYoungOperator lam =
      α • tensorYoungOperator lam := by
    rw [hq', ← KWS29P.TR_youngElt, ← map_mul, ← map_mul, hα', map_smul]
  have h2 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Yp_eq,
    Matrix.transpose_smul, ← Yp_eq] at h2
  rw [Matrix.mul_assoc]; exact h2

lemma Yp_sq (lam : Partition d n) :
    ∃ k : ℂ, k ≠ 0 ∧ tensorYoungOperator lam * tensorYoungOperator lam = k • tensorYoungOperator lam ∧
      Yp lam * Yp lam = k • Yp lam := by
  obtain ⟨k, hk, h⟩ := Y_sq lam
  refine ⟨k, hk, h, ?_⟩
  have h2 := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, ← Yp_eq, Matrix.transpose_smul, ← Yp_eq] at h2
  exact h2

lemma tr_Yp (lam : Partition d n) : (Yp lam).trace = (tensorYoungOperator lam).trace := by
  rw [Yp_eq, Matrix.trace_transpose]

lemma Am_comm (lam : Partition d n) (X : Matrix (Fin d) (Fin d) ℂ) :
    Am lam * piKron n X = piKron n X * Am lam := by
  unfold Am
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => KWS29P.tp_commute_piKron a X)

lemma Bm_comm (lam : Partition d n) (X : Matrix (Fin d) (Fin d) ℂ) :
    Bm lam * piKron n X = piKron n X * Bm lam := by
  unfold Bm
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_smul, KWS29P.tp_commute_piKron b X]

lemma Yp_comm (lam : Partition d n) (X : Matrix (Fin d) (Fin d) ℂ) :
    Yp lam * piKron n X = piKron n X * Yp lam := by
  unfold Yp
  rw [Matrix.mul_assoc, Am_comm, ← Matrix.mul_assoc, Bm_comm, Matrix.mul_assoc]

lemma tr_piKron_Yp (lam : Partition d n) (X : Matrix (Fin d) (Fin d) ℂ) :
    (piKron n X * Yp lam).trace = (piKron n X * tensorYoungOperator lam).trace := by
  rw [Y_eq, Yp, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, ← Am_comm,
    Matrix.mul_assoc]

/-- the highest weight basis vector -/
def eh (lam : Partition d n) : Idx d n → ℂ := Pi.single (hw lam) 1

lemma Bm_eh (lam : Partition d n) : Bm lam *ᵥ eh lam = wv lam := by
  funext y
  simp only [Bm, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, Pi.smul_apply, wv,
    smul_eq_mul]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  simp only [Matrix.mulVec, dotProduct, eh, tp, KeylW.tp_apply', Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma hw_row (lam : Partition d n) {a : Equiv.Perm (Fin n)} (ha : a ∈ rowPermutations lam) :
    hw lam ∘ ⇑a.symm = hw lam := by
  funext k
  apply Fin.ext
  show rowOf lam (a.symm k) = rowOf lam k
  have := (mem_R lam a⁻¹).1 (R_inv ha) k
  exact this

lemma Am_eh (lam : Partition d n) : Am lam *ᵥ eh lam = ((rowPermutations lam).card : ℂ) • eh lam := by
  funext y
  simp only [Am, Matrix.sum_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  simp only [Matrix.mulVec, dotProduct, eh, tp, KeylW.tp_apply', Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.cast_one, one_mul]
  rw [hw_row lam ha]

lemma card_R_ne (lam : Partition d n) : ((rowPermutations lam).card : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact Finset.card_ne_zero.2 ⟨1, one_mem_R lam⟩

lemma wv_eq_Yp (lam : Partition d n) :
    wv lam = ((rowPermutations lam).card : ℂ)⁻¹ • (Yp lam *ᵥ eh lam) := by
  rw [Yp, ← Matrix.mulVec_mulVec, Am_eh, Matrix.mulVec_smul, Bm_eh, smul_smul,
    inv_mul_cancel₀ (card_R_ne lam), one_smul]

end KeylW


set_option autoImplicit false
open MeasureTheory QAlgorithms QAlgorithms.Schur
open scoped Matrix ComplexOrder

noncomputable section

namespace KeylW
open KWS29

variable {d n : ℕ}

lemma piKron_mul (A B : Matrix (Fin d) (Fin d) ℂ) :
    piKron n (A * B) = piKron n A * piKron n B := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ, Finset.prod_mul_distrib]

lemma piKron_one' : piKron n (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma piKron_star (A : Matrix (Fin d) (Fin d) ℂ) : piKron n (star A) = star (piKron n A) := by
  ext x y
  simp [piKron, Matrix.star_apply, star_prod]

lemma piKron_unitary (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    star (piKron n U) * piKron n U = 1 := by
  rw [← piKron_star, ← piKron_mul, Matrix.mem_unitaryGroup_iff'.1 hU, piKron_one']

/-- the quadratic form -/
def qf (M : Matrix (Idx d n) (Idx d n) ℂ) (w : Idx d n → ℂ) : ℂ := star w ⬝ᵥ (M *ᵥ w)

lemma qf_eq (M : Matrix (Idx d n) (Idx d n) ℂ) (w : Idx d n → ℂ) :
    qf M w = ∑ y, ∑ x, star (w y) * M y x * w x := by
  unfold qf
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
  ring

lemma genPower_one (lam : Partition d n) : Tomography.keylGeneralizedPower lam 1 = 1 := by
  unfold Tomography.keylGeneralizedPower
  refine Finset.prod_eq_one (fun k _ => ?_)
  have : ((1 : Matrix (Fin d) (Fin d) ℂ).submatrix (fun i : Fin (k.val+1) => (⟨i.val, by omega⟩ : Fin d))
      (fun i : Fin (k.val+1) => (⟨i.val, by omega⟩ : Fin d))) = 1 := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one, one_pow]

lemma qf_wv (lam : Partition d n) (Z : Matrix (Fin d) (Fin d) ℂ) :
    qf (piKron n Z) (wv lam) = ((columnPermutations lam).card : ℂ) *
      Tomography.keylGeneralizedPower lam Z := by
  rw [qf_eq, quad_wv]

lemma qf_conj (P M : Matrix (Idx d n) (Idx d n) ℂ) (w : Idx d n → ℂ) :
    qf (star P * M * P) w = qf M (P *ᵥ w) := by
  unfold qf
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    Matrix.star_eq_conjTranspose]

section haar
set_option backward.isDefEq.respectTransparency.types false
open scoped Matrix.Norms.Elementwise

abbrev UG (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

lemma entry_cont (a b : Fin d) : Continuous (fun U : UG d => (U : Matrix (Fin d) (Fin d) ℂ) a b) :=
  (continuous_apply b).comp ((continuous_apply a).comp continuous_subtype_val)

lemma integ {g : UG d → ℂ} (hg : Continuous g) : Integrable g (unitaryHaar d) := by
  unfold unitaryHaar
  exact integrableOn_univ.1 (hg.continuousOn.integrableOn_compact isCompact_univ)

instance haar_prob : IsProbabilityMeasure (unitaryHaar d) := by
  unfold unitaryHaar
  exact ⟨Measure.haarMeasure_self⟩

lemma haar_inv (f : UG d → ℂ) (V : UG d) :
    ∫ U, f (V * U) ∂(unitaryHaar d) = ∫ U, f U ∂(unitaryHaar d) := by
  unfold unitaryHaar
  exact integral_mul_left_eq_self f V

/-- the orbit vector -/
def fU (lam : Partition d n) (U : UG d) : Idx d n → ℂ :=
  piKron n (U : Matrix (Fin d) (Fin d) ℂ) *ᵥ wv lam

lemma fU_cont (lam : Partition d n) (x : Idx d n) : Continuous (fun U : UG d => fU lam U x) := by
  unfold fU
  simp only [Matrix.mulVec, dotProduct, piKron, Matrix.of_apply]
  refine continuous_finsetSum _ (fun y _ => ?_)
  refine Continuous.mul (continuous_finsetProd _ (fun i _ => entry_cont _ _)) continuous_const

lemma fU_mul (lam : Partition d n) (V U : UG d) :
    fU lam (V * U) = piKron n (V : Matrix (Fin d) (Fin d) ℂ) *ᵥ fU lam U := by
  unfold fU
  rw [Matrix.mulVec_mulVec, ← piKron_mul]
  rfl

/-- the averaged rank-one operator -/
def Qm (lam : Partition d n) : Matrix (Idx d n) (Idx d n) ℂ :=
  Matrix.of fun x y => ∫ U, fU lam U x * star (fU lam U y) ∂(unitaryHaar d)

lemma prod_cont (lam : Partition d n) (x y : Idx d n) :
    Continuous (fun U : UG d => fU lam U x * star (fU lam U y)) :=
  (fU_cont lam x).mul (continuous_star.comp (fU_cont lam y))

lemma Qm_conj (lam : Partition d n) (V : UG d) :
    piKron n (V : Matrix (Fin d) (Fin d) ℂ) * Qm lam * star (piKron n (V : Matrix (Fin d) (Fin d) ℂ)) =
      Qm lam := by
  ext x y
  have h1 : (piKron n (V : Matrix (Fin d) (Fin d) ℂ) * Qm lam *
      star (piKron n (V : Matrix (Fin d) (Fin d) ℂ))) x y =
      ∫ U, (piKron n (V : Matrix (Fin d) (Fin d) ℂ) *ᵥ fU lam U) x *
        star ((piKron n (V : Matrix (Fin d) (Fin d) ℂ) *ᵥ fU lam U) y) ∂(unitaryHaar d) := by
    simp only [Matrix.mul_apply, Qm, Matrix.of_apply, Matrix.star_apply]
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [← integral_const_mul, ← integral_mul_const]
        congr 1; funext U; ring
      · intro w _
        exact integ (((continuous_const.mul (fU_cont lam w)).mul
          (continuous_const.mul (continuous_star.comp (fU_cont lam z)))))
    · intro z _
      exact integ (continuous_finsetSum _ (fun w _ => ((continuous_const.mul (fU_cont lam w)).mul
          (continuous_const.mul (continuous_star.comp (fU_cont lam z))))))
  have h2 : (∫ U, (piKron n (V : Matrix (Fin d) (Fin d) ℂ) *ᵥ fU lam U) x *
        star ((piKron n (V : Matrix (Fin d) (Fin d) ℂ) *ᵥ fU lam U) y) ∂(unitaryHaar d)) =
      ∫ U, (fun U => fU lam U x * star (fU lam U y)) (V * U) ∂(unitaryHaar d) := by
    congr 1; funext U; show _ = fU lam (V * U) x * star (fU lam (V * U) y); rw [fU_mul]
  rw [h1, h2, haar_inv (fun U => fU lam U x * star (fU lam U y)) V]
  rfl

lemma Qm_comm (lam : Partition d n) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) : Qm lam * piKron n U = piKron n U * Qm lam := by
  have h := Qm_conj lam ⟨U, hU⟩
  simp only at h
  calc Qm lam * piKron n U = (piKron n U * Qm lam * star (piKron n U)) * piKron n U := by rw [h]
    _ = piKron n U * Qm lam * (star (piKron n U) * piKron n U) := by simp only [Matrix.mul_assoc]
    _ = piKron n U * Qm lam := by rw [piKron_unitary U hU, Matrix.mul_one]

lemma qf_fU (lam : Partition d n) (U : UG d) (A : Matrix (Fin d) (Fin d) ℂ) :
    qf (piKron n (star (U : Matrix (Fin d) (Fin d) ℂ) * A * (U : Matrix (Fin d) (Fin d) ℂ))) (wv lam) = qf (piKron n A) (fU lam U) := by
  rw [piKron_mul, piKron_mul, piKron_star, qf_conj]
  rfl

lemma fU_norm (lam : Partition d n) (U : UG d) :
    qf 1 (fU lam U) = ((columnPermutations lam).card : ℂ) := by
  have := qf_fU lam U 1
  rw [Matrix.mul_one, Matrix.mem_unitaryGroup_iff'.1 U.2] at this
  rw [← piKron_one' (n := n), ← this, qf_wv, genPower_one, mul_one]

lemma trace_Qm (lam : Partition d n) :
    (Qm lam).trace = ((columnPermutations lam).card : ℂ) := by
  have h1 : (Qm lam).trace = ∫ U, qf 1 (fU lam U) ∂(unitaryHaar d) := by
    unfold Matrix.trace
    simp only [Matrix.diag, Qm, Matrix.of_apply]
    rw [← integral_finsetSum _ (fun x _ => integ (prod_cont lam x x))]
    congr 1; funext U
    rw [qf_eq]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_eq_single y]
    · simp [Matrix.one_apply]; ring
    · intro b _ hb; simp [Matrix.one_apply, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1]
  simp_rw [fU_norm]
  simp

lemma int_qf (lam : Partition d n) (A : Matrix (Fin d) (Fin d) ℂ) :
    ∫ U, qf (piKron n (star (U : Matrix (Fin d) (Fin d) ℂ) * A * (U : Matrix (Fin d) (Fin d) ℂ))) (wv lam) ∂(unitaryHaar d) =
      (piKron n A * Qm lam).trace := by
  simp_rw [qf_fU, qf_eq]
  rw [integral_finsetSum]
  · unfold Matrix.trace
    simp only [Matrix.diag, Matrix.mul_apply, Qm, Matrix.of_apply]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← integral_const_mul]
      congr 1; funext U; ring
    · intro x _
      exact integ (((continuous_star.comp (fU_cont lam y)).mul continuous_const).mul (fU_cont lam x))
  · intro y _
    exact integ (continuous_finsetSum _ (fun x _ =>
      ((continuous_star.comp (fU_cont lam y)).mul continuous_const).mul (fU_cont lam x)))

lemma Yp_fU (lam : Partition d n) (k : ℂ) (hk : Yp lam * Yp lam = k • Yp lam) (U : UG d) :
    Yp lam *ᵥ fU lam U = k • fU lam U := by
  set P := piKron n (U : Matrix (Fin d) (Fin d) ℂ) with hP
  set c := ((rowPermutations lam).card : ℂ)⁻¹ with hc
  have hf : fU lam U = c • (Yp lam *ᵥ (P *ᵥ eh lam)) := by
    unfold fU
    rw [← hP, wv_eq_Yp, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Yp_comm, ← Matrix.mulVec_mulVec]
  rw [hf, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hk, Matrix.smul_mulVec, smul_comm]

lemma Yp_Qm (lam : Partition d n) (k : ℂ) (hk : Yp lam * Yp lam = k • Yp lam) :
    Yp lam * Qm lam = k • Qm lam := by
  ext x y
  simp only [Matrix.mul_apply, Qm, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have e1 : ∀ z, Yp lam x z * ∫ U, fU lam U z * star (fU lam U y) ∂(unitaryHaar d) =
      ∫ U, Yp lam x z * (fU lam U z * star (fU lam U y)) ∂(unitaryHaar d) :=
    fun z => (integral_const_mul _ _).symm
  rw [Finset.sum_congr rfl (fun z _ => e1 z)]
  have hsum := integral_finsetSum (μ := unitaryHaar d) (s := Finset.univ)
    (f := fun z U => Yp lam x z * (fU lam U z * star (fU lam U y)))
    (fun z _ => integ (continuous_const.mul (prod_cont lam z y)))
  beta_reduce at hsum
  rw [← hsum, ← integral_const_mul]
  congr 1; funext U
  have h := congrFun (Yp_fU lam k hk U) x
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  rw [← mul_assoc, ← h, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  ring

lemma trace_polyRep (lam : Partition d n) (A : Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.trace ℂ (schurModule lam) (polynomialRepresentation lam A) =
      (piKron n A * KWS29P.projMat (schurModule lam)).trace := by
  unfold polynomialRepresentation
  rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  have h : (schurModule lam).subtype ∘ₗ ((schurModule lam).orthogonalProjectionOnto.toLinearMap ∘ₗ
      Matrix.toEuclideanLin (piKron n A)) =
      Matrix.toEuclideanLin (KWS29P.projMat (schurModule lam) * piKron n A) := by
    rw [KWS29P.toEL_mul, KWS29P.toEL_projMat]
    rfl
  rw [h, KWS29P.trace_toEL, Matrix.trace_mul_comm]

/-- **Haar average of Keyl's generalized power**: for every `d × d` matrix `A`,
`∫ Δ_λ(U† A U) dU = tr π_λ(A) / dim V_λ` (O'Donnell–Wright, eq. (12)). -/
theorem haar_genPower (lam : Partition d n) (A : Matrix (Fin d) (Fin d) ℂ) :
    ∫ U, Tomography.keylGeneralizedPower lam
        (star (U : Matrix (Fin d) (Fin d) ℂ) * A * (U : Matrix (Fin d) (Fin d) ℂ)) ∂(unitaryHaar d) =
      LinearMap.trace ℂ (schurModule lam) (polynomialRepresentation lam A) /
        (Module.finrank ℂ (schurModule lam) : ℂ) := by
  obtain ⟨k, hk, hY, hY'⟩ := Yp_sq lam
  set Cc := ((columnPermutations lam).card : ℂ) with hCc
  have hC : Cc ≠ 0 := by
    rw [hCc, Nat.cast_ne_zero]; exact Finset.card_ne_zero.2 ⟨1, one_mem_C lam⟩
  have hcomm : ∀ X : Matrix (Fin d) (Fin d) ℂ, Qm lam * piKron n X = piKron n X * Qm lam :=
    comm_all (Qm lam) (fun U hU => Qm_comm lam U hU)
  obtain ⟨q, hq⟩ := commutant (Qm lam) hcomm
  obtain ⟨α, hα⟩ := vN_Yp lam q
  rw [← hq] at hα
  have hYQ := Yp_Qm lam k hY'
  have hQY : Qm lam * Yp lam = (α / k) • Yp lam := by
    have h1 : k • (Qm lam * Yp lam) = α • Yp lam := by
      rw [← Matrix.smul_mul, ← hYQ, ← hα]
    calc Qm lam * Yp lam = k⁻¹ • (k • (Qm lam * Yp lam)) := by
          rw [smul_smul, inv_mul_cancel₀ hk, one_smul]
      _ = k⁻¹ • (α • Yp lam) := by rw [h1]
      _ = (α / k) • Yp lam := by rw [smul_smul, div_eq_inv_mul]
  have htr : ∀ M : Matrix (Idx d n) (Idx d n) ℂ, M * Qm lam = Qm lam * M →
      (M * Qm lam).trace = (α / k / k) * (M * Yp lam).trace := by
    intro M hM
    have hQ : Qm lam = k⁻¹ • (Yp lam * Qm lam) := by
      rw [hYQ, smul_smul, inv_mul_cancel₀ hk, one_smul]
    calc (M * Qm lam).trace = k⁻¹ * (M * (Yp lam * Qm lam)).trace := by
          conv_lhs => rw [hQ]
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      _ = k⁻¹ * (Yp lam * (Qm lam * M)).trace := by
          rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
      _ = k⁻¹ * (Yp lam * (M * Qm lam)).trace := by rw [hM]
      _ = k⁻¹ * (M * (Qm lam * Yp lam)).trace := by
          rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
      _ = (α / k / k) * (M * Yp lam).trace := by
          rw [hQY, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]; ring
  have hA := htr (piKron n A) (hcomm A).symm
  have h1 := htr 1 (by rw [Matrix.one_mul, Matrix.mul_one])
  rw [Matrix.one_mul, Matrix.one_mul, trace_Qm] at h1
  have hint : Cc * ∫ U, Tomography.keylGeneralizedPower lam
        (star (U : Matrix (Fin d) (Fin d) ℂ) * A * (U : Matrix (Fin d) (Fin d) ℂ)) ∂(unitaryHaar d) =
      (piKron n A * Qm lam).trace := by
    rw [← int_qf, ← integral_const_mul]
    congr 1; funext U
    rw [qf_wv]
  have hYtr : (tensorYoungOperator lam).trace ≠ 0 := by
    have := KWS29P.finrank_range hk hY
    intro h0
    rw [h0, mul_zero] at this
    exact KWS29P.finrank_schur_ne_zero lam (by exact_mod_cast this)
  rw [trace_polyRep, show schurModule lam =
      LinearMap.range (Matrix.toEuclideanLin (tensorYoungOperator lam)) from rfl,
    KWS29P.trace_mul_projMat hk hY _ (by
      rw [Y_eq, ← Matrix.mul_assoc, ← Am_comm, Matrix.mul_assoc, ← Bm_comm, Matrix.mul_assoc]),
    KWS29P.finrank_range hk hY]
  rw [hA, tr_piKron_Yp] at hint
  rw [tr_Yp, ← hCc] at h1
  rw [h1] at hint
  have hne : α / k / k ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact hC h1
  have hI : (∫ U, Tomography.keylGeneralizedPower lam
        (star (U : Matrix (Fin d) (Fin d) ℂ) * A * (U : Matrix (Fin d) (Fin d) ℂ)) ∂(unitaryHaar d)) =
      (piKron n A * tensorYoungOperator lam).trace / (tensorYoungOperator lam).trace := by
    rw [eq_div_iff hYtr]
    apply mul_left_cancel₀ hne
    linear_combination hint
  rw [hI, mul_div_mul_left _ _ (inv_ne_zero hk)]

end haar

end KeylW


open QAlgorithms QAlgorithms.Schur MeasureTheory in
theorem solution {d n : ℕ} (lambda : Schur.Partition d n)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    ∫ U, Tomography.keylGeneralizedPower lambda
        (star (U : Matrix (Fin d) (Fin d) ℂ) * A * (U : Matrix (Fin d) (Fin d) ℂ)) ∂(Schur.unitaryHaar d) =
      LinearMap.trace ℂ (Schur.schurModule lambda) (Schur.polynomialRepresentation lambda A) /
        (Module.finrank ℂ (Schur.schurModule lambda) : ℂ) :=
  KeylW.haar_genPower lambda A
