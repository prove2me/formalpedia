-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.positive_eigenvalue_component
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:14:52.411564+00:00
-- url     : https://prove2.me/submissions/820e8442-ca02-4066-95b6-06b49c0445ce

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

namespace X4CZL

open Polynomial

attribute [local instance] Classical.propDecidable

lemma rev_lin (r : ℝ) (hr : r ≠ 0) : (X - C r).reverse = C (-r) * (X - C r⁻¹) := by
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C]
  have h1 : (X : ℝ[X]).reverse = 1 := by
    have := reverse_X_mul (1 : ℝ[X]); rw [mul_one] at this; rw [this]; simpa using reverse_C (1 : ℝ)
  rw [h1, natDegree_X, pow_one, mul_sub, ← C_mul, show -r * r⁻¹ = -1 by field_simp]
  simp; ring

lemma rev_pow (f : ℝ[X]) (m : ℕ) : (f ^ m).reverse = f.reverse ^ m := by
  induction m with
  | zero => simpa using reverse_C (1 : ℝ)
  | succ k ih => rw [pow_succ, reverse_mul_of_domain, ih, pow_succ]

lemma mult_le (p : ℝ[X]) (r : ℝ) (hr : r ≠ 0) :
    rootMultiplicity r p ≤ rootMultiplicity r⁻¹ p.reverse := by
  by_cases hp : p = 0
  · simp [hp]
  rw [le_rootMultiplicity_iff (reverse_eq_zero.not.2 hp)]
  obtain ⟨q, hq⟩ := pow_rootMultiplicity_dvd p r
  conv_rhs => rw [hq]
  rw [reverse_mul_of_domain, rev_pow, rev_lin r hr, mul_pow]
  exact (dvd_mul_left _ _).mul_right _

lemma mult_rev (p : ℝ[X]) (c : ℝ) (h : p = C c * p.reverse) (x : ℝ) :
    rootMultiplicity x p = rootMultiplicity x p.reverse := by
  by_cases hp : p = 0
  · simp [hp]
  conv_lhs => rw [h]
  rw [rootMultiplicity_mul (by rw [← h]; exact hp), rootMultiplicity_C, zero_add]

lemma mult_inv (p : ℝ[X]) (c : ℝ) (h : p = C c * p.reverse) (r : ℝ) (hr : r ≠ 0) :
    rootMultiplicity r p = rootMultiplicity r⁻¹ p := by
  apply le_antisymm
  · rw [mult_rev p c h r⁻¹]; exact mult_le p r hr
  · have := mult_le p r⁻¹ (inv_ne_zero hr)
    rw [inv_inv, ← mult_rev p c h r] at this; exact this

lemma prod_sign (s : Multiset ℝ) :
    (s.map (fun r => 1 - r)).prod =
      (-1) ^ Multiset.card (s.filter (fun r => 1 < r)) * (s.map (fun r => |1 - r|)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.filter_cons, ih]
    split_ifs with h
    · rw [abs_of_neg (by linarith)]; simp [pow_succ]; ring
    · rw [abs_of_nonneg (by linarith)]; simp; ring

lemma eval_sign (p : ℝ[X]) (hm : p.Monic) :
    ∃ c > 0, p.eval 1 = (p.roots.map (fun r => 1 - r)).prod * c := by
  obtain ⟨q, hq⟩ := prod_multiset_X_sub_C_dvd p
  have hpm : (p.roots.map fun a => X - C a).prod.Monic :=
    monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hqm : q.Monic := hpm.of_mul_monic_left (hq ▸ hm)
  have hp0 : (p.roots.map fun a => X - C a).prod * q ≠ 0 := hq ▸ hm.ne_zero
  have hr := roots_mul hp0
  rw [← hq, roots_multiset_prod_X_sub_C] at hr
  have hqr : q.roots = 0 := by
    have := congrArg Multiset.card hr
    rw [Multiset.card_add] at this
    exact Multiset.card_eq_zero.1 (by omega)
  refine ⟨q.eval 1, ?_, ?_⟩
  · apply zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    · intro y hy
      have : y ∈ q.roots := (mem_roots hqm.ne_zero).2 hy
      rw [hqr] at this; simp at this
    · rw [hqm.leadingCoeff]; norm_num
  · conv_lhs => rw [hq]
    rw [eval_mul, eval_multiset_prod, Multiset.map_map]
    congr 2
    exact Multiset.map_congr rfl (fun r _ => by simp)

lemma card_filter (s : Multiset ℝ) (S : ℝ → Prop) [DecidablePred S] :
    Multiset.card (s.filter S) = ∑ x ∈ s.toFinset.filter S, s.count x := by
  rw [← Multiset.toFinset_sum_count_eq (s.filter S), Multiset.toFinset_filter]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Multiset.count_filter_of_pos (Finset.mem_filter.1 hx).2]

/-- the real counting statement. -/
lemma count_main (p : ℝ[X]) (hm : p.Monic) (c : ℝ) (h : p = C c * p.reverse) (h1 : p.eval 1 ≠ 0) :
    0 < p.eval 1 ↔ 4 ∣ Multiset.card (p.roots.filter (fun x => 0 < x)) := by
  set s := p.roots with hs
  have hcnt : ∀ x : ℝ, x ≠ 0 → s.count x = s.count x⁻¹ := by
    intro x hx; rw [hs, count_roots, count_roots]; exact mult_inv p c h x hx
  have hmem : ∀ x : ℝ, x ∈ s.toFinset ↔ 0 < s.count x := by
    intro x; rw [Multiset.mem_toFinset, Multiset.count_pos]
  have h1n : (1 : ℝ) ∉ s.toFinset := by
    rw [Multiset.mem_toFinset, hs, mem_roots hm.ne_zero]; exact h1
  -- N(0,1) = N(1,∞)
  have heq : ∑ x ∈ s.toFinset.filter (fun x => 0 < x ∧ x < 1), s.count x =
      ∑ x ∈ s.toFinset.filter (fun x => 1 < x), s.count x := by
    apply Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹)
    · intro x hx
      simp only [Finset.mem_filter, hmem] at hx ⊢
      refine ⟨by rw [← hcnt x hx.2.1.ne']; exact hx.1, ?_⟩
      exact (one_lt_inv₀ hx.2.1).2 hx.2.2
    · intro x hx
      simp only [Finset.mem_filter, hmem] at hx ⊢
      have hx0 : 0 < x := by linarith [hx.2]
      refine ⟨by rw [← hcnt x hx0.ne']; exact hx.1, inv_pos.2 hx0, inv_lt_one_of_one_lt₀ hx.2⟩
    · intro x _; simp
    · intro x _; simp
    · intro x hx
      simp only [Finset.mem_filter] at hx
      exact hcnt x hx.2.1.ne'
  have hsplit : Multiset.card (s.filter (fun x => 0 < x)) =
      2 * Multiset.card (s.filter (fun x => 1 < x)) := by
    rw [card_filter, card_filter, ← Finset.sum_filter_add_sum_filter_not _ (fun x => x < 1),
      Finset.filter_filter, Finset.filter_filter]
    have e1 : s.toFinset.filter (fun x => 0 < x ∧ x < 1) = s.toFinset.filter (fun x => 0 < x ∧ x < 1) := rfl
    have e2 : s.toFinset.filter (fun x => 0 < x ∧ ¬ x < 1) = s.toFinset.filter (fun x => 1 < x) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, h0, h1'⟩
        rcases lt_or_eq_of_le (not_lt.1 h1') with h | h
        · exact ⟨hx, h⟩
        · exact absurd (h ▸ hx) h1n
      · rintro ⟨hx, h⟩; exact ⟨hx, by linarith, by linarith⟩
    rw [e2, heq]; ring
  obtain ⟨c', hc', he⟩ := eval_sign p hm
  rw [hsplit, he, prod_sign]
  have hpos : 0 ≤ (s.map (fun r => |1 - r|)).prod :=
    Multiset.prod_nonneg (fun a ha => by
      obtain ⟨r, _, rfl⟩ := Multiset.mem_map.1 ha; exact abs_nonneg _)
  have hne : (s.map (fun r => |1 - r|)).prod ≠ 0 := by
    intro h0; apply h1; rw [he, prod_sign, ← hs, h0]; simp
  have hpos' := lt_of_le_of_ne hpos (Ne.symm hne)
  set N := Multiset.card (s.filter (fun x => 1 < x))
  rcases Nat.even_or_odd N with hN | hN
  · rw [hN.neg_one_pow]
    simp only [one_mul]
    constructor
    · intro _; obtain ⟨k, hk⟩ := hN; exact ⟨k, by omega⟩
    · intro _; positivity
  · rw [hN.neg_one_pow]
    constructor
    · intro hh; nlinarith [mul_pos hpos' hc']
    · intro ⟨k, hk⟩; obtain ⟨j, hj⟩ := hN; omega


lemma JJ (n : ℕ) : canonicalJ n * canonicalJ n = -1 := by
  unfold canonicalJ
  rw [Matrix.fromBlocks_multiply]
  simp
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]; simp

lemma pal {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A) :
    ∃ c : ℝ, A.charpoly = C c * A.charpoly.reverse := by
  set J := canonicalJ n
  have hBA : (-(J * A.transpose * J)) * A = 1 := by
    have : A.transpose * J * A = J := hA
    rw [neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc A.transpose, this, JJ, neg_neg]
  have hinv : A⁻¹ = -(J * A.transpose * J) := Matrix.inv_eq_left_inv hBA
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (Matrix.isUnit_det_of_left_inverse hBA)
  have hcp : A⁻¹.charpoly = A.charpoly := by
    have e : J * (-(J * A.transpose)) = A.transpose := by
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, JJ]; simp
    rw [hinv, ← neg_mul, Matrix.charpoly_mul_comm, e, Matrix.charpoly_transpose]
  refine ⟨(-1) ^ Fintype.card (Coord n) * Ring.inverse A.det, ?_⟩
  conv_lhs => rw [← hcp, Matrix.charpoly_inv A hu, ← Matrix.reverse_charpoly]
  rw [C_mul, C_pow, C_neg, C_1]


lemma eval_one {n : ℕ} (A : GroupedRealMatrix n) : A.charpoly.eval 1 = (A - 1).det := by
  rw [Matrix.eval_charpoly, map_one, ← neg_sub, Matrix.det_neg]
  simp [Fintype.card_sum, Even.neg_one_pow ⟨n, rfl⟩]

lemma sum_eq {n : ℕ} (A : GroupedRealMatrix n) :
    ∑ z ∈ (eigenvalues A).filter (fun z => z.im = 0 ∧ 0 < z.re), algebraicMultiplicity A z =
      Multiset.card (A.charpoly.roots.filter (fun x => 0 < x)) := by
  set p := A.charpoly
  have hm : p.Monic := Matrix.charpoly_monic A
  have hχ : (complexify A).charpoly = p.map Complex.ofRealHom := by
    rw [← Matrix.charpoly_map]; rfl
  have hχ0 : p.map Complex.ofRealHom ≠ 0 := (hm.map _).ne_zero
  have hmult : ∀ x : ℝ, rootMultiplicity (x : ℂ) (p.map Complex.ofRealHom) = rootMultiplicity x p :=
    fun x => (eq_rootMultiplicity_map Complex.ofReal_injective x).symm
  have hreal : ∀ z : ℂ, z.im = 0 → z = ((z.re : ℝ) : ℂ) := fun z hz => Complex.ext (by simp) (by simp [hz])
  unfold eigenvalues algebraicMultiplicity
  rw [hχ, card_filter]
  refine Finset.sum_nbij' (fun z : ℂ => z.re) (fun x : ℝ => (x : ℂ)) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Multiset.mem_toFinset, ← Multiset.count_pos, count_roots] at hz ⊢
    rw [hreal z hz.2.1, hmult] at hz
    exact ⟨hz.1, hz.2.2⟩
  · intro x hx
    simp only [Finset.mem_filter, Multiset.mem_toFinset, ← Multiset.count_pos, count_roots] at hx ⊢
    rw [hmult]
    exact ⟨hx.1, by simp, by simpa using hx.2⟩
  · intro z hz
    simp only [Finset.mem_filter] at hz
    exact (hreal z hz.2.1).symm
  · intro x _; simp
  · intro z hz
    simp only [Finset.mem_filter] at hz
    rw [count_roots, hreal z hz.2.1, hmult]
    simp

theorem main {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (hend : (A-1).det ≠ 0) :
    0 < (A-1).det ↔ 4 ∣ ∑ z ∈ (eigenvalues A).filter (fun z => z.im = 0 ∧ 0 < z.re),
      algebraicMultiplicity A z := by
  obtain ⟨c, hc⟩ := pal A hA
  rw [sum_eq, ← eval_one]
  rw [← eval_one] at hend
  exact count_main _ (Matrix.charpoly_monic A) c hc hend

end X4CZL

open QAlgorithms.Papers.Independent.Gap50repair.P01 in
theorem solution {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (hend : (A-1).det ≠ 0) :
    0 < (A-1).det ↔ 4 ∣ ∑ z ∈ (eigenvalues A).filter (fun z => z.im = 0 ∧ 0 < z.re),
      algebraicMultiplicity A z :=
  X4CZL.main A hA hend
