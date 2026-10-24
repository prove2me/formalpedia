-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.example_6_18
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:21:50.308656+00:00
-- url     : https://prove2.me/submissions/4570e3d8-af06-4f9a-b359-964dd9051b71

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8DM

/-- entries of depolarizing -/
lemma dep_apply (d : ℕ) (p q : Fin d × Fin d) :
    depolarizing d p q = if p.1 = p.2 ∧ q.1 = q.2 then (d : ℂ)⁻¹ else 0 := rfl

lemma dm_apply (d : ℕ) (a : ℝ) (p q : Fin d × Fin d) :
    depolarizingMixture d a p q =
      (a : ℂ) * (if p = q then 1 else 0) +
        ((1 - a : ℝ) : ℂ) * (if p.1 = p.2 ∧ q.1 = q.2 then (d : ℂ)⁻¹ else 0) := by
  simp only [depolarizingMixture, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    dep_apply, Complex.real_smul]

lemma applyMap_apply {d : ℕ} (t : Map d) (X : Mat d) (i j : Fin d) :
    applyMap t X i j = ∑ q : Fin d × Fin d, t (i, j) q * X q.1 q.2 := by
  simp [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

lemma applyMap_dm (d : ℕ) [NeZero d] (a : ℝ) (X : Mat d) :
    applyMap (depolarizingMixture d a) X =
      (a : ℂ) • X + (((1 - a : ℝ) : ℂ) * (d : ℂ)⁻¹ * X.trace) • (1 : Mat d) := by
  ext i j
  rw [applyMap_apply]
  simp only [dm_apply, add_mul, Finset.sum_add_distrib, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply]
  congr 1
  · rw [Finset.sum_eq_single (i, j)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · simp only [Matrix.trace, Matrix.diag]
    by_cases hij : i = j
    · subst hij
      simp only [true_and, if_true]
      rw [Fintype.sum_prod_type]
      simp only [mul_ite, ite_mul, zero_mul, mul_zero]
      simp only [mul_one]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_ite_eq]; simp
    · simp [hij]

/-- Kraus family for the depolarizing mixture. -/
def kr (d : ℕ) (a : ℝ) : Option (Fin d × Fin d) → Mat d
  | none => ((Real.sqrt a : ℝ) : ℂ) • (1 : Mat d)
  | some p => ((Real.sqrt ((1 - a) / d) : ℝ) : ℂ) • Matrix.single p.1 p.2 1

lemma isChannel_of_kraus {K ι : Type*} [Fintype K] [Fintype ι] [DecidableEq ι]
    (E : K → Matrix ι ι ℂ) (hE : QAlgorithms.IsKrausFamily E) (Φ : QAlgorithms.Superop ι ι)
    (hΦ : ∀ ρ, Φ ρ = QAlgorithms.krausApply E ρ) : QAlgorithms.IsChannel Φ := by
  classical
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun j => E (e.symm j), ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily at hE ⊢
    rw [← hE]
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  · intro ρ
    rw [hΦ]
    unfold QAlgorithms.krausApply
    exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm

lemma sq_sqrt_c {x : ℝ} (hx : 0 ≤ x) : ((Real.sqrt x : ℝ) : ℂ) * ((Real.sqrt x : ℝ) : ℂ) = x := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]

lemma unital (d : ℕ) [NeZero d] (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    UnitalChannel (depolarizingMixture d a) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hb : 0 ≤ (1 - a) / d := div_nonneg (by linarith) (Nat.cast_nonneg _)
  refine ⟨isChannel_of_kraus (kr d a) ?_ _ ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily
    rw [Fintype.sum_option]
    simp only [kr, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, Matrix.conjTranspose_one,
      sq_sqrt_c h0, sq_sqrt_c hb]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
      Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same]
    rw [Fintype.sum_prod_type]
    simp only [Matrix.single_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp only [and_self, if_true, mul_one]
      rw [Finset.sum_comm, Finset.sum_eq_single i]
      · simp only [true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        push_cast
        rw [nsmul_eq_mul]; field_simp; ring
      · intro b _ hb; simp [hb]
      · simp
    · simp only [hij, if_false]
      simp only [mul_ite, mul_zero, mul_one, ite_and]
      simp [hij]
  · intro ρ
    rw [applyMap_dm]
    unfold QAlgorithms.krausApply
    rw [Fintype.sum_option]
    simp only [kr, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, Matrix.one_mul,
      Matrix.conjTranspose_one, sq_sqrt_c h0, sq_sqrt_c hb]
    congr 1
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.conjTranspose_single,
      star_one, Matrix.one_apply]
    rw [Fintype.sum_prod_type]
    simp only [Matrix.single_mul_mul_single, Matrix.single_apply]
    by_cases hij : i = j
    · subst hij
      simp only [and_self, if_true, mul_one]
      rw [Finset.sum_eq_single i]
      · simp only [true_and]
        rw [← Finset.mul_sum]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.trace, Matrix.diag]
        push_cast; ring
      · intro b _ hb; simp [hb]
      · simp
    · simp only [hij, if_false, mul_zero]
      symm
      refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
      split_ifs with h
      · exact absurd (h.1.symm.trans h.2) hij
      · simp
  · rw [applyMap_dm]
    simp only [Matrix.trace_one, Fintype.card_fin]
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one, ← add_smul]
    push_cast
    simp

lemma primitive (d : ℕ) [NeZero d] (a : ℝ) (ha1 : a < 1) (ha0 : -1 < a) :
    Primitive (depolarizingMixture d a) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  unfold Primitive peripheral scalars
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro X ⟨c, hc, hX⟩
    rw [applyMap_dm] at hX
    have htr := congrArg Matrix.trace hX
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul] at htr
    have htr' : (1 - c) * X.trace = 0 := by
      have : ((1 - a : ℝ) : ℂ) * (d : ℂ)⁻¹ * X.trace * (d : ℂ) = ((1 - a : ℝ) : ℂ) * X.trace := by
        field_simp
      push_cast at htr this ⊢
      linear_combination htr - this
    rcases mul_eq_zero.mp htr' with h | h
    · have hc1 : c = 1 := by linear_combination -h
      subst hc1
      have hX' : X = ((d : ℂ)⁻¹ * X.trace) • (1 : Mat d) := by
        have hne : ((1 - a : ℝ) : ℂ) ≠ 0 := by
          rw [Complex.ofReal_ne_zero]; linarith
        ext i j
        have := congrFun (congrFun hX i) j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_mul] at this
        simp only [Matrix.smul_apply, smul_eq_mul]
        apply mul_left_cancel₀ hne
        push_cast at this ⊢
        linear_combination -this
      rw [hX']
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · have hX0 : X = 0 := by
        rw [h, mul_zero, zero_smul, add_zero] at hX
        have : ((a : ℂ) - c) • X = 0 := by rw [sub_smul, hX, sub_self]
        rcases smul_eq_zero.mp this with h' | h'
        · exfalso
          have : (a : ℂ) = c := by linear_combination h'
          have hn : ‖(a : ℂ)‖ = 1 := by rw [this, hc]
          rw [Complex.norm_real, Real.norm_eq_abs] at hn
          rcases abs_eq (zero_le_one) |>.mp hn with h3 | h3 <;> linarith
        · exact h'
      rw [hX0]; exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro X rfl
    refine Submodule.subset_span ⟨1, by simp, ?_⟩
    rw [applyMap_dm]
    simp only [Matrix.trace_one, Fintype.card_fin, one_smul]
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one, ← add_smul]
    push_cast
    simp

end X8DM

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8DM

lemma pow_idem {R : Type*} [Ring R] [Algebra ℝ R] (e : R) (he : e * e = e) (a : ℝ) (n : ℕ) :
    (a • (1 : R) + (1 - a) • e) ^ n = a ^ n • (1 : R) + (1 - a ^ n) • e := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, smul_mul_smul, one_mul, mul_one, he, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm]
    rw [pow_succ]
    module

lemma dep_idem (d : ℕ) [NeZero d] : depolarizing d * depolarizing d = depolarizing d := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  ext p q
  rw [Matrix.mul_apply]
  simp only [dep_apply]
  by_cases hp : p.1 = p.2
  · by_cases hq : q.1 = q.2
    · simp only [hp, hq, true_and, and_true, if_true]
      rw [Fintype.sum_prod_type]
      simp only [mul_ite, ite_mul, zero_mul, mul_zero]
      simp [Finset.sum_ite_eq]
      field_simp
    · simp [hq]
  · simp [hp]

lemma dm_eq (d : ℕ) (a : ℝ) :
    depolarizingMixture d a = a • (1 : Map d) + (1 - a) • depolarizing d := rfl

lemma dm_pow (d : ℕ) [NeZero d] (a : ℝ) (n : ℕ) :
    depolarizingMixture d a ^ n = depolarizingMixture d (a ^ n) := by
  rw [dm_eq, dm_eq, pow_idem _ (dep_idem d)]

/-- the quadratic witness -/
lemma not_two_copos (d : ℕ) (hd : 2 ≤ d) (a : ℝ) (ha : 1 / ((d : ℝ) + 1) < a) :
    ¬ TwoCopositive (depolarizingMixture d a) := by
  haveI : NeZero d := ⟨by omega⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  intro h
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  let ψ : Fin d × Fin 2 → ℂ := fun x => if x.1.val = x.2.val then 1 else 0
  have hZ := Matrix.posSemidef_vecMulVec_self_star ψ
  have hW := (h _ hZ).dotProduct_mulVec_nonneg
    (Pi.single (i0, (1 : Fin 2)) 1 - Pi.single (i1, (0 : Fin 2)) 1)
  have hent : ∀ p q : Fin d × Fin 2,
      amplify (depolarizingMixture d a * transposition d) 2 (Matrix.vecMulVec ψ (star ψ)) p q =
        (a : ℂ) * (ψ (q.1, p.2) * star (ψ (p.1, q.2))) +
          ((1 - a : ℝ) : ℂ) * (if p.1 = q.1 then (d : ℂ)⁻¹ else 0) *
            ∑ x : Fin d, ψ (x, p.2) * star (ψ (x, q.2)) := by
    intro p q
    simp only [amplify]
    have hT : ∀ x y : Fin d × Fin d, (depolarizingMixture d a * transposition d) x y =
        depolarizingMixture d a x (y.2, y.1) := by
      intro x y
      rw [Matrix.mul_apply]
      simp only [transposition]
      rw [Finset.sum_eq_single (y.2, y.1)]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    simp only [hT, dm_apply, Matrix.vecMulVec_apply, add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single q.1]
      · rw [Finset.sum_eq_single p.1]
        · simp
        · intro b _ hb
          simp only [Prod.mk.injEq]
          rw [if_neg (by tauto)]; simp
        · simp
      · intro b _ hb
        refine Finset.sum_eq_zero fun c _ => ?_
        simp only [Prod.mk.injEq]
        rw [if_neg (by tauto)]; simp
      · simp
    · by_cases hpq : p.1 = q.1
      · simp only [hpq, true_and, if_true]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single x]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      · simp [hpq]
  -- evaluate the quadratic form
  have key : star (Pi.single (i0, (1 : Fin 2)) (1 : ℂ) - Pi.single (i1, (0 : Fin 2)) 1) ⬝ᵥ
      (amplify (depolarizingMixture d a * transposition d) 2 (Matrix.vecMulVec ψ (star ψ)) *ᵥ
        (Pi.single (i0, (1 : Fin 2)) 1 - Pi.single (i1, (0 : Fin 2)) 1)) =
      ((2 * ((1 - a) / d - a) : ℝ) : ℂ) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    simp only [star_sub, ← Pi.single_star, star_one, sub_dotProduct, dotProduct_sub,
      single_dotProduct, one_mul, Matrix.col_apply]
    simp only [hent]
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have hs : ∀ k k' : Fin 2, (∑ x : Fin d, ψ (x, k) * star (ψ (x, k'))) =
        if k = k' then 1 else 0 := by
      intro k k'
      simp only [ψ, apply_ite star, star_one, star_zero, mul_ite, ite_mul, one_mul, zero_mul, mul_zero]
      rw [Finset.sum_eq_single ⟨k.val, by omega⟩]
      · fin_cases k <;> fin_cases k' <;> simp
      · intro b _ hb
        have : b.val ≠ k.val := fun h => hb (Fin.ext h)
        simp [this]
      · simp
    simp only [hs]
    simp [ψ, i0, i1, h01, Fin.ext_iff]
    push_cast
    ring
  rw [key] at hW
  have : (2 * ((1 - a) / d - a) : ℝ) < 0 := by
    have h1 : 1 < a * ((d : ℝ) + 1) := by
      rw [div_lt_iff₀ (by linarith)] at ha; linarith
    have : (1 - a) / d < a := by
      rw [div_lt_iff₀ hdpos]; linarith
    linarith
  exact absurd (Complex.zero_le_real.mp hW) (not_le.mpr this)

end X8DM

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8DM

/-- entries of beta -/
lemma beta_apply {d : ℕ} (U V : Unitary d) (p q : Fin d × Fin d) :
    beta U V p q = ∑ m : Fin d, (U : Mat d) p.1 m * conj ((U : Mat d) p.2 m) *
      conj ((V : Mat d) q.1 m) * (V : Mat d) q.2 m := by
  have h1 : ∀ j : Fin d × Fin d, (∑ r : Fin d × Fin d, ad (U : Mat d) p r * dephasing d r j) =
      if j.1 = j.2 then ad (U : Mat d) p j else 0 := by
    intro j
    simp only [dephasing]
    rw [Finset.sum_eq_single j]
    · by_cases h : j.1 = j.2 <;> simp [h]
    · intro b _ hb; simp [hb]
    · simp
  simp only [beta, Matrix.mul_apply, h1, ite_mul, zero_mul]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single m]
  · simp [ad, Matrix.conjTranspose_apply]; ring
  · intro b _ hb; simp [Ne.symm hb]
  · simp

/-- general closure: finite convex combination over any Fintype index. -/
lemma mtd_of {d : ℕ} {K : Type*} [Fintype K] (p : K → ℝ) (U V : K → Unitary d)
    (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (t : Map d) (ht : t = ∑ j, p j • beta (U j) (V j)) :
    MTD t := by
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun j => p (e.symm j), fun j => U (e.symm j), fun j => V (e.symm j),
    fun j => hp _, ?_, ?_⟩
  · rw [← hs]; exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  · rw [ht]; exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm

/-! characters -/

abbrev e3 : AddChar (ZMod 3) ℂ := ZMod.stdAddChar

lemma e3_norm (z : ZMod 3) : conj (e3 z) * e3 z = 1 := by
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

lemma sum_e3 (c : ZMod 3) : ∑ t : ZMod 3, e3 (c * t) = if c = 0 then 3 else 0 := by
  have := AddChar.sum_mulShift (ψ := e3) c (ZMod.isPrimitive_stdAddChar 3)
  simp only [ZMod.card] at this
  rw [Finset.sum_congr rfl (fun t _ => by rw [mul_comm]), this]
  split_ifs <;> simp

lemma e3_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 3) :
    e3 (∑ x ∈ s, f x) = ∏ x ∈ s, e3 (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, AddChar.map_add_eq_mul, ih]

/-- the four-point character sum -/
lemma char4 {d : ℕ} (a b c e : Fin d) :
    ∑ s : Fin d → ZMod 3, e3 (s a - s b - s c + s e) =
      if (a = b ∧ c = e) ∨ (a = c ∧ b = e) then (3 : ℂ) ^ d else 0 := by
  let n : Fin d → ℤ := fun x => (if x = a then 1 else 0) - (if x = b then 1 else 0) -
    (if x = c then 1 else 0) + (if x = e then 1 else 0)
  have hlin : ∀ s : Fin d → ZMod 3, s a - s b - s c + s e = ∑ x, (n x : ZMod 3) * s x := by
    intro s
    simp only [n]
    push_cast
    simp only [sub_mul, add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hlin, e3_sum]
  rw [← Fintype.prod_sum (fun x t => e3 ((n x : ZMod 3) * t))]
  simp only [sum_e3]
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hn : ∀ x, ((n x : ZMod 3) = 0 ↔ n x = 0) := by
    intro x
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have : -2 ≤ n x ∧ n x ≤ 2 := by simp only [n]; split_ifs <;> omega
    omega
  simp only [hn]
  congr 1
  apply propext
  constructor
  · intro h
    have ha := h a; have hb := h b; have hc := h c; have he := h e
    simp only [n] at ha hb hc he
    by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hae : a = e <;>
      by_cases hbc : b = c <;> by_cases hbe : b = e <;> by_cases hce : c = e <;>
      simp_all <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) x <;> simp only [n] <;> ring

end X8DM

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8DM

variable {d : ℕ} [NeZero d]

def ι (x : Fin d) : ZMod d := ZMod.finEquiv d x

abbrev ed (d : ℕ) [NeZero d] : AddChar (ZMod d) ℂ := ZMod.stdAddChar

lemma conj_e3 (z : ZMod 3) : conj (e3 z) = e3 (-z) := (AddChar.map_neg_eq_conj _ _).symm

lemma conj_ed (z : ZMod d) : conj (ed d z) = ed d (-z) := (AddChar.map_neg_eq_conj _ _).symm

lemma sum_ed (z : ZMod d) : ∑ m : Fin d, ed d (z * ι m) = if z = 0 then (d : ℂ) else 0 := by
  have := AddChar.sum_mulShift (ψ := ed d) z (ZMod.isPrimitive_stdAddChar d)
  simp only [ZMod.card] at this
  have h2 : ∑ m : Fin d, ed d (z * ι m) = ∑ x : ZMod d, ed d (x * z) :=
    Fintype.sum_equiv (ZMod.finEquiv d).toEquiv _ _ (fun m => by simp [ι, mul_comm])
  rw [h2, this]
  split_ifs <;> simp

lemma ed_norm (z : ZMod d) : conj (ed d z) * ed d z = 1 := by
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

lemma ed_norm' (z : ZMod d) : ed d z * conj (ed d z) = 1 := by
  rw [mul_comm, ed_norm]

lemma ι_inj {x y : Fin d} : ι x = ι y ↔ x = y := (ZMod.finEquiv d).injective.eq_iff

def cF (d : ℕ) : ℝ := (Real.sqrt d)⁻¹

lemma cF_sq : ((cF d : ℝ) : ℂ) * ((cF d : ℝ) : ℂ) = (d : ℂ)⁻¹ := by
  rw [← Complex.ofReal_mul, cF, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  push_cast; rfl

def F (d : ℕ) [NeZero d] : Mat d := fun x m => ((cF d : ℝ) : ℂ) * ed d (ι x * ι m)

lemma F_unit : F d ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [Matrix.mem_unitaryGroup_iff]
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, F, Complex.star_def, map_mul, Complex.conj_ofReal, conj_ed]
  have : ∀ m : Fin d, ((cF d : ℝ) : ℂ) * ed d (ι x * ι m) *
      (((cF d : ℝ) : ℂ) * ed d (-(ι y * ι m))) =
      (d : ℂ)⁻¹ * ed d ((ι x - ι y) * ι m) := by
    intro m
    rw [← cF_sq, mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2; ring
  simp only [this, ← Finset.mul_sum, sum_ed, sub_eq_zero, ι_inj, Matrix.one_apply]
  split_ifs <;> simp [hd]

def D (s : Fin d → ZMod 3) : Mat d := Matrix.diagonal fun x => e3 (s x)

lemma D_unit (s : Fin d → ZMod 3) : D s ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [D, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext x
  simp only [Pi.star_apply, Complex.star_def]
  rw [mul_comm, e3_norm]

def Us (s : Fin d → ZMod 3) : Unitary d :=
  ⟨D s * F d, Submonoid.mul_mem _ (D_unit s) F_unit⟩

lemma Us_apply (s : Fin d → ZMod 3) (x m : Fin d) :
    (Us s : Mat d) x m = e3 (s x) * F d x m := by
  simp [Us, D, Matrix.diagonal_mul]

lemma e3_four (a b c e : ZMod 3) :
    e3 a * conj (e3 b) * conj (e3 c) * e3 e = e3 (a - b - c + e) := by
  rw [conj_e3, conj_e3, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul]
  congr 1; ring

lemma ed_four (a b c e : ZMod d) :
    ed d a * conj (ed d b) * conj (ed d c) * ed d e = ed d (a - b - c + e) := by
  rw [conj_ed, conj_ed, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul]
  congr 1; ring

lemma F4 (p q : Fin d × Fin d) :
    ∑ m : Fin d, F d p.1 m * conj (F d p.2 m) * conj (F d q.1 m) * F d q.2 m =
      if ι p.1 - ι p.2 - ι q.1 + ι q.2 = 0 then (d : ℂ)⁻¹ else 0 := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have : ∀ m : Fin d, F d p.1 m * conj (F d p.2 m) * conj (F d q.1 m) * F d q.2 m =
      ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) * ed d ((ι p.1 - ι p.2 - ι q.1 + ι q.2) * ι m) := by
    intro m
    simp only [F, map_mul, Complex.conj_ofReal]
    rw [← cF_sq]
    have := ed_four (d := d) (ι p.1 * ι m) (ι p.2 * ι m) (ι q.1 * ι m) (ι q.2 * ι m)
    rw [show ι p.1 * ι m - ι p.2 * ι m - ι q.1 * ι m + ι q.2 * ι m =
      (ι p.1 - ι p.2 - ι q.1 + ι q.2) * ι m by ring] at this
    rw [← this]; ring
  simp only [this, ← Finset.mul_sum, sum_ed]
  split_ifs
  · field_simp
  · simp

/-- family 1 -/
lemma L1 (p q : Fin d × Fin d) :
    ∑ s : Fin d → ZMod 3, beta (Us s) (Us s) p q =
      if (p.1 = p.2 ∧ q.1 = q.2) ∨ (p.1 = q.1 ∧ p.2 = q.2) then (3 : ℂ) ^ d * (d : ℂ)⁻¹ else 0 := by
  have : ∀ s : Fin d → ZMod 3, beta (Us s) (Us s) p q =
      e3 (s p.1 - s p.2 - s q.1 + s q.2) *
        ∑ m : Fin d, F d p.1 m * conj (F d p.2 m) * conj (F d q.1 m) * F d q.2 m := by
    intro s
    rw [beta_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Us_apply, map_mul]
    rw [← e3_four]; ring
  simp only [this, ← Finset.sum_mul, char4, F4]
  split_ifs with h1 h2 <;> try simp
  exfalso
  rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> apply h2 <;> rw [h1, h1'] <;> ring

/-- family 2 -/
lemma L2 (p q : Fin d × Fin d) :
    ∑ s : Fin d → ZMod 3, beta (Us s) 1 p q =
      if p.1 = p.2 ∧ q.1 = q.2 then (3 : ℂ) ^ d * (d : ℂ)⁻¹ else 0 := by
  have : ∀ s : Fin d → ZMod 3, beta (Us s) 1 p q =
      (if q.1 = q.2 then 1 else 0) * e3 (s p.1 - s p.2 - s p.1 + s p.1) *
        (F d p.1 q.1 * conj (F d p.2 q.1)) := by
    intro s
    rw [beta_apply, Finset.sum_eq_single q.1]
    · simp only [OneMemClass.coe_one, Matrix.one_apply, if_true, map_one, Us_apply, map_mul]
      rw [show s p.1 - s p.2 - s p.1 + s p.1 = s p.1 - s p.2 by ring, sub_eq_add_neg,
        AddChar.map_add_eq_mul, ← conj_e3]
      by_cases hq : q.1 = q.2
      · simp [hq]; ring
      · have hq' : q.2 ≠ q.1 := fun h => hq h.symm
        simp [hq, hq']
    · intro b _ hb; simp [OneMemClass.coe_one, Matrix.one_apply, Ne.symm hb]
    · simp
  simp only [this]
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [char4]
  by_cases hq : q.1 = q.2
  · by_cases hp : p.1 = p.2
    · simp only [hp, hq, and_self, true_or, if_true, one_mul]
      simp only [F, map_mul, Complex.conj_ofReal]
      rw [mul_mul_mul_comm, cF_sq]
      simp [ed_norm, ed_norm']
    · have : ¬ ((p.1 = p.2 ∧ p.1 = p.1) ∨ (p.1 = p.1 ∧ p.2 = p.1)) := by
        rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact hp h
        · exact hp h.symm
      simp [hp, this, Ne.symm hp]
  · simp [hq]

/-- the dephasing map -/
lemma L3 (p q : Fin d × Fin d) :
    beta (1 : Unitary d) 1 p q = if p.1 = p.2 ∧ p = q then 1 else 0 := by
  rw [beta_apply]
  simp only [OneMemClass.coe_one, Matrix.one_apply, apply_ite (starRingEnd ℂ), map_one, map_zero]
  rw [Finset.sum_eq_single p.1]
  · obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only [Prod.mk.injEq]
    by_cases h1 : p1 = p2 <;> by_cases h2 : p1 = q1 <;> by_cases h3 : p1 = q2 <;>
      simp_all [eq_comm]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma card_fun : Fintype.card (Fin d → ZMod 3) = 3 ^ d := by simp

/-- the decomposition -/
lemma mtd_dm (s : ℝ) (hs0 : 0 ≤ s) (hs1 : ((d : ℝ) + 1) * s ≤ 1) :
    MTD (depolarizingMixture d s) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have h3 : (3 : ℝ) ^ d ≠ 0 := by positivity
  let K := (Fin d → ZMod 3) ⊕ (Fin d → ZMod 3) ⊕ Unit
  let w : K → ℝ := fun j => match j with
    | Sum.inl _ => d * s / 3 ^ d
    | Sum.inr (Sum.inl _) => (1 - (d + 1) * s) / 3 ^ d
    | Sum.inr (Sum.inr _) => s
  let U : K → Unitary d := fun j => match j with
    | Sum.inl t => Us t
    | Sum.inr (Sum.inl t) => Us t
    | Sum.inr (Sum.inr _) => 1
  let V : K → Unitary d := fun j => match j with
    | Sum.inl t => Us t
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr _) => 1
  refine mtd_of w U V ?_ ?_ _ ?_
  · rintro (t | t | t)
    · simp only [w]; positivity
    · simp only [w]; exact div_nonneg (by linarith) (by positivity)
    · simp only [w]; exact hs0
  · simp only [K, Fintype.sum_sum_type, w, Finset.sum_const, Finset.card_univ, card_fun,
      nsmul_eq_mul, Fintype.univ_unit, Finset.sum_singleton, Finset.card_singleton]
    push_cast
    field_simp
    ring
  · ext p q
    simp only [K, Fintype.sum_sum_type, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      Complex.real_smul, w, U, V, Fintype.univ_unit, Finset.sum_singleton]
    rw [← Finset.mul_sum, ← Finset.mul_sum, L1, L2, L3, dm_apply]
    have h3c : (3 : ℂ) ^ d ≠ 0 := by positivity
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only [Prod.mk.injEq]
    push_cast
    split_ifs <;> simp_all <;> (try field_simp) <;> (try ring_nf) <;> (exfalso; aesop)

end X8DM

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8DM

theorem x8_main {d : ℕ} (hd : 2 ≤ d) (a : ℝ)
    (ha : 1 / ((d : ℝ)+1) < a) (ha1 : a < 1) :
    UnitalChannel (depolarizingMixture d a) ∧ Primitive (depolarizingMixture d a) ∧
      Eventually MTD (depolarizingMixture d a) ∧ ¬ TwoCopositive (depolarizingMixture d a) := by
  haveI : NeZero d := ⟨by omega⟩
  have hpos : (0 : ℝ) < 1 / ((d : ℝ) + 1) := by positivity
  have ha0 : 0 < a := lt_trans hpos ha
  refine ⟨unital d a ha0.le ha1.le, primitive d a ha1 (by linarith), ?_, not_two_copos d hd a ha⟩
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one hpos ha1
  refine ⟨max n0 1, le_max_right _ _, fun n hn => ?_⟩
  rw [dm_pow]
  refine mtd_dm _ (pow_nonneg ha0.le _) ?_
  have h1 : a ^ n ≤ a ^ n0 := pow_le_pow_of_le_one ha0.le ha1.le (le_of_max_le_left hn)
  have h2 : a ^ n < 1 / ((d : ℝ) + 1) := lt_of_le_of_lt h1 hn0
  rw [lt_div_iff₀ (by positivity)] at h2
  linarith

end X8DM

end QAlgorithms.Papers.Independent.Information100.P26

section
attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 2 ≤ d) (a : ℝ)
    (ha : 1 / ((d : ℝ)+1) < a) (ha1 : a < 1) :
    UnitalChannel (depolarizingMixture d a) ∧ Primitive (depolarizingMixture d a) ∧
      Eventually MTD (depolarizingMixture d a) ∧ ¬ TwoCopositive (depolarizingMixture d a) :=
  X8DM.x8_main hd a ha ha1

end
