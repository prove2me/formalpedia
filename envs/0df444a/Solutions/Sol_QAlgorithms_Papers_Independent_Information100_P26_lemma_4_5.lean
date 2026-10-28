-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:10:37.005991+00:00
-- url     : https://prove2.me/submissions/3782a41e-6f2c-4627-92f0-c87b2c32b99f

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

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

namespace X8HA

variable {d : ℕ}

instance borelU : BorelSpace (Unitary d) := ⟨rfl⟩

instance cenM : ContinuousENorm (Map d) := SeminormedAddGroup.toContinuousENorm

instance pmM : TopologicalSpace.PseudoMetrizableSpace (Map d) :=
  PseudoEMetricSpace.pseudoMetrizableSpace

instance scM : SecondCountableTopology (Map d) :=
  inferInstanceAs (SecondCountableTopology (Fin d × Fin d → Fin d × Fin d → ℂ))

lemma unit_cpt : IsCompact (Matrix.unitaryGroup (Fin d) ℂ : Set (Mat d)) := by
  have hS : IsCompact (Set.pi Set.univ fun _ : Fin d =>
      Set.pi Set.univ fun _ : Fin d => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hC : IsClosed (Matrix.unitaryGroup (Fin d) ℂ : Set (Mat d)) := by
    have : (Matrix.unitaryGroup (Fin d) ℂ : Set (Mat d)) =
        {U | star U * U = 1} ∩ {U | U * star U = 1} := by
      ext U; exact Unitary.mem_iff
    rw [this]
    exact (isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
      continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const)
  refine hS.of_isClosed_subset hC ?_
  intro U hU
  simp only [Set.mem_pi, Set.mem_univ, Metric.mem_closedBall, dist_zero_right, forall_true_left]
  intro i j
  exact entry_norm_bound_of_unitary hU i j

instance cptU : CompactSpace (Unitary d) := isCompact_iff_compactSpace.mp unit_cpt

lemma integ {f : Unitary d → Map d} (hf : Continuous f) (mu : Measure (Unitary d))
    [IsFiniteMeasure mu] : Integrable f mu :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- integral commutes with ℝ-linear maps -/
lemma int_lin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] (L : Map d →ₗ[ℝ] E) {f : Unitary d → Map d} (mu : Measure (Unitary d))
    (hf : Integrable f mu) : ∫ V, L (f V) ∂mu = L (∫ V, f V ∂mu) := by
  have := ContinuousLinearMap.integral_comp_comm (LinearMap.toContinuousLinearMap L) hf
  exact this

def ev (p q : Fin d × Fin d) : Map d →ₗ[ℝ] ℂ where
  toFun M := M p q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma int_ent {f : Unitary d → Map d} (mu : Measure (Unitary d))
    (hf : Integrable f mu) (p q : Fin d × Fin d) : (∫ V, f V ∂mu) p q = ∫ V, f V p q ∂mu :=
  (int_lin (ev p q) mu hf).symm

def lmul (A : Map d) : Map d →ₗ[ℝ] Map d where
  toFun M := A * M
  map_add' _ _ := Matrix.mul_add _ _ _
  map_smul' _ _ := Matrix.mul_smul _ _ _

def rmul (A : Map d) : Map d →ₗ[ℝ] Map d where
  toFun M := M * A
  map_add' _ _ := Matrix.add_mul _ _ _
  map_smul' _ _ := Matrix.smul_mul _ _ _

lemma int_lmul {f : Unitary d → Map d} (mu : Measure (Unitary d))
    (hf : Integrable f mu) (A : Map d) : ∫ V, A * f V ∂mu = A * ∫ V, f V ∂mu :=
  int_lin (lmul A) mu hf

lemma int_rmul {f : Unitary d → Map d} (mu : Measure (Unitary d))
    (hf : Integrable f mu) (A : Map d) : ∫ V, f V * A ∂mu = (∫ V, f V ∂mu) * A :=
  int_lin (rmul A) mu hf

lemma cont_coe : Continuous (fun V : Unitary d => (V : Mat d)) := continuous_subtype_val

lemma cont_ad {g : Unitary d → Mat d} (hg : Continuous g) :
    Continuous (fun V => ad (g V)) := by
  unfold ad
  refine continuous_pi fun p => continuous_pi fun q => ?_
  exact ((hg.matrix_elem _ _).mul (Complex.continuous_conj.comp (hg.matrix_elem _ _)))

lemma cont_ad_coe : Continuous (fun V : Unitary d => ad (V : Mat d)) := cont_ad cont_coe

lemma cont_ad_star : Continuous (fun V : Unitary d => ad (V : Mat d)ᴴ) :=
  cont_ad cont_coe.matrix_conjTranspose

/-- left invariance -/
lemma int_left (mu : Measure (Unitary d))
    (hmu : ∀ U : Unitary d, Measure.map (fun V => U * V) mu = mu)
    {f : Unitary d → Map d} (hf : Continuous f) (W : Unitary d) :
    ∫ V, f (W * V) ∂mu = ∫ V, f V ∂mu := by
  have hm : Measurable (fun V : Unitary d => W * V) := (continuous_const_mul W).measurable
  conv_rhs => rw [← hmu W]
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8HA

variable {d : ℕ}

lemma ad_apply (B : Mat d) (p q : Fin d × Fin d) : ad B p q = B p.1 q.1 * conj (B p.2 q.2) := rfl

lemma ad_mul (A B : Mat d) : ad A * ad B = ad (A * B) := by
  ext p q
  simp only [Matrix.mul_apply, ad_apply, map_sum, map_mul, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma ad_one : ad (1 : Mat d) = 1 := by
  ext p q
  simp only [ad_apply, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

lemma uU (U : Unitary d) : (U : Mat d) * (U : Mat d)ᴴ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp U.2
  rwa [Matrix.star_eq_conjTranspose] at this

lemma Uu (U : Unitary d) : (U : Mat d)ᴴ * (U : Mat d) = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp U.2
  rwa [Matrix.star_eq_conjTranspose] at this

lemma adUU (U : Unitary d) : ad (U : Mat d) * ad (U : Mat d)ᴴ = 1 := by
  rw [ad_mul, uU, ad_one]

lemma adUU' (U : Unitary d) : ad (U : Mat d)ᴴ * ad (U : Mat d) = 1 := by
  rw [ad_mul, Uu, ad_one]

/-- trace preserving, unital -/
def TPm (M : Map d) : Prop := ∀ q : Fin d × Fin d, ∑ i, M (i,i) q = if q.1 = q.2 then 1 else 0

def Um (M : Map d) : Prop := ∀ p : Fin d × Fin d, ∑ i, M p (i,i) = if p.1 = p.2 then 1 else 0

lemma sum_diag (f : Fin d × Fin d → ℂ) :
    ∑ r : Fin d × Fin d, (if r.1 = r.2 then (1 : ℂ) else 0) * f r = ∑ j, f (j, j) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x] <;> simp_all [eq_comm]

lemma sum_diag' (f : Fin d × Fin d → ℂ) :
    ∑ r : Fin d × Fin d, f r * (if r.1 = r.2 then (1 : ℂ) else 0) = ∑ j, f (j, j) := by
  rw [← sum_diag]; exact Finset.sum_congr rfl fun r _ => mul_comm _ _

lemma tp_mul {M N : Map d} (hM : TPm M) (hN : TPm N) : TPm (M * N) := by
  intro q
  calc ∑ i, (M * N) (i, i) q = ∑ i, ∑ r, M (i, i) r * N r q :=
        Finset.sum_congr rfl fun i _ => Matrix.mul_apply
    _ = ∑ r, (∑ i, M (i, i) r) * N r q := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun r _ => (Finset.sum_mul _ _ _).symm
    _ = ∑ r : Fin d × Fin d, (if r.1 = r.2 then (1 : ℂ) else 0) * N r q :=
        Finset.sum_congr rfl fun r _ => by rw [hM r]
    _ = _ := by rw [sum_diag]; exact hN q

lemma un_mul {M N : Map d} (hM : Um M) (hN : Um N) : Um (M * N) := by
  intro p
  calc ∑ i, (M * N) p (i, i) = ∑ i, ∑ r, M p r * N r (i, i) :=
        Finset.sum_congr rfl fun i _ => Matrix.mul_apply
    _ = ∑ r, M p r * (∑ i, N r (i, i)) := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun r _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ r : Fin d × Fin d, M p r * (if r.1 = r.2 then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl fun r _ => by rw [hN r]
    _ = _ := by rw [sum_diag']; exact hM p

lemma tp_ad (B : Mat d) (h : Bᴴ * B = 1) : TPm (ad B) := by
  intro q
  have := congrFun (congrFun h q.2) q.1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
  have e : (if q.1 = q.2 then (1 : ℂ) else 0) = if q.2 = q.1 then 1 else 0 := by
    simp only [eq_comm]
  rw [e, ← this]
  exact Finset.sum_congr rfl fun i _ => by rw [ad_apply, Complex.star_def]; ring

lemma un_ad (B : Mat d) (h : B * Bᴴ = 1) : Um (ad B) := by
  intro p
  have := congrFun (congrFun h p.1) p.2
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
  simp only [ad_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => by rw [Complex.star_def]

lemma tp_adU (U : Unitary d) : TPm (ad (U : Mat d)) := tp_ad _ (Uu U)
lemma un_adU (U : Unitary d) : Um (ad (U : Mat d)) := un_ad _ (uU U)
lemma tp_adU' (U : Unitary d) : TPm (ad (U : Mat d)ᴴ) := tp_ad _ (by rw [Matrix.conjTranspose_conjTranspose, uU])
lemma un_adU' (U : Unitary d) : Um (ad (U : Mat d)ᴴ) := un_ad _ (by rw [Matrix.conjTranspose_conjTranspose, Uu])

lemma dep_mul {M : Map d} (hM : TPm M) : depolarizing d * M = depolarizing d := by
  ext p q
  simp only [Matrix.mul_apply, X8DM.dep_apply]
  rw [Fintype.sum_prod_type]
  by_cases hp : p.1 = p.2
  · simp only [hp, true_and, ite_mul, zero_mul]
    have : ∀ x : Fin d, (∑ y : Fin d, if x = y then (d : ℂ)⁻¹ * M (x, y) q else 0) =
        (d : ℂ)⁻¹ * M (x, x) q := fun x => by simp
    simp only [this, ← Finset.mul_sum, hM q]
    split_ifs <;> simp
  · simp [hp]

lemma mul_dep {M : Map d} (hM : Um M) : M * depolarizing d = depolarizing d := by
  ext p q
  simp only [Matrix.mul_apply, X8DM.dep_apply]
  rw [Fintype.sum_prod_type]
  by_cases hq : q.1 = q.2
  · simp only [hq, and_true, mul_ite, mul_zero]
    have : ∀ x : Fin d, (∑ y : Fin d, if x = y then M p (x, y) * (d : ℂ)⁻¹ else 0) =
        M p (x, x) * (d : ℂ)⁻¹ := fun x => by simp
    simp only [this, ← Finset.sum_mul, hM p]
    split_ifs <;> simp
  · simp [hq]

lemma un_deph : Um (dephasing d) := by
  intro p
  simp only [dephasing, Prod.ext_iff]
  by_cases hp : p.1 = p.2
  · rw [Finset.sum_eq_single p.1]
    · simp [hp]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · simp [hp]

lemma tp_deph : TPm (dephasing d) := by
  intro q
  simp only [dephasing, Prod.ext_iff]
  by_cases hq : q.1 = q.2
  · rw [Finset.sum_eq_single q.1]
    · simp [hq]
    · intro b _ hb; simp [hb]
    · simp
  · simp only [hq, if_false]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h
    · exact absurd (h.2.1.symm.trans h.2.2) hq
    · rfl

lemma un_dep [NeZero d] : Um (depolarizing d) := by
  intro p
  simp only [X8DM.dep_apply, and_true]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  split_ifs <;> simp [hd]

lemma tp_dep [NeZero d] : TPm (depolarizing d) := by
  intro q
  simp only [X8DM.dep_apply, true_and]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  split_ifs <;> simp [hd]

lemma tp_one : TPm (1 : Map d) := by
  intro q
  simp only [Matrix.one_apply, Prod.ext_iff]
  by_cases hq : q.1 = q.2
  · rw [Finset.sum_eq_single q.1] <;> simp_all [eq_comm]
  · simp only [hq, if_false]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h
    · exact absurd (h.1.symm.trans h.2) hq
    · rfl

lemma un_one : Um (1 : Map d) := by
  intro p
  simp only [Matrix.one_apply, Prod.ext_iff]
  by_cases hp : p.1 = p.2
  · rw [Finset.sum_eq_single p.1] <;> simp_all [eq_comm]
  · simp only [hp, if_false]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h
    · exact absurd (h.1.trans h.2.symm) hp
    · rfl

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8HA

variable {d : ℕ}

lemma ad_diag (v : Fin d → ℂ) (p r : Fin d × Fin d) :
    ad (Matrix.diagonal v) p r = if p = r then v p.1 * conj (v p.2) else 0 := by
  simp only [ad_apply, Matrix.diagonal_apply, Prod.ext_iff]
  split_ifs <;> simp_all

lemma comm_diag {R : Map d} (v : Fin d → ℂ)
    (h : ad (Matrix.diagonal v) * R = R * ad (Matrix.diagonal v)) (p q : Fin d × Fin d) :
    v p.1 * conj (v p.2) * R p q = R p q * (v q.1 * conj (v q.2)) := by
  have := congrFun (congrFun h p) q
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single p, Finset.sum_eq_single q] at this
  · simpa [ad_diag] using this
  · intro b _ hb; rw [ad_diag, if_neg hb, mul_zero]
  · simp
  · intro b _ hb; rw [ad_diag, if_neg (Ne.symm hb), zero_mul]
  · simp

def ind (k x : Fin d) : ZMod 3 := if x = k then 1 else 0

lemma e3_pair (s : Fin d → ZMod 3) (a b : Fin d) :
    X8DM.e3 (s a) * conj (X8DM.e3 (s b)) = X8DM.e3 (s a - s b) := by
  rw [X8DM.conj_e3, ← AddChar.map_add_eq_mul, sub_eq_add_neg]

variable [NeZero d]

def DU (s : Fin d → ZMod 3) : Unitary d := ⟨X8DM.D s, X8DM.D_unit s⟩

lemma sup {R : Map d} (hR : ∀ W : Unitary d, ad (W : Mat d) * R = R * ad (W : Mat d))
    (p q : Fin d × Fin d) (h : R p q ≠ 0) : p = q ∨ (p.1 = p.2 ∧ q.1 = q.2) := by
  have key : ∀ k : Fin d, ind k p.1 - ind k p.2 = ind k q.1 - ind k q.2 := by
    intro k
    have := comm_diag (fun x => X8DM.e3 (ind k x)) (hR (DU (ind k))) p q
    simp only [e3_pair] at this
    rw [mul_comm] at this
    have := mul_left_cancel₀ h this
    exact ZMod.injective_stdAddChar this
  have h1 := key p.1
  have h2 := key p.2
  have h3 := key q.1
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [ind] at h1 h2 h3
  simp only [Prod.mk.injEq]
  by_cases e12 : p1 = p2
  · subst e12
    right
    refine ⟨rfl, ?_⟩
    by_contra hq
    simp only [sub_self, if_true, Ne.symm hq, if_false] at h3
    revert h3; decide
  · left
    have ne : p2 ≠ p1 := Ne.symm e12
    simp only [if_true, ne, e12, if_false, sub_zero, zero_sub] at h1 h2
    refine ⟨?_, ?_⟩
    · by_contra c
      rw [if_neg (show ¬ q1 = p1 from fun e => c e.symm)] at h1
      split_ifs at h1 <;> revert h1 <;> decide
    · by_contra c
      rw [if_neg (show ¬ q2 = p2 from fun e => c e.symm)] at h2
      split_ifs at h2 <;> revert h2 <;> decide

def Pm (σ : Equiv.Perm (Fin d)) : Mat d := fun i j => if i = σ j then 1 else 0

omit [NeZero d] in
lemma Pm_unit (σ : Equiv.Perm (Fin d)) : Pm σ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ i)]
  · simp [Pm, Matrix.one_apply, Matrix.star_apply]
  · intro b _ hb; simp [Pm, Matrix.star_apply, hb]
  · simp

omit [NeZero d] in
lemma ad_Pm (σ : Equiv.Perm (Fin d)) (p r : Fin d × Fin d) :
    ad (Pm σ) p r = if p.1 = σ r.1 ∧ p.2 = σ r.2 then 1 else 0 := by
  simp only [ad_apply, Pm]
  split_ifs <;> simp_all

omit [NeZero d] in
lemma perm_inv {R : Map d} (hR : ∀ W : Unitary d, ad (W : Mat d) * R = R * ad (W : Mat d))
    (σ : Equiv.Perm (Fin d)) (p q : Fin d × Fin d) :
    R (σ p.1, σ p.2) (σ q.1, σ q.2) = R p q := by
  have := congrFun (congrFun (hR ⟨Pm σ, Pm_unit σ⟩) (σ p.1, σ p.2)) q
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single p,
    Finset.sum_eq_single (σ q.1, σ q.2)] at this
  · simpa [ad_Pm] using this.symm
  · intro b _ hb; rw [ad_Pm, if_neg, mul_zero]
    rintro ⟨h1, h2⟩; exact hb (Prod.ext h1 h2)
  · simp
  · intro b _ hb; rw [ad_Pm, if_neg, zero_mul]
    rintro ⟨h1, h2⟩; exact hb (Prod.ext (σ.injective h1).symm (σ.injective h2).symm)
  · simp

omit [NeZero d] in
lemma ex_perm2 {i j k l : Fin d} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ σ : Equiv.Perm (Fin d), σ i = k ∧ σ j = l := by
  refine ⟨(Equiv.swap i k).trans (Equiv.swap (Equiv.swap i k j) l), ?_, ?_⟩
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    have h1 : k ≠ Equiv.swap i k j := by
      intro h
      have : Equiv.swap i k i = Equiv.swap i k j := by rw [Equiv.swap_apply_left]; exact h
      exact hij ((Equiv.swap i k).injective this)
    exact Equiv.swap_apply_of_ne_of_ne h1 hkl
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]

section shape

variable {R : Map d} (hR : ∀ W : Unitary d, ad (W : Mat d) * R = R * ad (W : Mat d))
  (i1 : Fin d) (h01 : (0 : Fin d) ≠ i1)
include hR h01

lemma off_const {x y : Fin d} (hxy : x ≠ y) : R (x, y) (x, y) = R (0, i1) (0, i1) := by
  obtain ⟨σ, h1, h2⟩ := ex_perm2 h01 hxy
  have := perm_inv hR σ (0, i1) (0, i1)
  simpa [h1, h2] using this

omit h01 in
lemma diag_const (x : Fin d) : R (x, x) (x, x) = R (0, 0) (0, 0) := by
  have := perm_inv hR (Equiv.swap 0 x) (0, 0) (0, 0)
  simpa using this

lemma cross_const {x y : Fin d} (hxy : x ≠ y) : R (x, x) (y, y) = R (i1, i1) (0, 0) := by
  obtain ⟨σ, h1, h2⟩ := ex_perm2 (Ne.symm h01) hxy
  have := perm_inv hR σ (i1, i1) (0, 0)
  simpa [h1, h2] using this

lemma shape (p q : Fin d × Fin d) :
    R p q = if p = q ∧ p.1 ≠ p.2 then R (0, i1) (0, i1) else
      if p.1 = p.2 ∧ q.1 = q.2 then (if p.1 = q.1 then R (0, 0) (0, 0) else R (i1, i1) (0, 0))
      else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases c1 : (p1, p2) = (q1, q2) ∧ p1 ≠ p2
  · rw [if_pos c1]
    obtain ⟨e, ne⟩ := c1
    rw [← e]; exact off_const hR i1 h01 ne
  · rw [if_neg c1]
    by_cases c2 : p1 = p2 ∧ q1 = q2
    · rw [if_pos c2]
      obtain ⟨e1, e2⟩ := c2
      subst e1; subst e2
      by_cases c3 : p1 = q1
      · rw [if_pos c3]; subst c3; exact diag_const hR p1
      · rw [if_neg c3]; exact cross_const hR i1 h01 c3
    · rw [if_neg c2]
      by_contra h
      rcases sup hR _ _ h with e | e
      · apply c2
        have : p1 = p2 := by
          by_contra ne; exact c1 ⟨e, ne⟩
        simp only [Prod.mk.injEq] at e
        exact ⟨this, e.1 ▸ e.2 ▸ this⟩
      · exact c2 e

end shape

def FU : Unitary d := ⟨X8DM.F d, X8DM.F_unit⟩

lemma ι0 : X8DM.ι (0 : Fin d) = 0 := by simp [X8DM.ι]

lemma F0 (j : Fin d) : X8DM.F d 0 j = ((X8DM.cF d : ℝ) : ℂ) := by
  simp [X8DM.F, ι0]

lemma F_0 (j : Fin d) : X8DM.F d j 0 = ((X8DM.cF d : ℝ) : ℂ) := by
  simp [X8DM.F, ι0]

lemma sumF {y : Fin d} (hy : y ≠ 0) : ∑ j, conj (X8DM.F d y j) = 0 := by
  have h : ∀ j, conj (X8DM.F d y j) = ((X8DM.cF d : ℝ) : ℂ) * X8DM.ed d (-X8DM.ι y * X8DM.ι j) := by
    intro j
    simp only [X8DM.F, map_mul, Complex.conj_ofReal, X8DM.conj_ed, neg_mul]
  rw [Finset.sum_congr rfl fun j _ => h j, ← Finset.mul_sum, X8DM.sum_ed]
  have : -X8DM.ι y ≠ 0 := by
    rw [neg_ne_zero, ← ι0]; exact fun e => hy (X8DM.ι_inj.mp e)
  rw [if_neg this, mul_zero]


lemma cF_ne : ((X8DM.cF d : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < X8DM.cF d := by
    unfold X8DM.cF
    have : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
    positivity
  exact_mod_cast this.ne'

section frel

variable {R : Map d} (hR : ∀ W : Unitary d, ad (W : Mat d) * R = R * ad (W : Mat d))
  (i1 : Fin d) (h01 : (0 : Fin d) ≠ i1)
include hR h01

lemma col0 (r1 r2 : Fin d) :
    R (r1, r2) (0, 0) = if r1 = r2 then
      (if r1 = 0 then R (0, 0) (0, 0) else R (i1, i1) (0, 0)) else 0 := by
  rw [shape hR i1 h01]
  by_cases h : r1 = r2
  · subst h; simp
  · rw [if_neg (fun c => h ((Prod.mk.inj c.1).1.trans (Prod.mk.inj c.1).2.symm)),
      if_neg (fun c => h c.1), if_neg h]

lemma row0 (r : Fin d × Fin d) :
    R (0, i1) r = if r = (0, i1) then R (0, i1) (0, i1) else 0 := by
  rw [shape hR i1 h01]
  by_cases h : r = (0, i1)
  · subst h; simp [h01]
  · rw [if_neg (fun c => h c.1.symm), if_neg (fun c => h01 c.1), if_neg h]

lemma frel : R (0, i1) (0, i1) = R (0, 0) (0, 0) - R (i1, i1) (0, 0) := by
  have h := congrFun (congrFun (hR FU) (0, i1)) (0, 0)
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  have hFU : ((FU : Unitary d) : Mat d) = X8DM.F d := rfl
  have hL : ∑ r, ad ((FU : Unitary d) : Mat d) (0, i1) r * R r (0, 0) =
      ((X8DM.cF d : ℝ) : ℂ) * ((X8DM.cF d : ℝ) : ℂ) * (R (0, 0) (0, 0) - R (i1, i1) (0, 0)) := by
    rw [Fintype.sum_prod_type]
    have e : ∀ x y : Fin d, ad ((FU : Unitary d) : Mat d) (0, i1) (x, y) * R (x, y) (0, 0) =
        if x = y then ((X8DM.cF d : ℝ) : ℂ) * conj (X8DM.F d i1 x) *
          (R (i1, i1) (0, 0) + if x = 0 then R (0, 0) (0, 0) - R (i1, i1) (0, 0) else 0)
        else 0 := by
      intro x y
      rw [col0 hR i1 h01, ad_apply, hFU, F0]
      by_cases hxy : x = y
      · subst hxy; rw [if_pos rfl, if_pos rfl]
        by_cases hx : x = 0
        · rw [if_pos hx, if_pos hx]; ring
        · rw [if_neg hx, if_neg hx]; ring
      · rw [if_neg hxy, if_neg hxy, mul_zero]
    simp only [e, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_add, Finset.sum_add_distrib,
      mul_ite, mul_zero, Finset.sum_ite_eq']
    rw [← Finset.sum_mul, ← Finset.mul_sum, sumF (Ne.symm h01), F_0]
    simp only [Complex.conj_ofReal]; ring
  have hRt : ∑ r, R (0, i1) r * ad ((FU : Unitary d) : Mat d) r (0, 0) =
      R (0, i1) (0, i1) * (((X8DM.cF d : ℝ) : ℂ) * ((X8DM.cF d : ℝ) : ℂ)) := by
    rw [Finset.sum_eq_single (0, i1)]
    · rw [ad_apply, hFU, F_0, F_0, Complex.conj_ofReal]
    · intro b _ hb; rw [row0 hR i1 h01 b, if_neg hb, zero_mul]
    · simp
  rw [hL, hRt] at h
  have hc : ((X8DM.cF d : ℝ) : ℂ) * ((X8DM.cF d : ℝ) : ℂ) ≠ 0 := mul_ne_zero cF_ne cF_ne
  apply mul_right_cancel₀ hc
  rw [← h]; ring

end frel

theorem cls (hd : 2 ≤ d) {R : Map d}
    (hR : ∀ W : Unitary d, ad (W : Mat d) * R = R * ad (W : Mat d)) :
    ∃ a b : ℂ, R = a • (1 : Map d) + b • depolarizing d := by
  let i1 : Fin d := ⟨1, by omega⟩
  have h01 : (0 : Fin d) ≠ i1 := by
    intro h; have := congrArg Fin.val h; simp [i1] at this
  have hdc : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hf := frel hR i1 h01
  refine ⟨R (0, i1) (0, i1), (d : ℂ) * R (i1, i1) (0, 0), ?_⟩
  ext p q
  rw [shape hR i1 h01 p q]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, X8DM.dep_apply, smul_eq_mul]
  by_cases c1 : p = q ∧ p.1 ≠ p.2
  · rw [if_pos c1, if_pos c1.1, if_neg (fun c => c1.2 c.1)]; ring
  · rw [if_neg c1]
    by_cases c2 : p.1 = p.2 ∧ q.1 = q.2
    · rw [if_pos c2, if_pos c2]
      by_cases c3 : p.1 = q.1
      · have : p = q := Prod.ext c3 (c2.1.symm.trans (c3.trans c2.2))
        rw [if_pos c3, if_pos this, hf]; field_simp; ring
      · have : p ≠ q := fun e => c3 (congrArg Prod.fst e)
        rw [if_neg c3, if_neg this]; field_simp; ring
    · have : p ≠ q := by
        rintro rfl
        exact c2 ⟨by by_contra ne; exact c1 ⟨rfl, ne⟩, by by_contra ne; exact c1 ⟨rfl, ne⟩⟩
      rw [if_neg c2, if_neg this, if_neg c2]; ring

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

namespace X8HA

variable {d : ℕ}

lemma integ_ent {f : Unitary d → Map d} {mu : Measure (Unitary d)} (hf : Integrable f mu)
    (p q : Fin d × Fin d) : Integrable (fun V => f V p q) mu :=
  (LinearMap.toContinuousLinearMap (ev p q)).integrable_comp hf

lemma int_cst (mu : Measure (Unitary d)) [IsProbabilityMeasure mu] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (A : E) : ∫ _V, A ∂mu = A := by
  rw [integral_const, probReal_univ, one_smul]

lemma int_tp {mu : Measure (Unitary d)} [IsProbabilityMeasure mu] {f : Unitary d → Map d}
    (hf : Integrable f mu) (h : ∀ V, TPm (f V)) : TPm (∫ V, f V ∂mu) := by
  intro q
  rw [Finset.sum_congr rfl fun i _ => int_ent mu hf (i, i) q,
    ← integral_finsetSum _ fun i _ => integ_ent hf (i, i) q]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun V => h V q)]
  exact int_cst mu _

lemma int_un {mu : Measure (Unitary d)} [IsProbabilityMeasure mu] {f : Unitary d → Map d}
    (hf : Integrable f mu) (h : ∀ V, Um (f V)) : Um (∫ V, f V ∂mu) := by
  intro p
  rw [Finset.sum_congr rfl fun i _ => int_ent mu hf p (i, i),
    ← integral_finsetSum _ fun i _ => integ_ent hf p (i, i)]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun V => h V p)]
  exact int_cst mu _

lemma coe_mulU (W V : Unitary d) : ((W * V : Unitary d) : Mat d) = (W : Mat d) * V := rfl

def col (T : Map d) (q : Fin d × Fin d) : Mat d := Matrix.of fun i j => T (i, j) q

lemma adT (W : Mat d) (T : Map d) (a b : Fin d) (q : Fin d × Fin d) :
    (ad W * T) (a, b) q = (W * col T q * Wᴴ) a b := by
  simp only [Matrix.mul_apply, ad_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    Finset.sum_mul, col, Matrix.of_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
    rw [Complex.star_def]; ring

variable [NeZero d]

lemma scal {X : Mat d} (hX : ∀ W : Unitary d, (W : Mat d) * X * (W : Mat d)ᴴ = X) (i j : Fin d) :
    X i j = if i = j then X 0 0 else 0 := by
  have hc : ∀ W : Unitary d, (W : Mat d) * X = X * W := by
    intro W
    have := congrArg (· * (W : Mat d)) (hX W)
    simp only [Matrix.mul_assoc, Uu, Matrix.mul_one] at this
    exact this
  have hoff : ∀ i j : Fin d, i ≠ j → X i j = 0 := by
    intro i j hij
    have := congrFun (congrFun (hc (DU (ind i))) i) j
    simp only [DU, X8DM.D, Matrix.diagonal_mul, Matrix.mul_diagonal, ind, if_pos rfl,
      if_neg (Ne.symm hij), if_true] at this
    have h1 : X8DM.e3 1 ≠ X8DM.e3 0 := fun e => absurd (ZMod.injective_stdAddChar e) (by decide)
    by_contra hne
    exact h1 (mul_right_cancel₀ hne (this.trans (mul_comm _ _)))
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have := congrFun (congrFun (hc FU) 0) i
    have hFU : ((FU : Unitary d) : Mat d) = X8DM.F d := rfl
    rw [hFU, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single i,
      Finset.sum_eq_single 0, F0] at this
    · exact mul_left_cancel₀ cF_ne (this.trans (mul_comm _ _))
    · intro b _ hb; rw [hoff 0 b (Ne.symm hb), zero_mul]
    · simp
    · intro b _ hb; rw [hoff b i hb, mul_zero]
    · simp
  · rw [if_neg hij]; exact hoff i j hij

omit [NeZero d] in
lemma col_fix {T : Map d} (inv : ∀ W : Unitary d, ad (W : Mat d) * T = T) (q : Fin d × Fin d)
    (W : Unitary d) : (W : Mat d) * col T q * (W : Mat d)ᴴ = col T q := by
  ext a b
  rw [← adT, inv W]
  rfl

variable (mu : Measure (Unitary d)) (hmu : NormalizedHaar mu)
include hmu

lemma twirl1 : ∫ V, ad (V : Mat d) ∂mu = depolarizing d := by
  haveI := hmu.1
  have hI := integ (cont_ad_coe (d := d)) mu
  set T := ∫ V, ad (V : Mat d) ∂mu with hT
  have inv : ∀ W : Unitary d, ad (W : Mat d) * T = T := by
    intro W
    rw [hT, ← int_lmul mu hI]
    simp only [ad_mul]
    exact int_left mu hmu.2 (f := fun V => ad (V : Mat d)) cont_ad_coe W
  have htp : TPm T := int_tp hI fun V => tp_adU V
  clear_value T
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  ext p q
  have hs := scal (col_fix inv q) p.1 p.2
  have hsum := htp q
  have : ∀ i : Fin d, T (i, i) q = T (0, 0) q := fun i => by
    have := scal (col_fix inv q) i i
    simpa [col] using this
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have e1 : T p q = col T q p.1 p.2 := rfl
  have e2 : col T q 0 0 = T (0, 0) q := rfl
  rw [e1, hs, e2, X8DM.dep_apply]
  by_cases hp : p.1 = p.2
  · rw [if_pos hp]
    by_cases hq : q.1 = q.2
    · rw [if_pos hq] at hsum; rw [if_pos ⟨hp, hq⟩]; field_simp; rw [mul_comm]; exact hsum
    · rw [if_neg hq] at hsum; rw [if_neg (fun c => hq c.2)]
      exact (mul_eq_zero.mp hsum).resolve_left hd
  · rw [if_neg hp, if_neg (fun c => hp c.1)]


lemma twirl2 : ∫ V, ad (V : Mat d)ᴴ ∂mu = depolarizing d := by
  haveI := hmu.1
  have hI := integ (cont_ad_star (d := d)) mu
  have hI1 := integ (cont_ad_coe (d := d)) mu
  set T := ∫ V, ad (V : Mat d)ᴴ ∂mu with hT
  have inv : ∀ W : Unitary d, T * ad (W : Mat d)ᴴ = T := by
    intro W
    rw [hT, ← int_rmul mu hI]
    simp only [ad_mul]
    have := int_left mu hmu.2 (f := fun V => ad (V : Mat d)ᴴ) cont_ad_star W
    simp only [coe_mulU, Matrix.conjTranspose_mul] at this
    exact this
  have hun : Um T := int_un hI fun V => un_adU' V
  have h1 : T * ∫ V, ad (V : Mat d) ∂mu = T := by
    rw [← int_lmul mu hI1]
    have : ∀ U : Unitary d, T * ad (U : Mat d) = T := by
      intro U
      have := inv (star U)
      rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose] at this
    simp only [this]
    exact int_cst mu T
  clear_value T
  rw [twirl1 mu hmu, mul_dep hun] at h1
  exact h1.symm

lemma twirl_cov (Φ : Map d) (W : Unitary d) :
    ad (W : Mat d) * (∫ V, ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ ∂mu) =
      (∫ V, ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ ∂mu) * ad (W : Mat d) := by
  haveI := hmu.1
  have hc : Continuous (fun V : Unitary d => ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ) :=
    (cont_ad_coe.matrix_mul continuous_const).matrix_mul cont_ad_star
  have hI := integ hc mu
  have hc2 : Continuous (fun V : Unitary d =>
      ad (W : Mat d) * (ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ)) := continuous_const.matrix_mul hc
  have key : ad (W : Mat d) * (∫ V, ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ ∂mu) * ad (W : Mat d)ᴴ =
      ∫ V, ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ ∂mu := by
    rw [← int_lmul mu hI, ← int_rmul mu (integ hc2 mu)]
    have e : ∀ V : Unitary d, ad (W : Mat d) * (ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ) *
        ad (W : Mat d)ᴴ = ad ((W * V : Unitary d) : Mat d) * Φ * ad ((W * V : Unitary d) : Mat d)ᴴ := by
      intro V
      rw [coe_mulU, Matrix.conjTranspose_mul, ← ad_mul, ← ad_mul]
      simp only [Matrix.mul_assoc]
    simp only [e]
    exact int_left mu hmu.2 (f := fun V => ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ) hc W
  calc ad (W : Mat d) * (∫ V, ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ ∂mu)
      = ad (W : Mat d) * (∫ V, ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ ∂mu) *
          (ad (W : Mat d)ᴴ * ad (W : Mat d)) := by rw [adUU', Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, key]

omit hmu in
lemma trace_dep : Matrix.trace (depolarizing d) = 1 := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simp only [Matrix.trace, Matrix.diag, X8DM.dep_apply, Fintype.sum_prod_type, and_self]
  simp [Finset.sum_ite_eq, hd]

omit hmu in
lemma un00 (a b : ℂ) :
    ∑ i : Fin d, (a • (1 : Map d) + b • depolarizing d) (0, 0) (i, i) = a + b := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, X8DM.dep_apply, smul_eq_mul,
    Finset.sum_add_distrib, Prod.mk.injEq, and_self, true_and, if_true]
  simp [Finset.sum_ite_eq]
  field_simp

omit hmu in
lemma tr_comb (a b : ℂ) :
    Matrix.trace (a • (1 : Map d) + b • depolarizing d) = a * (d : ℂ) ^ 2 + b := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, trace_dep]
  simp [Fintype.card_prod, sq]

lemma twirl_val (hd : 2 ≤ d) (Φ : Map d) (hΦ : Um Φ) :
    (∫ V, ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ ∂mu) =
      ((Matrix.trace Φ - 1) / ((d : ℂ) ^ 2 - 1)) • (1 : Map d) +
        (1 - (Matrix.trace Φ - 1) / ((d : ℂ) ^ 2 - 1)) • depolarizing d := by
  haveI := hmu.1
  have hc : Continuous (fun V : Unitary d => ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ) :=
    (cont_ad_coe.matrix_mul continuous_const).matrix_mul cont_ad_star
  have hI := integ hc mu
  obtain ⟨a, b, hR⟩ := cls hd (twirl_cov mu hmu Φ)
  have hun := int_un hI (fun V => un_mul (un_mul (un_adU V) hΦ) (un_adU' V))
  have htr : Matrix.trace (∫ V, ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ ∂mu) = Matrix.trace Φ := by
    have := int_lin (Matrix.traceLinearMap (Fin d × Fin d) ℝ ℂ) mu hI
    simp only [Matrix.traceLinearMap_apply] at this
    rw [← this]
    have e : ∀ V : Unitary d, Matrix.trace (ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ) = Matrix.trace Φ := by
      intro V; rw [Matrix.trace_mul_cycle, adUU', Matrix.one_mul]
    simp only [e]
    exact int_cst mu _
  rw [hR] at hun htr ⊢
  have h1 := hun (0, 0)
  rw [un00] at h1
  simp only [if_true] at h1
  rw [tr_comb] at htr
  have hd1 : (d : ℂ) ^ 2 - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have : ((d : ℝ) ^ 2 - 1 : ℝ) ≠ 0 := by nlinarith
    exact_mod_cast this
  have ha : a = (Matrix.trace Φ - 1) / ((d : ℂ) ^ 2 - 1) := by
    rw [eq_div_iff hd1]; linear_combination htr - h1
  have hb : b = 1 - a := by linear_combination h1
  rw [hb, ha]

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

namespace X8HA

variable {d : ℕ}

lemma rsmul (r : ℝ) (M : Map d) : r • M = (r : ℂ) • M := by
  ext p q; simp [Complex.real_smul]

lemma tr_real (U : Unitary d) :
    Matrix.trace (dephasing d * ad (U : Mat d)ᴴ) =
      ((∑ i, Complex.normSq ((U : Mat d)ᴴ i i) : ℝ) : ℂ) := by
  have e : ∀ p : Fin d × Fin d, (dephasing d * ad (U : Mat d)ᴴ) p p =
      if p.1 = p.2 then ad (U : Mat d)ᴴ p p else 0 := by
    intro p
    rw [Matrix.mul_apply, Finset.sum_eq_single p]
    · simp only [dephasing, and_true]; split_ifs <;> simp
    · intro b _ hb; simp only [dephasing]; rw [if_neg (fun c => hb c.2.symm), zero_mul]
    · simp
  simp only [Matrix.trace, Matrix.diag, e, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ad_apply, Complex.mul_conj]
  push_cast; rfl

lemma tr_deph : Matrix.trace (dephasing d) = d := by
  simp only [Matrix.trace, Matrix.diag, dephasing, Fintype.sum_prod_type, and_true]
  simp

variable [NeZero d] (mu : Measure (Unitary d)) (hmu : NormalizedHaar mu)
include hmu

lemma part1 : weightedIntegral mu (fun _ _ => 1) = depolarizing d := by
  haveI := hmu.1
  unfold weightedIntegral
  have inner : ∀ U : Unitary d, ∫ V, (1 : ℝ) • beta U V ∂mu =
      ad (U : Mat d) * (dephasing d * depolarizing d) := by
    intro U
    simp only [one_smul, beta]
    rw [int_lmul mu (integ cont_ad_star mu), twirl2 mu hmu, Matrix.mul_assoc]
  simp only [inner]
  rw [int_rmul mu (integ cont_ad_coe mu), twirl1 mu hmu, mul_dep un_deph, dep_mul tp_dep]

lemma part3 (hd : 2 ≤ d) (U : Unitary d) :
    (∫ V : Unitary d, beta V (V * U) ∂mu) =
      (((Matrix.trace (dephasing d * ad (U : Mat d)ᴴ)).re - 1) / ((d : ℝ) ^ 2 - 1)) • (1 : Map d) +
      (1 - ((Matrix.trace (dephasing d * ad (U : Mat d)ᴴ)).re - 1) / ((d : ℝ) ^ 2 - 1)) •
        depolarizing d := by
  have e : ∀ V : Unitary d, beta V (V * U) =
      ad (V : Mat d) * (dephasing d * ad (U : Mat d)ᴴ) * ad (V : Mat d)ᴴ := by
    intro V
    simp only [beta, coe_mulU, Matrix.conjTranspose_mul, ← ad_mul, Matrix.mul_assoc]
  simp only [e]
  rw [twirl_val mu hmu hd _ (un_mul un_deph (un_adU' U)), rsmul, rsmul]
  rw [tr_real, Complex.ofReal_re]
  push_cast
  rfl

lemma part4 (hd : 2 ≤ d) :
    (∫ V : Unitary d, beta V V ∂mu) =
      (1 / ((d : ℝ) + 1)) • (1 : Map d) + ((d : ℝ) / ((d : ℝ) + 1)) • depolarizing d := by
  have h := part3 mu hmu hd 1
  simp only [mul_one] at h
  have h1 : ((1 : Unitary d) : Mat d) = 1 := rfl
  rw [h1, Matrix.conjTranspose_one, ad_one, Matrix.mul_one, tr_deph, Complex.natCast_re] at h
  rw [h]
  have hd1 : ((d : ℝ) ^ 2 - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hd2 : (d : ℝ) + 1 ≠ 0 := by positivity
  have ea : ((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1) = 1 / ((d : ℝ) + 1) := by
    rw [div_eq_div_iff hd1 hd2]; ring
  have eb : 1 - 1 / ((d : ℝ) + 1) = (d : ℝ) / ((d : ℝ) + 1) := by
    field_simp; ring
  rw [ea, eb]

theorem x8_main (hd : 2 ≤ d) :
    weightedIntegral mu (fun _ _ => 1) = depolarizing d ∧ MTD (depolarizing d) ∧
    (∀ U : Unitary d,
      let a : ℝ := ((Matrix.trace (dephasing d * ad (U : Mat d)ᴴ)).re - 1) /
        ((d : ℝ)^2-1)
      (∫ V : Unitary d, beta V (V * U) ∂mu) = a • (1 : Map d) + (1-a) • depolarizing d) ∧
    (∫ V : Unitary d, beta V V ∂mu) =
      (1 / ((d : ℝ)+1)) • (1 : Map d) + ((d : ℝ)/((d : ℝ)+1)) • depolarizing d := by
  refine ⟨part1 mu hmu, ?_, fun U => part3 mu hmu hd U, part4 mu hmu hd⟩
  have := X8DM.mtd_dm (d := d) 0 le_rfl (by simp)
  simpa [depolarizingMixture] using this

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

namespace X8HA

variable {d : ℕ}

lemma adH (B : Mat d) : (ad B)ᴴ = ad Bᴴ := by
  ext p q
  simp [ad_apply, Matrix.conjTranspose_apply, mul_comm]

def sig (M : Map d) : ℂ := ∑ i, ∑ j, M (i, i) (j, j)

def sigL : Map d →ₗ[ℝ] ℂ where
  toFun := sig
  map_add' _ _ := by simp [sig, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [sig, Finset.smul_sum]

lemma sig_mul {A M B : Map d} (hA : TPm A) (hB : Um B) : sig (A * M * B) = sig M := by
  unfold sig
  have e : ∀ i j, (A * M * B) (i, i) (j, j) = ∑ r, ∑ s, A (i, i) r * M r s * B s (j, j) := by
    intro i j
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_comm
  simp only [e]
  calc ∑ i, ∑ j, ∑ r, ∑ s, A (i, i) r * M r s * B s (j, j)
      = ∑ r, ∑ s, (∑ i, A (i, i) r) * M r s * (∑ j, B s (j, j)) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
        rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => Finset.sum_comm]
        rw [Finset.sum_comm]
        rw [Finset.sum_congr rfl fun r _ => Finset.sum_comm]
        exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by
          rw [Finset.sum_comm]
    _ = ∑ r : Fin d × Fin d, ∑ s : Fin d × Fin d, (if r.1 = r.2 then (1 : ℂ) else 0) * M r s *
          (if s.1 = s.2 then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by rw [hA r, hB s]
    _ = ∑ i, ∑ j, M (i, i) (j, j) := by
        have : ∀ r : Fin d × Fin d, (∑ s : Fin d × Fin d, (if r.1 = r.2 then (1 : ℂ) else 0) *
            M r s * (if s.1 = s.2 then (1 : ℂ) else 0)) =
            (if r.1 = r.2 then (1 : ℂ) else 0) * ∑ j, M r (j, j) := by
          intro r
          rw [← sum_diag']
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
        simp only [this]
        exact sum_diag (fun r => ∑ j, M r (j, j))

variable [NeZero d]

omit [NeZero d] in
lemma sig_one : sig (1 : Map d) = d := by
  simp [sig, Matrix.one_apply]

lemma sig_dep : sig (depolarizing d) = d := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simp [sig, X8DM.dep_apply]

variable (mu : Measure (Unitary d)) (hmu : NormalizedHaar mu)
include hmu

lemma twirl_gen (hd : 2 ≤ d) (Φ : Map d) :
    (∫ V, ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ ∂mu) =
      ((Matrix.trace Φ - sig Φ / d) / ((d : ℂ) ^ 2 - 1)) • (1 : Map d) +
        (sig Φ / d - (Matrix.trace Φ - sig Φ / d) / ((d : ℂ) ^ 2 - 1)) • depolarizing d := by
  haveI := hmu.1
  have hc : Continuous (fun V : Unitary d => ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ) :=
    (cont_ad_coe.matrix_mul continuous_const).matrix_mul cont_ad_star
  have hI := integ hc mu
  obtain ⟨a, b, hR⟩ := cls hd (twirl_cov mu hmu Φ)
  have htr : Matrix.trace (∫ V, ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ ∂mu) = Matrix.trace Φ := by
    have := int_lin (Matrix.traceLinearMap (Fin d × Fin d) ℝ ℂ) mu hI
    simp only [Matrix.traceLinearMap_apply] at this
    rw [← this]
    have e : ∀ V : Unitary d, Matrix.trace (ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ) = Matrix.trace Φ := by
      intro V; rw [Matrix.trace_mul_cycle, adUU', Matrix.one_mul]
    simp only [e]
    exact int_cst mu _
  have hsg : sig (∫ V, ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ ∂mu) = sig Φ := by
    have := int_lin sigL mu hI
    change ∫ V, sig (ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ) ∂mu = sig _ at this
    rw [← this]
    have e : ∀ V : Unitary d, sig (ad (V : Mat d) * Φ * ad (V : Mat d)ᴴ) = sig Φ :=
      fun V => sig_mul (tp_adU V) (un_adU' V)
    simp only [e]
    exact int_cst mu _
  rw [hR] at htr hsg ⊢
  rw [tr_comb] at htr
  have hs2 : sig (a • (1 : Map d) + b • depolarizing d) = a * d + b * d := by
    rw [show sig (a • (1 : Map d) + b • depolarizing d) = a * sig (1 : Map d) + b * sig (depolarizing d) by
      simp [sig, Finset.sum_add_distrib, Finset.mul_sum]]
    rw [sig_one, sig_dep]
  rw [hs2] at hsg
  have hdc : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hd1 : (d : ℂ) ^ 2 - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have : ((d : ℝ) ^ 2 - 1 : ℝ) ≠ 0 := by nlinarith
    exact_mod_cast this
  have ha : a = (Matrix.trace Φ - sig Φ / d) / ((d : ℂ) ^ 2 - 1) := by
    rw [eq_div_iff hd1, ← htr, ← hsg]; field_simp; ring
  have hb : b = sig Φ / d - a := by
    rw [← hsg]; field_simp; ring
  rw [hb, ha]

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

namespace X8HA

variable {d : ℕ}

lemma ent_single (A : Map d) (r s p a : Fin d × Fin d) :
    (A * Matrix.single r s (1 : ℂ) * Aᴴ) p a = A p r * conj (A a s) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [Matrix.conjTranspose_apply, Matrix.mul_apply, Finset.sum_eq_single r]
    · simp [Complex.star_def]
    · intro b _ hb; simp only [Matrix.single_apply]; rw [if_neg (fun h => hb h.1.symm)]; simp
    · simp
  · intro b _ hb
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro c _; simp [Matrix.single_apply, Ne.symm hb]
  · simp

lemma tr_single (r s : Fin d × Fin d) :
    Matrix.trace (Matrix.single r s (1 : ℂ)) = if r = s then 1 else 0 := by
  by_cases h : r = s
  · subst h; rw [Matrix.trace_single_eq_same, if_pos rfl]
  · rw [Matrix.trace_single_eq_of_ne _ _ _ h, if_neg h]

/-- the coefficient matrices -/
def al (d : ℕ) (k l : Fin d) : ℂ := ((if k = l then 1 else 0) - 1 / (d : ℂ)) / ((d : ℂ) ^ 2 - 1)

def be (d : ℕ) (k l : Fin d) : ℂ := 1 / (d : ℂ) - al d k l

def Mk (d : ℕ) (k l : Fin d) : Map d := al d k l • (1 : Map d) + be d k l • depolarizing d

lemma sig_single (k l : Fin d) :
    sig (Matrix.single ((k, k) : Fin d × Fin d) (l, l) (1 : ℂ)) = 1 := by
  unfold sig
  rw [Finset.sum_eq_single k, Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [Matrix.single_apply, Ne.symm hb]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [Matrix.single_apply, Ne.symm hb]
  · simp

variable [NeZero d] (mu : Measure (Unitary d)) (hmu : NormalizedHaar mu)
include hmu

lemma Ient (hd : 2 ≤ d) (p a : Fin d × Fin d) (k l : Fin d) :
    ∫ V, ad (V : Mat d) p (k, k) * conj (ad (V : Mat d) a (l, l)) ∂mu = Mk d k l p a := by
  haveI := hmu.1
  have hc : Continuous (fun V : Unitary d =>
      ad (V : Mat d) * Matrix.single ((k, k) : Fin d × Fin d) (l, l) (1 : ℂ) * ad (V : Mat d)ᴴ) :=
    (cont_ad_coe.matrix_mul continuous_const).matrix_mul cont_ad_star
  have h := congrFun (congrFun (twirl_gen mu hmu hd (Matrix.single ((k, k) : Fin d × Fin d) (l, l) (1 : ℂ)))
    p) a
  rw [int_ent mu (integ hc mu)] at h
  have e : ∀ V : Unitary d, (ad (V : Mat d) * Matrix.single ((k, k) : Fin d × Fin d) (l, l) (1 : ℂ) *
      ad (V : Mat d)ᴴ) p a = ad (V : Mat d) p (k, k) * conj (ad (V : Mat d) a (l, l)) := by
    intro V; rw [← adH]; exact ent_single _ _ _ _ _
  simp only [e] at h
  rw [h, tr_single, sig_single]
  have hkl : (((k, k) : Fin d × Fin d) = (l, l)) ↔ k = l := by simp
  simp only [hkl]
  unfold Mk be al
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8HA

variable {d : ℕ}

lemma Mk_swap (k l : Fin d) (a b : Fin d × Fin d) :
    Mk d k l (a.2, a.1) (b.2, b.1) = Mk d k l b a := by
  simp only [Mk, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, X8DM.dep_apply, smul_eq_mul]
  congr 2
  · by_cases h : a = b
    · subst h; simp
    · rw [if_neg (fun e => h (Prod.ext (congrArg Prod.snd e) (congrArg Prod.fst e))),
        if_neg (fun e => h e.symm)]
  · simp only [eq_comm (a := a.2), eq_comm (a := b.2), and_comm]

variable [NeZero d]

lemma MtM {t : Map d} (hU : Um t) (hT : TPm t) (x y : ℂ) :
    (x • (1 : Map d) + y • depolarizing d) * t * (x • (1 : Map d) + y • depolarizing d) =
      (x ^ 2) • t + (2 * x * y + y ^ 2) • depolarizing d := by
  have h1 : t * depolarizing d = depolarizing d := mul_dep hU
  have h2 : depolarizing d * t = depolarizing d := dep_mul hT
  have h3 : depolarizing d * depolarizing d = depolarizing d := dep_mul tp_dep
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, h1, h2, h3, smul_smul]
  module

omit [NeZero d] in
lemma sum_e (c0 c1 : ℂ) :
    ∑ k : Fin d, ∑ l : Fin d, (c0 + c1 * (if k = l then 1 else 0)) = (d : ℂ) ^ 2 * c0 + d * c1 := by
  simp only [Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma sum_al2 (hd : 2 ≤ d) :
    ∑ k : Fin d, ∑ l : Fin d, al d k l ^ 2 =
      1 / (((d : ℂ) - 1) * ((d : ℂ) + 1) ^ 2) := by
  have hdc : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (d : ℂ) - 1 ≠ 0 := by
    have : ((d : ℝ) - 1) ≠ 0 := by linarith
    exact_mod_cast this
  have hd2 : (d : ℂ) + 1 ≠ 0 := by
    have : ((d : ℝ) + 1) ≠ 0 := by linarith
    exact_mod_cast this
  have hsq : (d : ℂ) ^ 2 - 1 = ((d : ℂ) - 1) * ((d : ℂ) + 1) := by ring
  have e : ∀ k l : Fin d, al d k l ^ 2 = (1 / (d : ℂ) ^ 2) / ((d : ℂ) ^ 2 - 1) ^ 2 +
      ((1 - 2 / (d : ℂ)) / ((d : ℂ) ^ 2 - 1) ^ 2) * (if k = l then 1 else 0) := by
    intro k l
    have hne : (d : ℂ) ^ 2 - 1 ≠ 0 := by rw [hsq]; exact mul_ne_zero hd1 hd2
    unfold al
    split_ifs <;> field_simp <;> ring
  simp only [e]
  rw [sum_e, hsq]
  field_simp
  ring

lemma sum_ab (hd : 2 ≤ d) :
    ∑ k : Fin d, ∑ l : Fin d, (2 * al d k l * be d k l + be d k l ^ 2) =
      1 - 1 / (((d : ℂ) - 1) * ((d : ℂ) + 1) ^ 2) := by
  have hdc : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have e : ∀ k l : Fin d, 2 * al d k l * be d k l + be d k l ^ 2 = 1 / (d : ℂ) ^ 2 - al d k l ^ 2 := by
    intro k l; unfold be; ring
  simp only [e, Finset.sum_sub_distrib]
  rw [sum_al2 hd]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8HA

variable {d : ℕ}

lemma ent_single' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (r s i j : n) :
    (A * Matrix.single r s (1 : ℂ) * Aᴴ) i j = A i r * conj (A j s) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [Matrix.conjTranspose_apply, Matrix.mul_apply, Finset.sum_eq_single r]
    · simp [Complex.star_def]
    · intro b _ hb; simp only [Matrix.single_apply]; rw [if_neg (fun h => hb h.1.symm)]; simp
    · simp
  · intro b _ hb
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro c _; simp [Matrix.single_apply, Ne.symm hb]
  · simp

lemma kraus_form {t : Map d} (ht : UnitalChannel t) :
    ∃ m : ℕ, ∃ E : Fin m → Mat d, (∑ j, (E j)ᴴ * E j = 1) ∧ t = ∑ j, ad (E j) := by
  obtain ⟨m, E, hK, hE⟩ := ht.1
  refine ⟨m, E, hK, ?_⟩
  ext p q
  have h := congrFun (congrFun (hE (Matrix.single q.1 q.2 1)) p.1) p.2
  rw [X8DM.applyMap_apply, Finset.sum_eq_single q] at h
  · rw [Matrix.sum_apply]
    simp only [Matrix.single_apply, and_self, if_true, mul_one] at h
    rw [h]
    simp only [QAlgorithms.krausApply, Matrix.sum_apply, ent_single']
    rfl
  · intro b _ hb
    rw [Matrix.single_apply, if_neg (fun c => hb (Prod.ext c.1.symm c.2.symm)), mul_zero]
  · simp

lemma tp_sum {m : ℕ} (E : Fin m → Mat d) (hK : ∑ j, (E j)ᴴ * E j = 1) :
    TPm (∑ j, ad (E j)) := by
  intro q
  have h := congrFun (congrFun hK q.2) q.1
  rw [Matrix.sum_apply] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
  simp only [Matrix.sum_apply, ad_apply]
  rw [Finset.sum_comm]
  have e : (if q.1 = q.2 then (1 : ℂ) else 0) = if q.2 = q.1 then 1 else 0 := by
    simp only [eq_comm]
  rw [e, ← h]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    rw [Complex.star_def]; ring

lemma un_of {t : Map d} (ht : UnitalChannel t) : Um t := by
  intro p
  have h := congrFun (congrFun ht.2 p.1) p.2
  rw [X8DM.applyMap_apply] at h
  rw [← sum_diag']
  rw [Matrix.one_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.one_apply]

lemma hs_ad (A K : Mat d) :
    hsInner (ad A) (ad K) = ((Complex.normSq (∑ i, ∑ j, conj (A i j) * K i j) : ℝ) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  unfold hsInner
  simp only [ad_apply, Fintype.sum_prod_type, map_sum, map_mul, Complex.conj_conj,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

lemma hs_sum_left {ι : Type*} (s : Finset ι) (f : ι → Map d) (t : Map d) :
    hsInner (∑ m ∈ s, f m) t = ∑ m ∈ s, hsInner (f m) t := by
  unfold hsInner
  simp only [Matrix.sum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm]
  exact Finset.sum_comm

lemma hs_sum_right {ι : Type*} (s : Finset ι) (f : ι → Map d) (t : Map d) :
    hsInner t (∑ m ∈ s, f m) = ∑ m ∈ s, hsInner t (f m) := by
  unfold hsInner
  simp only [Matrix.sum_apply, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm]
  exact Finset.sum_comm

lemma deph_sum : dephasing d = ∑ m : Fin d, ad (Matrix.single m m (1 : ℂ)) := by
  ext p q
  rw [Matrix.sum_apply]
  simp only [ad_apply, Matrix.single_apply, dephasing]
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h : p1 = p2 ∧ (p1, p2) = (q1, q2)
  · obtain ⟨h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    subst h1
    rw [if_pos ⟨rfl, rfl⟩, Finset.sum_eq_single p1]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun m _ => ?_).symm
    by_contra hne
    apply h
    have h1 : m = p1 ∧ m = q1 := by
      by_contra c; rw [if_neg c, zero_mul] at hne; exact hne rfl
    have h2 : m = p2 ∧ m = q2 := by
      by_contra c; rw [if_neg c, map_zero, mul_zero] at hne; exact hne rfl
    refine ⟨h1.1.symm.trans h2.1, ?_⟩
    simp only [Prod.mk.injEq]
    exact ⟨h1.1.symm.trans h1.2, h2.1.symm.trans h2.2⟩

lemma beta_sum (U V : Unitary d) :
    beta U V = ∑ m : Fin d, ad ((U : Mat d) * Matrix.single m m (1 : ℂ) * (V : Mat d)ᴴ) := by
  rw [beta, deph_sum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ad_mul, ad_mul]

lemma w_real (U V : Unitary d) {t : Map d} (ht : UnitalChannel t) :
    (((hsInner (beta U V) t).re : ℝ) : ℂ) = hsInner (beta U V) t := by
  obtain ⟨m, E, _, hE⟩ := kraus_form ht
  rw [hE, beta_sum, hs_sum_left]
  simp only [hs_sum_right, hs_ad]
  simp only [← Complex.ofReal_sum, Complex.ofReal_re]

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

namespace X8HA

variable {d : ℕ}

lemma cont_adX' {X : Type*} [TopologicalSpace X] {g : X → Mat d} (hg : Continuous g) :
    Continuous (fun x => ad (g x)) := by
  unfold ad
  refine continuous_pi fun p => continuous_pi fun q => ?_
  exact ((hg.matrix_elem _ _).mul (Complex.continuous_conj.comp (hg.matrix_elem _ _)))

lemma cont_beta' : Continuous (fun z : Unitary d × Unitary d => beta z.1 z.2) := by
  unfold beta
  exact ((cont_adX' (cont_coe.comp continuous_fst)).matrix_mul continuous_const).matrix_mul
    (cont_adX' (cont_coe.comp continuous_snd).matrix_conjTranspose)

instance scMat' : SecondCountableTopology (Mat d) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℂ))

instance scU' : SecondCountableTopology (Unitary d) :=
  TopologicalSpace.Subtype.secondCountableTopology _

lemma cont_w' (t : Map d) :
    Continuous (fun z : Unitary d × Unitary d => (hsInner (beta z.1 z.2) t).re) := by
  unfold hsInner
  refine Complex.continuous_re.comp (continuous_finsetSum _ fun p _ =>
    continuous_finsetSum _ fun q _ => ?_)
  exact (Complex.continuous_conj.comp (cont_beta'.matrix_elem p q)).mul continuous_const

lemma par_cont' (mu : Measure (Unitary d)) [IsFiniteMeasure mu]
    {f : Unitary d → Unitary d → Map d} (hf : Continuous (Function.uncurry f)) :
    Continuous (fun U => ∫ V, f U V ∂mu) := by
  have := continuous_parametric_integral_of_continuous (μ := mu) hf isCompact_univ
  rw [Measure.restrict_univ] at this
  exact this

lemma integC {f : Unitary d → ℂ} (hf : Continuous f) (mu : Measure (Unitary d))
    [IsFiniteMeasure mu] : Integrable f mu :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma dbl {X : Type*} [Fintype X] (mu : Measure (Unitary d)) [IsFiniteMeasure mu]
    (c : X → ℂ) (f g : X → Unitary d → ℂ) (hf : ∀ x, Continuous (f x)) (hg : ∀ x, Continuous (g x)) :
    ∫ U, ∫ V, ∑ x, c x * f x U * g x V ∂mu ∂mu =
      ∑ x, c x * (∫ U, f x U ∂mu) * (∫ V, g x V ∂mu) := by
  have inner : ∀ U, ∫ V, ∑ x, c x * f x U * g x V ∂mu = ∑ x, c x * f x U * ∫ V, g x V ∂mu := by
    intro U
    rw [integral_finsetSum _ fun x _ => (integC (hg x) mu).const_mul (c x * f x U)]
    exact Finset.sum_congr rfl fun x _ => integral_const_mul _ _
  simp only [inner]
  rw [integral_finsetSum _ fun x _ =>
    (((integC (hf x) mu).const_mul (c x)).mul_const (∫ V, g x V ∂mu))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_mul_const, integral_const_mul]

lemma beta_ent (U V : Unitary d) (p q : Fin d × Fin d) :
    beta U V p q = ∑ m : Fin d, ad (U : Mat d) p (m, m) * ad (V : Mat d) (q.2, q.1) (m, m) := by
  rw [X8DM.beta_apply]
  exact Finset.sum_congr rfl fun m _ => by simp only [ad_apply]; ring

/-- pointwise expansion of the integrand -/
lemma expand (U V : Unitary d) (t : Map d) (p q : Fin d × Fin d) :
    hsInner (beta U V) t * beta U V p q =
      ∑ a : Fin d × Fin d, ∑ b : Fin d × Fin d, ∑ k : Fin d, ∑ l : Fin d,
        t a b * (ad (U : Mat d) p (k, k) * conj (ad (U : Mat d) a (l, l))) *
          (ad (V : Mat d) (q.2, q.1) (k, k) * conj (ad (V : Mat d) (b.2, b.1) (l, l))) := by
  unfold hsInner
  simp only [beta_ent, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

namespace X8HA

variable {d : ℕ}

lemma perm4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ k, ∑ l, F a b k l = ∑ k, ∑ l, ∑ b, ∑ a, F a b k l := by
  calc ∑ a, ∑ b, ∑ k, ∑ l, F a b k l = ∑ a, ∑ k, ∑ b, ∑ l, F a b k l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ k, ∑ l, ∑ b, F a b k l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ l, ∑ b, F a b k l := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, F a b k l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ b, ∑ a, F a b k l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm

lemma nest (F : Fin d × Fin d → Fin d × Fin d → Fin d → Fin d → ℂ) :
    ∑ x : (Fin d × Fin d) × (Fin d × Fin d) × (Fin d × Fin d), F x.1 x.2.1 x.2.2.1 x.2.2.2 =
      ∑ a, ∑ b, ∑ k, ∑ l, F a b k l := by
  simp only [Fintype.sum_prod_type]

lemma MtM_ent (t : Map d) (k l : Fin d) (p q : Fin d × Fin d) :
    ∑ a, ∑ b, t a b * Mk d k l p a * Mk d k l b q = (Mk d k l * t * Mk d k l) p q := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

variable [NeZero d]

theorem x8_45 (hd : 2 ≤ d) (mu : Measure (Unitary d))
    (hmu : NormalizedHaar mu) (t : Map d) (ht : UnitalChannel t) :
    weightedIntegral mu (fun U V => (hsInner (beta U V) t).re) =
      (integralDenominator d)⁻¹ • t +
        (1 - (integralDenominator d)⁻¹) • depolarizing d := by
  haveI := hmu.1
  have hU := un_of ht
  obtain ⟨m, E, hK, hE⟩ := kraus_form ht
  have hT : TPm t := hE ▸ tp_sum E hK
  have hf : Continuous (Function.uncurry fun U V => (hsInner (beta U V) t).re • beta (d := d) U V) := by
    exact (cont_w' t).smul cont_beta'
  ext p q
  unfold weightedIntegral
  rw [int_ent mu (integ (par_cont' mu hf) mu)]
  have inner : ∀ U : Unitary d, (∫ V, (hsInner (beta U V) t).re • beta U V ∂mu) p q =
      ∫ V, hsInner (beta U V) t * beta U V p q ∂mu := by
    intro U
    have hi : Integrable (fun V => (hsInner (beta U V) t).re • beta U V) mu :=
      integ (hf.comp (Continuous.prodMk_right U)) mu
    rw [int_ent mu hi]
    congr 1; funext V
    rw [Matrix.smul_apply, Complex.real_smul, w_real U V ht]
  simp only [inner, expand]
  let c : (Fin d × Fin d) × (Fin d × Fin d) × (Fin d × Fin d) → ℂ := fun x => t x.1 x.2.1
  let f : (Fin d × Fin d) × (Fin d × Fin d) × (Fin d × Fin d) → Unitary d → ℂ := fun x U =>
    ad (U : Mat d) p (x.2.2.1, x.2.2.1) * conj (ad (U : Mat d) x.1 (x.2.2.2, x.2.2.2))
  let g : (Fin d × Fin d) × (Fin d × Fin d) × (Fin d × Fin d) → Unitary d → ℂ := fun x V =>
    ad (V : Mat d) (q.2, q.1) (x.2.2.1, x.2.2.1) *
      conj (ad (V : Mat d) (x.2.1.2, x.2.1.1) (x.2.2.2, x.2.2.2))
  have e : ∀ U V : Unitary d, (∑ a : Fin d × Fin d, ∑ b : Fin d × Fin d, ∑ k : Fin d, ∑ l : Fin d,
        t a b * (ad (U : Mat d) p (k, k) * conj (ad (U : Mat d) a (l, l))) *
          (ad (V : Mat d) (q.2, q.1) (k, k) * conj (ad (V : Mat d) (b.2, b.1) (l, l)))) =
      ∑ x, c x * f x U * g x V := by
    intro U V
    exact (nest (fun a b k l => t a b * (ad (U : Mat d) p (k, k) * conj (ad (U : Mat d) a (l, l))) *
          (ad (V : Mat d) (q.2, q.1) (k, k) * conj (ad (V : Mat d) (b.2, b.1) (l, l))))).symm
  simp only [e]
  have hfc : ∀ x, Continuous (f x) := fun x =>
    (cont_ad_coe.matrix_elem _ _).mul (Complex.continuous_conj.comp (cont_ad_coe.matrix_elem _ _))
  have hgc : ∀ x, Continuous (g x) := fun x =>
    (cont_ad_coe.matrix_elem _ _).mul (Complex.continuous_conj.comp (cont_ad_coe.matrix_elem _ _))
  rw [dbl mu c f g hfc hgc]
  simp only [c, f, g, Ient mu hmu hd, Mk_swap]
  rw [nest (fun a b k l => t a b * Mk d k l p a * Mk d k l b q), perm4]
  have e2 : ∀ k l : Fin d, ∑ b, ∑ a, t a b * Mk d k l p a * Mk d k l b q =
      al d k l ^ 2 * t p q + (2 * al d k l * be d k l + be d k l ^ 2) * depolarizing d p q := by
    intro k l
    rw [Finset.sum_comm, MtM_ent, Mk, MtM hU hT]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => e2 k l).trans ?_
  have hsplit : ∀ (A B : Fin d → Fin d → ℂ) (x y : ℂ),
      ∑ k, ∑ l, (A k l * x + B k l * y) = (∑ k, ∑ l, A k l) * x + (∑ k, ∑ l, B k l) * y := by
    intro A B x y
    simp only [Finset.sum_add_distrib, Finset.sum_mul]
  rw [hsplit (fun k l => al d k l ^ 2) (fun k l => 2 * al d k l * be d k l + be d k l ^ 2),
    sum_al2 hd, sum_ab hd]
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, integralDenominator]
  push_cast
  ring

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26

section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 2 ≤ d) (mu : Measure (Unitary d))
    (hmu : NormalizedHaar mu) (t : Map d) (ht : UnitalChannel t) :
    weightedIntegral mu (fun U V => (hsInner (beta U V) t).re) =
      (integralDenominator d)⁻¹ • t +
        (1 - (integralDenominator d)⁻¹) • depolarizing d := by
  haveI : NeZero d := ⟨by omega⟩
  exact X8HA.x8_45 hd mu hmu t ht

end
