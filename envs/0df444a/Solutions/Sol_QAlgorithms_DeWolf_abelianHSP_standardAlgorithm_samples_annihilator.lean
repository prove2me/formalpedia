-- Prove2me | solution 1 for QAlgorithms.DeWolf.abelianHSP_standardAlgorithm_samples_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:04:56.105711+00:00
-- url     : https://prove2.me/submissions/463a1402-9269-46d4-b609-baef872026cd

import Definitions.Def_QAlgorithms_Defs_Fourier
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open QAlgorithms Classical
open scoped BigOperators

private lemma char_std {l : ℕ} {N : Fin l → ℕ} [∀ i, NeZero (N i)]
    (g x : (i : Fin l) → ZMod (N i)) :
    abelianChar g x = ∏ i, ZMod.stdAddChar (g i * x i) := by
  apply Finset.prod_congr rfl
  intro i _
  rw [ZMod.stdAddChar_apply]
  have he := ZMod.toCircle_natCast (N := N i) ((g i).val * (x i).val)
  simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using he.symm

private lemma char_add {l : ℕ} {N : Fin l → ℕ} [∀ i, NeZero (N i)]
    (g x y : (i : Fin l) → ZMod (N i)) :
    abelianChar g (x + y) = abelianChar g x * abelianChar g y := by
  simp only [char_std, Pi.add_apply, mul_add, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

private lemma char_norm {l : ℕ} {N : Fin l → ℕ} [∀ i, NeZero (N i)]
    (g x : (i : Fin l) → ZMod (N i)) : ‖abelianChar g x‖ = 1 := by
  simp [char_std, ZMod.stdAddChar_apply, norm_prod, Circle.norm_coe]

private noncomputable def fiberEquiv {G S : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (f : G → S) (hf : AddHides f H) (t : G) :
    H ≃ {x : G // f x = f t} where
  toFun h := ⟨t + h, ((hf t (t + h)).2 (by simp)).symm⟩
  invFun x := ⟨-t + x, (hf t x).1 x.property.symm⟩
  left_inv h := by ext; simp
  right_inv x := by ext; simp

private lemma fiber_sum {G S : Type*} [AddCommGroup G] [Fintype G] [DecidableEq S]
    (H : AddSubgroup G) (f : G → S) (hf : AddHides f H) (t : G) (c : G → ℂ) :
    ∑ x, (if f x = f t then c x else 0) = ∑ h : H, c (t + h) := by
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
  simpa [fiberEquiv] using (Equiv.sum_comp (fiberEquiv H f hf t) (fun x => c x.val)).symm

private lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) : act (A * B) v = act A (act B v) := by
  exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec _ _ _).symm

private lemma state_apply {l : ℕ} {N : Fin l → ℕ} [∀ i, NeZero (N i)]
    {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
    (f : ((i : Fin l) → ZMod (N i)) → S) (g : (i : Fin l) → ZMod (N i)) (s : S) :
    hspStandardState N f (g,s) =
      ((Fintype.card ((i : Fin l) → ZMod (N i)) : ℂ)⁻¹) *
        ∑ x, if f x = s then abelianChar g x else 0 := by
  have hs : (Real.sqrt (Fintype.card ((i : Fin l) → ZMod (N i)))) ^ 2 =
      Fintype.card ((i : Fin l) → ZMod (N i)) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hc : (↑(Real.sqrt (Fintype.card ((i : Fin l) → ZMod (N i)))) : ℂ) ^ 2 =
      Fintype.card ((i : Fin l) → ZMod (N i)) := by exact_mod_cast hs
  have hsym : ∀ x, abelianChar x g = abelianChar g x := by
    intro x; simp only [char_std, mul_comm]
  rw [hspStandardState, act_mul]
  have hquery : act (xorOracle f)
      (tensorVec (uniformState ((i : Fin l) → ZMod (N i))) (ket (0 : S))) =
      WithLp.toLp 2 (fun p => if p.2 = f p.1 then
        ((Real.sqrt (Fintype.card ((i : Fin l) → ZMod (N i))))⁻¹ : ℂ) else 0) := by
    ext p
    simp [act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, xorOracle,
      tensorVec, uniformState, ket, PiLp.single_apply, PiLp.toLp_apply,
      ite_and, eq_comm]
  rw [hquery]
  simp only [act, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply, qftAbelian,
    Matrix.of_apply]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hsym]
  have hnorm : (↑(Real.sqrt (Fintype.card ((i : Fin l) → ZMod (N i)))) : ℂ)⁻¹ *
      (↑(Real.sqrt (Fintype.card ((i : Fin l) → ZMod (N i)))) : ℂ)⁻¹ =
      (Fintype.card ((i : Fin l) → ZMod (N i)) : ℂ)⁻¹ := by
    rw [← mul_inv, ← sq, hc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : f x = s
  · simp only [hx, if_true]
    calc
      _ = ((↑(Real.sqrt (Fintype.card ((i : Fin l) → ZMod (N i)))) : ℂ)⁻¹ *
          (↑(Real.sqrt (Fintype.card ((i : Fin l) → ZMod (N i)))) : ℂ)⁻¹) *
          abelianChar g x := by ring
      _ = _ := by rw [hnorm]
  · simp [hx, Ne.symm hx]

private lemma subgroup_sum_zero {l : ℕ} {N : Fin l → ℕ} [∀ i, NeZero (N i)]
    (H : AddSubgroup ((i : Fin l) → ZMod (N i)))
    (g : (i : Fin l) → ZMod (N i)) (hg : g ∉ annihilator H) :
    ∑ h : H, abelianChar g h = 0 := by
  let χ : AddChar H ℂ := {
    toFun := fun h => abelianChar g h
    map_zero_eq_one' := by simp [abelianChar]
    map_add_eq_mul' := fun h k => char_add g h k }
  change ∑ h, χ h = 0
  apply AddChar.sum_eq_zero_iff_ne_zero.mpr
  intro he
  apply hg
  intro x hx
  have hc := congrArg (fun c : AddChar H ℂ => c ⟨x,hx⟩) he
  simpa [χ] using hc

private lemma fiber_card_total {G S : Type*} [Fintype G] [Fintype S] [DecidableEq S] (f : G → S) :
    ∑ s, Fintype.card {x : G // f x = s} = Fintype.card G := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

theorem solution {l : ℕ} (N : Fin l → ℕ)
    [∀ i, NeZero (N i)] {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
    (H : AddSubgroup ((i : Fin l) → ZMod (N i))) (f : ((i : Fin l) → ZMod (N i)) → S)
    (hf : AddHides f H) (g : (i : Fin l) → ZMod (N i)) :
    (g ∈ annihilator H →
      marginalFst (hspStandardState N f) g =
        (Nat.card H : ℝ) / (Fintype.card ((i : Fin l) → ZMod (N i)) : ℝ)) ∧
    (g ∉ annihilator H → marginalFst (hspStandardState N f) g = 0) := by
  have hn : (Fintype.card ((i : Fin l) → ZMod (N i)) : ℝ) ≠ 0 := by positivity
  have hp (s : S) : prob (hspStandardState N f) (g,s) =
      (Fintype.card ((i : Fin l) → ZMod (N i)) : ℝ)⁻¹ ^ 2 *
        ‖∑ x, if f x = s then abelianChar g x else 0‖ ^ 2 := by
    simp only [prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul, state_apply,
      norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  constructor
  · intro hg
    have hterm (s : S) : prob (hspStandardState N f) (g,s) =
        (Fintype.card ((i : Fin l) → ZMod (N i)) : ℝ)⁻¹ ^ 2 * (Nat.card H : ℝ) *
          (Fintype.card {x : ((i : Fin l) → ZMod (N i)) // f x = s} : ℝ) := by
      rw [hp]
      by_cases hs : ∃ t, f t = s
      · obtain ⟨t,rfl⟩ := hs
        have hc : Fintype.card {x : ((i : Fin l) → ZMod (N i)) // f x = f t} = Nat.card H := by
          rw [Nat.card_eq_fintype_card]
          exact Fintype.card_congr (fiberEquiv H f hf t).symm
        have hsum : ∑ x, (if f x = f t then abelianChar g x else 0) =
            abelianChar g t * (Nat.card H : ℂ) := by
          rw [fiber_sum H f hf t]
          simp_rw [char_add, hg _ (Subtype.property _), mul_one]
          simp [Nat.card_eq_fintype_card, mul_comm]
        rw [hsum, norm_mul, char_norm, one_mul, Complex.norm_natCast, hc]
        ring
      · have hempty : IsEmpty {x : ((i : Fin l) → ZMod (N i)) // f x = s} := ⟨fun x => hs ⟨x,x.property⟩⟩
        have hz : ∀ x, f x ≠ s := fun x h => hs ⟨x,h⟩
        simp [hz]
    simp only [marginalFst, hterm]
    rw [← Finset.mul_sum, ← Nat.cast_sum]
    rw [fiber_card_total f]
    field_simp
  · intro hg
    have hz (s : S) : prob (hspStandardState N f) (g,s) = 0 := by
      rw [hp]
      by_cases hs : ∃ t, f t = s
      · obtain ⟨t,rfl⟩ := hs
        rw [fiber_sum H f hf t]
        simp_rw [char_add]
        rw [← Finset.mul_sum, subgroup_sum_zero H g hg]
        simp
      · have hz : ∀ x, f x ≠ s := fun x h => hs ⟨x,h⟩
        simp [hz]
    simp [marginalFst, hz]
