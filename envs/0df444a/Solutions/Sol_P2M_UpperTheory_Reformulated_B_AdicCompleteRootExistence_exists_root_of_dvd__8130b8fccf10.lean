-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:50.047926+00:00
-- url     : https://prove2.me/submissions/b0c41243-0337-417a-93fe-8324fe5b957a

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRootOfAdicComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
namespace UpperTheory.Reformulated.B.AdicCompleteRootExistence
private lemma exists_root_of_adicComplete {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.eval a = 0 ∧ a - a₀ ∈ I := by
  classical
  obtain ⟨f', hf'⟩ : ∃ f' : R[X], f' = derivative f := ⟨_, rfl⟩
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℕ → R, c 0 = a₀ ∧
      ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f'.eval (c n)) :=
    ⟨fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * Ring.inverse (f'.eval b), rfl,
      fun _ => rfl⟩
  rw [← hf'] at h₂
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rw [hc0]
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [hc0, zero_add, pow_one] using h₁
    | succ n ih =>
      obtain ⟨q, hq⟩ := Polynomial.binomExpansion f (c n)
        (-(f.eval (c n) * Ring.inverse (f'.eval (c n))))
      rw [hc, sub_eq_add_neg, hq]
      have hcancel : f'.eval (c n) * Ring.inverse (f'.eval (c n)) = 1 :=
        Ring.mul_inverse_cancel _ (hf'c n)
      have hz : eval (c n) f + eval (c n) (derivative f) *
          (-(f.eval (c n) * Ring.inverse (f'.eval (c n)))) = 0 := by
        rw [← hf']
        linear_combination (-(f.eval (c n))) * hcancel
      rw [hz, zero_add]
      have hle : I ^ (2 * (n + 1)) ≤ I ^ (n + 1 + 1) :=
        Ideal.pow_le_pow_right (by omega)
      refine Ideal.mul_mem_left _ _ (hle ?_)
      rw [pow_mul']
      exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih =>
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · specialize ha (0 + 1)
    rw [hc, hc0, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁
private lemma root_of_local {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {ϖ : R}
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R) (f : R[X]) (a : R) (k : ℕ) (ε : Rˣ)
    (h1 : f.derivative.eval a = ϖ ^ k * ε) (h2 : ϖ ^ (2 * k + 1) ∣ f.eval a) :
    ∃ b : R, f.eval b = 0 ∧ ϖ ^ (k + 1) ∣ b - a := by
  obtain ⟨c, hc⟩ := h2
  obtain ⟨q, hq⟩ := Polynomial.binomExpansion (f.map C) (C a) (C (ϖ ^ (k + 1)) * X)
  have hcomp : eval (C a + C (ϖ ^ (k + 1)) * X) (f.map C) =
      f.comp (C a + C (ϖ ^ (k + 1)) * X) := by
    rw [eval_map]; rfl
  rw [hcomp, eval_map_apply, derivative_map, eval_map_apply, h1, hc] at hq
  let g : R[X] := C c + C (ε : R) * X + C ϖ * q * X ^ 2
  have hgy : ∀ y, g.eval y = c + ε * y + ϖ * (q.eval y * y ^ 2) := by
    intro y; simp only [g, eval_add, eval_mul, eval_C, eval_X, eval_pow]; ring
  have hg'y : ∀ y, g.derivative.eval y =
      ε + ϖ * (q.derivative.eval y * y ^ 2 + q.eval y * (2 * y)) := by
    intro y
    simp only [g, derivative_add, derivative_mul, derivative_C, derivative_X, derivative_X_pow,
      eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero, eval_one, map_natCast, eval_natCast]
    norm_num
    ring
  set y₀ : R := -((ε⁻¹ : Rˣ) : R) * c with hy₀
  have hεy : (ε : R) * y₀ = -c := by
    rw [hy₀, ← mul_assoc, mul_neg, Units.mul_inv]; ring
  have hroot₀ : g.eval y₀ ∈ IsLocalRing.maximalIdeal R := by
    rw [hgy, add_assoc, ← add_assoc c, hεy, add_neg_cancel, zero_add]
    exact Ideal.mul_mem_right _ _ hϖ
  have hunit : IsUnit (g.derivative.eval y₀) := by
    rw [hg'y]
    by_contra hn
    have hm := (IsLocalRing.mem_maximalIdeal _).2 hn
    have hε : (ε : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hm (Ideal.mul_mem_right
        (q.derivative.eval y₀ * y₀ ^ 2 + q.eval y₀ * (2 * y₀)) _ hϖ)
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).1 hε ε.isUnit
  obtain ⟨y, hy, -⟩ := exists_root_of_adicComplete (IsLocalRing.maximalIdeal R) g y₀ hroot₀
    (hunit.map _)
  refine ⟨a + ϖ ^ (k + 1) * y, ?_, ⟨y, by ring⟩⟩
  have hev := congrArg (eval y) hq
  simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_pow] at hev
  rw [hev]
  have : ϖ ^ (2 * k + 1) * g.eval y = 0 := by rw [hy, mul_zero]
  rw [hgy] at this
  linear_combination this
end UpperTheory.Reformulated.B.AdicCompleteRootExistence
end

set_option autoImplicit false
open Polynomial
namespace UpperTheory.Reformulated.B.AdicCompleteRootExistence.exists_root_of_dvd
theorem _root_.solution.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] [IsNonarchimedeanLocalField K]
      {ϖ : ↥(ValuativeRel.valuation K).integer},
      Irreducible ϖ →
        ∀ (f : Polynomial ↥(ValuativeRel.valuation K).integer) (a : ↥(ValuativeRel.valuation K).integer) (k : ℕ)
          (ε : (↥(ValuativeRel.valuation K).integer)ˣ),
          Polynomial.eval a
                ((Polynomial.derivative :
                    Polynomial ↥(ValuativeRel.valuation K).integer → Polynomial ↥(ValuativeRel.valuation K).integer)
                  f) =
              ϖ ^ k * (↑ε : ↥(ValuativeRel.valuation K).integer) →
            ϖ ^ ((2 : ℕ) * k + (1 : ℕ)) ∣ Polynomial.eval a f →
              ∃ (b : ↥(ValuativeRel.valuation K).integer),
                Polynomial.eval b f = (0 : ↥(ValuativeRel.valuation K).integer) ∧ ϖ ^ (k + (1 : ℕ)) ∣ b - a := by
  intro K _ _ _ _ ϖ hϖ f a k ε h1 h2
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact UpperTheory.Reformulated.B.AdicCompleteRootExistence.root_of_local
    ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit) f a k ε h1 h2
end UpperTheory.Reformulated.B.AdicCompleteRootExistence.exists_root_of_dvd
