-- Prove2me | solution 1 for Polynomial.abhyankar_isStandardEtale_finrank_and_algEquiv_laurentPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T06:41:41.503273+00:00
-- url     : https://prove2.me/submissions/f5ec684b-a129-45f2-8ab2-fc007805f471

import Mathlib

set_option autoImplicit false

namespace AbhyankarCoverSol

open Polynomial
open LaurentPolynomial (T T_pow T_add T_zero)
open scoped LaurentPolynomial

variable (Fq : Type*) [Field Fq] (n : ℕ)

/-- The Abhyankar polynomial `Y^(n+1) - T Y + 1` over `F_q[T]`. -/
noncomputable def abhPoly : Fq[X][X] := X ^ (n + 1) - C X * X + 1

theorem abhPoly_eq : abhPoly Fq n = X ^ (n + 1) + (1 - C X * X) := by
  rw [abhPoly]; ring

theorem degree_abh_lt (hn : 1 ≤ n) : degree (1 - C X * X : Fq[X][X]) < degree (X ^ (n + 1) : Fq[X][X]) := by
  rw [degree_X_pow]
  calc degree (1 - C X * X : Fq[X][X]) ≤ 1 := by compute_degree
    _ < ((n + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : 1 < n + 1)

theorem abhPoly_monic (hn : 1 ≤ n) : (abhPoly Fq n).Monic := by
  rw [abhPoly_eq]
  exact (monic_X_pow (n + 1)).add_of_left (degree_abh_lt Fq n hn)

theorem abhPoly_natDegree (hn : 1 ≤ n) : (abhPoly Fq n).natDegree = n + 1 := by
  rw [abhPoly_eq, natDegree_add_eq_left_of_degree_lt (degree_abh_lt Fq n hn), natDegree_X_pow]

theorem derivative_abhPoly (hp : (n : Fq) = 0) : derivative (abhPoly Fq n) = X ^ n - C X := by
  have h1 : ((n + 1 : ℕ) : Fq[X]) = 1 := by
    rw [Nat.cast_succ, ← map_natCast (algebraMap Fq Fq[X]) n, hp, map_zero, zero_add]
  rw [abhPoly, derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul_X, derivative_one, add_zero,
    h1, C_1, one_mul, Nat.add_sub_cancel]

/-- The standard etale pair `(f, 1)`: `f' · (-Y) + f · 1 = 1`. -/
noncomputable def abhPair (hn : 1 ≤ n) (hp : (n : Fq) = 0) : StandardEtalePair Fq[X] where
  f := abhPoly Fq n
  monic_f := abhPoly_monic Fq n hn
  g := 1
  cond := ⟨-X, 1, 0, by rw [derivative_abhPoly Fq n hp, abhPoly]; ring⟩

theorem hasMap_root (hn : 1 ≤ n) (hp : (n : Fq) = 0) :
    (abhPair Fq n hn hp).HasMap (AdjoinRoot.root (abhPoly Fq n)) := by
  refine ⟨?_, ?_⟩
  · show aeval (AdjoinRoot.root (abhPoly Fq n)) (abhPoly Fq n) = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · show IsUnit (aeval (AdjoinRoot.root (abhPoly Fq n)) (1 : Fq[X][X]))
    rw [map_one]
    exact isUnit_one

theorem abh_lift_bijective (hn : 1 ≤ n) (hp : (n : Fq) = 0) :
    Function.Bijective ((abhPair Fq n hn hp).lift _ (hasMap_root Fq n hn hp)) := by
  have hX : (abhPoly Fq n).eval₂ (Algebra.ofId Fq[X] (abhPair Fq n hn hp).Ring : Fq[X] →+* _)
      (abhPair Fq n hn hp).X = 0 := by
    have h := (abhPair Fq n hn hp).hasMap_X.1
    rw [aeval_def] at h
    exact h
  let inv := AdjoinRoot.liftAlgHom (abhPoly Fq n) (Algebra.ofId Fq[X] (abhPair Fq n hn hp).Ring)
    (abhPair Fq n hn hp).X hX
  refine Function.bijective_iff_has_inverse.2 ⟨inv, fun x => ?_, fun y => ?_⟩
  · have h : inv.comp ((abhPair Fq n hn hp).lift _ (hasMap_root Fq n hn hp)) = AlgHom.id _ _ :=
      (abhPair Fq n hn hp).hom_ext (by simp [inv, StandardEtalePair.lift_X])
    exact DFunLike.congr_fun h x
  · have h : ((abhPair Fq n hn hp).lift _ (hasMap_root Fq n hn hp)).comp inv = AlgHom.id _ _ :=
      AdjoinRoot.algHom_ext (by simp [inv, StandardEtalePair.lift_X])
    exact DFunLike.congr_fun h y

/-- The standard etale presentation of `F_q[T][Y]/(f)`. -/
noncomputable def abhPres (hn : 1 ≤ n) (hp : (n : Fq) = 0) :
    StandardEtalePresentation Fq[X] (AdjoinRoot (abhPoly Fq n)) where
  __ := abhPair Fq n hn hp
  x := AdjoinRoot.root _
  hasMap := hasMap_root Fq n hn hp
  lift_bijective := abh_lift_bijective Fq n hn hp

theorem abh_isStandardEtale (hn : 1 ≤ n) (hp : (n : Fq) = 0) :
    Algebra.IsStandardEtale Fq[X] (AdjoinRoot (abhPoly Fq n)) :=
  ⟨⟨abhPres Fq n hn hp⟩⟩

/-- **The Abhyankar cover is etale.** -/
theorem abh_etale (hn : 1 ≤ n) (hp : (n : Fq) = 0) : Algebra.Etale Fq[X] (AdjoinRoot (abhPoly Fq n)) := by
  haveI := abh_isStandardEtale Fq n hn hp
  infer_instance

theorem abh_free (hn : 1 ≤ n) : Module.Free Fq[X] (AdjoinRoot (abhPoly Fq n)) :=
  (abhPoly_monic Fq n hn).free_adjoinRoot

theorem abh_finite (hn : 1 ≤ n) : Module.Finite Fq[X] (AdjoinRoot (abhPoly Fq n)) :=
  (abhPoly_monic Fq n hn).finite_adjoinRoot

/-- **Degree `n + 1`.** -/
theorem abh_finrank (hn : 1 ≤ n) : Module.finrank Fq[X] (AdjoinRoot (abhPoly Fq n)) = n + 1 := by
  rw [(AdjoinRoot.powerBasis' (abhPoly_monic Fq n hn)).finrank, AdjoinRoot.powerBasis'_dim,
    abhPoly_natDegree Fq n hn]

/-- `y · (T - y^n) = 1`: the root is a unit. -/
theorem root_mul_abh : AdjoinRoot.root (abhPoly Fq n) *
    (AdjoinRoot.of (abhPoly Fq n) X - AdjoinRoot.root (abhPoly Fq n) ^ n) = 1 := by
  have h : AdjoinRoot.mk (abhPoly Fq n) (X ^ (n + 1) - C X * X + 1) = 0 := AdjoinRoot.mk_self
  rw [map_add, map_sub, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_one] at h
  linear_combination -h

/-- The root as a unit. -/
noncomputable def abhUnit : (AdjoinRoot (abhPoly Fq n))ˣ :=
  ⟨AdjoinRoot.root _, AdjoinRoot.of (abhPoly Fq n) X - AdjoinRoot.root _ ^ n, root_mul_abh Fq n,
    by rw [mul_comm]; exact root_mul_abh Fq n⟩

theorem abh_eval_T : (abhPoly Fq n).eval₂
    ((aeval (T n + T (-1)) : Fq[X] →ₐ[Fq] Fq[T;T⁻¹]) : Fq[X] →+* Fq[T;T⁻¹]) (T 1) = 0 := by
  rw [abhPoly]
  simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_mul, Polynomial.eval₂_C, eval₂_X, eval₂_one,
    RingHom.coe_coe, aeval_X]
  rw [T_pow, add_mul, ← T_add, ← T_add]
  have e : ((n + 1 : ℕ) : ℤ) * 1 = (n : ℤ) + 1 := by push_cast; ring
  rw [e, show (-1 : ℤ) + 1 = 0 by norm_num, T_zero]
  ring

/-- `Y ↦ x`, `T ↦ x^n + 1/x`. -/
noncomputable def abhToLaurent : AdjoinRoot (abhPoly Fq n) →ₐ[Fq] Fq[T;T⁻¹] :=
  AdjoinRoot.liftAlgHom (abhPoly Fq n) (aeval (T n + T (-1)) : Fq[X] →ₐ[Fq] Fq[T;T⁻¹]) (T 1) (abh_eval_T Fq n)

/-- `x ↦ Y` (the root is a unit). -/
noncomputable def abhOfLaurent : Fq[T;T⁻¹] →ₐ[Fq] AdjoinRoot (abhPoly Fq n) :=
  { LaurentPolynomial.eval₂ (algebraMap Fq (AdjoinRoot (abhPoly Fq n))) (abhUnit Fq n) with
    commutes' := fun r => by
      show LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.C r) = _
      rw [LaurentPolynomial.eval₂_C] }

theorem abhOfLaurent_T (m : ℤ) :
    abhOfLaurent Fq n (T m) = (((abhUnit Fq n) ^ m : (AdjoinRoot (abhPoly Fq n))ˣ) : AdjoinRoot (abhPoly Fq n)) :=
  LaurentPolynomial.eval₂_T _ _ m

/-- **The Abhyankar cover is `G_m`**: `F_q[T][Y]/(Y^(n+1) - TY + 1) ≃ F_q[x, 1/x]`, `Y ↦ x`, `T ↦ x^n + 1/x`. -/
noncomputable def abhEquiv : AdjoinRoot (abhPoly Fq n) ≃ₐ[Fq] Fq[T;T⁻¹] :=
  AlgEquiv.ofAlgHom (abhToLaurent Fq n) (abhOfLaurent Fq n)
    (by
      apply AlgHom.coe_ringHom_injective
      apply IsLocalization.ringHom_ext (Submonoid.powers (X : Fq[X]))
      apply Polynomial.ringHom_ext
      · intro a
        show abhToLaurent Fq n (abhOfLaurent Fq n (algebraMap Fq[X] Fq[T;T⁻¹] (C a))) =
          algebraMap Fq[X] Fq[T;T⁻¹] (C a)
        rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C,
          show (LaurentPolynomial.C a : Fq[T;T⁻¹]) = algebraMap Fq Fq[T;T⁻¹] a from rfl, AlgHom.commutes,
          AlgHom.commutes]
      · show abhToLaurent Fq n (abhOfLaurent Fq n (algebraMap Fq[X] Fq[T;T⁻¹] X)) = algebraMap Fq[X] Fq[T;T⁻¹] X
        rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X, abhOfLaurent_T, zpow_one]
        show abhToLaurent Fq n (AdjoinRoot.root _) = _
        rw [abhToLaurent, AdjoinRoot.liftAlgHom_root])
    (by
      ext
      · show abhOfLaurent Fq n (abhToLaurent Fq n (AdjoinRoot.of _ X)) = AdjoinRoot.of _ X
        simp only [abhToLaurent, AdjoinRoot.liftAlgHom_of, aeval_X, map_add, abhOfLaurent_T, zpow_natCast,
          Units.val_pow_eq_pow_val, zpow_neg_one]
        show AdjoinRoot.root _ ^ n + (AdjoinRoot.of (abhPoly Fq n) X - AdjoinRoot.root _ ^ n) = _
        ring
      · show abhOfLaurent Fq n (abhToLaurent Fq n (AdjoinRoot.root _)) = AdjoinRoot.root _
        rw [abhToLaurent, AdjoinRoot.liftAlgHom_root, abhOfLaurent_T, zpow_one]
        rfl)

theorem abhEquiv_root : abhEquiv Fq n (AdjoinRoot.root _) = T 1 := by
  show abhToLaurent Fq n (AdjoinRoot.root _) = T 1
  rw [abhToLaurent, AdjoinRoot.liftAlgHom_root]

theorem abhEquiv_T : abhEquiv Fq n (AdjoinRoot.of _ X) = T n + T (-1) := by
  show abhToLaurent Fq n (AdjoinRoot.of _ X) = _
  rw [abhToLaurent, AdjoinRoot.liftAlgHom_of, aeval_X]

end AbhyankarCoverSol

theorem solution
    (F : Type*) [Field F] (n : ℕ) (hn : 1 ≤ n) (hp : (n : F) = 0) :
    Algebra.IsStandardEtale (Polynomial F)
        (AdjoinRoot (Polynomial.X ^ (n + 1) - Polynomial.C Polynomial.X * Polynomial.X + 1 :
          Polynomial (Polynomial F))) ∧
      Algebra.Etale (Polynomial F)
        (AdjoinRoot (Polynomial.X ^ (n + 1) - Polynomial.C Polynomial.X * Polynomial.X + 1 :
          Polynomial (Polynomial F))) ∧
      Module.Free (Polynomial F)
        (AdjoinRoot (Polynomial.X ^ (n + 1) - Polynomial.C Polynomial.X * Polynomial.X + 1 :
          Polynomial (Polynomial F))) ∧
      Module.Finite (Polynomial F)
        (AdjoinRoot (Polynomial.X ^ (n + 1) - Polynomial.C Polynomial.X * Polynomial.X + 1 :
          Polynomial (Polynomial F))) ∧
      Module.finrank (Polynomial F)
        (AdjoinRoot (Polynomial.X ^ (n + 1) - Polynomial.C Polynomial.X * Polynomial.X + 1 :
          Polynomial (Polynomial F))) = n + 1 ∧
      ∃ e : AdjoinRoot (Polynomial.X ^ (n + 1) - Polynomial.C Polynomial.X * Polynomial.X + 1 :
          Polynomial (Polynomial F)) ≃ₐ[F] LaurentPolynomial F,
        e (AdjoinRoot.root _) = LaurentPolynomial.T 1 ∧
          e (AdjoinRoot.of _ Polynomial.X) = LaurentPolynomial.T (n : ℤ) + LaurentPolynomial.T (-1) := by
  exact ⟨AbhyankarCoverSol.abh_isStandardEtale F n hn hp, AbhyankarCoverSol.abh_etale F n hn hp,
    AbhyankarCoverSol.abh_free F n hn, AbhyankarCoverSol.abh_finite F n hn, AbhyankarCoverSol.abh_finrank F n hn,
    AbhyankarCoverSol.abhEquiv F n, AbhyankarCoverSol.abhEquiv_root F n, AbhyankarCoverSol.abhEquiv_T F n⟩
