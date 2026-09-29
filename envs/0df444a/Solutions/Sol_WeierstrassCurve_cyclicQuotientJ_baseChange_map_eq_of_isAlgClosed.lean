-- Prove2me | solution 1 for WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0a79555a-b1f9-5733-acb2-703bb429f768

import Mathlib
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_VeluEquivariance
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed

open WeierstrassCurve

namespace P2MKcCQJbc

variable {A B : Type*} [Field A] [Field B] [DecidableEq A] [DecidableEq B] (f : A →+* B)

noncomputable def ptMap (V : WeierstrassCurve A) : V.toAffine.Point →+ (V.map f).toAffine.Point :=
  letI : Algebra A B := f.toAlgebra
  (WeierstrassCurve.Affine.Point.map (W' := V) (Algebra.ofId A B) :
    (V.baseChange A).toAffine.Point →+ (V.baseChange B).toAffine.Point)

theorem ptMap_zero (V : WeierstrassCurve A) : ptMap f V 0 = 0 := rfl

theorem ptMap_some (V : WeierstrassCurve A) {x y : A} (h : V.toAffine.Nonsingular x y) :
    ptMap f V (.some x y h) = .some (f x) (f y) ((Affine.map_nonsingular _ f.injective x y).2 h) := rfl

theorem ptMap_injective (V : WeierstrassCurve A) : Function.Injective (ptMap f V) := by
  letI : Algebra A B := f.toAlgebra
  exact WeierstrassCurve.Affine.Point.map_injective (W' := V) (Algebra.ofId A B)

theorem coordsOrZero_ptMap (V : WeierstrassCurve A) (P : V.toAffine.Point) :
    (ptMap f V P).coordsOrZero = Prod.map f f P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · change (ptMap f V 0).coordsOrZero = Prod.map f f (0, 0)
    rw [ptMap_zero]
    change ((0, 0) : B × B) = (f 0, f 0)
    rw [map_zero]
  · rfl

theorem ptMap_ne_zero (V : WeierstrassCurve A) {P : V.toAffine.Point} :
    ptMap f V P ≠ 0 ↔ P ≠ 0 := by
  rw [Ne, Ne, ← ptMap_zero f V, (ptMap_injective f V).eq_iff]

theorem kernelXSet_map (V : WeierstrassCurve A) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) :
    (V.map f).kernelXSet (H.map (ptMap f V)) ℓ = f '' V.kernelXSet H ℓ := by
  ext x'
  simp only [kernelXSet, Set.mem_image, Set.mem_setOf_eq, AddSubgroup.mem_map]
  constructor
  · rintro ⟨P', ⟨⟨P, hP, rfl⟩, hne, hsm⟩, rfl⟩
    refine ⟨P.coordsOrZero.1, ⟨P, ⟨hP, (ptMap_ne_zero f V).1 hne, ?_⟩, rfl⟩, ?_⟩
    · apply ptMap_injective f V
      rw [map_nsmul, hsm, map_zero]
    · rw [coordsOrZero_ptMap]; rfl
  · rintro ⟨x, ⟨P, ⟨hP, hne, hsm⟩, rfl⟩, rfl⟩
    refine ⟨ptMap f V P, ⟨⟨P, hP, rfl⟩, (ptMap_ne_zero f V).2 hne, ?_⟩, ?_⟩
    · rw [← map_nsmul, hsm, map_zero]
    · rw [coordsOrZero_ptMap]; rfl

theorem coKernelXSet_map (V : WeierstrassCurve A) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) :
    (V.map f).coKernelXSet (H.map (ptMap f V)) ℓ = f '' V.coKernelXSet H ℓ := by
  ext x'
  simp only [coKernelXSet, Set.mem_image, Set.mem_setOf_eq, AddSubgroup.mem_map]
  constructor
  · rintro ⟨P', ⟨⟨P, hP, rfl⟩, hsm⟩, rfl⟩
    refine ⟨P.coordsOrZero.1, ⟨P, ⟨hP, fun h => hsm ?_⟩, rfl⟩, ?_⟩
    · rw [← map_nsmul, h, map_zero]
    · rw [coordsOrZero_ptMap]; rfl
  · rintro ⟨x, ⟨P, ⟨hP, hsm⟩, rfl⟩, rfl⟩
    refine ⟨ptMap f V P, ⟨⟨P, hP, rfl⟩, fun h => hsm ?_⟩, ?_⟩
    · apply ptMap_injective f V
      rw [map_nsmul, h, map_zero]
    · rw [coordsOrZero_ptMap]; rfl

omit [DecidableEq A] [DecidableEq B] in
theorem xVeluT_map (V : WeierstrassCurve A) (x : A) : (V.map f).xVeluT (f x) = f (V.xVeluT x) := by
  simp only [xVeluT, map_b₂, map_b₄, map_add, map_mul, map_pow, map_ofNat]

omit [DecidableEq A] [DecidableEq B] in
theorem xVeluU_map (V : WeierstrassCurve A) (x : A) : (V.map f).xVeluU (f x) = f (V.xVeluU x) := by
  simp only [xVeluU, map_b₂, map_b₄, map_b₆, map_add, map_mul, map_pow, map_ofNat]

omit [DecidableEq A] [DecidableEq B] in
theorem xVeluW_map (V : WeierstrassCurve A) (x : A) : (V.map f).xVeluW (f x) = f (V.xVeluW x) := by
  simp [xVeluW, xVeluT_map, xVeluU_map]

omit [DecidableEq A] [DecidableEq B] in
theorem twoTorsionY_map (V : WeierstrassCurve A) (x : A) :
    (V.map f).twoTorsionY (f x) = f (V.twoTorsionY x) := by
  simp only [twoTorsionY, map_a₁, map_a₃, map_div₀, map_neg, map_add, map_mul, map_ofNat]

omit [DecidableEq A] [DecidableEq B] in
theorem xVeluG_map (V : WeierstrassCurve A) (x : A) : (V.map f).xVeluG (f x) = f (V.xVeluG x) := by
  rw [xVeluG, xVeluG, twoTorsionY_map, map_veluGx]

omit [DecidableEq A] [DecidableEq B] in

theorem absSum_image_eq {TA : A → A} {TB : B → B} (hT : ∀ x, TB (f x) = f (TA x)) (X : Set A) :
    absSum (f '' X) TB = f (absSum X TA) := by
  by_cases hX : X.Finite
  · have hX' : (f '' X).Finite := hX.image f
    rw [absSum, if_pos hX', absSum, if_pos hX, finsum_mem_image f.injective.injOn]
    simp_rw [hT]
    exact ((f : A →+ B).map_finsum_mem' (hX.inter_of_left _)).symm
  · have hX' : ¬ (f '' X).Finite := fun h => hX (Set.Finite.of_finite_image h f.injective.injOn)
    rw [absSum, if_neg hX', absSum, if_neg hX, map_zero]

omit [DecidableEq A] [DecidableEq B] in
theorem xVeluCurve_map (V : WeierstrassCurve A) (X : Set A) :
    (V.map f).xVeluCurve (f '' X) = (V.xVeluCurve X).map f := by
  have hT := absSum_image_eq f (xVeluT_map f V) X
  have hW := absSum_image_eq f (xVeluW_map f V) X
  ext
  · rfl
  · rfl
  · rfl
  · simp only [xVeluCurve_a₄, map_a₄, hT, map_sub, map_mul, map_ofNat]
  · simp only [xVeluCurve_a₆, map_a₆, map_b₂, hT, hW, map_sub, map_mul, map_ofNat]

omit [DecidableEq A] [DecidableEq B] in
theorem twoVeluCurve_map (V : WeierstrassCurve A) (X : Set A) :
    (V.map f).twoVeluCurve (f '' X) = (V.twoVeluCurve X).map f := by
  have hG := absSum_image_eq f (xVeluG_map f V) X
  have hXG := absSum_image_eq f (TA := fun x => x * V.xVeluG x)
    (TB := fun y => y * (V.map f).xVeluG y) (fun x => by simp only [xVeluG_map, map_mul]) X
  ext
  · rfl
  · rfl
  · rfl
  · simp only [twoVeluCurve_a₄, map_a₄, hG, map_sub, map_mul, map_ofNat]
  · simp only [twoVeluCurve_a₆, map_a₆, map_b₂, hG, hXG, map_sub, map_mul, map_ofNat]

omit [DecidableEq A] [DecidableEq B] in
theorem xVeluX_map (V : WeierstrassCurve A) (X : Set A) (x : A) :
    (V.map f).xVeluX (f '' X) (f x) = f (V.xVeluX X x) := by
  rw [xVeluX, xVeluX, map_add, absSum_image_eq f
    (TA := fun x₀ => V.xVeluT x₀ / (x - x₀) + V.xVeluU x₀ / (x - x₀) ^ 2)
    (TB := fun y₀ => (V.map f).xVeluT y₀ / (f x - y₀) + (V.map f).xVeluU y₀ / (f x - y₀) ^ 2)]
  intro x₀
  simp only [xVeluT_map, xVeluU_map, map_add, map_div₀, map_sub, map_pow]

omit [DecidableEq A] [DecidableEq B] in
theorem twoVeluX_map (V : WeierstrassCurve A) (X : Set A) (x : A) :
    (V.map f).twoVeluX (f '' X) (f x) = f (V.twoVeluX X x) := by
  rw [twoVeluX, twoVeluX, map_add, absSum_image_eq f
    (TA := fun x₀ => V.xVeluG x₀ / (x - x₀)) (TB := fun y₀ => (V.map f).xVeluG y₀ / (f x - y₀))]
  intro x₀
  simp only [xVeluG_map, map_div₀, map_sub]

theorem stepCurve_map (V : WeierstrassCurve A) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) :
    (V.map f).stepCurve (H.map (ptMap f V)) ℓ = (V.stepCurve H ℓ).map f := by
  by_cases hℓ : ℓ = 2
  · subst hℓ
    rw [stepCurve_two, stepCurve_two, kernelXSet_map, twoVeluCurve_map]
  · rw [stepCurve_of_ne_two _ _ hℓ, stepCurve_of_ne_two _ _ hℓ, kernelXSet_map, xVeluCurve_map]

theorem stepX_map (V : WeierstrassCurve A) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) (x : A) :
    (V.map f).stepX (H.map (ptMap f V)) ℓ (f x) = f (V.stepX H ℓ x) := by
  by_cases hℓ : ℓ = 2
  · subst hℓ
    rw [stepX_two, stepX_two, kernelXSet_map, twoVeluX_map]
  · rw [stepX_of_ne_two _ _ hℓ, stepX_of_ne_two _ _ hℓ, kernelXSet_map, xVeluX_map]

theorem subgroupOfX_map [IsAlgClosed A] (V : WeierstrassCurve A) (Y : Set A) :
    subgroupOfX (V.map f) (f '' Y) = (subgroupOfX V Y).map (ptMap f V) := by
  rw [subgroupOfX, subgroupOfX, AddMonoidHom.map_closure]
  congr 1
  ext P'
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hne, ⟨x, hxY, hx⟩⟩
    rcases P' with _ | ⟨x', y', h'⟩
    · exact absurd rfl hne
    · simp only [Affine.Point.coordsOrZero] at hx
      subst hx

      have heq : (V.map f).toAffine.Equation (f x) y' := h'.1
      set q : Polynomial A := Polynomial.X ^ 2 + Polynomial.C (V.a₁ * x + V.a₃) * Polynomial.X -
        Polynomial.C (x ^ 3 + V.a₂ * x ^ 2 + V.a₄ * x + V.a₆) with hq
      have hqm : q.Monic := by
        rw [hq]
        refine (Polynomial.monic_X_pow 2).add_of_left ?_ |>.sub_of_left ?_
        · exact (Polynomial.degree_C_mul_X_le _).trans_lt (by
            rw [Polynomial.degree_X_pow]; exact WithBot.coe_lt_coe.2 (by norm_num))
        · refine (Polynomial.degree_C_le).trans_lt ?_
          rw [Polynomial.degree_add_eq_left_of_degree_lt] <;> rw [Polynomial.degree_X_pow]
          · exact WithBot.coe_lt_coe.2 (by norm_num)
          · exact (Polynomial.degree_C_mul_X_le _).trans_lt (WithBot.coe_lt_coe.2 (by norm_num))
      have hsplit : (q.map f).Splits := (IsAlgClosed.splits q).map f
      have hroot : (q.map f).IsRoot y' := by
        rw [Affine.equation_iff] at heq
        simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
        rw [Polynomial.IsRoot.def, Polynomial.eval_map, hq]
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
          Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, map_add, map_mul, map_pow]
        linear_combination heq
      have hy' : y' ∈ (q.map f).roots := (Polynomial.mem_roots (Polynomial.map_ne_zero hqm.ne_zero)).2 hroot
      rw [(IsAlgClosed.splits q).roots_map f, Multiset.mem_map] at hy'
      obtain ⟨y, -, rfl⟩ := hy'
      have h : V.toAffine.Nonsingular x y := (Affine.map_nonsingular _ f.injective x y).1 h'
      exact ⟨.some x y h, ⟨Affine.Point.some_ne_zero h, hxY⟩, ptMap_some f V h⟩
  · rintro ⟨P, ⟨hne, hY⟩, rfl⟩
    refine ⟨(ptMap_ne_zero f V).2 hne, ⟨P.coordsOrZero.1, hY, ?_⟩⟩
    rw [coordsOrZero_ptMap]; rfl

noncomputable def stMap (s : CQJState A) : CQJState B :=
  ⟨⟨s.1.1.map f, s.1.2.map (ptMap f s.1.1)⟩, s.2⟩

theorem sigma_eq_of_eq {V₁ V₂ : WeierstrassCurve B} (h : V₁ = V₂) {Y₁ Y₂ : Set B} (hY : Y₁ = Y₂) :
    (⟨V₁, subgroupOfX V₁ Y₁⟩ : Σ V : WeierstrassCurve B, AddSubgroup V.toAffine.Point) =
      ⟨V₂, subgroupOfX V₂ Y₂⟩ := by
  subst h hY; rfl

theorem cqjStep_stMap [IsAlgClosed A] (s : CQJState A) : cqjStep (stMap f s) = stMap f (cqjStep s) := by
  obtain ⟨⟨V, H⟩, n⟩ := s
  change (⟨⟨(V.map f).stepCurve (H.map (ptMap f V)) n.minFac,
      (V.map f).stepSubgroup (H.map (ptMap f V)) n.minFac⟩, n / n.minFac⟩ : CQJState B) =
    ⟨⟨(V.stepCurve H n.minFac).map f, (V.stepSubgroup H n.minFac).map (ptMap f _)⟩, n / n.minFac⟩
  congr 1
  rw [stepSubgroup, stepSubgroup, ← subgroupOfX_map]
  refine sigma_eq_of_eq (stepCurve_map f V H _) ?_
  rw [coKernelXSet_map, Set.image_image, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  exact stepX_map f V H _ x

theorem iterate_cqjStep_stMap [IsAlgClosed A] (n : ℕ) (s : CQJState A) :
    cqjStep^[n] (stMap f s) = stMap f (cqjStep^[n] s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, cqjStep_stMap, ih]

theorem cyclicQuotientJ_map [IsAlgClosed A] (V : WeierstrassCurve A) (H : AddSubgroup V.toAffine.Point)
    (N : ℕ) : (V.map f).cyclicQuotientJ (H.map (ptMap f V)) N = f (V.cyclicQuotientJ H N) := by
  have h := iterate_cqjStep_stMap f N.primeFactorsList.length ⟨⟨V, H⟩, N⟩
  have hc : (V.map f).cyclicQuotientCurve (H.map (ptMap f V)) N = (V.cyclicQuotientCurve H N).map f := by
    rw [cyclicQuotientCurve_def, cyclicQuotientCurve_def, cqjIterate_def, cqjIterate_def]
    exact congrArg (fun s : CQJState B => s.1.1) h
  rw [cyclicQuotientJ_def, cyclicQuotientJ_def, hc, map_c₄, map_Δ, map_div₀, map_pow]

theorem cyclicQuotientJ_map' [IsAlgClosed A] (V : WeierstrassCurve A) (VB : WeierstrassCurve B)
    (hVB : V.map f = VB) (φ : V.toAffine.Point →+ VB.toAffine.Point)
    (hφ : ∀ (x y : A) (h : V.toAffine.Nonsingular x y), ∃ h', φ (.some x y h) = .some (f x) (f y) h')
    (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    VB.cyclicQuotientJ (H.map φ) N = f (V.cyclicQuotientJ H N) := by
  subst hVB
  have hφ' : φ = ptMap f V := by
    ext P
    rcases P with _ | ⟨x, y, h⟩
    · exact (map_zero φ).trans (map_zero _).symm
    · obtain ⟨h', e⟩ := hφ x y h
      rw [e, ptMap_some]
  rw [hφ']
  exact cyclicQuotientJ_map f V H N

end P2MKcCQJbc

open P2MKcCQJbc in
universe u v w in
theorem solution
    {R : Type u} [CommRing R] (E : WeierstrassCurve R)
    {A : Type v} {B : Type w} [Field A] [DecidableEq A] [IsAlgClosed A] [Field B] [DecidableEq B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (H : AddSubgroup (E.baseChange A).toAffine.Point) (N : ℕ) :
    (E.baseChange B).cyclicQuotientJ (H.map (WeierstrassCurve.Affine.Point.map f)) N =
      f ((E.baseChange A).cyclicQuotientJ H N) := by
  refine cyclicQuotientJ_map' (f : A →+* B) (E.baseChange A) (E.baseChange B) ?_ _ ?_ H N
  · exact E.map_baseChange f
  · intro x y h
    exact ⟨_, WeierstrassCurve.Affine.Point.map_some f h⟩

end S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed (solution)
