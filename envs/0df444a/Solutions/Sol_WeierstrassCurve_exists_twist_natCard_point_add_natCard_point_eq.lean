-- Prove2me | solution 1 for WeierstrassCurve.exists_twist_natCard_point_add_natCard_point_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T15:20:50.557173+00:00
-- url     : https://prove2.me/submissions/a8994823-25a8-449a-80b6-02cbb46c142a

import Mathlib
import Definitions.Def_RPLib_S2_TateNFA
import Definitions.Def_RPLib_S2_EllFq

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine RPLib.TateNF RPLib.EllFq

namespace RPLib.TwistCount

section Aut

variable {K : Type*} [Field K]

/-- The negation change of variables `(x, y) ↦ (x, -y - a₁x - a₃)`. -/
def negVC (W : WeierstrassCurve K) : VariableChange K := ⟨-1, 0, -W.a₁, -W.a₃⟩

lemma ui_negVC (W : WeierstrassCurve K) : ui (negVC W) = -1 := by
  simp [ui, negVC]

lemma negVC_smul (W : WeierstrassCurve K) : negVC W • W = W := by
  ext
  · rw [vc_a₁, ui_negVC]; simp only [negVC]; ring
  · rw [vc_a₂, ui_negVC]; simp only [negVC]; ring
  · rw [vc_a₃, ui_negVC]; simp only [negVC]; ring
  · rw [vc_a₄, ui_negVC]; simp only [negVC]; ring
  · rw [vc_a₆, ui_negVC]; simp only [negVC]; ring

lemma ptMap_negVC (W : WeierstrassCurve K) (h : negVC W • W = W) (P : W.toAffine.Point) :
    ptMap (negVC W) h P = -P := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · rw [ptMap_some, Point.neg_some, Point.some.injEq]
    simp only [vcX, vcY, ui_negVC]
    simp only [negVC, negY]
    constructor <;> ring

lemma negVC_mul_self (W : WeierstrassCurve K) : negVC W * negVC W = 1 := by
  rw [VariableChange.mul_def, VariableChange.one_def]
  simp only [negVC]
  congr 1 <;> first | (push_cast; ring) | simp

lemma vc_eq_of {C : VariableChange K} {u : Kˣ} {r s t : K} (hu : C.u = u) (hr : C.r = r)
    (hs : C.s = s) (ht : C.t = t) : C = ⟨u, r, s, t⟩ := by
  cases C; simp only at hu hr hs ht; subst hu hr hs ht; rfl

end Aut

section Frob

variable {F : Type*} [Field F] [Fintype F] {K : Type*} [Field K] [Algebra F K]

variable (F K) in
/-- The `q`-power Frobenius of `K` as a ring hom. -/
noncomputable def frobK : K →+* K := (FiniteField.frobeniusAlgHom F K : K →+* K)

lemma frobK_apply (x : K) : frobK F K x = x ^ Fintype.card F := rfl

lemma frobK_algebraMap (a : F) : frobK F K (algebraMap F K a) = algebraMap F K a :=
  (FiniteField.frobeniusAlgHom F K).commutes a

lemma frobK_eq_self_iff (x : K) : frobK F K x = x ↔ x ∈ (algebraMap F K).range := by
  rw [frobK_apply]; exact pow_card_eq_self_iff x

lemma baseChange_map_frobK (W : WeierstrassCurve F) :
    (W.baseChange K).map (frobK F K) = W.baseChange K :=
  WeierstrassCurve.map_baseChange (R := F) (S := F) (A := K) (B := K) W
    (FiniteField.frobeniusAlgHom F K)

lemma ui_map {L : Type*} [Field L] (C : VariableChange K) (φ : K →+* L) :
    ui (C.map φ) = φ (ui C) := by
  simp only [ui, VariableChange.map_u, Units.coe_map_inv, MonoidHom.coe_coe]

/-- The Frobenius conjugate of an isomorphism between base-changed curves is again one. -/
lemma frob_smul (C : VariableChange K) {W W' : WeierstrassCurve F}
    (h : C • W.baseChange K = W'.baseChange K) :
    C.map (frobK F K) • W.baseChange K = W'.baseChange K := by
  have e := map_variableChange (W.baseChange K) C (frobK F K)
  rw [baseChange_map_frobK W, h, baseChange_map_frobK W'] at e
  exact e

/-- **J3.** `σ ∘ ptMap C = ptMap (σ C) ∘ σ` on points of base-changed curves. -/
theorem frob_ptMap [DecidableEq K] (C : VariableChange K) {W W' : WeierstrassCurve F}
    (h : C • W.baseChange K = W'.baseChange K) (P : (W.baseChange K).toAffine.Point) :
    frob W' K (ptMap C h P) = ptMap (C.map (frobK F K)) (frob_smul C h) (frob W K P) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · obtain ⟨h1, e1⟩ := frob_some W K hxy
    rw [e1, ptMap_some, ptMap_some]
    obtain ⟨h2, e2⟩ := frob_some W' K (x := vcX C x) (y := vcY C x y)
      (h ▸ (nonsingular_vc (W.baseChange K) C x y).mpr hxy)
    rw [e2, Point.some.injEq]
    constructor <;> simp only [← frobK_apply, vcX, vcY, ui_map, VariableChange.map_r,
      VariableChange.map_s, VariableChange.map_t, map_mul, map_pow, map_sub]

omit [Fintype F] in
/-- A change of variables over `F`, base changed, maps base-changed curves. -/
lemma baseChange_smul (D : VariableChange F) {W W' : WeierstrassCurve F} (h : D • W = W') :
    D.baseChange K • W.baseChange K = W'.baseChange K := by
  rw [← h]; exact map_variableChange W D (algebraMap F K)

omit [Fintype F] in
/-- Point maps of changes of variables over `F` commute with base change. -/
theorem ptMap_baseChange [DecidableEq F] [DecidableEq K] (D : VariableChange F)
    {W W' : WeierstrassCurve F} (h : D • W = W') (hK : D.baseChange K • W.baseChange K = W'.baseChange K)
    (P : W.toAffine.Point) :
    ptMap (D.baseChange K) hK (baseChangePt W K P) = baseChangePt W' K (ptMap D h P) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · obtain ⟨h1, e1⟩ := baseChangePt_some W K hxy
    rw [e1, ptMap_some, ptMap_some]
    obtain ⟨h2, e2⟩ := baseChangePt_some W' K (x := vcX D x) (y := vcY D x y)
      (h ▸ (nonsingular_vc W D x y).mpr hxy)
    rw [e2, Point.some.injEq]
    constructor <;> simp only [vcX, vcY, VariableChange.baseChange, ui_map, VariableChange.map_r,
      VariableChange.map_s, VariableChange.map_t, map_mul, map_pow, map_sub]

/-- Galois descent for changes of variables. -/
theorem exists_vc_of_frobK (C : VariableChange K) (hC : C.map (frobK F K) = C) :
    ∃ D : VariableChange F, D.baseChange K = C := by
  have hu : frobK F K (C.u : K) = C.u := by
    simpa using congrArg (fun D : VariableChange K => (D.u : K)) hC
  have hr : frobK F K C.r = C.r := by simpa using congrArg VariableChange.r hC
  have hs : frobK F K C.s = C.s := by simpa using congrArg VariableChange.s hC
  have ht : frobK F K C.t = C.t := by simpa using congrArg VariableChange.t hC
  obtain ⟨a, ha⟩ := RingHom.mem_range.mp ((frobK_eq_self_iff _).mp hu)
  obtain ⟨b, hb⟩ := RingHom.mem_range.mp ((frobK_eq_self_iff _).mp hr)
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp ((frobK_eq_self_iff _).mp hs)
  obtain ⟨d, hd⟩ := RingHom.mem_range.mp ((frobK_eq_self_iff _).mp ht)
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [map_zero] at ha; exact C.u.ne_zero ha.symm
  refine ⟨⟨Units.mk0 a ha0, b, c, d⟩, ?_⟩
  symm
  exact vc_eq_of (Units.ext (by simp [ha])) hb.symm hc.symm hd.symm

/-- Galois descent for Weierstrass curves. -/
theorem exists_curve_of_frobK (X : WeierstrassCurve K) (hX : X.map (frobK F K) = X) :
    ∃ W : WeierstrassCurve F, W.baseChange K = X := by
  have h1 : frobK F K X.a₁ = X.a₁ := by simpa using congrArg WeierstrassCurve.a₁ hX
  have h2 : frobK F K X.a₂ = X.a₂ := by simpa using congrArg WeierstrassCurve.a₂ hX
  have h3 : frobK F K X.a₃ = X.a₃ := by simpa using congrArg WeierstrassCurve.a₃ hX
  have h4 : frobK F K X.a₄ = X.a₄ := by simpa using congrArg WeierstrassCurve.a₄ hX
  have h6 : frobK F K X.a₆ = X.a₆ := by simpa using congrArg WeierstrassCurve.a₆ hX
  obtain ⟨b1, e1⟩ := RingHom.mem_range.mp ((frobK_eq_self_iff _).mp h1)
  obtain ⟨b2, e2⟩ := RingHom.mem_range.mp ((frobK_eq_self_iff _).mp h2)
  obtain ⟨b3, e3⟩ := RingHom.mem_range.mp ((frobK_eq_self_iff _).mp h3)
  obtain ⟨b4, e4⟩ := RingHom.mem_range.mp ((frobK_eq_self_iff _).mp h4)
  obtain ⟨b6, e6⟩ := RingHom.mem_range.mp ((frobK_eq_self_iff _).mp h6)
  refine ⟨⟨b1, b2, b3, b4, b6⟩, ?_⟩
  ext <;> simp [WeierstrassCurve.baseChange, e1, e2, e3, e4, e6]

end Frob

section Twist

variable {F : Type*} [Field F] [Fintype F] {K : Type*} [Field K] [Algebra F K] [IsAlgClosed K]

lemma two_le_card : 2 ≤ Fintype.card F := Fintype.one_lt_card

/-- In an algebraically closed extension there is `u ≠ 0` with `σ u = -u`. -/
lemma exists_frobK_eq_neg : ∃ u : K, u ≠ 0 ∧ frobK F K u = -u := by
  have hq := two_le_card (F := F)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) (n := Fintype.card F - 1) (by omega)
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hu
    exact one_ne_zero (neg_eq_zero.mp hu.symm)
  refine ⟨u, hu0, ?_⟩
  rw [frobK_apply, show Fintype.card F = (Fintype.card F - 1) + 1 by omega, pow_succ, hu]
  ring

open Polynomial in
/-- In an algebraically closed extension, `σ s = -s - a` is solvable for every `a`. -/
lemma exists_frobK_eq_neg_sub (a : K) : ∃ s : K, frobK F K s = -s - a := by
  have hq := two_le_card (F := F)
  have hlt : (X + C a : K[X]).degree < (X ^ Fintype.card F : K[X]).degree := by
    rw [degree_X_add_C, degree_X_pow]; exact_mod_cast (by omega : 1 < Fintype.card F)
  have hdeg : (X ^ Fintype.card F + (X + C a) : K[X]).degree = Fintype.card F := by
    rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_root (X ^ Fintype.card F + (X + C a) : K[X])
    (by rw [hdeg]; exact_mod_cast (by omega : Fintype.card F ≠ 0))
  refine ⟨s, ?_⟩
  have hs' := hs.eq_zero
  simp only [eval_add, eval_pow, eval_X, eval_C] at hs'
  rw [frobK_apply]; linear_combination hs'

/-- **J4.** The quadratic twist: for every `W` over `F` there are `Wt` over `F` and a change of
variables `Ct` over `K` with `Ct • W_K = Wt_K` and `σ(Ct) = Ct * negVC W_K`. -/
theorem exists_twist (W : WeierstrassCurve F) :
    ∃ (Wt : WeierstrassCurve F) (Ct : VariableChange K),
      Ct • W.baseChange K = Wt.baseChange K ∧
        Ct.map (frobK F K) = Ct * negVC (W.baseChange K) := by
  obtain ⟨u, hu0, hu⟩ := exists_frobK_eq_neg (F := F) (K := K)
  obtain ⟨s, hs⟩ := exists_frobK_eq_neg_sub (F := F) ((W.baseChange K).a₁)
  obtain ⟨t, ht⟩ := exists_frobK_eq_neg_sub (F := F) ((W.baseChange K).a₃)
  have key : (⟨Units.mk0 u hu0, 0, s, t⟩ : VariableChange K).map (frobK F K) =
      ⟨Units.mk0 u hu0, 0, s, t⟩ * negVC (W.baseChange K) := by
    rw [VariableChange.mul_def]
    refine vc_eq_of ?_ ?_ ?_ ?_
    · ext; simp [negVC, hu]
    · simp [negVC]
    · simp only [VariableChange.map_s, negVC, hs]; push_cast; ring
    · simp only [VariableChange.map_t, negVC, ht]; push_cast; ring
  have hX : ((⟨Units.mk0 u hu0, 0, s, t⟩ : VariableChange K) • W.baseChange K).map (frobK F K) =
      (⟨Units.mk0 u hu0, 0, s, t⟩ : VariableChange K) • W.baseChange K := by
    rw [← map_variableChange, baseChange_map_frobK, key, mul_smul, negVC_smul]
  obtain ⟨Wt, hWt⟩ := exists_curve_of_frobK _ hX
  exact ⟨Wt, _, hWt.symm, key⟩

end Twist

section PointEquiv

variable {L : Type*} [Field L]

/-- Points satisfying a predicate that holds at `0` and is given coordinatewise on affine points. -/
def ptSubtypeEquiv (W : WeierstrassCurve L) (Pr : W.toAffine.Point → Prop) (h0 : Pr 0)
    (pr : L → L → Prop) (hs : ∀ x y (h : W.toAffine.Nonsingular x y), Pr (.some x y h) ↔ pr x y) :
    {R // Pr R} ≃ Option {p : L × L // W.toAffine.Nonsingular p.1 p.2 ∧ pr p.1 p.2} where
  toFun R := match R with
    | ⟨.zero, _⟩ => none
    | ⟨.some x y h, hR⟩ => some ⟨(x, y), h, (hs x y h).mp hR⟩
  invFun o := match o with
    | none => ⟨0, h0⟩
    | some p => ⟨.some p.1.1 p.1.2 p.2.1, (hs _ _ _).mpr p.2.2⟩
  left_inv := by rintro ⟨_ | ⟨x, y, h⟩, hR⟩ <;> rfl
  right_inv := by rintro (_ | ⟨⟨x, y⟩, h1, h2⟩) <;> rfl

end PointEquiv

section Count

variable {F : Type*} [Field F] [Fintype F] {K : Type*} [Field K] [DecidableEq K] [Algebra F K]
  (W : WeierstrassCurve F)

lemma frob_some_eq_self_iff {x y : K} (h : (W.baseChange K).toAffine.Nonsingular x y) :
    frob W K (.some x y h) = .some x y h ↔ frobK F K x = x ∧ frobK F K y = y := by
  obtain ⟨h', e⟩ := frob_some W K h
  rw [e, Point.some.injEq]; exact Iff.rfl

lemma frob_some_eq_neg_iff {x y : K} (h : (W.baseChange K).toAffine.Nonsingular x y) :
    frob W K (.some x y h) = -(.some x y h) ↔
      frobK F K x = x ∧ frobK F K y = (W.baseChange K).toAffine.negY x y := by
  obtain ⟨h', e⟩ := frob_some W K h
  rw [e, Point.neg_some, Point.some.injEq]; exact Iff.rfl

/-- `a₁ x₀ + a₃`. -/
def bF (x0 : F) : F := W.a₁ * x0 + W.a₃

/-- `x₀³ + a₂ x₀² + a₄ x₀ + a₆`. -/
def cF (x0 : F) : F := x0 ^ 3 + W.a₂ * x0 ^ 2 + W.a₄ * x0 + W.a₆

omit [Fintype F] [DecidableEq K] in
lemma equation_baseChange_iff (x0 : F) (y : K) :
    (W.baseChange K).toAffine.Equation (algebraMap F K x0) y ↔
      y ^ 2 + algebraMap F K (bF W x0) * y - algebraMap F K (cF W x0) = 0 := by
  rw [equation_iff]
  simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, bF, cF, map_add,
    map_mul, map_pow]
  constructor <;> intro h <;> linear_combination h

omit [Fintype F] [DecidableEq K] in
lemma negY_baseChange (x0 : F) (y : K) :
    (W.baseChange K).toAffine.negY (algebraMap F K x0) y = -y - algebraMap F K (bF W x0) := by
  simp only [negY, WeierstrassCurve.baseChange, map_a₁, map_a₃, bF, map_add, map_mul]; ring

omit [DecidableEq K] in
lemma root_pair {b c y z : K} (hy : y ^ 2 + b * y - c = 0) (hz : z ^ 2 + b * z - c = 0) :
    z = y ∨ z = -y - b := by
  have : (z - y) * (z - (-y - b)) = 0 := by linear_combination hz - hy
  rcases mul_eq_zero.mp this with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact sub_eq_zero.mp h

omit [Fintype F] [Algebra F K] in
lemma count_pt {b y s : K} (h : s = y ∨ s = -y - b) :
    ((if s = y then 1 else 0) + (if s = -y - b then 1 else 0) : ℕ) = if y = -y - b then 2 else 1 := by
  rcases h with rfl | rfl
  · by_cases hy : s = -s - b
    · rw [if_pos rfl, if_pos hy, if_pos hy]
    · rw [if_pos rfl, if_neg hy, if_neg hy]
  · by_cases hy : y = -y - b
    · rw [if_pos hy.symm, if_pos rfl, if_pos hy]
    · rw [if_neg (Ne.symm hy), if_pos rfl, if_neg hy]

variable [IsAlgClosed K]

open Polynomial in
omit [Fintype F] [DecidableEq K] [Algebra F K] in
lemma exists_quad_root (b c : K) : ∃ y : K, y ^ 2 + b * y - c = 0 := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (C 1 * X ^ 2 + C b * X + C (-c) : K[X])
    (by rw [degree_quadratic one_ne_zero]; exact_mod_cast (by norm_num : (2 : ℕ) ≠ 0))
  refine ⟨y, ?_⟩
  have h := hy.eq_zero
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X] at h
  linear_combination h

/-- A root of the fibre equation over `x₀`. -/
noncomputable def y1 (x0 : F) : K :=
  Classical.choose (exists_quad_root (algebraMap F K (bF W x0)) (algebraMap F K (cF W x0)))

omit [Fintype F] [DecidableEq K] in
lemma y1_spec (x0 : F) : y1 W (K := K) x0 ^ 2 + algebraMap F K (bF W x0) * y1 W x0 -
    algebraMap F K (cF W x0) = 0 :=
  Classical.choose_spec (exists_quad_root _ _)

/-- The fibre of `W_K` over `x₀ ∈ F`: `{y₁, -y₁ - b}`. -/
noncomputable def fibre (x0 : F) : Finset K := {y1 W x0, -y1 W x0 - algebraMap F K (bF W x0)}

omit [Fintype F] in
lemma mem_fibre (x0 : F) (y : K) :
    y ∈ fibre W (K := K) x0 ↔ (W.baseChange K).toAffine.Equation (algebraMap F K x0) y := by
  rw [equation_baseChange_iff, fibre, Finset.mem_insert, Finset.mem_singleton]
  have h := y1_spec W (K := K) x0
  constructor
  · rintro (rfl | rfl) <;> linear_combination h
  · intro hy
    exact root_pair h hy

lemma card_fibre_filter (x0 : F) :
    ((fibre W (K := K) x0).filter (fun y => frobK F K y = y)).card +
      ((fibre W (K := K) x0).filter
        (fun y => frobK F K y = -y - algebraMap F K (bF W x0))).card = 2 := by
  have hroot : ∀ y ∈ fibre W (K := K) x0,
      y ^ 2 + algebraMap F K (bF W x0) * y - algebraMap F K (cF W x0) = 0 := fun y hy =>
    (equation_baseChange_iff W x0 y).mp ((mem_fibre W x0 y).mp hy)
  have hσ : ∀ y ∈ fibre W (K := K) x0,
      frobK F K y = y ∨ frobK F K y = -y - algebraMap F K (bF W x0) := fun y hy => by
    refine root_pair (hroot y hy) ?_
    have := congrArg (frobK F K) (hroot y hy)
    simpa only [map_sub, map_add, map_mul, map_pow, frobK_algebraMap, map_zero] using this
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun y hy => count_pt (hσ y hy))]
  have h1 : y1 W (K := K) x0 ∈ fibre W (K := K) x0 := Finset.mem_insert_self _ _
  by_cases h12 : y1 W (K := K) x0 = -y1 W x0 - algebraMap F K (bF W x0)
  · have hR : fibre W (K := K) x0 = {y1 W x0} := by
      rw [fibre, ← h12]; exact Finset.insert_eq_of_mem (Finset.mem_singleton_self _)
    rw [hR, Finset.sum_singleton, if_pos h12]
  · rw [fibre, Finset.sum_pair h12, if_neg h12, if_neg]
    intro h; apply h12; linear_combination -h

/-- The fibrewise description of the affine points of `W_K` with `σ x = x` and `σ y = g x₀ y`. -/
noncomputable def sigmaEquiv (hΔ : W.Δ ≠ 0) (g : F → K → K) (condK : K → K → Prop)
    (hc : ∀ x0 y, condK (algebraMap F K x0) y ↔ frobK F K y = g x0 y) :
    (Σ x0 : F, ↥((fibre W (K := K) x0).filter (fun y => frobK F K y = g x0 y))) ≃
      {p : K × K // (W.baseChange K).toAffine.Nonsingular p.1 p.2 ∧
        (frobK F K p.1 = p.1 ∧ condK p.1 p.2)} := by
  have hΔK : (W.baseChange K).Δ ≠ 0 := by simp [WeierstrassCurve.baseChange, hΔ]
  refine Equiv.ofBijective (fun z => ⟨(algebraMap F K z.1, z.2.1), ?_, ?_, ?_⟩) ⟨?_, ?_⟩
  · have hz := Finset.mem_filter.mp z.2.2
    exact ((W.baseChange K).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔK).mp
      ((mem_fibre W z.1 z.2.1).mp hz.1)
  · exact frobK_algebraMap _
  · exact (hc z.1 z.2.1).mpr (Finset.mem_filter.mp z.2.2).2
  · rintro ⟨x0, y⟩ ⟨x0', y'⟩ h
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := (algebraMap F K).injective h1
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact Subtype.ext h2
  · rintro ⟨⟨x, y⟩, hns, hx, hcy⟩
    obtain ⟨x0, rfl⟩ := RingHom.mem_range.mp ((frobK_eq_self_iff x).mp hx)
    refine ⟨⟨x0, ⟨y, Finset.mem_filter.mpr ⟨(mem_fibre W x0 y).mpr hns.1, (hc x0 y).mp hcy⟩⟩⟩, rfl⟩

/-- **J5 (twist count).** `#{σR = R} + #{σR = -R} = 2q + 2` on `W(K)`. -/
theorem card_fix_add_card_negfix (hΔ : W.Δ ≠ 0) :
    Nat.card {R : (W.baseChange K).toAffine.Point // frob W K R = R} +
      Nat.card {R : (W.baseChange K).toAffine.Point // frob W K R = -R} =
        2 * Fintype.card F + 2 := by
  have cP : Nat.card {R : (W.baseChange K).toAffine.Point // frob W K R = R} =
      ∑ x0 : F, ((fibre W (K := K) x0).filter (fun y => frobK F K y = y)).card + 1 := by
    have e := (ptSubtypeEquiv (W.baseChange K) (fun R => frob W K R = R) (frob_zero W K)
      (fun x y => frobK F K x = x ∧ frobK F K y = y) (fun x y h => frob_some_eq_self_iff W h)).trans
      (Equiv.optionCongr (sigmaEquiv W hΔ (fun _ y => y) (fun _ y => frobK F K y = y)
        (fun _ _ => Iff.rfl)).symm)
    rw [Nat.card_congr e, Finite.card_option, Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp only [Fintype.card_coe]
  have cN : Nat.card {R : (W.baseChange K).toAffine.Point // frob W K R = -R} =
      ∑ x0 : F, ((fibre W (K := K) x0).filter
        (fun y => frobK F K y = -y - algebraMap F K (bF W x0))).card + 1 := by
    have e := (ptSubtypeEquiv (W.baseChange K) (fun R => frob W K R = -R)
      (by rw [frob_zero, neg_zero])
      (fun x y => frobK F K x = x ∧ frobK F K y = (W.baseChange K).toAffine.negY x y)
      (fun x y h => frob_some_eq_neg_iff W h)).trans
      (Equiv.optionCongr (sigmaEquiv W hΔ (fun x0 y => -y - algebraMap F K (bF W x0))
        (fun x y => frobK F K y = (W.baseChange K).toAffine.negY x y)
        (fun x0 y => by rw [negY_baseChange])).symm)
    rw [Nat.card_congr e, Finite.card_option, Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp only [Fintype.card_coe]
  rw [cP, cN, add_add_add_comm, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun x0 _ => card_fibre_filter W x0)]
  simp [Finset.sum_const, Finset.card_univ, mul_comm]

end Count

section PtEquiv

variable {L : Type*} [Field L]

/-- The point map of a change of variables as an equivalence. -/
def ptEquiv (C : VariableChange L) {W W' : WeierstrassCurve L} (h : C • W = W') :
    W.toAffine.Point ≃ W'.toAffine.Point where
  toFun := ptMap C h
  invFun := ptMap C⁻¹ (inv_smul_eq C h)
  left_inv := ptMap_inv_ptMap C h (inv_smul_eq C h)
  right_inv S := by
    have h'' : C⁻¹⁻¹ • W = W' := by rw [inv_inv]; exact h
    rw [ptMap_congr (inv_inv C).symm h h'']
    exact ptMap_inv_ptMap C⁻¹ (inv_smul_eq C h) h'' S

lemma ptEquiv_apply (C : VariableChange L) {W W' : WeierstrassCurve L} (h : C • W = W')
    (R : W.toAffine.Point) : ptEquiv C h R = ptMap C h R := rfl

end PtEquiv

end RPLib.TwistCount

open RPLib.TwistCount in
theorem solution
    {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic] :
    ∃ W' : WeierstrassCurve F,
      (∃ C : WeierstrassCurve.VariableChange (AlgebraicClosure F),
        C • W.baseChange (AlgebraicClosure F) = W'.baseChange (AlgebraicClosure F)) ∧
      Nat.card W.toAffine.Point + Nat.card W'.toAffine.Point = 2 * Fintype.card F + 2 := by
  classical
  obtain ⟨Wt, Ct, h, hσ⟩ := exists_twist (K := AlgebraicClosure F) W
  refine ⟨Wt, ⟨Ct, h⟩, ?_⟩
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  have hN : (negVC (W.baseChange (AlgebraicClosure F))) • W.baseChange (AlgebraicClosure F) =
      W.baseChange (AlgebraicClosure F) := negVC_smul _
  have hCN : (Ct * negVC (W.baseChange (AlgebraicClosure F))) • W.baseChange (AlgebraicClosure F) =
      Wt.baseChange (AlgebraicClosure F) := by rw [mul_smul, hN, h]
  have key : ∀ R, frob Wt (AlgebraicClosure F) (ptMap Ct h R) =
      ptMap Ct h (-frob W (AlgebraicClosure F) R) := by
    intro R
    rw [frob_ptMap Ct h, ptMap_congr hσ (frob_smul Ct h) hCN, ptMap_mul Ct _ hN h hCN, ptMap_negVC]
  have hW : Nat.card W.toAffine.Point =
      Nat.card {R : (W.baseChange (AlgebraicClosure F)).toAffine.Point //
        frob W (AlgebraicClosure F) R = R} :=
    numPoints_eq_card_fixed W (AlgebraicClosure F)
  have hWt : Nat.card Wt.toAffine.Point =
      Nat.card {R : (W.baseChange (AlgebraicClosure F)).toAffine.Point //
        frob W (AlgebraicClosure F) R = -R} := by
    rw [show Nat.card Wt.toAffine.Point = numPoints Wt from rfl,
      numPoints_eq_card_fixed Wt (AlgebraicClosure F)]
    symm
    refine Nat.card_congr ((ptEquiv Ct h).subtypeEquiv fun R => ?_)
    rw [ptEquiv_apply, key, (ptMap_injective Ct h).eq_iff, neg_eq_iff_eq_neg]
  rw [hW, hWt]
  exact card_fix_add_card_negfix (K := AlgebraicClosure F) W hΔ

