-- Prove2me | solution 1 for Viterbo.exists_polytope_prod_systolicRatio_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:04:49.695589+00:00
-- url     : https://prove2.me/submissions/3f5b7c0b-434d-47a5-b226-e5d31d0ba6d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_Viterbo_systolicRatio_pProduct_one_prod_pProduct_top
import Theorems.Thm_Viterbo_volume_pentagon_and_systolicRatio_pentagonK_prod_pentagonT
import Theorems.Thm_Viterbo_exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ
import Theorems.Thm_Viterbo_cEHZ_prod_eq_min_action_and_min_billiard_and_min_notTranslatable

namespace Viterbo.PolyProd

open OAI.SymmetricPolar Viterbo MeasureTheory Set
open scoped ENNReal Pointwise

/-! ## The pentagons are convex domains containing `0` -/

namespace Pent

/-- Generic: a finite family in the plane summing to zero with two independent members spans a convex domain. -/
theorem convDomain_of_sum_zero (v : ℕ → Position 2) (hsum : ∑ k ∈ Finset.range 5, v k = 0)
    (hdet : v 0 0 * v 1 1 - v 0 1 * v 1 0 ≠ 0) :
    IsConvexDomain (convexHull ℝ (v '' (Finset.range 5 : Set ℕ))) ∧
      (0 : Position 2) ∈ convexHull ℝ (v '' (Finset.range 5 : Set ℕ)) := by
  have hfin : (v '' (Finset.range 5 : Set ℕ)).Finite := (Finset.finite_toSet _).image _
  have h0 : (0 : Position 2) ∈ convexHull ℝ (v '' (Finset.range 5 : Set ℕ)) := by
    have : (0 : Position 2) = ∑ k ∈ Finset.range 5, (1 / 5 : ℝ) • v k := by
      rw [← Finset.smul_sum, hsum, smul_zero]
    rw [this]
    refine (convex_convexHull ℝ _).sum_mem (fun _ _ => by norm_num) (by simp) ?_
    intro k hk
    exact subset_convexHull ℝ _ ⟨k, by simpa using hk, rfl⟩
  refine ⟨⟨(isBounded_convexHull).mpr hfin.isBounded, convex_convexHull ℝ _, ?_⟩, h0⟩
  have hspan : affineSpan ℝ (v '' (Finset.range 5 : Set ℕ)) = ⊤ := by
    have h0s : (0 : Position 2) ∈ affineSpan ℝ (v '' (Finset.range 5 : Set ℕ)) :=
      convexHull_subset_affineSpan _ h0
    have hv : ∀ k ∈ Finset.range 5, v k ∈ affineSpan ℝ (v '' (Finset.range 5 : Set ℕ)) :=
      fun k hk => subset_affineSpan ℝ _ ⟨k, by simpa using hk, rfl⟩
    rw [← AffineSubspace.direction_eq_top_iff_of_nonempty ⟨0, h0s⟩]
    have hd : ∀ k ∈ Finset.range 5, v k ∈ (affineSpan ℝ (v '' (Finset.range 5 : Set ℕ))).direction := by
      intro k hk
      simpa using AffineSubspace.vsub_mem_direction (hv k hk) h0s
    have hli : LinearIndependent ℝ ![v 0, v 1] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have e0 := congrArg (fun w : Position 2 => w 0) hst
      have e1 := congrArg (fun w : Position 2 => w 1) hst
      simp at e0 e1
      have hs : s * (v 0 0 * v 1 1 - v 0 1 * v 1 0) = 0 := by linear_combination v 1 1 * e0 - v 1 0 * e1
      have ht : t * (v 0 0 * v 1 1 - v 0 1 * v 1 0) = 0 := by linear_combination v 0 0 * e1 - v 0 1 * e0
      exact ⟨(mul_eq_zero.mp hs).resolve_right hdet, (mul_eq_zero.mp ht).resolve_right hdet⟩
    have htop : Submodule.span ℝ (Set.range ![v 0, v 1]) = ⊤ := by
      apply hli.span_eq_top_of_card_eq_finrank'
      simp
    rw [eq_top_iff, ← htop, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hd 0 (by simp)
    · exact hd 1 (by simp)
  have := (interior_convexHull_nonempty_iff_affineSpan_eq_top (s := v '' (Finset.range 5 : Set ℕ))).mpr hspan
  exact this


open Real in
theorem trig_vals :
    Real.cos (2 * π / 5) = (√5 - 1) / 4 ∧ Real.cos (4 * π / 5) = -(1 + √5) / 4 ∧
    Real.cos (6 * π / 5) = -(1 + √5) / 4 ∧ Real.cos (8 * π / 5) = (√5 - 1) / 4 ∧
    Real.sin (6 * π / 5) = - Real.sin (4 * π / 5) ∧ Real.sin (8 * π / 5) = - Real.sin (2 * π / 5) := by
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have c1 : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
    have : 2 * π / 5 = 2 * (π / 5) := by ring
    rw [this, Real.cos_two_mul, Real.cos_pi_div_five]; nlinarith
  have c2 : Real.cos (4 * π / 5) = -(1 + √5) / 4 := by
    have : 4 * π / 5 = 2 * (2 * π / 5) := by ring
    rw [this, Real.cos_two_mul, c1]; nlinarith
  refine ⟨c1, c2, ?_, ?_, ?_, ?_⟩
  · have : 6 * π / 5 = 2 * π - 4 * π / 5 := by ring
    rw [this, Real.cos_two_pi_sub, c2]
  · have : 8 * π / 5 = 2 * π - 2 * π / 5 := by ring
    rw [this, Real.cos_two_pi_sub, c1]
  · have : 6 * π / 5 = 2 * π - 4 * π / 5 := by ring
    rw [this, Real.sin_two_pi_sub]
  · have : 8 * π / 5 = 2 * π - 2 * π / 5 := by ring
    rw [this, Real.sin_two_pi_sub]

theorem sin_pos1 : 0 < Real.sin (2 * Real.pi / 5) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

theorem cos_rot (x : ℝ) : Real.cos (-(Real.pi / 2) + x) = Real.sin x := by
  rw [Real.cos_add]; simp
theorem sin_rot (x : ℝ) : Real.sin (-(Real.pi / 2) + x) = - Real.cos x := by
  rw [Real.sin_add]; simp

theorem pentagonK_conv : IsConvexDomain pentagonK ∧ (0 : Position 2) ∈ pentagonK := by
  obtain ⟨c1, c2, c3, c4, s3, s4⟩ := trig_vals
  have hs := sin_pos1
  have a2 : 2 * Real.pi * 2 / 5 = 4 * Real.pi / 5 := by ring
  have a3 : 2 * Real.pi * 3 / 5 = 6 * Real.pi / 5 := by ring
  have a4 : 2 * Real.pi * 4 / 5 = 8 * Real.pi / 5 := by ring
  unfold pentagonK
  refine convDomain_of_sum_zero pentagonVertex ?_ ?_
  · ext i
    fin_cases i
    · simp [Finset.sum_range_succ, pentagonVertex]
      rw [a2, a3, a4, c1, c2, c3, c4]; ring
    · simp [Finset.sum_range_succ, pentagonVertex]
      rw [a2, a3, a4, s3, s4]; ring
  · simp [pentagonVertex]
    exact hs.ne'

theorem pentagonT_conv : IsConvexDomain pentagonT ∧ (0 : Position 2) ∈ pentagonT := by
  obtain ⟨c1, c2, c3, c4, s3, s4⟩ := trig_vals
  have hs := sin_pos1
  have a2 : 2 * Real.pi * 2 / 5 = 4 * Real.pi / 5 := by ring
  have a3 : 2 * Real.pi * 3 / 5 = 6 * Real.pi / 5 := by ring
  have a4 : 2 * Real.pi * 4 / 5 = 8 * Real.pi / 5 := by ring
  unfold pentagonT
  refine convDomain_of_sum_zero rotatedVertex ?_ ?_
  · ext i
    fin_cases i
    · simp [Finset.sum_range_succ, rotatedVertex, cos_rot]
      rw [a2, a3, a4, s3, s4]; ring
    · simp [Finset.sum_range_succ, rotatedVertex, sin_rot]
      rw [a2, a3, a4, c1, c2, c3, c4]; ring
  · simp [rotatedVertex, cos_rot, sin_rot]
    exact hs.ne'

end Pent

/-! ## Polytopes -/

/-- The convex hull of a finite set. -/
def IsPoly {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) : Prop :=
  ∃ s : Finset E, S = convexHull ℝ (s : Set E)

theorem IsPoly.image {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [DecidableEq F] {S : Set E} (h : IsPoly S) {f : E → F} (hf : IsLinearMap ℝ f) :
    IsPoly (f '' S) := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨s.image f, by rw [hf.image_convexHull, Finset.coe_image]⟩

theorem IsPoly.smul {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]
    {S : Set E} (h : IsPoly S) (a : ℝ) : IsPoly (a • S) := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨a • s, by rw [Finset.coe_smul_finset, convexHull_smul]⟩

theorem IsPoly.prod {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {S : Set E} {T : Set F} (hS : IsPoly S) (hT : IsPoly T) : IsPoly (S ×ˢ T) := by
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨t, rfl⟩ := hT
  exact ⟨s ×ˢ t, by rw [Finset.coe_product, convexHull_prod]⟩

theorem IsPoly.singleton {E : Type*} [AddCommGroup E] [Module ℝ E] (x : E) : IsPoly ({x} : Set E) :=
  ⟨{x}, by simp⟩

theorem IsPoly.hull_union {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]
    {S T : Set E} (hS : IsPoly S) (hT : IsPoly T) : IsPoly (convexHull ℝ (S ∪ T)) := by
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨t, rfl⟩ := hT
  exact ⟨s ∪ t, by rw [convexHull_convexHull_union_left, convexHull_convexHull_union_right,
    Finset.coe_union]⟩

/-! ## Convex domains -/

theorem cdImage {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set E} (h : IsConvexDomain S) (f : E ≃L[ℝ] F) :
    IsConvexDomain (f '' S) := by
  obtain ⟨hb, hc, hi⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · exact (f : E →L[ℝ] F).lipschitz.isBounded_image hb
  · exact hc.linear_image (f : E →ₗ[ℝ] F)
  · exact (hi.image f).mono (f.toHomeomorph.isOpenMap.image_interior_subset S)

theorem cdSmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    (h : IsConvexDomain S) {a : ℝ} (ha : a ≠ 0) : IsConvexDomain (a • S) := by
  obtain ⟨hb, hc, hi⟩ := h
  refine ⟨hb.smul₀ a, hc.smul a, ?_⟩
  rw [interior_smul₀ ha]
  exact hi.smul_set

theorem cdProd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set E} {T : Set F}
    (hS : IsConvexDomain S) (hT : IsConvexDomain T) : IsConvexDomain (S ×ˢ T) := by
  obtain ⟨hb, hc, hi⟩ := hS
  obtain ⟨hb', hc', hi'⟩ := hT
  refine ⟨hb.prod hb', hc.prod hc', ?_⟩
  rw [interior_prod_eq]
  exact hi.prod hi'

/-- The convex hull of `X × {0} ∪ {0} × Y`. -/
theorem cdHull {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set E} {T : Set F}
    (hS : IsConvexDomain S) (hT : IsConvexDomain T) (h0S : (0 : E) ∈ S) (h0T : (0 : F) ∈ T) :
    IsConvexDomain (convexHull ℝ (S ×ˢ ({0} : Set F) ∪ ({0} : Set E) ×ˢ T)) := by
  have hsub : S ×ˢ ({0} : Set F) ∪ ({0} : Set E) ×ˢ T ⊆ S ×ˢ T := by
    rintro ⟨x, y⟩ (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · simp only [mem_singleton_iff] at hy; subst hy; exact ⟨hx, h0T⟩
    · simp only [mem_singleton_iff] at hx; subst hx; exact ⟨h0S, hy⟩
  have hprod := cdProd hS hT
  refine ⟨?_, convex_convexHull _ _, ?_⟩
  · exact hprod.1.subset (convexHull_min hsub hprod.2.1)
  · have hhalf : ((1/2 : ℝ) • S) ×ˢ ((1/2 : ℝ) • T) ⊆
        convexHull ℝ (S ×ˢ ({0} : Set F) ∪ ({0} : Set E) ×ˢ T) := by
      rintro ⟨x, y⟩ ⟨⟨x', hx', rfl⟩, ⟨y', hy', rfl⟩⟩
      have h1 : ((x', 0) : E × F) ∈ convexHull ℝ (S ×ˢ ({0} : Set F) ∪ ({0} : Set E) ×ˢ T) :=
        subset_convexHull _ _ (Or.inl ⟨hx', rfl⟩)
      have h2 : ((0, y') : E × F) ∈ convexHull ℝ (S ×ˢ ({0} : Set F) ∪ ({0} : Set E) ×ˢ T) :=
        subset_convexHull _ _ (Or.inr ⟨rfl, hy'⟩)
      have := (convex_convexHull ℝ _) h1 h2 (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
      convert this using 1
      ext <;> simp
    refine Nonempty.mono (interior_mono hhalf) ?_
    rw [interior_prod_eq, interior_smul₀ (by norm_num), interior_smul₀ (by norm_num)]
    exact hS.2.2.smul_set.prod hT.2.2.smul_set


/-! ## The append map -/

@[simp] theorem appendPos_castAdd {m k : ℕ} (x : Position m) (y : Position k) (i : Fin m) :
    appendPos x y (Fin.castAdd k i) = x i := by
  simp [appendPos]

@[simp] theorem appendPos_natAdd {m k : ℕ} (x : Position m) (y : Position k) (j : Fin k) :
    appendPos x y (Fin.natAdd m j) = y j := by
  simp [appendPos]

theorem appendPos_add {m k : ℕ} (x x' : Position m) (y y' : Position k) :
    appendPos (x + x') (y + y') = appendPos x y + appendPos x' y' := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem appendPos_smul {m k : ℕ} (c : ℝ) (x : Position m) (y : Position k) :
    appendPos (c • x) (c • y) = c • appendPos x y := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem appendPos_bij {m k : ℕ} : Function.Bijective
    (fun xy : Position m × Position k => appendPos xy.1 xy.2) := by
  constructor
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only at h
    have h1 : x = x' := by
      ext i
      have := congrArg (fun z : Position (m + k) => z (Fin.castAdd k i)) h
      simpa using this
    have h2 : y = y' := by
      ext j
      have := congrArg (fun z : Position (m + k) => z (Fin.natAdd m j)) h
      simpa using this
    rw [h1, h2]
  · intro z
    refine ⟨((WithLp.equiv 2 _).symm (fun i => z (Fin.castAdd k i)),
      (WithLp.equiv 2 _).symm (fun j => z (Fin.natAdd m j))), ?_⟩
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

noncomputable def appendLin (m k : ℕ) : (Position m × Position k) →ₗ[ℝ] Position (m + k) where
  toFun xy := appendPos xy.1 xy.2
  map_add' a b := appendPos_add a.1 b.1 a.2 b.2
  map_smul' c a := appendPos_smul c a.1 a.2

noncomputable def appendL (m k : ℕ) : (Position m × Position k) ≃L[ℝ] Position (m + k) :=
  (LinearEquiv.ofBijective (appendLin m k) appendPos_bij).toContinuousLinearEquiv

theorem appendL_coe {m k : ℕ} :
    (⇑(appendL m k) : Position m × Position k → Position (m + k)) =
      fun xy => appendPos xy.1 xy.2 := rfl

theorem appendL_isLinear {m k : ℕ} : IsLinearMap ℝ (⇑(appendL m k)) :=
  (appendL m k).toLinearMap.isLinear

/-! ## The two `p`-products -/

theorem pProduct_top_eq {m k : ℕ} (X : Set (Position m)) (Y : Set (Position k)) :
    pProduct ⊤ X Y = appendL m k '' (X ×ˢ Y) := by
  rw [appendL_coe]
  ext z
  simp only [pProduct, ENNReal.inv_top, ENNReal.toReal_zero, Real.rpow_zero, one_smul, mem_iUnion,
    exists_prop]
  constructor
  · rintro ⟨t, -, h⟩; exact h
  · intro h; exact ⟨0, ⟨le_rfl, zero_le_one⟩, h⟩

theorem hull_eq {m k : ℕ} (X : Set (Position m)) (Y : Set (Position k))
    (hX : Convex ℝ X) (hY : Convex ℝ Y) (hX0 : X.Nonempty) (hY0 : Y.Nonempty) :
    (⋃ t ∈ Icc (0 : ℝ) 1, ((1 - t) • X) ×ˢ (t • Y)) =
      convexHull ℝ (X ×ˢ ({0} : Set (Position k)) ∪ ({0} : Set (Position m)) ×ˢ Y) := by
  rw [convexHull_union (hX0.prod (singleton_nonempty _)) ((singleton_nonempty _).prod hY0),
    (hX.prod (convex_singleton _)).convexHull_eq, ((convex_singleton _).prod hY).convexHull_eq]
  ext ⟨x, y⟩
  simp only [mem_iUnion, exists_prop, mem_prod, mem_convexJoin]
  constructor
  · rintro ⟨t, ht, ⟨x', hx', rfl⟩, ⟨y', hy', rfl⟩⟩
    refine ⟨(x', 0), ⟨hx', rfl⟩, (0, y'), ⟨rfl, hy'⟩, 1 - t, t, by linarith [ht.2], ht.1,
      by ring, ?_⟩
    ext <;> simp
  · rintro ⟨⟨x', z'⟩, ⟨hx', hz'⟩, ⟨w', y'⟩, ⟨hw', hy'⟩, a, b, ha, hb, hab, heq⟩
    simp only [mem_singleton_iff] at hz' hw'
    subst hz' hw'
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero,
      add_zero, zero_add] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine ⟨b, ⟨hb, by linarith⟩, ⟨x', hx', ?_⟩, ⟨y', hy', rfl⟩⟩
    rw [show 1 - b = a by linarith]

theorem pProduct_one_eq {m k : ℕ} (X : Set (Position m)) (Y : Set (Position k))
    (hX : Convex ℝ X) (hY : Convex ℝ Y) (hX0 : X.Nonempty) (hY0 : Y.Nonempty) :
    pProduct 1 X Y = appendL m k '' convexHull ℝ (X ×ˢ ({0} : Set (Position k)) ∪
      ({0} : Set (Position m)) ×ˢ Y) := by
  rw [← hull_eq X Y hX hY hX0 hY0, appendL_coe, image_iUnion₂]
  simp only [pProduct, inv_one, ENNReal.toReal_one, Real.rpow_one]

/-! ## Scaling -/

theorem smul_prod {n : ℕ} {a : ℝ} (ha : a ≠ 0) (K T : Set (Position n)) :
    a • (K ×ˢ T) = (a • K) ×ˢ (a • T) := by
  ext ⟨x, y⟩
  simp [mem_smul_set_iff_inv_smul_mem₀ ha]

theorem cEHZ_smul {n : ℕ} (hn : 1 ≤ n) {A : Set (Phase n)} (hA : IsConvexDomain A) {a : ℝ}
    (ha : 0 < a) : cEHZ (a • A) = ENNReal.ofReal (a ^ 2) * cEHZ A := by
  obtain ⟨⟨c, hc, hcK⟩, -⟩ := exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ n hn
  rw [← hcK _ hA, ← hcK _ (cdSmul hA ha.ne'), hc.2.1 a ha]

theorem volume_smul {n : ℕ} (A : Set (Phase n)) (a : ℝ) (ha : 0 < a) :
    volume (a • A) = ENNReal.ofReal ((a ^ 2) ^ n) * volume A := by
  have : (volume : Measure (Phase n)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [Measure.addHaar_smul, Module.finrank_prod, finrank_euclideanSpace_fin,
    abs_of_pos (pow_pos ha _), ← pow_mul, two_mul]

theorem systolicRatio_smul {n : ℕ} (hn : 1 ≤ n) {A : Set (Phase n)} (hA : IsConvexDomain A)
    {a : ℝ} (ha : 0 < a) : systolicRatio (a • A) = systolicRatio A := by
  unfold systolicRatio
  rw [cEHZ_smul hn hA ha, volume_smul A a ha, mul_pow, ← ENNReal.ofReal_pow (sq_nonneg a),
    mul_left_comm]
  refine ENNReal.mul_div_mul_left _ _ ?_ ENNReal.ofReal_ne_top
  rw [Ne, ENNReal.ofReal_eq_zero, not_le]
  positivity

theorem cEHZ_pos_fin {n : ℕ} (hn : 1 ≤ n) {A : Set (Phase n)} (hA : IsConvexDomain A) {r : ℝ}
    (hr : 0 < r) (h : systolicRatio A = ENNReal.ofReal r) : cEHZ A ≠ 0 ∧ cEHZ A ≠ ⊤ := by
  unfold systolicRatio at h
  have hv : (n.factorial : ℝ≥0∞) * volume A ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hA.1.measure_lt_top.ne
  have hrz : ENNReal.ofReal r ≠ 0 := by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hr
  constructor
  · intro h0
    rw [h0, zero_pow (by omega), ENNReal.zero_div] at h
    exact hrz h.symm
  · intro ht
    rw [ht, ENNReal.top_pow (by omega), ENNReal.top_div_of_ne_top hv] at h
    exact ENNReal.ofReal_ne_top h.symm

/-! ## The induction -/

/-- The induction statement. -/
def P (n : ℕ) : Prop :=
  ∃ K T : Set (Position n), IsPoly K ∧ IsPoly T ∧ IsConvexDomain K ∧ IsConvexDomain T ∧
    (0 : Position n) ∈ K ∧ (0 : Position n) ∈ T ∧
    systolicRatio (K ×ˢ T) = ENNReal.ofReal (((Real.sqrt 5 + 3) / 5) ^ (n / 2))

theorem P_two : P 2 := by
  classical
  refine ⟨pentagonK, pentagonT, ⟨(Finset.range 5).image pentagonVertex, ?_⟩,
    ⟨(Finset.range 5).image rotatedVertex, ?_⟩, Pent.pentagonK_conv.1,
    Pent.pentagonT_conv.1, Pent.pentagonK_conv.2, Pent.pentagonT_conv.2, ?_⟩
  · rw [Finset.coe_image]; rfl
  · rw [Finset.coe_image]; rfl
  · rw [volume_pentagon_and_systolicRatio_pentagonK_prod_pentagonT.2.2.1]
    norm_num

/-! ### The base `n = 1`: the square `[-1, 1] × [-1, 1]` -/

/-- The interval `[-1, 1]` in `ℝ¹`. -/
def Kint : Set (Position 1) := {x | x 0 ∈ Icc (-1 : ℝ) 1}

/-- The unit vector of `ℝ¹`. -/
noncomputable def e1 : Position 1 := EuclideanSpace.single 0 1

theorem norm1 (x : Position 1) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

theorem inner1 (x u : Position 1) : inner ℝ x u = x 0 * u 0 := by
  simp [PiLp.inner_apply, mul_comm]

theorem e1_apply : e1 0 = 1 := by simp [e1]

theorem pos1_ext {x y : Position 1} (h : x 0 = y 0) : x = y := by
  ext i
  fin_cases i
  exact h

theorem Kint_eq : Kint = convexHull ℝ ({e1, -e1} : Set (Position 1)) := by
  rw [convexHull_pair]
  ext x
  simp only [Kint, mem_ofPred_eq, mem_Icc, segment]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(1 + x 0) / 2, (1 - x 0) / 2, by linarith, by linarith, by ring, pos1_ext ?_⟩
    simp [e1_apply]
    ring
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    simp [e1_apply]
    constructor <;> linarith

theorem ball_sub_Kint : Metric.ball (0 : Position 1) 1 ⊆ Kint := by
  intro x hx
  rw [mem_ball_zero_iff, norm1] at hx
  exact ⟨by linarith [neg_abs_le (x 0)], by linarith [le_abs_self (x 0)]⟩

theorem ball_sub_interior : Metric.ball (0 : Position 1) 1 ⊆ interior Kint :=
  interior_maximal ball_sub_Kint Metric.isOpen_ball

theorem abs_lt_of_interior {x : Position 1} (hx : x ∈ interior Kint) : |x 0| < 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  have hp : x + (ε / 2) • e1 ∈ Kint := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm1]
    simp [e1_apply]; rw [abs_of_pos (half_pos hε)]; linarith)
  have hm : x - (ε / 2) • e1 ∈ Kint := hball (by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm1]
    simp [e1_apply]; rw [abs_of_pos (half_pos hε)]; linarith)
  simp only [Kint, mem_ofPred_eq, mem_Icc] at hp hm
  simp [e1_apply] at hp hm
  rw [abs_lt]
  constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]

theorem zero_mem_interior : (0 : Position 1) ∈ interior Kint :=
  ball_sub_interior (Metric.mem_ball_self one_pos)

theorem Kint_cd : IsConvexDomain Kint := by
  refine ⟨?_, ?_, ⟨0, zero_mem_interior⟩⟩
  · refine (Metric.isBounded_closedBall (x := (0 : Position 1)) (r := 1)).subset ?_
    intro x hx
    rw [mem_closedBall_zero_iff, norm1, abs_le]
    exact hx
  · rw [Kint_eq]; exact convex_convexHull _ _

theorem volume_Kint : volume Kint = ENNReal.ofReal 2 := by
  have hmp : MeasurePreserving (fun x : Position 1 => x 0) := by
    have := (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))
    exact this
  have := hmp.measure_preimage (s := Icc (-1 : ℝ) 1) measurableSet_Icc.nullMeasurableSet
  rw [Real.volume_Icc] at this
  rw [show Kint = (fun x : Position 1 => x 0) ⁻¹' Icc (-1 : ℝ) 1 from rfl, this]
  norm_num

theorem supp_Kint (u : Position 1) : supportFunction Kint u = |u 0| := by
  unfold supportFunction
  apply IsGreatest.csSup_eq
  refine ⟨⟨(if 0 ≤ u 0 then 1 else -1 : ℝ) • e1, ?_, ?_⟩, ?_⟩
  · simp only [Kint, mem_ofPred_eq, mem_Icc]
    split_ifs <;> simp [e1_apply]
  · simp only [inner1]
    split_ifs with h
    · simp [e1_apply, abs_of_nonneg h]
    · simp [e1_apply, abs_of_neg (not_le.1 h)]
  · rintro _ ⟨x, hx, rfl⟩
    simp only [inner1]
    have hx' : |x 0| ≤ 1 := abs_le.2 hx
    calc x 0 * u 0 ≤ |x 0 * u 0| := le_abs_self _
      _ = |x 0| * |u 0| := abs_mul _ _
      _ ≤ 1 * |u 0| := mul_le_mul_of_nonneg_right hx' (abs_nonneg _)
      _ = |u 0| := one_mul _

theorem length2 (q : Fin 2 → Position 1) :
    polygonLength Kint q = 2 * |q 1 0 - q 0 0| := by
  unfold polygonLength
  rw [Fin.sum_univ_two, supp_Kint, supp_Kint]
  have h0 : finRotate 2 0 = 1 := rfl
  have h1 : finRotate 2 1 = 0 := rfl
  rw [h0, h1]
  simp only [PiLp.sub_apply]
  rw [abs_sub_comm (q 0 0)]
  ring

theorem notTrans_le (q : Fin 2 → Position 1) (h : NotTranslatableIntoInterior Kint q) :
    2 ≤ |q 1 0 - q 0 0| := by
  by_contra hlt
  push Not at hlt
  rw [abs_lt] at hlt
  apply h (((q 0 0 + q 1 0) / 2) • e1)
  intro j
  rw [Set.add_singleton]
  refine ⟨q j - ((q 0 0 + q 1 0) / 2) • e1, ball_sub_interior ?_, sub_add_cancel _ _⟩
  rw [mem_ball_zero_iff, norm1]
  simp only [PiLp.sub_apply, PiLp.smul_apply, e1_apply, smul_eq_mul, mul_one]
  rw [abs_lt]
  fin_cases j <;> simp <;> constructor <;> linarith [hlt.1, hlt.2]

theorem notTrans_witness : NotTranslatableIntoInterior Kint ![-e1, e1] := by
  intro t ht
  have h0 := ht 0
  have h1 := ht 1
  rw [Set.add_singleton] at h0 h1
  obtain ⟨a, ha, hae⟩ := h0
  obtain ⟨b, hb, hbe⟩ := h1
  have ha' := abs_lt_of_interior ha
  have hb' := abs_lt_of_interior hb
  have hae' := congrArg (fun z : Position 1 => z 0) hae
  have hbe' := congrArg (fun z : Position 1 => z 0) hbe
  simp [e1_apply] at hae' hbe'
  rw [abs_lt] at ha' hb'
  linarith [ha'.1, ha'.2, hb'.1, hb'.2]

theorem notTrans_small (m : ℕ) (hm : m ≤ 1) (q : Fin m → Position 1) :
    ¬ NotTranslatableIntoInterior Kint q := by
  intro h
  interval_cases m
  · exact h 0 (fun j => j.elim0)
  · apply h (q 0)
    intro j
    fin_cases j
    rw [Set.add_singleton]
    exact ⟨0, zero_mem_interior, by simp⟩

theorem cEHZ_square : cEHZ (Kint ×ˢ Kint) = ENNReal.ofReal 4 := by
  obtain ⟨L, hL, -, -, -, ⟨m, q, hm, hq, hlen⟩, hmin⟩ :=
    cEHZ_prod_eq_min_action_and_min_billiard_and_min_notTranslatable 1 le_rfl Kint Kint Kint_cd
      Kint_cd zero_mem_interior
  have h4 : L ≤ 4 := by
    have := hmin 2 ![-e1, e1] le_rfl notTrans_witness
    rw [length2] at this
    simp [e1_apply] at this
    norm_num at this
    linarith
  have h4' : 4 ≤ L := by
    rcases (show m ≤ 1 ∨ m = 2 by omega) with h | rfl
    · exact absurd hq (notTrans_small m h q)
    · rw [← hlen, length2]
      linarith [notTrans_le q hq]
  rw [hL, le_antisymm h4 h4']

theorem P_one : P 1 := by
  classical
  have hp : IsPoly Kint := ⟨{e1, -e1}, by rw [Kint_eq]; simp⟩
  have h0 : (0 : Position 1) ∈ Kint := interior_subset zero_mem_interior
  refine ⟨Kint, Kint, hp, hp, Kint_cd, Kint_cd, h0, h0, ?_⟩
  unfold systolicRatio
  rw [cEHZ_square, Measure.volume_eq_prod, Measure.prod_prod, volume_Kint]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)

theorem P_step (n : ℕ) (hn : 1 ≤ n) (h : P n) : P (n + 2) := by
  classical
  obtain ⟨K, T, hKp, hTp, hKd, hTd, hK0, hT0, hs⟩ := h
  obtain ⟨Kp, Tp, hKpp, hTpp, hKpd, hTpd, hKp0, hTp0, hsp⟩ := P_two
  have hr : 0 < (Real.sqrt 5 + 3) / 5 := by positivity
  rw [show (2 : ℕ) / 2 = 1 from rfl, pow_one] at hsp
  have hKT := cdProd hKd hTd
  have hP := cdProd hKpd hTpd
  obtain ⟨h1, h1'⟩ := cEHZ_pos_fin hn hKT (pow_pos hr _) hs
  obtain ⟨h2, h2'⟩ := cEHZ_pos_fin (by norm_num) hP hr hsp
  obtain ⟨c1, hc1, hc1e⟩ : ∃ c1, 0 < c1 ∧ cEHZ (K ×ˢ T) = ENNReal.ofReal c1 :=
    ⟨_, ENNReal.toReal_pos h1 h1', (ENNReal.ofReal_toReal h1').symm⟩
  obtain ⟨c2, hc2, hc2e⟩ : ∃ c2, 0 < c2 ∧ cEHZ (Kp ×ˢ Tp) = ENNReal.ofReal c2 :=
    ⟨_, ENNReal.toReal_pos h2 h2', (ENNReal.ofReal_toReal h2').symm⟩
  set α := Real.sqrt (c2 / c1) with hαdef
  have hα : 0 < α := Real.sqrt_pos.2 (div_pos hc2 hc1)
  have hscale : cEHZ ((α • K) ×ˢ (α • T)) = cEHZ (Kp ×ˢ Tp) := by
    rw [← smul_prod hα.ne', cEHZ_smul hn hKT hα, hc1e, ← ENNReal.ofReal_mul (sq_nonneg _),
      hαdef, Real.sq_sqrt (div_pos hc2 hc1).le, div_mul_cancel₀ _ hc1.ne', hc2e]
  have hX1 := cdSmul hKd hα.ne'
  have hY1 := cdSmul hTd hα.ne'
  have hX10 : (0 : Position n) ∈ α • K := ⟨0, hK0, smul_zero α⟩
  have hY10 : (0 : Position n) ∈ α • T := ⟨0, hT0, smul_zero α⟩
  have key := systolicRatio_pProduct_one_prod_pProduct_top n 2 hn (by norm_num) (α • K) (α • T)
    Kp Tp hX1 hY1 hKpd hTpd ⟨hX10, hY10, hKp0, hTp0⟩ hscale
  have hK1 := pProduct_one_eq (α • K) Kp hX1.2.1 hKpd.2.1 ⟨0, hX10⟩ ⟨0, hKp0⟩
  have hT1 := pProduct_top_eq (α • T) Tp
  refine ⟨pProduct 1 (α • K) Kp, pProduct ⊤ (α • T) Tp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK1]
    exact (IsPoly.hull_union ((hKp.smul α).prod (IsPoly.singleton 0))
      ((IsPoly.singleton 0).prod hKpp)).image appendL_isLinear
  · rw [hT1]
    exact ((hTp.smul α).prod hTpp).image appendL_isLinear
  · rw [hK1]
    exact cdImage (cdHull hX1 hKpd hX10 hKp0) _
  · rw [hT1]
    exact cdImage (cdProd hY1 hTpd) _
  · rw [hK1]
    exact ⟨0, subset_convexHull _ _ (Or.inl ⟨hX10, rfl⟩), map_zero _⟩
  · rw [hT1]
    exact ⟨0, ⟨hY10, hTp0⟩, map_zero _⟩
  · rw [key, ← smul_prod hα.ne', systolicRatio_smul hn hKT hα, hs, hsp,
      ← ENNReal.ofReal_mul (by positivity), show (n + 2) / 2 = n / 2 + 1 by omega, pow_succ]

theorem P_all (k : ℕ) : P (k + 1) ∧ P (k + 2) := by
  induction k with
  | zero => exact ⟨P_one, P_two⟩
  | succ k ih => exact ⟨ih.2, P_step (k + 1) (by omega) ih.1⟩

end Viterbo.PolyProd

open scoped ENNReal

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ K T : Set (OAI.SymmetricPolar.Position n),
      (∃ s : Finset (OAI.SymmetricPolar.Position n), K = convexHull ℝ (s : Set _)) ∧
      (∃ s : Finset (OAI.SymmetricPolar.Position n), T = convexHull ℝ (s : Set _)) ∧
      Viterbo.IsConvexDomain K ∧ Viterbo.IsConvexDomain T ∧
      Viterbo.systolicRatio (K ×ˢ T) = ENNReal.ofReal (((Real.sqrt 5 + 3) / 5) ^ (n / 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, T, hK, hT, hKd, hTd, -, -, hs⟩ := (Viterbo.PolyProd.P_all k).1
  exact ⟨K, T, hK, hT, hKd, hTd, hs⟩
