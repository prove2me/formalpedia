-- Prove2me | solution 1 for ThompsonAmenability.isAmenable_F_of_isExtensivelyAmenableOn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T01:46:38.426001+00:00
-- url     : https://prove2.me/submissions/4e34b886-29a6-4201-bc0d-5ef1a34fb228

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_Garrido_Amenability
import Definitions.Def_ThompsonAmenability
import Theorems.Thm_Garrido_isAmenable_of_commGroup
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson
import Theorems.Thm_CannonFloydParry_bijOn_dyadic

/-!
# Extensive amenability of `F ↷ D` implies amenability of `F`

`D` is the set of dyadic rationals in `(0,1)`. Chornyi (arXiv:1907.01440, p. 7, proof of
Corollary 3) defines `c(g)(x) = g'₊(x) / g'₋(x)`, valued in the powers of `2`, observes that
`g ↦ (c(g), g)` is a cocycle with trivial kernel, and applies the criterion of
Juschenko–Matte Bon–Monod–de la Salle (arXiv:1503.04977, Corollary 1.4 and Remark 1.5).
This file proves the case of that criterion the argument needs, with the exponents of `2`
(the group `ℤ`) as lamps:

* (C) The slope-jump cocycle `c : F → (UI →₀ ℤ)` (supported in `D`) makes the affine action
  `g ⋆ φ = c g + g · φ` free: no `g ≠ 1` fixes any `φ` (`φ = 0` is the trivial kernel).
* (B) Extensive amenability of `F ↷ D` gives a finitely additive probability on `Set (UI →₀ ℤ)`
  invariant under the linear action of `F` and under translations supported in `D`; hence
  invariant under `⋆`.
* (A) A free action with an invariant finitely additive probability makes the group amenable.
-/

open scoped ENNReal Pointwise

namespace FAmenChild

/-! ## Part A -/


namespace PartA
open scoped ENNReal Pointwise

/-- The chosen representative of the orbit of `y`. -/
noncomputable def rep (G : Type*) {Y : Type*} [Group G] [MulAction G Y] (y : Y) : Y :=
  (Quotient.mk (MulAction.orbitRel G Y) y).out

lemma exists_smul_rep {G Y : Type*} [Group G] [MulAction G Y] (y : Y) :
    ∃ g : G, g • rep G y = y := by
  have h : rep G y ∈ MulAction.orbit G y := by
    have := Quotient.mk_out (s := MulAction.orbitRel G Y) y
    exact (MulAction.orbitRel_apply).1 this
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 h
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

lemma rep_smul {G Y : Type*} [Group G] [MulAction G Y] (h : G) (y : Y) :
    rep G (h • y) = rep G y := by
  unfold rep
  congr 1
  exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit y h))

/-- The coordinate of `y`: the group element carrying the representative to `y`. -/
noncomputable def coord (G : Type*) {Y : Type*} [Group G] [MulAction G Y] (y : Y) : G :=
  (exists_smul_rep (G := G) y).choose

lemma coord_smul_rep {G Y : Type*} [Group G] [MulAction G Y] (y : Y) :
    coord G y • rep G y = y :=
  (exists_smul_rep (G := G) y).choose_spec

lemma coord_smul {G Y : Type*} [Group G] [MulAction G Y]
    (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1) (h : G) (y : Y) :
    coord G (h • y) = h * coord G y := by
  have e1 := coord_smul_rep (G := G) (h • y)
  rw [rep_smul] at e1
  have e2 : (h * coord G y) • rep G y = h • y := by rw [mul_smul, coord_smul_rep]
  have : ((h * coord G y)⁻¹ * coord G (h • y)) • rep G y = rep G y := by
    rw [mul_smul, e1, ← e2, inv_smul_smul]
  have h1 := hfree _ _ this
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem isAmenable_of_free {G Y : Type*} [Group G] [MulAction G Y]
    (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1)
    (m : Set Y → ℝ≥0∞) (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (hinv : ∀ (g : G) (S : Set Y), m (g • S) = m S) : Garrido.IsAmenable G := by
  refine ⟨fun S => m ((coord G : Y → G) ⁻¹' S), ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa using hm.1
  · intro s t hst
    simpa [Set.preimage_union] using hm.2 _ _ (hst.preimage _)
  · simpa using h1
  · intro g S
    have : (coord G : Y → G) ⁻¹' (g • S) = g • ((coord G : Y → G) ⁻¹' S) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul,
        coord_smul hfree]
    simp only
    rw [this, hinv]

end PartA

alias isAmenable_of_free := PartA.isAmenable_of_free

/-! ## Part B1: integrating `[0,1]`-valued functions against a finitely additive probability -/

/-- `∑_{k < 2^n} 2^{-n} m {f ≥ (k+1)/2^n}`: the integral of `⌊2^n f⌋ / 2^n`. -/
noncomputable def layerSum {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), (m {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ f a}).toReal / 2 ^ n

/-- The integral: the supremum of the layer sums. -/
noncomputable def integ {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) : ℝ := ⨆ n, layerSum m f n


namespace PartB1
open scoped ENNReal

open FAmenChild

variable {α : Type*} {m : Set α → ℝ≥0∞}

/-! ### Elementary facts about a finitely additive probability -/

lemma fa_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) {S T : Set α} (h : S ⊆ T) :
    m S ≤ m T := by
  have hd : Disjoint S (T \ S) := Set.disjoint_sdiff_right
  have := hm.2 S (T \ S) hd
  rw [Set.union_sdiff_cancel h] at this
  rw [this]
  exact le_self_add

lemma fa_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (S : Set α) :
    m S ≤ 1 := h1 ▸ fa_mono hm (Set.subset_univ S)

lemma fa_ne_top (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (S : Set α) :
    m S ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (fa_le_one hm h1 S)

lemma fa_union_le (hm : Garrido.IsFinitelyAdditiveMeasure m) (S T : Set α) :
    m (S ∪ T) ≤ m S + m T := by
  have hd : Disjoint S (T \ S) := Set.disjoint_sdiff_right
  have := hm.2 S (T \ S) hd
  rw [Set.union_sdiff_self] at this
  rw [this]
  gcongr
  exact fa_mono hm Set.sdiff_subset

lemma fa_toReal_union (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {S T : Set α} (h : Disjoint S T) :
    (m (S ∪ T)).toReal = (m S).toReal + (m T).toReal := by
  rw [hm.2 S T h, ENNReal.toReal_add (fa_ne_top hm h1 S) (fa_ne_top hm h1 T)]

lemma fa_toReal_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {S T : Set α} (h : S ⊆ T) : (m S).toReal ≤ (m T).toReal :=
  ENNReal.toReal_mono (fa_ne_top hm h1 T) (fa_mono hm h)

lemma fa_toReal_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (S : Set α) : (m S).toReal ≤ 1 := by
  have := fa_toReal_mono hm h1 (Set.subset_univ S)
  rwa [h1, ENNReal.toReal_one] at this

/-! ### Bounds on the layer sums -/

lemma layerSum_nonneg (f : α → ℝ) (n : ℕ) : 0 ≤ layerSum m f n := by
  unfold layerSum
  exact Finset.sum_nonneg fun k _ => div_nonneg ENNReal.toReal_nonneg (by positivity)

lemma layerSum_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (f : α → ℝ) (n : ℕ) : layerSum m f n ≤ 1 := by
  unfold layerSum
  calc ∑ k ∈ Finset.range (2 ^ n), (m {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ f a}).toReal / 2 ^ n
      ≤ ∑ _k ∈ Finset.range (2 ^ n), (1 : ℝ) / 2 ^ n := by
        gcongr with k
        exact fa_toReal_le_one hm h1 _
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

lemma bddAbove_layerSum (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (f : α → ℝ) : BddAbove (Set.range (layerSum m f)) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact layerSum_le_one hm h1 f n⟩

/-! ### The four easy lemmas -/

theorem integ_indicator (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (S : Set α) : integ m (S.indicator 1) = (m S).toReal := by
  have key : ∀ n, layerSum m (S.indicator 1) n = (m S).toReal := by
    intro n
    unfold layerSum
    have hset : ∀ k ∈ Finset.range (2 ^ n),
        {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ S.indicator 1 a} = S := by
      intro k hk
      have hk' : k + 1 ≤ 2 ^ n := Finset.mem_range.1 hk
      have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / 2 ^ n := by positivity
      have hle : ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast hk'
      push_cast at hpos hle
      ext a
      by_cases ha : a ∈ S
      · simp [ha, hle]
      · simp [ha, hpos]
    rw [Finset.sum_congr rfl fun k hk => by rw [hset k hk], Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
  unfold integ
  simp only [key, ciSup_const]

theorem integ_congr (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f g : α → ℝ} (h : m {a | f a ≠ g a} = 0) : integ m f = integ m g := by
  have hle : ∀ (f g : α → ℝ), m {a | f a ≠ g a} = 0 → ∀ c : ℝ,
      m {a | c ≤ f a} ≤ m {a | c ≤ g a} := by
    intro f g h c
    calc m {a | c ≤ f a} ≤ m ({a | c ≤ g a} ∪ {a | f a ≠ g a}) := by
          apply fa_mono hm
          intro a ha
          by_cases hfg : f a = g a
          · left; simp only [Set.mem_ofPred_eq] at ha ⊢; rwa [← hfg]
          · right; exact hfg
      _ ≤ m {a | c ≤ g a} + m {a | f a ≠ g a} := fa_union_le hm _ _
      _ = m {a | c ≤ g a} := by rw [h, add_zero]
  have h' : m {a | g a ≠ f a} = 0 := by
    simpa only [ne_comm] using h
  have heq : ∀ c : ℝ, m {a | c ≤ f a} = m {a | c ≤ g a} := fun c =>
    le_antisymm (hle f g h c) (hle g f h' c)
  unfold integ layerSum
  simp only [heq]

theorem integ_comp_equiv (τ : α ≃ α) (hτ : ∀ S : Set α, m (τ '' S) = m S) (f : α → ℝ) :
    integ m (f ∘ τ) = integ m f := by
  have heq : ∀ c : ℝ, m {a | c ≤ (f ∘ τ) a} = m {a | c ≤ f a} := by
    intro c
    have : {a | c ≤ (f ∘ τ) a} = τ ⁻¹' {a | c ≤ f a} := rfl
    rw [this, ← hτ (τ ⁻¹' {a | c ≤ f a}), Equiv.image_preimage]
  unfold integ layerSum
  simp only [heq]

theorem integ_nonneg_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) : 0 ≤ integ m f ∧ integ m f ≤ 1 :=
  ⟨Real.iSup_nonneg fun n => layerSum_nonneg f n,
    Real.iSup_le (fun n => layerSum_le_one hm h1 f n) zero_le_one⟩

/-! ### `ℕ`-valued layer sums: the integral of a finitely-valued function -/

/-- `∑_{k<N} m{φ ≥ k+1}`: the integral of an `ℕ`-valued function `φ ≤ N`. -/
noncomputable def J (m : Set α → ℝ≥0∞) (φ : α → ℕ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (m {a | k + 1 ≤ φ a}).toReal

lemma J_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {φ ψ : α → ℕ} (h : ∀ a, φ a ≤ ψ a) (N : ℕ) : J m φ N ≤ J m ψ N := by
  unfold J
  exact Finset.sum_le_sum fun k _ => fa_toReal_mono hm h1 fun a ha => le_trans ha (h a)

lemma J_extend (hm : Garrido.IsFinitelyAdditiveMeasure m) {φ : α → ℕ} {N : ℕ}
    (h : ∀ a, φ a ≤ N) (N' : ℕ) (hN' : N ≤ N') : J m φ N' = J m φ N := by
  induction N', hN' using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    unfold J at ih ⊢
    rw [Finset.sum_range_succ, ih]
    have : {a | n + 1 ≤ φ a} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact Nat.lt_succ_of_le ((h a).trans hn)
    rw [this, hm.1, ENNReal.toReal_zero, add_zero]

lemma sum_level (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (A : Set α) (φ : α → ℕ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (m {a | a ∈ A ∧ φ a = k}).toReal =
      (m {a | a ∈ A ∧ φ a < N}).toReal := by
  induction N with
  | zero => simp [hm.1]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, ← fa_toReal_union hm h1]
    · congr 2
      ext a
      by_cases ha : a ∈ A <;> (simp [ha]; try omega)
    · rw [Set.disjoint_left]
      rintro a ⟨_, ha⟩ ⟨_, hb⟩
      omega

/-- Adding a `{0,1}`-valued function adds the measure of its support. -/
lemma J_add_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (φ χ : α → ℕ) (N : ℕ) (hχ : ∀ a, χ a ≤ 1) (h : ∀ a, φ a + χ a ≤ N) :
    J m (φ + χ) N = J m φ N + (m {a | 1 ≤ χ a}).toReal := by
  have hterm : ∀ k, (m {a | k + 1 ≤ (φ + χ) a}).toReal =
      (m {a | k + 1 ≤ φ a}).toReal + (m {a | a ∈ {a | 1 ≤ χ a} ∧ φ a = k}).toReal := by
    intro k
    rw [← fa_toReal_union hm h1]
    · congr 2
      ext a
      have := hχ a
      simp only [Pi.add_apply, Set.mem_ofPred_eq, Set.mem_union]
      omega
    · rw [Set.disjoint_left]
      rintro a ha ⟨hb, hc⟩
      simp only [Set.mem_ofPred_eq] at ha hb
      omega
  unfold J
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib, sum_level hm h1]
  congr 3
  ext a
  simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
  intro ha
  have := h a
  omega

lemma J_zero (hm : Garrido.IsFinitelyAdditiveMeasure m) (N : ℕ) : J m 0 N = 0 := by
  unfold J
  refine Finset.sum_eq_zero fun k _ => ?_
  have : {a : α | k + 1 ≤ (0 : α → ℕ) a} = ∅ := by
    ext a; simp
  rw [this, hm.1, ENNReal.toReal_zero]

/-- Additivity of `J` (induction on a bound for `ψ`). -/
lemma J_add (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (N : ℕ) :
    ∀ (M : ℕ) (φ ψ : α → ℕ), (∀ a, ψ a ≤ M) → (∀ a, φ a + ψ a ≤ N) →
      J m (φ + ψ) N = J m φ N + J m ψ N := by
  intro M
  induction M with
  | zero =>
    intro φ ψ hψ _
    have hψ0 : ψ = 0 := funext fun a => Nat.le_zero.1 (hψ a)
    subst hψ0
    rw [add_zero, J_zero hm, add_zero]
  | succ M ih =>
    intro φ ψ hψ h
    have hsplit : ψ = (fun a => min (ψ a) M) + (fun a => ψ a - M) :=
      funext fun a => by simp only [Pi.add_apply]; omega
    have hχ : ∀ a, (fun a => ψ a - M) a ≤ 1 := fun a => by
      have := hψ a; try dsimp only
      omega
    rw [hsplit, ← add_assoc, J_add_le_one hm h1 _ _ N hχ, ih φ _ (fun a => min_le_right _ _),
      J_add_le_one hm h1 _ _ N hχ]
    · ring
    all_goals
      intro a; have := h a; have := hψ a
      try dsimp only [Pi.add_apply]
      omega

/-! ### The layer sums through `J` -/

lemma layerSum_eq (f : α → ℝ) (n : ℕ) :
    layerSum m f n = J m (fun a => ⌊2 ^ n * f a⌋₊) (2 ^ n) / 2 ^ n := by
  unfold layerSum J
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 3
  ext a
  simp only [Set.mem_ofPred_eq]
  rw [← Nat.cast_succ, Nat.le_floor_iff' (Nat.succ_ne_zero k), div_le_iff₀ (by positivity),
    mul_comm]

lemma floor_le_pow {f : α → ℝ} (hf1 : ∀ a, f a ≤ 1) (n : ℕ) (a : α) :
    ⌊2 ^ n * f a⌋₊ ≤ 2 ^ n := by
  apply Nat.floor_le_of_le
  push_cast
  have : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith [hf1 a]

lemma layerSum_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) : Monotone (layerSum m f) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [layerSum_eq, layerSum_eq]
  set φ : α → ℕ := fun a => ⌊2 ^ n * f a⌋₊ with hφdef
  have hφ : ∀ a, φ a ≤ 2 ^ n := floor_le_pow hf1 n
  have h2 : ∀ a, (φ + φ) a ≤ ⌊2 ^ (n + 1) * f a⌋₊ := by
    intro a
    apply Nat.le_floor
    have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * f a by have := hf a; positivity)
    simp only [Pi.add_apply, hφdef]
    push_cast
    rw [pow_succ]
    linarith
  have key : 2 * J m φ (2 ^ n) ≤ J m (fun a => ⌊2 ^ (n + 1) * f a⌋₊) (2 ^ (n + 1)) := by
    calc 2 * J m φ (2 ^ n) = J m φ (2 ^ (n + 1)) + J m φ (2 ^ (n + 1)) := by
          rw [J_extend hm hφ (2 ^ (n + 1)) (Nat.pow_le_pow_right (by norm_num) (by omega))]
          ring
      _ = J m (φ + φ) (2 ^ (n + 1)) :=
          (J_add hm h1 _ (2 ^ n) φ φ hφ fun a => by have := hφ a; rw [pow_succ]; omega).symm
      _ ≤ _ := J_mono hm h1 h2 _
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_div_iff₀ hp (by positivity)]
  have e : J m φ (2 ^ n) * (2 : ℝ) ^ (n + 1) = 2 * J m φ (2 ^ n) * 2 ^ n := by
    rw [pow_succ]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right key hp.le

/-! ### Additivity -/

theorem integ_add (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f g : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a) (hfg : ∀ a, f a + g a ≤ 1) :
    integ m (f + g) = integ m f + integ m g := by
  have hfg0 : ∀ a, 0 ≤ (f + g) a := fun a => add_nonneg (hf a) (hg a)
  have hf1 : ∀ a, f a ≤ 1 := fun a => by linarith [hfg a, hg a]
  have hg1 : ∀ a, g a ≤ 1 := fun a => by linarith [hfg a, hf a]
  have hfg1 : ∀ a, (f + g) a ≤ 1 := hfg
  have tf := tendsto_atTop_ciSup (layerSum_mono hm h1 hf hf1) (bddAbove_layerSum hm h1 f)
  have tg := tendsto_atTop_ciSup (layerSum_mono hm h1 hg hg1) (bddAbove_layerSum hm h1 g)
  have tfg := tendsto_atTop_ciSup (layerSum_mono hm h1 hfg0 hfg1) (bddAbove_layerSum hm h1 (f + g))
  have hbound : ∀ n, layerSum m f n + layerSum m g n ≤ layerSum m (f + g) n ∧
      layerSum m (f + g) n ≤ layerSum m f n + layerSum m g n + (1 / 2) ^ n := by
    intro n
    rw [layerSum_eq, layerSum_eq, layerSum_eq]
    set φ : α → ℕ := fun a => ⌊2 ^ n * f a⌋₊ with hφdef
    set ψ : α → ℕ := fun a => ⌊2 ^ n * g a⌋₊ with hψdef
    set χ : α → ℕ := fun a => ⌊2 ^ n * (f + g) a⌋₊ with hχdef
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    have hlow : ∀ a, (φ + ψ) a ≤ χ a := by
      intro a
      apply Nat.le_floor
      have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * f a by have := hf a; positivity)
      have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * g a by have := hg a; positivity)
      simp only [Pi.add_apply, hφdef, hψdef]
      push_cast
      linarith
    have hup : ∀ a, χ a ≤ (φ + ψ + 1) a := by
      intro a
      have hlt : χ a < φ a + ψ a + 2 := by
        apply (Nat.floor_lt (by have := hfg0 a; positivity)).2
        have := Nat.lt_floor_add_one ((2 : ℝ) ^ n * f a)
        have := Nat.lt_floor_add_one ((2 : ℝ) ^ n * g a)
        simp only [Pi.add_apply, hφdef, hψdef]
        push_cast
        linarith
      simp only [Pi.add_apply, Pi.one_apply]
      omega
    have hχ : ∀ a, χ a ≤ 2 ^ n := floor_le_pow hfg1 n
    have hφ : ∀ a, φ a ≤ 2 ^ n := floor_le_pow hf1 n
    have hφψ : ∀ a, φ a + ψ a ≤ 2 ^ n := fun a => le_trans (hlow a) (hχ a)
    have hadd := J_add hm h1 (2 ^ n) (2 ^ n) φ ψ (floor_le_pow hg1 n) hφψ
    have h_lower : J m φ (2 ^ n) + J m ψ (2 ^ n) ≤ J m χ (2 ^ n) :=
      hadd ▸ J_mono hm h1 hlow (2 ^ n)
    have h_upper : J m χ (2 ^ n) ≤ J m φ (2 ^ n) + J m ψ (2 ^ n) + 1 := by
      rw [← J_extend hm hχ (2 ^ n + 1) (by omega)]
      calc J m χ (2 ^ n + 1) ≤ J m (φ + ψ + 1) (2 ^ n + 1) := J_mono hm h1 hup _
        _ = J m (φ + ψ) (2 ^ n + 1) + (m {a | 1 ≤ (1 : α → ℕ) a}).toReal :=
            J_add_le_one hm h1 _ _ _ (fun a => le_refl _)
              (fun a => by have := hφψ a; simp only [Pi.add_apply, Pi.one_apply]; omega)
        _ ≤ J m (φ + ψ) (2 ^ n + 1) + 1 := by gcongr; exact fa_toReal_le_one hm h1 _
        _ = J m φ (2 ^ n) + J m ψ (2 ^ n) + 1 := by
            rw [J_extend hm (N := 2 ^ n) (fun a => by simpa only [Pi.add_apply] using hφψ a)
              (2 ^ n + 1) (by omega), hadd]
    rw [one_div_pow, ← add_div, ← add_div]
    exact ⟨div_le_div_of_nonneg_right h_lower hp.le, div_le_div_of_nonneg_right h_upper hp.le⟩
  have hd : Filter.Tendsto (fun n => layerSum m (f + g) n - (layerSum m f n + layerSum m g n))
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => by linarith [(hbound n).1]) (fun n => by linarith [(hbound n).2])
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have := tendsto_nhds_unique (tfg.sub (tf.add tg)) hd
  unfold integ
  linarith

end PartB1

section B1
variable {α : Type*} {m : Set α → ℝ≥0∞}

alias integ_indicator := PartB1.integ_indicator

alias integ_add := PartB1.integ_add

alias integ_congr := PartB1.integ_congr

alias integ_comp_equiv := PartB1.integ_comp_equiv

alias integ_nonneg_le_one := PartB1.integ_nonneg_le_one

end B1

/-! ## Part B2: symmetric translation-invariant means on finitely supported `ℤ`-functions -/


namespace PartB2
open scoped ENNReal Pointwise

/-- Right composition with a permutation is injective. -/
lemma comp_perm_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun w : Fin n → ℤ => w ∘ σ) := by
  intro a b h
  funext i
  have := congrFun h (σ.symm i)
  simpa using this

/-- Right composition with a permutation is surjective. -/
lemma comp_perm_surjective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Surjective (fun w : Fin n → ℤ => w ∘ σ) := by
  intro w
  exact ⟨w ∘ σ.symm, by funext i; simp⟩

theorem exists_symMean (n : ℕ) : ∃ μ : Set (Fin n → ℤ) → ℝ≥0∞,
    Garrido.IsFinitelyAdditiveMeasure μ ∧ μ Set.univ = 1 ∧
    (∀ (v : Fin n → ℤ) (S : Set (Fin n → ℤ)), μ ((v + ·) '' S) = μ S) ∧
    (∀ (σ : Equiv.Perm (Fin n)) (S : Set (Fin n → ℤ)), μ ((fun w => w ∘ σ) '' S) = μ S) := by
  obtain ⟨m, hm, h1, hinv⟩ := Garrido.isAmenable_of_commGroup (Multiplicative (Fin n → ℤ))
  -- transport to `Fin n → ℤ`
  set m' : Set (Fin n → ℤ) → ℝ≥0∞ := fun S => m (Multiplicative.toAdd ⁻¹' S) with hm'def
  have hm'0 : m' ∅ = 0 := by simp [hm'def, hm.1]
  have hm'add : ∀ s t : Set (Fin n → ℤ), Disjoint s t → m' (s ∪ t) = m' s + m' t := by
    intro s t hst
    simp only [hm'def, Set.preimage_union]
    exact hm.2 _ _ (hst.preimage _)
  have hm'1 : m' Set.univ = 1 := by simp [hm'def, h1]
  have hm'tr : ∀ (v : Fin n → ℤ) (S : Set (Fin n → ℤ)), m' ((v + ·) '' S) = m' S := by
    intro v S
    have key : Multiplicative.toAdd ⁻¹' ((v + ·) '' S) =
        Multiplicative.ofAdd v • (Multiplicative.toAdd ⁻¹' S) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_smul_set, smul_eq_mul]
      constructor
      · rintro ⟨s, hs, hsg⟩
        refine ⟨Multiplicative.ofAdd s, by simpa using hs, ?_⟩
        rw [← ofAdd_add, hsg, ofAdd_toAdd]
      · rintro ⟨y, hy, rfl⟩
        exact ⟨Multiplicative.toAdd y, hy, by simp⟩
    simp only [hm'def]
    rw [key, hinv]
  -- symmetrise
  set c : ℝ≥0∞ := ((Fintype.card (Equiv.Perm (Fin n)) : ℕ) : ℝ≥0∞)⁻¹ with hc
  refine ⟨fun S => c * ∑ σ : Equiv.Perm (Fin n), m' ((fun w => w ∘ σ) '' S), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [hm'0]
  · intro s t hst
    simp only [Set.image_union]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact hm'add _ _ ((Set.disjoint_image_iff (comp_perm_injective σ)).mpr hst)
  · simp only [Set.image_univ_of_surjective (comp_perm_surjective _), hm'1, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, hc]
    exact ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _)
  · intro v S
    simp only
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    have : (fun w : Fin n → ℤ => w ∘ σ) '' ((v + ·) '' S) =
        ((v ∘ σ) + ·) '' ((fun w : Fin n → ℤ => w ∘ σ) '' S) := by
      simp only [Set.image_image]
      rfl
    rw [this, hm'tr]
  · intro τ S
    simp only
    congr 1
    have : ∀ σ : Equiv.Perm (Fin n), (fun w : Fin n → ℤ => w ∘ σ) '' ((fun w => w ∘ τ) '' S) =
        (fun w : Fin n → ℤ => w ∘ (Equiv.mulLeft τ σ)) '' S := by
      intro σ
      simp only [Set.image_image, Equiv.coe_mulLeft, Equiv.Perm.coe_mul]
      rfl
    simp only [this]
    exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => m' ((fun w : Fin n → ℤ => w ∘ σ) '' S))
end PartB2

alias exists_symMean := PartB2.exists_symMean

noncomputable def symMean (n : ℕ) : Set (Fin n → ℤ) → ℝ≥0∞ := (exists_symMean n).choose

/-- The finitely supported function on `X` that is `w` on `A` (through `A.equivFin`) and `0`
off `A`. -/
noncomputable def extendFin {X : Type*} (A : Finset X) (w : Fin A.card → ℤ) : X →₀ ℤ :=
  Finsupp.onFinset A (fun x => open Classical in if h : x ∈ A then w (A.equivFin ⟨x, h⟩) else 0)
    (by intro x hx; by_contra h; simp [h] at hx)

/-- The mean on `X →₀ ℤ` carried by the finite set `A`. -/
noncomputable def meanOn {X : Type*} (A : Finset X) (S : Set (X →₀ ℤ)) : ℝ≥0∞ :=
  symMean A.card {w | extendFin A w ∈ S}


namespace PartB2
open scoped ENNReal Pointwise
section B2
variable {X : Type*}

lemma symMean_spec (n : ℕ) :
    Garrido.IsFinitelyAdditiveMeasure (symMean n) ∧ symMean n Set.univ = 1 ∧
    (∀ (v : Fin n → ℤ) (S : Set (Fin n → ℤ)), symMean n ((v + ·) '' S) = symMean n S) ∧
    (∀ (σ : Equiv.Perm (Fin n)) (S : Set (Fin n → ℤ)),
      symMean n ((fun w => w ∘ σ) '' S) = symMean n S) :=
  (FAmenChild.exists_symMean n).choose_spec

lemma meanOn_eq (A : Finset X) (S : Set (X →₀ ℤ)) :
    meanOn A S = symMean A.card (extendFin A ⁻¹' S) := rfl

lemma extendFin_apply (A : Finset X) (w : Fin A.card → ℤ) (x : X) :
    extendFin A w x = open Classical in if h : x ∈ A then w (A.equivFin ⟨x, h⟩) else 0 := by
  simp [extendFin, Finsupp.onFinset_apply]

lemma extendFin_add (A : Finset X) (u v : Fin A.card → ℤ) :
    extendFin A (u + v) = extendFin A u + extendFin A v := by
  ext x
  simp only [extendFin_apply, Finsupp.coe_add, Pi.add_apply]
  split_ifs <;> simp

lemma extendFin_neg (A : Finset X) (u : Fin A.card → ℤ) :
    extendFin A (-u) = -extendFin A u := by
  ext x
  simp only [extendFin_apply, Finsupp.coe_neg, Pi.neg_apply]
  split_ifs <;> simp

lemma extendFin_restrict (A : Finset X) (w : X →₀ ℤ) (hw : (↑w.support : Set X) ⊆ ↑A) :
    extendFin A (fun i => w (A.equivFin.symm i)) = w := by
  ext x
  rw [extendFin_apply]
  split_ifs with h
  · simp
  · have : x ∉ w.support := fun hx => h (hw hx)
    simp only [Finsupp.mem_support_iff, not_not] at this
    exact this.symm

/-- Right composition with an equivalence, as a preimage, symmetrises away. -/
lemma symMean_preimage_comp (k l : ℕ) (τ : Fin k ≃ Fin l) (T : Set (Fin k → ℤ)) :
    symMean l ((fun w : Fin l → ℤ => w ∘ τ) ⁻¹' T) = symMean k T := by
  obtain rfl : k = l := by simpa using Fintype.card_congr τ
  have : (fun w : Fin k → ℤ => w ∘ τ) ⁻¹' T = (fun w : Fin k → ℤ => w ∘ τ.symm) '' T := by
    ext w
    constructor
    · intro h
      exact ⟨w ∘ τ, h, by funext i; simp⟩
    · rintro ⟨u, hu, rfl⟩
      simpa [Set.mem_preimage, Function.comp_def] using hu
  rw [this]
  exact (symMean_spec k).2.2.2 τ.symm T

theorem meanOn_isFinitelyAdditiveMeasure (A : Finset X) :
    Garrido.IsFinitelyAdditiveMeasure (meanOn A) ∧ meanOn A Set.univ = 1 := by
  obtain ⟨⟨h0, hadd⟩, h1, -, -⟩ := symMean_spec A.card
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [meanOn_eq] using h0
  · intro s t hst
    simp only [meanOn_eq, Set.preimage_union]
    exact hadd _ _ (hst.preimage _)
  · simpa [meanOn_eq] using h1

theorem meanOn_add (A : Finset X) (w : X →₀ ℤ) (hw : (↑w.support : Set X) ⊆ ↑A)
    (S : Set (X →₀ ℤ)) : meanOn A ((w + ·) '' S) = meanOn A S := by
  set w₀ : Fin A.card → ℤ := fun i => w (A.equivFin.symm i) with hw₀
  have hext : extendFin A w₀ = w := extendFin_restrict A w hw
  have key : extendFin A ⁻¹' ((w + ·) '' S) = (w₀ + ·) '' (extendFin A ⁻¹' S) := by
    rw [Set.image_add_left, Set.image_add_left, ← Set.preimage_comp, ← Set.preimage_comp]
    congr 1
    funext u
    simp only [Function.comp_apply]
    rw [extendFin_add, extendFin_neg, hext]
  rw [meanOn_eq, meanOn_eq, key]
  exact (symMean_spec A.card).2.2.1 w₀ _

theorem meanOn_perm (σ : Equiv.Perm X) (A : Finset X) (S : Set (X →₀ ℤ)) :
    meanOn (A.map σ.toEmbedding) ((Finsupp.mapDomain σ) '' S) = meanOn A S := by
  set B := A.map σ.toEmbedding with hB
  have hmem : ∀ x, x ∈ A ↔ σ x ∈ B := fun x => by
    simp [hB]
  let e : A ≃ B := σ.subtypeEquiv hmem
  let τ : Fin A.card ≃ Fin B.card := A.equivFin.symm.trans (e.trans B.equivFin)
  have hτ : ∀ x (h : x ∈ A), τ (A.equivFin ⟨x, h⟩) = B.equivFin ⟨σ x, (hmem x).1 h⟩ := by
    intro x h
    simp [τ, e]
  have hid : ∀ w : Fin B.card → ℤ,
      extendFin B w = Finsupp.mapDomain σ (extendFin A (w ∘ τ)) := by
    intro w
    ext y
    obtain ⟨x, rfl⟩ := σ.surjective y
    rw [Finsupp.mapDomain_apply σ.injective, extendFin_apply, extendFin_apply]
    by_cases h : x ∈ A
    · rw [dif_pos h, dif_pos ((hmem x).1 h), Function.comp_apply, hτ x h]
    · rw [dif_neg h, dif_neg (fun h' => h ((hmem x).2 h'))]
  have key : extendFin B ⁻¹' ((Finsupp.mapDomain σ) '' S) =
      (fun w : Fin B.card → ℤ => w ∘ τ) ⁻¹' (extendFin A ⁻¹' S) := by
    ext w
    simp only [Set.mem_preimage, hid w]
    exact (Finsupp.mapDomain_injective σ.injective).mem_set_image
  rw [meanOn_eq, meanOn_eq, key]
  exact symMean_preimage_comp A.card B.card τ _

end B2

end PartB2

section B2
variable {X : Type*}

alias meanOn_isFinitelyAdditiveMeasure := PartB2.meanOn_isFinitelyAdditiveMeasure

alias meanOn_add := PartB2.meanOn_add

alias meanOn_perm := PartB2.meanOn_perm

end B2

/-! ## Part B3: the mean on `X →₀ ℤ` from extensive amenability -/


namespace PartB3
open scoped ENNReal Pointwise

lemma fam_mono {α : Type*} {m : Set α → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    {s t : Set α} (hst : s ⊆ t) : m s ≤ m t := by
  have := hm.2 s (t \ s) disjoint_sdiff_self_right
  rw [Set.union_sdiff_cancel hst] at this
  rw [this]
  exact le_self_add

lemma fam_le_one {α : Type*} {m : Set α → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    (h1 : m Set.univ = 1) (s : Set α) : m s ≤ 1 :=
  h1 ▸ fam_mono hm (Set.subset_univ s)

lemma fam_compl_eq_zero {α : Type*} {m : Set α → ℝ≥0∞}
    (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) {s : Set α}
    (hs : m s = 1) : m sᶜ = 0 := by
  have := hm.2 s sᶜ disjoint_compl_right
  rw [Set.union_compl_self, h1, hs] at this
  have h' : (1 : ℝ≥0∞) + m sᶜ = 1 + 0 := by rw [← this, add_zero]
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h'

lemma meanOn_le_one {X : Type*} (A : Finset X) (S : Set (X →₀ ℤ)) : meanOn A S ≤ 1 :=
  fam_le_one (meanOn_isFinitelyAdditiveMeasure A).1 (meanOn_isFinitelyAdditiveMeasure A).2 S

lemma meanOn_ne_top {X : Type*} (A : Finset X) (S : Set (X →₀ ℤ)) : meanOn A S ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (meanOn_le_one A S)

theorem exists_affine_mean {G X : Type*} [Group G] [MulAction G X] (Y : Set X)
    (h : ThompsonAmenability.IsExtensivelyAmenableOn G X Y) :
    ∃ μ : Set (X →₀ ℤ) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure μ ∧ μ Set.univ = 1 ∧
      (∀ (g : G) (S : Set (X →₀ ℤ)), μ ((Finsupp.mapDomain (fun x => g • x)) '' S) = μ S) ∧
      (∀ w : X →₀ ℤ, (↑w.support : Set X) ⊆ Y → ∀ S, μ ((w + ·) '' S) = μ S) := by
  obtain ⟨m, hm, -, h1, hinv, hfull⟩ := h
  refine ⟨fun S => ENNReal.ofReal (integ m (fun A => (meanOn A S).toReal)), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- `μ ∅ = 0`
    have h0 : (fun A : Finset X => (meanOn A (∅ : Set (X →₀ ℤ))).toReal)
        = (∅ : Set (Finset X)).indicator 1 := by
      funext A
      rw [(meanOn_isFinitelyAdditiveMeasure A).1.1, Set.indicator_empty]
      rfl
    simp only
    rw [h0, integ_indicator hm h1, hm.1]
    simp
  · -- finite additivity
    intro s t hst
    have hadd : ∀ A : Finset X, meanOn A (s ∪ t) = meanOn A s + meanOn A t :=
      fun A => (meanOn_isFinitelyAdditiveMeasure A).1.2 s t hst
    have hfun : (fun A : Finset X => (meanOn A (s ∪ t)).toReal)
        = (fun A => (meanOn A s).toReal) + (fun A => (meanOn A t).toReal) := by
      funext A
      rw [hadd A, Pi.add_apply, ENNReal.toReal_add (meanOn_ne_top A s) (meanOn_ne_top A t)]
    have hle : ∀ A : Finset X, (meanOn A s).toReal + (meanOn A t).toReal ≤ 1 := by
      intro A
      rw [← ENNReal.toReal_add (meanOn_ne_top A s) (meanOn_ne_top A t), ← hadd A]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by rw [ENNReal.ofReal_one]; exact meanOn_le_one A _)
    have hf0 : ∀ A : Finset X, 0 ≤ (meanOn A s).toReal := fun A => ENNReal.toReal_nonneg
    have hg0 : ∀ A : Finset X, 0 ≤ (meanOn A t).toReal := fun A => ENNReal.toReal_nonneg
    have hf1 : ∀ A : Finset X, (meanOn A s).toReal ≤ 1 := fun A =>
      le_trans (le_add_of_nonneg_right (hg0 A)) (hle A)
    have hg1 : ∀ A : Finset X, (meanOn A t).toReal ≤ 1 := fun A =>
      le_trans (le_add_of_nonneg_left (hf0 A)) (hle A)
    simp only
    rw [hfun, integ_add hm h1 hf0 hg0 hle,
      ENNReal.ofReal_add (integ_nonneg_le_one hm h1 hf0 hf1).1
        (integ_nonneg_le_one hm h1 hg0 hg1).1]
  · -- `μ univ = 1`
    have hu : (fun A : Finset X => (meanOn A (Set.univ : Set (X →₀ ℤ))).toReal)
        = (Set.univ : Set (Finset X)).indicator 1 := by
      funext A
      rw [(meanOn_isFinitelyAdditiveMeasure A).2, Set.indicator_univ]
      rfl
    simp only
    rw [hu, integ_indicator hm h1, h1]
    simp
  · -- invariance under the linear action of `G`
    intro g S
    simp only
    congr 1
    let τ : Finset X ≃ Finset X := (MulAction.toPerm g⁻¹ : Equiv.Perm X).finsetCongr
    have hτ : ∀ T : Set (Finset X), m (τ '' T) = m T := fun T => hinv g⁻¹ T
    have hfun : (fun A : Finset X => (meanOn A (Finsupp.mapDomain (fun x => g • x) '' S)).toReal)
        = (fun A : Finset X => (meanOn A S).toReal) ∘ τ := by
      funext A
      have key := meanOn_perm (MulAction.toPerm g) (A.map (MulAction.toPerm g⁻¹).toEmbedding) S
      have hA : (A.map (MulAction.toPerm g⁻¹ : Equiv.Perm X).toEmbedding).map
          (MulAction.toPerm g : Equiv.Perm X).toEmbedding = A := by
        rw [Finset.map_map]
        ext x
        simp
      rw [hA] at key
      exact congrArg ENNReal.toReal key
    rw [hfun, integ_comp_equiv τ hτ]
  · -- invariance under translations supported in `Y`
    intro w hw S
    simp only
    congr 1
    apply integ_congr hm h1
    have hsub : {A : Finset X | (meanOn A ((w + ·) '' S)).toReal ≠ (meanOn A S).toReal}
        ⊆ {A : Finset X | w.support ⊆ A}ᶜ := by
      intro A hA hwA
      apply hA
      rw [meanOn_add A w (by exact_mod_cast hwA) S]
    have hc : m {A : Finset X | w.support ⊆ A}ᶜ = 0 :=
      fam_compl_eq_zero hm h1 (hfull w.support hw)
    exact le_antisymm (hc ▸ fam_mono hm hsub) bot_le

end PartB3

alias exists_affine_mean := PartB3.exists_affine_mean

/-! ## Part C: the slope-jump cocycle of `F` and freeness of its affine action -/

open CannonFloydParry

/-- The dyadic rationals of `(0,1)`. -/
def D : Set UI := {x | 0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ IsDyadic x}

/-- The exponent `n` of the slope `2^n` of `f` just to the right of `x` (`0` if there is none). -/
noncomputable def rexp (f : UI ≃o UI) (x : UI) : ℤ :=
  open Classical in
  if h : ∃ (n : ℤ) (c δ : ℝ), 0 < δ ∧ ∀ z : UI, (x : ℝ) ≤ z → (z : ℝ) ≤ x + δ →
      (f z : ℝ) = 2 ^ n * z + c then h.choose else 0

/-- The exponent of the slope of `f` just to the left of `x` (`0` if there is none). -/
noncomputable def lexp (f : UI ≃o UI) (x : UI) : ℤ :=
  open Classical in
  if h : ∃ (n : ℤ) (c δ : ℝ), 0 < δ ∧ ∀ z : UI, (x : ℝ) - δ ≤ z → (z : ℝ) ≤ x →
      (f z : ℝ) = 2 ^ n * z + c then h.choose else 0

/-- The jump of the slope exponent at a point of `D` (`0` elsewhere). -/
noncomputable def jumpFun (f : UI ≃o UI) (x : UI) : ℤ :=
  open Classical in if x ∈ D then rexp f x - lexp f x else 0


namespace PartC1
open scoped ENNReal Pointwise
open CannonFloydParry

open FAmenChild

/-! ### Elementary helpers -/

/-- Two affine maps with power-of-two slopes that agree at two distinct points have the same
slope exponent. -/
lemma zpow_eq_of_two_points {n m : ℤ} {c c' p q : ℝ} (hpq : p < q)
    (hp : (2 : ℝ) ^ n * p + c = 2 ^ m * p + c') (hq : (2 : ℝ) ^ n * q + c = 2 ^ m * q + c') :
    n = m := by
  have h : (2 : ℝ) ^ n * (q - p) = 2 ^ m * (q - p) := by linarith
  have h2 : (2 : ℝ) ^ n = 2 ^ m := mul_right_cancel₀ (sub_ne_zero.mpr hpq.ne') h
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) h2

/-- A finite set of reals stays a positive distance (below any prescribed `ε`) from any point
other than its own elements. -/
lemma exists_gap (B : Finset ℝ) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ ≤ ε ∧ ∀ b ∈ B, b ≠ x → δ ≤ |b - x| := by
  induction B using Finset.induction_on with
  | empty => exact ⟨ε, hε, le_rfl, by simp⟩
  | insert b B _ ih =>
    obtain ⟨δ, hδ, hδε, hδB⟩ := ih
    by_cases hbx : b = x
    · refine ⟨δ, hδ, hδε, ?_⟩
      intro t ht htx
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact absurd hbx htx
      · exact hδB t ht htx
    · refine ⟨min δ |b - x|, lt_min hδ (abs_pos.mpr (sub_ne_zero.mpr hbx)),
        (min_le_left _ _).trans hδε, ?_⟩
      intro t ht htx
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hδB t ht htx)

lemma inter_eq_empty_of_gap {B : Finset ℝ} {x δ a b : ℝ}
    (hδB : ∀ t ∈ B, t ≠ x → δ ≤ |t - x|) (hxB : ∀ t ∈ B, t ∈ Set.Ioo a b → t ≠ x)
    (hab : ∀ t ∈ Set.Ioo a b, |t - x| < δ) : Set.Ioo a b ∩ (B : Set ℝ) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ⟨ht, htB⟩ => ?_
  have := hδB t htB (hxB t htB ht)
  have := hab t ht
  linarith

/-- The image of a point of `D` under an element of `F` is in `D`. -/
lemma mapsTo_D {g : UI ≃o UI} (hg : g ∈ F) {x : UI} (hx : x ∈ D) : g x ∈ D := by
  obtain ⟨h0, h1, hd⟩ := hx
  refine ⟨?_, ?_, (bijOn_dyadic hg).mapsTo hd⟩
  · have hlt : (⟨0, zero_mem_UI⟩ : UI) < x := h0
    have h2 : g ⟨0, zero_mem_UI⟩ < g x := g.lt_iff_lt.mpr hlt
    exact lt_of_le_of_lt (g ⟨0, zero_mem_UI⟩).2.1 h2
  · have hlt : x < (⟨1, one_mem_UI⟩ : UI) := h1
    have h2 : g x < g ⟨1, one_mem_UI⟩ := g.lt_iff_lt.mpr hlt
    exact lt_of_lt_of_le h2 (g ⟨1, one_mem_UI⟩).2.2

lemma lt_one_apply {g : UI ≃o UI} {x : UI} (hx : (x : ℝ) < 1) : (g x : ℝ) < 1 := by
  have hlt : x < (⟨1, one_mem_UI⟩ : UI) := hx
  have h2 : g x < g ⟨1, one_mem_UI⟩ := g.lt_iff_lt.mpr hlt
  exact lt_of_lt_of_le h2 (g ⟨1, one_mem_UI⟩).2.2

lemma pos_apply {g : UI ≃o UI} {x : UI} (hx : 0 < (x : ℝ)) : 0 < (g x : ℝ) := by
  have hlt : (⟨0, zero_mem_UI⟩ : UI) < x := hx
  have h2 : g ⟨0, zero_mem_UI⟩ < g x := g.lt_iff_lt.mpr hlt
  exact lt_of_le_of_lt (g ⟨0, zero_mem_UI⟩).2.1 h2

/-! ### The one-sided slope exponents -/

/-- Any power-of-two slope that `f` has just to the right of `x` is `2 ^ rexp f x`. -/
lemma rexp_eq {f : UI ≃o UI} {x : UI} (hx : (x : ℝ) < 1) {n : ℤ} {c δ : ℝ} (hδ : 0 < δ)
    (h : ∀ z : UI, (x : ℝ) ≤ z → (z : ℝ) ≤ x + δ → (f z : ℝ) = 2 ^ n * z + c) :
    rexp f x = n := by
  have hex : ∃ (n : ℤ) (c δ : ℝ), 0 < δ ∧ ∀ z : UI, (x : ℝ) ≤ z → (z : ℝ) ≤ x + δ →
      (f z : ℝ) = 2 ^ n * z + c := ⟨n, c, δ, hδ, h⟩
  unfold rexp
  rw [dif_pos hex]
  obtain ⟨c', δ', hδ', h'⟩ := hex.choose_spec
  set ε := min (min δ δ') (1 - x) with hε
  have hε0 : 0 < ε := lt_min (lt_min hδ hδ') (sub_pos.mpr hx)
  have hε1 : ε ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ δ' := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ 1 - x := min_le_right _ _
  have hy : (x : ℝ) + ε ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [x.2.1], by linarith⟩
  have hx1 : (x : ℝ) ≤ x + δ := by linarith
  have hx2 : (x : ℝ) ≤ x + δ' := by linarith
  refine zpow_eq_of_two_points (p := x) (q := x + ε) (c := c') (c' := c) (by linarith)
    ((h' x le_rfl hx2).symm.trans (h x le_rfl hx1))
    ((h' ⟨_, hy⟩ (by simp; linarith) (by simp; linarith)).symm.trans
      (h ⟨_, hy⟩ (by simp; linarith) (by simp; linarith)))

/-- Any power-of-two slope that `f` has just to the left of `x` is `2 ^ lexp f x`. -/
lemma lexp_eq {f : UI ≃o UI} {x : UI} (hx : 0 < (x : ℝ)) {n : ℤ} {c δ : ℝ} (hδ : 0 < δ)
    (h : ∀ z : UI, (x : ℝ) - δ ≤ z → (z : ℝ) ≤ x → (f z : ℝ) = 2 ^ n * z + c) :
    lexp f x = n := by
  have hex : ∃ (n : ℤ) (c δ : ℝ), 0 < δ ∧ ∀ z : UI, (x : ℝ) - δ ≤ z → (z : ℝ) ≤ x →
      (f z : ℝ) = 2 ^ n * z + c := ⟨n, c, δ, hδ, h⟩
  unfold lexp
  rw [dif_pos hex]
  obtain ⟨c', δ', hδ', h'⟩ := hex.choose_spec
  set ε := min (min δ δ') (x : ℝ) with hε
  have hε0 : 0 < ε := lt_min (lt_min hδ hδ') hx
  have hε1 : ε ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ δ' := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ x := min_le_right _ _
  have hy : (x : ℝ) - ε ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [x.2.2]⟩
  have hx1 : (x : ℝ) - δ ≤ x := by linarith
  have hx2 : (x : ℝ) - δ' ≤ x := by linarith
  refine zpow_eq_of_two_points (p := x - ε) (q := x) (c := c') (c' := c) (by linarith)
    ((h' ⟨_, hy⟩ (by simp; linarith) (by simp; linarith)).symm.trans
      (h ⟨_, hy⟩ (by simp; linarith) (by simp; linarith)))
    ((h' x hx2 le_rfl).symm.trans (h x hx1 le_rfl))

theorem rexp_spec {f : UI ≃o UI} (hf : f ∈ F) {x : UI} (hx : (x : ℝ) < 1) :
    ∃ c δ : ℝ, 0 < δ ∧ ∀ z : UI, (x : ℝ) ≤ z → (z : ℝ) ≤ x + δ →
      (f z : ℝ) = 2 ^ rexp f x * z + c := by
  have hex : ∃ (n : ℤ) (c δ : ℝ), 0 < δ ∧ ∀ z : UI, (x : ℝ) ≤ z → (z : ℝ) ≤ x + δ →
      (f z : ℝ) = 2 ^ n * z + c := by
    obtain ⟨B, -, hB⟩ := mem_F_iff_isThompson.mp hf
    obtain ⟨δ, hδ, hδε, hδB⟩ := exists_gap B (x : ℝ) (sub_pos.mpr hx)
    have hy : (x : ℝ) + δ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [x.2.1], by linarith⟩
    obtain ⟨n, c, hnc⟩ := hB x ⟨_, hy⟩ (by simp; linarith)
      (inter_eq_empty_of_gap hδB (fun t _ ht => ne_of_gt ht.1)
        (fun t ht => by rw [abs_of_pos (by linarith [ht.1])]; simp at ht; linarith [ht.2]))
    exact ⟨n, c, δ, hδ, fun z h1 h2 => hnc z ⟨h1, h2⟩⟩
  unfold rexp
  rw [dif_pos hex]
  exact hex.choose_spec

theorem lexp_spec {f : UI ≃o UI} (hf : f ∈ F) {x : UI} (hx : 0 < (x : ℝ)) :
    ∃ c δ : ℝ, 0 < δ ∧ ∀ z : UI, (x : ℝ) - δ ≤ z → (z : ℝ) ≤ x →
      (f z : ℝ) = 2 ^ lexp f x * z + c := by
  have hex : ∃ (n : ℤ) (c δ : ℝ), 0 < δ ∧ ∀ z : UI, (x : ℝ) - δ ≤ z → (z : ℝ) ≤ x →
      (f z : ℝ) = 2 ^ n * z + c := by
    obtain ⟨B, -, hB⟩ := mem_F_iff_isThompson.mp hf
    obtain ⟨δ, hδ, hδε, hδB⟩ := exists_gap B (x : ℝ) hx
    have hy : (x : ℝ) - δ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [x.2.2]⟩
    obtain ⟨n, c, hnc⟩ := hB ⟨_, hy⟩ x (by simp; linarith)
      (inter_eq_empty_of_gap hδB (fun t _ ht => ne_of_lt (by simpa using ht.2))
        (fun t ht => by
          simp at ht
          rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.1]))
    exact ⟨n, c, δ, hδ, fun z h1 h2 => hnc z ⟨h1, h2⟩⟩
  unfold lexp
  rw [dif_pos hex]
  exact hex.choose_spec

theorem jumpFun_finite {f : UI ≃o UI} (hf : f ∈ F) : (Function.support (jumpFun f)).Finite := by
  obtain ⟨B, -, hB⟩ := mem_F_iff_isThompson.mp hf
  refine (B.finite_toSet.preimage Subtype.val_injective.injOn).subset ?_
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxB
  have hxB' : (x : ℝ) ∉ B := by simpa using hxB
  apply hx
  unfold jumpFun
  split_ifs with hD
  · obtain ⟨h0, h1, -⟩ := hD
    obtain ⟨δ, hδ, hδε, hδB⟩ := exists_gap B (x : ℝ) (lt_min h0 (sub_pos.mpr h1))
    have hδ0 : δ ≤ x := hδε.trans (min_le_left _ _)
    have hδ1 : δ ≤ 1 - x := hδε.trans (min_le_right _ _)
    have ha : (x : ℝ) - δ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [x.2.2]⟩
    have hb : (x : ℝ) + δ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [x.2.1], by linarith⟩
    obtain ⟨n, c, hnc⟩ := hB ⟨_, ha⟩ ⟨_, hb⟩ (by simp; linarith)
      (inter_eq_empty_of_gap hδB (fun t htB _ htx => hxB' (htx ▸ htB))
        (fun t ht => by simp at ht; rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]))
    rw [rexp_eq h1 hδ (fun z hz1 hz2 => hnc z ⟨by simp; linarith, hz2⟩),
      lexp_eq h0 hδ (fun z hz1 hz2 => hnc z ⟨hz1, by simp; linarith⟩), sub_self]
  · rfl
end PartC1

alias rexp_spec := PartC1.rexp_spec

alias lexp_spec := PartC1.lexp_spec

alias jumpFun_finite := PartC1.jumpFun_finite

noncomputable def jump (g : F) : UI →₀ ℤ :=
  Finsupp.ofSupportFinite (jumpFun (g : UI ≃o UI)) (jumpFun_finite g.2)

/-- The cocycle `c g = g · jump g`, i.e. `c g x = jump g (g⁻¹ x)`. -/
noncomputable def cocycle (g : F) : UI →₀ ℤ := Finsupp.mapDomain (fun x => g • x) (jump g)


namespace PartC1
open scoped ENNReal Pointwise
open CannonFloydParry
open FAmenChild
theorem cocycle_support (g : F) : (↑(cocycle g).support : Set UI) ⊆ D := by
  classical
  intro y hy
  have hy' := Finsupp.mapDomain_support (f := fun x => g • x) (s := jump g) hy
  rw [Finset.mem_image] at hy'
  obtain ⟨x, hx, rfl⟩ := hy'
  have hxD : x ∈ D := by
    by_contra hD
    rw [Finsupp.mem_support_iff] at hx
    apply hx
    simp only [jump, Finsupp.ofSupportFinite_coe, jumpFun]
    rw [if_neg hD]
  exact mapsTo_D g.2 hxD

/-- The chain rule for right slope exponents. -/
lemma rexp_mul {g h : UI ≃o UI} (hg : g ∈ F) (hh : h ∈ F) {x : UI} (hx : (x : ℝ) < 1) :
    rexp (g * h) x = rexp g (h x) + rexp h x := by
  obtain ⟨c1, δ1, hδ1, h1⟩ := rexp_spec hh hx
  obtain ⟨c2, δ2, hδ2, h2⟩ := rexp_spec hg (lt_one_apply (g := h) hx)
  have ha : (0 : ℝ) < 2 ^ rexp h x := zpow_pos two_pos _
  refine rexp_eq hx (c := 2 ^ rexp g (h x) * c1 + c2) (δ := min δ1 (δ2 / 2 ^ rexp h x))
    (lt_min hδ1 (div_pos hδ2 ha)) ?_
  intro z hz1 hz2
  have hzd1 : (z : ℝ) ≤ x + δ1 := hz2.trans (by linarith [min_le_left δ1 (δ2 / 2 ^ rexp h x)])
  have hzd2 : (z : ℝ) - x ≤ δ2 / 2 ^ rexp h x := by
    linarith [min_le_right δ1 (δ2 / 2 ^ rexp h x)]
  have e1 := h1 z hz1 hzd1
  have e0 := h1 x le_rfl (by linarith)
  have hdiff : (h z : ℝ) - h x = 2 ^ rexp h x * ((z : ℝ) - x) := by rw [e1, e0]; ring
  have hle1 : (h x : ℝ) ≤ h z := by
    have := mul_nonneg ha.le (sub_nonneg.mpr hz1); linarith
  have hle2 : (h z : ℝ) ≤ h x + δ2 := by
    have := mul_le_mul_of_nonneg_left hzd2 ha.le
    rw [mul_div_cancel₀ _ ha.ne'] at this; linarith
  rw [RelIso.mul_apply, h2 (h z) hle1 hle2, e1, zpow_add₀ two_ne_zero]
  ring

/-- The chain rule for left slope exponents. -/
lemma lexp_mul {g h : UI ≃o UI} (hg : g ∈ F) (hh : h ∈ F) {x : UI} (hx : 0 < (x : ℝ)) :
    lexp (g * h) x = lexp g (h x) + lexp h x := by
  obtain ⟨c1, δ1, hδ1, h1⟩ := lexp_spec hh hx
  obtain ⟨c2, δ2, hδ2, h2⟩ := lexp_spec hg (pos_apply (g := h) hx)
  have ha : (0 : ℝ) < 2 ^ lexp h x := zpow_pos two_pos _
  refine lexp_eq hx (c := 2 ^ lexp g (h x) * c1 + c2) (δ := min δ1 (δ2 / 2 ^ lexp h x))
    (lt_min hδ1 (div_pos hδ2 ha)) ?_
  intro z hz1 hz2
  have hzd1 : (x : ℝ) - δ1 ≤ z := le_trans (by linarith [min_le_left δ1 (δ2 / 2 ^ lexp h x)]) hz1
  have hzd2 : (x : ℝ) - z ≤ δ2 / 2 ^ lexp h x := by
    linarith [min_le_right δ1 (δ2 / 2 ^ lexp h x)]
  have e1 := h1 z hzd1 hz2
  have e0 := h1 x (by linarith) le_rfl
  have hdiff : (h x : ℝ) - h z = 2 ^ lexp h x * ((x : ℝ) - z) := by rw [e1, e0]; ring
  have hle1 : (h z : ℝ) ≤ h x := by
    have := mul_nonneg ha.le (sub_nonneg.mpr hz2); linarith
  have hle2 : (h x : ℝ) - δ2 ≤ h z := by
    have := mul_le_mul_of_nonneg_left hzd2 ha.le
    rw [mul_div_cancel₀ _ ha.ne'] at this; linarith
  rw [RelIso.mul_apply, h2 (h z) hle2 hle1, e1, zpow_add₀ two_ne_zero]
  ring

lemma jumpFun_mul {g h : UI ≃o UI} (hg : g ∈ F) (hh : h ∈ F) (x : UI) :
    jumpFun (g * h) x = jumpFun g (h x) + jumpFun h x := by
  by_cases hD : x ∈ D
  · have hhD : h x ∈ D := mapsTo_D hh hD
    unfold jumpFun
    rw [if_pos hD, if_pos hD, if_pos hhD, rexp_mul hg hh hD.2.1, lexp_mul hg hh hD.1]
    ring
  · have hhD : h x ∉ D := fun h' => hD (by simpa using mapsTo_D (inv_mem hh) h')
    unfold jumpFun
    rw [if_neg hD, if_neg hD, if_neg hhD, add_zero]

lemma jump_mul (g h : F) :
    jump (g * h) = Finsupp.mapDomain (fun x => h⁻¹ • x) (jump g) + jump h := by
  ext x
  have e : (Finsupp.mapDomain (fun x => h⁻¹ • x) (jump g)) x = jump g (h • x) := by
    conv_lhs => rw [← inv_smul_smul h x]
    exact Finsupp.mapDomain_apply (MulAction.injective h⁻¹) _ _
  rw [Finsupp.add_apply, e]
  simp only [jump, Finsupp.ofSupportFinite_coe]
  exact jumpFun_mul g.2 h.2 x

theorem cocycle_mul (g h : F) :
    cocycle (g * h) = cocycle g + Finsupp.mapDomain (fun x => g • x) (cocycle h) := by
  have e1 : (fun x : UI => (g * h) • x) ∘ (fun x => h⁻¹ • x) = fun x => g • x := by
    funext x; simp [mul_smul]
  have e2 : (fun x : UI => (g * h) • x) = (fun x => g • x) ∘ (fun x => h • x) := by
    funext x; simp [mul_smul]
  unfold cocycle
  rw [jump_mul, Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp, e1, e2,
    Finsupp.mapDomain_comp]

end PartC1

alias cocycle_support := PartC1.cocycle_support

alias cocycle_mul := PartC1.cocycle_mul


namespace PartC2
open scoped ENNReal Pointwise
open CannonFloydParry

open FAmenChild

/-! ### Uniqueness of slope exponents -/

theorem two_zpow_inj {n m : ℤ} (h : (2:ℝ) ^ n = 2 ^ m) : n = m :=
  zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) h

/-- If `f` is affine with slope `2^n` on `[x, y]`, `x < y`, then `rexp f x = n`. -/
theorem rexp_eq_of_affine {f : UI ≃o UI} (hf : f ∈ F) {x y : UI} (hxy : (x:ℝ) < y) {n : ℤ}
    {c : ℝ} (h : ∀ z : UI, (x:ℝ) ≤ z → (z:ℝ) ≤ y → (f z : ℝ) = 2 ^ n * z + c) :
    rexp f x = n := by
  have hx1 : (x:ℝ) < 1 := lt_of_lt_of_le hxy y.2.2
  obtain ⟨c', δ, hδ, h'⟩ := rexp_spec hf hx1
  set t : ℝ := min ((x:ℝ) + δ) y with ht
  have htx : (x:ℝ) < t := lt_min (by linarith) hxy
  have hty : t ≤ y := min_le_right _ _
  have htd : t ≤ (x:ℝ) + δ := min_le_left _ _
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [x.2.1], le_trans hty y.2.2⟩
  have e1 : (f x : ℝ) = 2 ^ n * x + c := h x le_rfl hxy.le
  have e2 : (f x : ℝ) = 2 ^ rexp f x * x + c' := h' x le_rfl (by linarith)
  have e3 : (f ⟨t, htI⟩ : ℝ) = 2 ^ n * t + c := h ⟨t, htI⟩ htx.le hty
  have e4 : (f ⟨t, htI⟩ : ℝ) = 2 ^ rexp f x * t + c' := h' ⟨t, htI⟩ htx.le htd
  have key : (2:ℝ) ^ n * (t - x) = 2 ^ rexp f x * (t - x) := by
    linear_combination e1 - e3 + e4 - e2
  have hne : t - (x:ℝ) ≠ 0 := by linarith
  exact (two_zpow_inj (mul_right_cancel₀ hne key)).symm

/-- If `f` is affine with slope `2^n` on `[x, y]`, `x < y`, then `lexp f y = n`. -/
theorem lexp_eq_of_affine {f : UI ≃o UI} (hf : f ∈ F) {x y : UI} (hxy : (x:ℝ) < y) {n : ℤ}
    {c : ℝ} (h : ∀ z : UI, (x:ℝ) ≤ z → (z:ℝ) ≤ y → (f z : ℝ) = 2 ^ n * z + c) :
    lexp f y = n := by
  have hy0 : 0 < (y:ℝ) := lt_of_le_of_lt x.2.1 hxy
  obtain ⟨c', δ, hδ, h'⟩ := lexp_spec hf hy0
  set t : ℝ := max ((y:ℝ) - δ) x with ht
  have hty : t < (y:ℝ) := max_lt (by linarith) hxy
  have htx : (x:ℝ) ≤ t := le_max_right _ _
  have htd : (y:ℝ) - δ ≤ t := le_max_left _ _
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans x.2.1 htx, by linarith [y.2.2]⟩
  have e1 : (f y : ℝ) = 2 ^ n * y + c := h y hxy.le le_rfl
  have e2 : (f y : ℝ) = 2 ^ lexp f y * y + c' := h' y (by linarith) le_rfl
  have e3 : (f ⟨t, htI⟩ : ℝ) = 2 ^ n * t + c := h ⟨t, htI⟩ htx hty.le
  have e4 : (f ⟨t, htI⟩ : ℝ) = 2 ^ lexp f y * t + c' := h' ⟨t, htI⟩ htd hty.le
  have key : (2:ℝ) ^ n * (y - t) = 2 ^ lexp f y * (y - t) := by
    linear_combination e3 - e1 + e2 - e4
  have hne : (y:ℝ) - t ≠ 0 := by linarith
  exact (two_zpow_inj (mul_right_cancel₀ hne key)).symm

/-- No jump strictly inside an interval on which `f` is affine. -/
theorem jumpFun_eq_zero_of_affine {f : UI ≃o UI} (hf : f ∈ F) {p q : UI} {n : ℤ} {c : ℝ}
    (h : ∀ z : UI, (p:ℝ) ≤ z → (z:ℝ) ≤ q → (f z : ℝ) = 2 ^ n * z + c) {y : UI}
    (hpy : (p:ℝ) < y) (hyq : (y:ℝ) < q) : jumpFun f y = 0 := by
  have h1 : rexp f y = n :=
    rexp_eq_of_affine hf hyq (fun z hz1 hz2 => h z (by linarith) hz2)
  have h2 : lexp f y = n :=
    lexp_eq_of_affine hf hpy (fun z hz1 hz2 => h z hz1 (by linarith))
  unfold jumpFun
  split_ifs <;> simp [h1, h2]

/-! ### Telescoping the jumps -/

/-- The sum of the slope jumps of `f` strictly between `p` and `q`. -/
noncomputable def jsum (f : UI ≃o UI) (p q : UI) : ℤ := ∑ᶠ y ∈ Set.Ioo p q, jumpFun f y

theorem jsum_split {f : UI ≃o UI} (hf : f ∈ F) {p b q : UI} (hpb : p < b) (hbq : b < q) :
    jsum f p q = jumpFun f b + jsum f p b + jsum f b q := by
  have hfin : ∀ s : Set UI, (s ∩ Function.support (jumpFun f)).Finite :=
    fun s => (jumpFun_finite hf).subset Set.inter_subset_right
  unfold jsum
  rw [← Set.Ioc_union_Ioo_eq_Ioo hpb.le hbq, ← Set.Ioo_insert_right hpb]
  rw [finsum_mem_union' _ (hfin _) (hfin _)]
  · rw [finsum_mem_insert' _ (fun h => lt_irrefl _ h.2) (hfin _)]
  · rw [Set.Ioo_insert_right hpb]
    exact Set.disjoint_left.2 (fun y h1 h2 => absurd h2.1 (not_lt.2 h1.2))

/-- The jumps of a Thompson map over `(p, q)` add up to `lexp f q - rexp f p`. -/
theorem jsum_eq {f : UI ≃o UI} (hf : f ∈ F) {p q : UI} (hpq : p < q) :
    jsum f p q = lexp f q - rexp f p := by
  obtain ⟨B, hBd, hB⟩ := mem_F_iff_isThompson.1 hf
  suffices H : ∀ k : ℕ, ∀ p q : UI, p < q →
      (B.filter (fun b => (p:ℝ) < b ∧ b < q)).card ≤ k → jsum f p q = lexp f q - rexp f p from
    H _ p q hpq le_rfl
  intro k
  induction k with
  | zero =>
    intro p q hpq hk
    have hempty : Set.Ioo (p:ℝ) q ∩ (B : Set ℝ) = ∅ := by
      ext b
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Finset.mem_coe, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro ⟨h1, h2⟩ hb
      have : b ∈ B.filter (fun b => (p:ℝ) < b ∧ b < q) := Finset.mem_filter.2 ⟨hb, h1, h2⟩
      rw [Nat.le_zero, Finset.card_eq_zero] at hk
      simp [hk] at this
    obtain ⟨n, c, haff⟩ := hB p q hpq hempty
    have haff' : ∀ z : UI, (p:ℝ) ≤ z → (z:ℝ) ≤ q → (f z : ℝ) = 2 ^ n * z + c :=
      fun z h1 h2 => haff z ⟨h1, h2⟩
    rw [rexp_eq_of_affine hf hpq haff', lexp_eq_of_affine hf hpq haff', sub_self]
    exact finsum_mem_eq_zero_of_forall_eq_zero
      (fun y hy => jumpFun_eq_zero_of_affine hf haff' hy.1 hy.2)
  | succ k ih =>
    intro p q hpq hk
    by_cases hex : ∃ b ∈ B, (p:ℝ) < b ∧ b < q
    · obtain ⟨b, hbB, hpb, hbq⟩ := hex
      have hbI : b ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [p.2.1], by linarith [q.2.2]⟩
      set bU : UI := ⟨b, hbI⟩ with hbU
      have hpb' : p < bU := hpb
      have hbq' : bU < q := hbq
      have hmem : b ∈ B.filter (fun b => (p:ℝ) < b ∧ b < q) := Finset.mem_filter.2 ⟨hbB, hpb, hbq⟩
      have hcard1 : (B.filter (fun x => (p:ℝ) < x ∧ x < (bU:ℝ))).card ≤ k := by
        have : (B.filter (fun x => (p:ℝ) < x ∧ x < (bU:ℝ))) ⊂
            B.filter (fun b => (p:ℝ) < b ∧ b < q) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨b, hmem, ?_⟩
            simp [bU]
          · intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, hx.2.1, lt_trans hx.2.2 hbq⟩
        have := Finset.card_lt_card this
        omega
      have hcard2 : (B.filter (fun x => (bU:ℝ) < x ∧ x < q)).card ≤ k := by
        have : (B.filter (fun x => (bU:ℝ) < x ∧ x < q)) ⊂
            B.filter (fun b => (p:ℝ) < b ∧ b < q) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨b, hmem, ?_⟩
            simp [bU]
          · intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, lt_trans hpb hx.2.1, hx.2.2⟩
        have := Finset.card_lt_card this
        omega
      have hD : bU ∈ D := ⟨by simpa [bU] using lt_of_le_of_lt p.2.1 hpb,
        by simpa [bU] using lt_of_lt_of_le hbq q.2.2, hBd b hbB⟩
      have hj : jumpFun f bU = rexp f bU - lexp f bU := by
        unfold jumpFun; rw [if_pos hD]
      rw [jsum_split hf hpb' hbq', hj, ih p bU hpb' hcard1, ih bU q hbq' hcard2]
      ring
    · have hempty : Set.Ioo (p:ℝ) q ∩ (B : Set ℝ) = ∅ := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Finset.mem_coe, Set.mem_empty_iff_false,
          iff_false, not_and]
        rintro ⟨h1, h2⟩ hb
        exact hex ⟨b, hb, h1, h2⟩
      obtain ⟨n, c, haff⟩ := hB p q hpq hempty
      have haff' : ∀ z : UI, (p:ℝ) ≤ z → (z:ℝ) ≤ q → (f z : ℝ) = 2 ^ n * z + c :=
        fun z h1 h2 => haff z ⟨h1, h2⟩
      rw [rexp_eq_of_affine hf hpq haff', lexp_eq_of_affine hf hpq haff', sub_self]
      exact finsum_mem_eq_zero_of_forall_eq_zero
        (fun y hy => jumpFun_eq_zero_of_affine hf haff' hy.1 hy.2)

/-! ### The cocycle relation forces the jumps over a fixed interval to cancel -/

theorem jumpFun_eq_of_cocycle (g : F) (φ : UI →₀ ℤ)
    (h : cocycle g + Finsupp.mapDomain (fun x => g • x) φ = φ) (x : UI) :
    jumpFun (g : UI ≃o UI) x = φ ((g : UI ≃o UI) x) - φ x := by
  have e1 : (cocycle g) (g • x) = jump g x :=
    Finsupp.mapDomain_apply (MulAction.injective g) (jump g) x
  have e2 : (Finsupp.mapDomain (fun x => g • x) φ) (g • x) = φ x :=
    Finsupp.mapDomain_apply (MulAction.injective g) φ x
  have e3 : jump g x = jumpFun (g : UI ≃o UI) x := by
    rw [jump, Finsupp.ofSupportFinite_coe]
  have := DFunLike.congr_fun h (g • x)
  rw [Finsupp.add_apply, e1, e2, e3] at this
  change jumpFun (g : UI ≃o UI) x + φ x = φ ((g : UI ≃o UI) x) at this
  omega

theorem jsum_eq_zero_of_cocycle (g : F) (φ : UI →₀ ℤ)
    (h : cocycle g + Finsupp.mapDomain (fun x => g • x) φ = φ) {p q : UI}
    (hp : (g : UI ≃o UI) p = p) (hq : (g : UI ≃o UI) q = q) :
    jsum (g : UI ≃o UI) p q = 0 := by
  set f : UI ≃o UI := (g : UI ≃o UI) with hfdef
  have hf : f ∈ F := g.2
  have hrel := jumpFun_eq_of_cocycle g φ h
  have hfinφ : ∀ s : Set UI, (s ∩ Function.support φ).Finite :=
    fun s => φ.support.finite_toSet.subset (by rw [← Finsupp.fun_support_eq]; exact Set.inter_subset_right)
  have hfinJ : ∀ s : Set UI, (s ∩ Function.support (jumpFun f)).Finite :=
    fun s => (jumpFun_finite hf).subset Set.inter_subset_right
  -- `∑ φ ∘ f = ∑ φ` over `(p, q)`, since `f` permutes `(p, q)`.
  have hbij : Set.BijOn f (Set.Ioo p q) (Set.Ioo p q) := by
    have := (f.injective.injOn (s := Set.Ioo p q)).bijOn_image
    rwa [f.image_Ioo, hp, hq] at this
  have hperm : ∑ᶠ y ∈ Set.Ioo p q, φ (f y) = ∑ᶠ y ∈ Set.Ioo p q, φ y :=
    finsum_mem_eq_of_bijOn f hbij (fun _ _ => rfl)
  have hsum : ∑ᶠ y ∈ Set.Ioo p q, φ (f y) =
      ∑ᶠ y ∈ Set.Ioo p q, jumpFun f y + ∑ᶠ y ∈ Set.Ioo p q, φ y := by
    rw [← finsum_mem_add_distrib' (hfinJ _) (hfinφ _)]
    exact finsum_mem_congr rfl (fun y _ => by rw [hrel y]; ring)
  unfold jsum
  rw [hperm] at hsum
  omega

/-! ### A maximal interval of moved points -/

theorem exists_component_pos (E : ℝ ≃o ℝ) (h0 : E 0 = 0) (h1 : E 1 = 1) {z0 : ℝ}
    (hz0 : 0 ≤ z0) (hz1 : z0 ≤ 1) (hlt : z0 < E z0) :
    ∃ p q : ℝ, 0 ≤ p ∧ p < q ∧ q ≤ 1 ∧ E p = p ∧ E q = q ∧
      ∀ z, p < z → z < q → z < E z := by
  have hc : Continuous E := E.continuous
  have hclosed : IsClosed {t : ℝ | E t ≤ t} := isClosed_le hc continuous_id
  have hclosed' : IsClosed {t : ℝ | t ≤ E t} := isClosed_le continuous_id hc
  -- the left end
  set S1 : Set ℝ := Set.Icc 0 z0 ∩ {t : ℝ | E t ≤ t} with hS1
  have hS1c : IsClosed S1 := isClosed_Icc.inter hclosed
  have hS1ne : S1.Nonempty := ⟨0, ⟨le_rfl, hz0⟩, by simp [h0]⟩
  have hS1b : BddAbove S1 := ⟨z0, fun t ht => ht.1.2⟩
  have hp : sSup S1 ∈ S1 := hS1c.csSup_mem hS1ne hS1b
  set p := sSup S1 with hpdef
  have hpz : p < z0 := by
    refine lt_of_le_of_ne hp.1.2 (fun he => ?_)
    have h2 : E p ≤ p := hp.2
    rw [he] at h2
    linarith
  have hR : ∀ z, p < z → z ≤ z0 → z < E z := by
    intro z hpz' hzz
    by_contra hle
    push Not at hle
    have hmem : z ∈ S1 := ⟨⟨le_trans hp.1.1 hpz'.le, hzz⟩, hle⟩
    have := le_csSup hS1b hmem
    linarith
  have hEp : E p = p := by
    apply le_antisymm hp.2
    have hsub : Set.Ioc p z0 ⊆ {t | t ≤ E t} := fun z hz => (hR z hz.1 hz.2).le
    have := closure_minimal hsub hclosed'
    rw [closure_Ioc hpz.ne] at this
    exact this ⟨le_rfl, hpz.le⟩
  -- the right end
  set S2 : Set ℝ := Set.Icc z0 1 ∩ {t : ℝ | E t ≤ t} with hS2
  have hS2c : IsClosed S2 := isClosed_Icc.inter hclosed
  have hS2ne : S2.Nonempty := ⟨1, ⟨hz1, le_rfl⟩, by simp [h1]⟩
  have hS2b : BddBelow S2 := ⟨z0, fun t ht => ht.1.1⟩
  have hq : sInf S2 ∈ S2 := hS2c.csInf_mem hS2ne hS2b
  set q := sInf S2 with hqdef
  have hzq : z0 < q := by
    refine lt_of_le_of_ne hq.1.1 (fun he => ?_)
    have h2 : E q ≤ q := hq.2
    rw [← he] at h2
    linarith
  have hL : ∀ z, z0 ≤ z → z < q → z < E z := by
    intro z hzz hzq'
    by_contra hle
    push Not at hle
    have hmem : z ∈ S2 := ⟨⟨hzz, le_trans hzq'.le hq.1.2⟩, hle⟩
    have := csInf_le hS2b hmem
    linarith
  have hEq : E q = q := by
    apply le_antisymm hq.2
    have hsub : Set.Ico z0 q ⊆ {t | t ≤ E t} := fun z hz => (hL z hz.1 hz.2).le
    have := closure_minimal hsub hclosed'
    rw [closure_Ico hzq.ne] at this
    exact this ⟨hzq.le, le_rfl⟩
  refine ⟨p, q, hp.1.1, by linarith, hq.1.2, hEp, hEq, fun z hz1' hz2' => ?_⟩
  rcases le_total z z0 with hz | hz
  · exact hR z hz1' hz
  · exact hL z hz hz2'

theorem exists_component (E : ℝ ≃o ℝ) (h0 : E 0 = 0) (h1 : E 1 = 1) {z0 : ℝ}
    (hz0 : 0 ≤ z0) (hz1 : z0 ≤ 1) (hne : E z0 ≠ z0) :
    ∃ p q : ℝ, 0 ≤ p ∧ p < q ∧ q ≤ 1 ∧ E p = p ∧ E q = q ∧
      ((∀ z, p < z → z < q → z < E z) ∨ (∀ z, p < z → z < q → E z < z)) := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- `E z0 < z0`: apply the positive case to `E.symm` at `E z0`
    have hs0 : E.symm 0 = 0 := by rw [E.symm_apply_eq, h0]
    have hs1 : E.symm 1 = 1 := by rw [E.symm_apply_eq, h1]
    have hw0 : 0 ≤ E z0 := by rw [← h0]; exact E.monotone hz0
    have hw1 : E z0 ≤ 1 := by rw [← h1]; exact E.monotone hz1
    have hw : E z0 < E.symm (E z0) := by rw [E.symm_apply_apply]; exact hlt
    obtain ⟨p, q, hp0, hpq, hq1, hEp, hEq, hR⟩ := exists_component_pos E.symm hs0 hs1 hw0 hw1 hw
    have hEp' : E p = p := by
      have := congrArg E hEp
      rwa [E.apply_symm_apply, eq_comm] at this
    have hEq' : E q = q := by
      have := congrArg E hEq
      rwa [E.apply_symm_apply, eq_comm] at this
    refine ⟨p, q, hp0, hpq, hq1, hEp', hEq', Or.inr fun z hpz hzq => ?_⟩
    have h1' : p < E z := by rw [← hEp']; exact E.strictMono hpz
    have h2' : E z < q := by rw [← hEq']; exact E.strictMono hzq
    have := hR (E z) h1' h2'
    rwa [E.symm_apply_apply] at this
  · obtain ⟨p, q, hp0, hpq, hq1, hEp, hEq, hR⟩ := exists_component_pos E h0 h1 hz0 hz1 hlt
    exact ⟨p, q, hp0, hpq, hq1, hEp, hEq, Or.inl hR⟩

/-! ### Fixing the endpoints -/

theorem apply_zero (f : UI ≃o UI) : (f ⟨0, zero_mem_UI⟩ : ℝ) = 0 := by
  apply le_antisymm _ (f _).2.1
  have hle : (⟨0, zero_mem_UI⟩ : UI) ≤ f.symm ⟨0, zero_mem_UI⟩ := (f.symm _).2.1
  have := f.monotone hle
  rw [f.apply_symm_apply] at this
  exact this

theorem apply_one (f : UI ≃o UI) : (f ⟨1, one_mem_UI⟩ : ℝ) = 1 := by
  apply le_antisymm (f _).2.2
  have hle : f.symm ⟨1, one_mem_UI⟩ ≤ (⟨1, one_mem_UI⟩ : UI) := (f.symm _).2.2
  have := f.monotone hle
  rw [f.apply_symm_apply] at this
  exact this

/-! ### Freeness -/

theorem cocycle_free (g : F) (φ : UI →₀ ℤ)
    (h : cocycle g + Finsupp.mapDomain (fun x => g • x) φ = φ) : g = 1 := by
  set f : UI ≃o UI := (g : UI ≃o UI) with hfdef
  have hf : f ∈ F := g.2
  by_contra hg1
  obtain ⟨z0, hz0⟩ : ∃ z0 : UI, f z0 ≠ z0 := by
    by_contra hall
    push Not at hall
    apply hg1
    apply Subtype.ext
    ext x
    rw [show (g : UI ≃o UI) x = x from hall x]
    simp
  set E : ℝ ≃o ℝ := extend f with hE
  have hEz : ∀ z : UI, E z = (f z : ℝ) := fun z => by
    simp only [E, extend_apply]
    exact extendFun_of_mem f z.2
  have hE0 : E 0 = 0 := by
    rw [show (0:ℝ) = ((⟨0, zero_mem_UI⟩ : UI) : ℝ) from rfl, hEz]; exact apply_zero f
  have hE1 : E 1 = 1 := by
    rw [show (1:ℝ) = ((⟨1, one_mem_UI⟩ : UI) : ℝ) from rfl, hEz]; exact apply_one f
  have hEne : E z0 ≠ z0 := by
    rw [hEz]; intro he; exact hz0 (Subtype.ext he)
  obtain ⟨p, q, hp0, hpq, hq1, hEp, hEq, hsign⟩ := exists_component E hE0 hE1 z0.2.1 z0.2.2 hEne
  set pU : UI := ⟨p, hp0, by linarith⟩ with hpU
  set qU : UI := ⟨q, by linarith, hq1⟩ with hqU
  have hfp : f pU = pU := Subtype.ext (by rw [← hEz]; exact hEp)
  have hfq : f qU = qU := Subtype.ext (by rw [← hEz]; exact hEq)
  -- the slope exponents at the two ends agree
  have hjs := jsum_eq_zero_of_cocycle g φ h hfp hfq
  rw [jsum_eq hf (show pU < qU from hpq)] at hjs
  have hn : lexp f qU = rexp f pU := by omega
  set n := rexp f pU with hndef
  obtain ⟨c, δ, hδ, hr⟩ := rexp_spec hf (show (pU:ℝ) < 1 by simp [pU]; linarith)
  obtain ⟨c', δ', hδ', hl⟩ := lexp_spec hf (show 0 < (qU:ℝ) by simp [qU]; linarith)
  rw [hn] at hl
  -- a point just right of `p` and a point just left of `q`
  set z1 : ℝ := p + min δ ((q - p) / 2) with hz1
  set z2 : ℝ := q - min δ' ((q - p) / 2) with hz2
  have hm1 : 0 < min δ ((q - p) / 2) := lt_min hδ (by linarith)
  have hm1' : min δ ((q - p) / 2) ≤ δ := min_le_left _ _
  have hm1'' : min δ ((q - p) / 2) ≤ (q - p) / 2 := min_le_right _ _
  have hm2 : 0 < min δ' ((q - p) / 2) := lt_min hδ' (by linarith)
  have hm2' : min δ' ((q - p) / 2) ≤ δ' := min_le_left _ _
  have hm2'' : min δ' ((q - p) / 2) ≤ (q - p) / 2 := min_le_right _ _
  have hz1I : z1 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hz2I : z2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have ep : (p:ℝ) = 2 ^ n * p + c := by
    have := hr pU le_rfl (by simp [pU]; linarith)
    rw [hfp] at this; exact this
  have eq' : (q:ℝ) = 2 ^ n * q + c' := by
    have := hl qU (by simp [qU]; linarith) le_rfl
    rw [hfq] at this; exact this
  have e1 : (f ⟨z1, hz1I⟩ : ℝ) = 2 ^ n * z1 + c :=
    hr ⟨z1, hz1I⟩ (by simp [pU]; linarith) (by simp [pU]; linarith)
  have e2 : (f ⟨z2, hz2I⟩ : ℝ) = 2 ^ n * z2 + c' :=
    hl ⟨z2, hz2I⟩ (by simp [qU]; linarith) (by simp [qU]; linarith)
  have d1 : E z1 - z1 = (2 ^ n - 1) * (z1 - p) := by
    rw [show z1 = ((⟨z1, hz1I⟩ : UI) : ℝ) from rfl, hEz]
    linear_combination e1 - ep
  have d2 : E z2 - z2 = (2 ^ n - 1) * (z2 - q) := by
    rw [show z2 = ((⟨z2, hz2I⟩ : UI) : ℝ) from rfl, hEz]
    linear_combination e2 - eq'
  have hu : 0 < z1 - p := by linarith
  have hv : z2 - q < 0 := by linarith
  have hz1pq : p < z1 ∧ z1 < q := ⟨by linarith, by linarith⟩
  have hz2pq : p < z2 ∧ z2 < q := ⟨by linarith, by linarith⟩
  rcases hsign with hpos | hneg
  · have k1 : 0 < (2 ^ n - 1) * (z1 - p) := by rw [← d1]; linarith [hpos z1 hz1pq.1 hz1pq.2]
    have k2 : 0 < (2 ^ n - 1) * (z2 - q) := by rw [← d2]; linarith [hpos z2 hz2pq.1 hz2pq.2]
    nlinarith [mul_pos k1 (neg_pos.2 hv), mul_pos k2 hu]
  · have k1 : (2 ^ n - 1) * (z1 - p) < 0 := by rw [← d1]; linarith [hneg z1 hz1pq.1 hz1pq.2]
    have k2 : (2 ^ n - 1) * (z2 - q) < 0 := by rw [← d2]; linarith [hneg z2 hz2pq.1 hz2pq.2]
    nlinarith [mul_pos_of_neg_of_neg k1 hv, mul_neg_of_neg_of_pos k2 hu]

end PartC2

alias cocycle_free := PartC2.cocycle_free

/-! ## Assembly -/


namespace PartZ
open scoped ENNReal Pointwise
open CannonFloydParry

/-- The linear part: `g · φ = mapDomain (g • ·) φ`. -/
noncomputable def lin (g : F) (φ : UI →₀ ℤ) : UI →₀ ℤ := Finsupp.mapDomain (fun x => g • x) φ

theorem lin_one (φ : UI →₀ ℤ) : lin 1 φ = φ := by
  simp only [lin, one_smul]
  exact Finsupp.mapDomain_id

theorem lin_mul (g h : F) (φ : UI →₀ ℤ) : lin (g * h) φ = lin g (lin h φ) := by
  simp only [lin]
  rw [← Finsupp.mapDomain_comp]
  congr 1

theorem lin_add (g : F) (φ ψ : UI →₀ ℤ) : lin g (φ + ψ) = lin g φ + lin g ψ :=
  Finsupp.mapDomain_add

theorem cocycle_one : cocycle (1 : F) = 0 := by
  have h := cocycle_mul (1 : F) 1
  have h2 : Finsupp.mapDomain (fun x => (1 : F) • x) (cocycle 1) = cocycle 1 := lin_one _
  rw [mul_one, h2] at h
  have := congrArg (fun φ => φ - cocycle (1 : F)) h
  simpa using this.symm

/-- The affine action `g ⋆ φ = cocycle g + g · φ`. -/
@[instance_reducible] noncomputable def affAction : MulAction F (UI →₀ ℤ) where
  smul g φ := cocycle g + lin g φ
  one_smul φ := by
    show cocycle 1 + lin 1 φ = φ
    rw [cocycle_one, lin_one, zero_add]
  mul_smul g h φ := by
    show cocycle (g * h) + lin (g * h) φ = cocycle g + lin g (cocycle h + lin h φ)
    rw [cocycle_mul, lin_mul, lin_add]
    simp only [lin]
    abel

theorem isAmenable_F_of_isExtensivelyAmenableOn
    (h : ThompsonAmenability.IsExtensivelyAmenableOn CannonFloydParry.F CannonFloydParry.UI
      {x : CannonFloydParry.UI | 0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ CannonFloydParry.IsDyadic x}) :
    Garrido.IsAmenable CannonFloydParry.F := by
  obtain ⟨μ, hμ, h1, hlin, htr⟩ := exists_affine_mean _ h
  let _ := affAction
  have hsmul : ∀ (g : F) (φ : UI →₀ ℤ), g • φ = cocycle g + lin g φ := fun _ _ => rfl
  refine isAmenable_of_free (G := F) (Y := UI →₀ ℤ) ?_ μ hμ h1 ?_
  · intro g φ hg
    rw [hsmul] at hg
    exact cocycle_free g φ hg
  · intro g S
    have hS : g • S = (cocycle g + ·) '' ((Finsupp.mapDomain (fun x => g • x)) '' S) := by
      ext φ
      simp only [Set.mem_smul_set, Set.mem_image, hsmul, lin]
      constructor
      · rintro ⟨ψ, hψ, rfl⟩; exact ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩; exact ⟨ψ, hψ, rfl⟩
    rw [hS, htr (cocycle g) (cocycle_support g)]
    exact hlin g S

end PartZ


end FAmenChild

open ThompsonAmenability in
theorem solution
    (h : IsExtensivelyAmenableOn CannonFloydParry.F CannonFloydParry.UI
      {x : CannonFloydParry.UI | 0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ CannonFloydParry.IsDyadic x}) :
    Garrido.IsAmenable CannonFloydParry.F :=
  FAmenChild.PartZ.isAmenable_F_of_isExtensivelyAmenableOn h
