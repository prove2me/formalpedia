-- Prove2me | solution 1 for ThompsonAmenability.isAmenable_of_isExtensivelyAmenableOn_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:14:54.838358+00:00
-- url     : https://prove2.me/submissions/86e0af1b-c583-4173-abd4-7057cd9dc237

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_ThompsonAmenability
import Theorems.Thm_Garrido_isAmenable_of_commGroup

section
/-!
# A JMMS-type criterion, generic in the lamp group

Parts A, B1, B2, B3 of the Chornyi child (`Solutions/FAmenChild`, assembled in
`f-amenability-mission/solutions/Sol_isAmenable_F_of_isExtensivelyAmenableOn.lean`), with the
lamp group `ℤ` replaced by an arbitrary additive commutative group `L`.

* (A) A free action with an invariant finitely additive probability makes the group amenable.
* (B) Extensive amenability of `G ↷ Y ⊆ X` gives a finitely additive probability on
  `Set (X →₀ L)` invariant under the linear action of `G` and under translations supported
  in `Y`.
-/

open scoped ENNReal Pointwise

namespace FAmenHZ.Lib

variable {L : Type*} [AddCommGroup L]

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

open FAmenHZ.Lib

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

/-! ## Part B2: symmetric translation-invariant means on finitely supported `L`-functions -/


namespace PartB2
open scoped ENNReal Pointwise

/-- Right composition with a permutation is injective. -/
lemma comp_perm_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun w : Fin n → L => w ∘ σ) := by
  intro a b h
  funext i
  have := congrFun h (σ.symm i)
  simpa using this

/-- Right composition with a permutation is surjective. -/
lemma comp_perm_surjective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Surjective (fun w : Fin n → L => w ∘ σ) := by
  intro w
  exact ⟨w ∘ σ.symm, by funext i; simp⟩

theorem exists_symMean (n : ℕ) : ∃ μ : Set (Fin n → L) → ℝ≥0∞,
    Garrido.IsFinitelyAdditiveMeasure μ ∧ μ Set.univ = 1 ∧
    (∀ (v : Fin n → L) (S : Set (Fin n → L)), μ ((v + ·) '' S) = μ S) ∧
    (∀ (σ : Equiv.Perm (Fin n)) (S : Set (Fin n → L)), μ ((fun w => w ∘ σ) '' S) = μ S) := by
  obtain ⟨m, hm, h1, hinv⟩ := Garrido.isAmenable_of_commGroup (Multiplicative (Fin n → L))
  -- transport to `Fin n → L`
  set m' : Set (Fin n → L) → ℝ≥0∞ := fun S => m (Multiplicative.toAdd ⁻¹' S) with hm'def
  have hm'0 : m' ∅ = 0 := by simp [hm'def, hm.1]
  have hm'add : ∀ s t : Set (Fin n → L), Disjoint s t → m' (s ∪ t) = m' s + m' t := by
    intro s t hst
    simp only [hm'def, Set.preimage_union]
    exact hm.2 _ _ (hst.preimage _)
  have hm'1 : m' Set.univ = 1 := by simp [hm'def, h1]
  have hm'tr : ∀ (v : Fin n → L) (S : Set (Fin n → L)), m' ((v + ·) '' S) = m' S := by
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
    have : (fun w : Fin n → L => w ∘ σ) '' ((v + ·) '' S) =
        ((v ∘ σ) + ·) '' ((fun w : Fin n → L => w ∘ σ) '' S) := by
      simp only [Set.image_image]
      rfl
    rw [this, hm'tr]
  · intro τ S
    simp only
    congr 1
    have : ∀ σ : Equiv.Perm (Fin n), (fun w : Fin n → L => w ∘ σ) '' ((fun w => w ∘ τ) '' S) =
        (fun w : Fin n → L => w ∘ (Equiv.mulLeft τ σ)) '' S := by
      intro σ
      simp only [Set.image_image, Equiv.coe_mulLeft, Equiv.Perm.coe_mul]
      rfl
    simp only [this]
    exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => m' ((fun w : Fin n → L => w ∘ σ) '' S))
end PartB2

alias exists_symMean := PartB2.exists_symMean

variable (L) in
noncomputable def symMean (n : ℕ) : Set (Fin n → L) → ℝ≥0∞ := (exists_symMean n).choose

/-- The finitely supported function on `X` that is `w` on `A` (through `A.equivFin`) and `0`
off `A`. -/
noncomputable def extendFin {X : Type*} (A : Finset X) (w : Fin A.card → L) : X →₀ L :=
  Finsupp.onFinset A (fun x => open Classical in if h : x ∈ A then w (A.equivFin ⟨x, h⟩) else 0)
    (by intro x hx; by_contra h; simp [h] at hx)

/-- The mean on `X →₀ L` carried by the finite set `A`. -/
noncomputable def meanOn {X : Type*} (A : Finset X) (S : Set (X →₀ L)) : ℝ≥0∞ :=
  symMean L A.card {w | extendFin A w ∈ S}


namespace PartB2
open scoped ENNReal Pointwise
section B2
variable {X : Type*}

variable (L) in
lemma symMean_spec (n : ℕ) :
    Garrido.IsFinitelyAdditiveMeasure (symMean L n) ∧ symMean L n Set.univ = 1 ∧
    (∀ (v : Fin n → L) (S : Set (Fin n → L)), symMean L n ((v + ·) '' S) = symMean L n S) ∧
    (∀ (σ : Equiv.Perm (Fin n)) (S : Set (Fin n → L)),
      symMean L n ((fun w => w ∘ σ) '' S) = symMean L n S) :=
  (FAmenHZ.Lib.exists_symMean n).choose_spec

lemma meanOn_eq (A : Finset X) (S : Set (X →₀ L)) :
    meanOn A S = symMean L A.card (extendFin A ⁻¹' S) := rfl

lemma extendFin_apply (A : Finset X) (w : Fin A.card → L) (x : X) :
    extendFin A w x = open Classical in if h : x ∈ A then w (A.equivFin ⟨x, h⟩) else 0 := by
  simp [extendFin, Finsupp.onFinset_apply]

lemma extendFin_add (A : Finset X) (u v : Fin A.card → L) :
    extendFin A (u + v) = extendFin A u + extendFin A v := by
  ext x
  simp only [extendFin_apply, Finsupp.coe_add, Pi.add_apply]
  split_ifs <;> simp

lemma extendFin_neg (A : Finset X) (u : Fin A.card → L) :
    extendFin A (-u) = -extendFin A u := by
  ext x
  simp only [extendFin_apply, Finsupp.coe_neg, Pi.neg_apply]
  split_ifs <;> simp

lemma extendFin_restrict (A : Finset X) (w : X →₀ L) (hw : (↑w.support : Set X) ⊆ ↑A) :
    extendFin A (fun i => w (A.equivFin.symm i)) = w := by
  ext x
  rw [extendFin_apply]
  split_ifs with h
  · simp
  · have : x ∉ w.support := fun hx => h (hw hx)
    simp only [Finsupp.mem_support_iff, not_not] at this
    exact this.symm

/-- Right composition with an equivalence, as a preimage, symmetrises away. -/
lemma symMean_preimage_comp (k l : ℕ) (τ : Fin k ≃ Fin l) (T : Set (Fin k → L)) :
    symMean L l ((fun w : Fin l → L => w ∘ τ) ⁻¹' T) = symMean L k T := by
  obtain rfl : k = l := by simpa using Fintype.card_congr τ
  have : (fun w : Fin k → L => w ∘ τ) ⁻¹' T = (fun w : Fin k → L => w ∘ τ.symm) '' T := by
    ext w
    constructor
    · intro h
      exact ⟨w ∘ τ, h, by funext i; simp⟩
    · rintro ⟨u, hu, rfl⟩
      simpa [Set.mem_preimage, Function.comp_def] using hu
  rw [this]
  exact (symMean_spec L k).2.2.2 τ.symm T

variable (L) in
theorem meanOn_isFinitelyAdditiveMeasure (A : Finset X) :
    Garrido.IsFinitelyAdditiveMeasure (meanOn (L := L) A) ∧ meanOn (L := L) A Set.univ = 1 := by
  obtain ⟨⟨h0, hadd⟩, h1, -, -⟩ := symMean_spec L A.card
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [meanOn_eq] using h0
  · intro s t hst
    simp only [meanOn_eq, Set.preimage_union]
    exact hadd _ _ (hst.preimage _)
  · simpa [meanOn_eq] using h1

theorem meanOn_add (A : Finset X) (w : X →₀ L) (hw : (↑w.support : Set X) ⊆ ↑A)
    (S : Set (X →₀ L)) : meanOn A ((w + ·) '' S) = meanOn A S := by
  set w₀ : Fin A.card → L := fun i => w (A.equivFin.symm i) with hw₀
  have hext : extendFin A w₀ = w := extendFin_restrict A w hw
  have key : extendFin A ⁻¹' ((w + ·) '' S) = (w₀ + ·) '' (extendFin A ⁻¹' S) := by
    rw [Set.image_add_left, Set.image_add_left, ← Set.preimage_comp, ← Set.preimage_comp]
    congr 1
    funext u
    simp only [Function.comp_apply]
    rw [extendFin_add, extendFin_neg, hext]
  rw [meanOn_eq, meanOn_eq, key]
  exact (symMean_spec L A.card).2.2.1 w₀ _

theorem meanOn_perm (σ : Equiv.Perm X) (A : Finset X) (S : Set (X →₀ L)) :
    meanOn (A.map σ.toEmbedding) ((Finsupp.mapDomain σ) '' S) = meanOn A S := by
  set B := A.map σ.toEmbedding with hB
  have hmem : ∀ x, x ∈ A ↔ σ x ∈ B := fun x => by
    simp [hB]
  let e : A ≃ B := σ.subtypeEquiv hmem
  let τ : Fin A.card ≃ Fin B.card := A.equivFin.symm.trans (e.trans B.equivFin)
  have hτ : ∀ x (h : x ∈ A), τ (A.equivFin ⟨x, h⟩) = B.equivFin ⟨σ x, (hmem x).1 h⟩ := by
    intro x h
    simp [τ, e]
  have hid : ∀ w : Fin B.card → L,
      extendFin B w = Finsupp.mapDomain σ (extendFin A (w ∘ τ)) := by
    intro w
    ext y
    obtain ⟨x, rfl⟩ := σ.surjective y
    rw [Finsupp.mapDomain_apply σ.injective, extendFin_apply, extendFin_apply]
    by_cases h : x ∈ A
    · rw [dif_pos h, dif_pos ((hmem x).1 h), Function.comp_apply, hτ x h]
    · rw [dif_neg h, dif_neg (fun h' => h ((hmem x).2 h'))]
  have key : extendFin B ⁻¹' ((Finsupp.mapDomain σ) '' S) =
      (fun w : Fin B.card → L => w ∘ τ) ⁻¹' (extendFin A ⁻¹' S) := by
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

/-! ## Part B3: the mean on `X →₀ L` from extensive amenability -/


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

lemma meanOn_le_one {X : Type*} (A : Finset X) (S : Set (X →₀ L)) : meanOn A S ≤ 1 :=
  fam_le_one (meanOn_isFinitelyAdditiveMeasure L A).1 (meanOn_isFinitelyAdditiveMeasure L A).2 S

lemma meanOn_ne_top {X : Type*} (A : Finset X) (S : Set (X →₀ L)) : meanOn A S ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (meanOn_le_one A S)

theorem exists_affine_mean {G X : Type*} [Group G] [MulAction G X] (Y : Set X)
    (h : ThompsonAmenability.IsExtensivelyAmenableOn G X Y) :
    ∃ μ : Set (X →₀ L) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure μ ∧ μ Set.univ = 1 ∧
      (∀ (g : G) (S : Set (X →₀ L)), μ ((Finsupp.mapDomain (fun x => g • x)) '' S) = μ S) ∧
      (∀ w : X →₀ L, (↑w.support : Set X) ⊆ Y → ∀ S, μ ((w + ·) '' S) = μ S) := by
  obtain ⟨m, hm, -, h1, hinv, hfull⟩ := h
  refine ⟨fun S => ENNReal.ofReal (integ m (fun A => (meanOn A S).toReal)), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- `μ ∅ = 0`
    have h0 : (fun A : Finset X => (meanOn A (∅ : Set (X →₀ L))).toReal)
        = (∅ : Set (Finset X)).indicator 1 := by
      funext A
      rw [(meanOn_isFinitelyAdditiveMeasure L A).1.1, Set.indicator_empty]
      rfl
    simp only
    rw [h0, integ_indicator hm h1, hm.1]
    simp
  · -- finite additivity
    intro s t hst
    have hadd : ∀ A : Finset X, meanOn A (s ∪ t) = meanOn A s + meanOn A t :=
      fun A => (meanOn_isFinitelyAdditiveMeasure L A).1.2 s t hst
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
    have hu : (fun A : Finset X => (meanOn A (Set.univ : Set (X →₀ L))).toReal)
        = (Set.univ : Set (Finset X)).indicator 1 := by
      funext A
      rw [(meanOn_isFinitelyAdditiveMeasure L A).2, Set.indicator_univ]
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

end FAmenHZ.Lib
end

section
/-!
# A JMMS-type amenability criterion

`G ↷ X`, a lamp group `L` (any additive commutative group), and a cocycle
`c : G → (X →₀ L)`, `c (g h) = c g + g · c h`, with all supports in `Y ⊆ X`. If the affine action
`g ⋆ φ = c g + g · φ` is free and `G ↷ Y` is extensively amenable, then `G` is amenable.
(Juschenko–Matte Bon–Monod–de la Salle, arXiv:1503.04977, Corollary 1.4 and Remark 1.5, in the
case of the functor `X ↦ L^(X)`.) Also: adjoining a `G`-fixed point to `Y` keeps extensive
amenability.
-/

open scoped ENNReal Pointwise

namespace FAmenHZ

open FAmenHZ.Lib

section Criterion

variable {G X L : Type*} [Group G] [MulAction G X] [AddCommGroup L]

/-- The linear part `g · φ = mapDomain (g • ·) φ`. -/
noncomputable def lin (g : G) (φ : X →₀ L) : X →₀ L := Finsupp.mapDomain (fun x => g • x) φ

theorem lin_one (φ : X →₀ L) : lin (1 : G) φ = φ := by
  simp only [lin, one_smul]
  exact Finsupp.mapDomain_id

theorem lin_mul (g h : G) (φ : X →₀ L) : lin (g * h) φ = lin g (lin h φ) := by
  simp only [lin]
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext x
  simp [mul_smul]

theorem lin_add (g : G) (φ ψ : X →₀ L) : lin g (φ + ψ) = lin g φ + lin g ψ :=
  Finsupp.mapDomain_add

theorem cocycle_one_eq_zero (c : G → X →₀ L) (hmul : ∀ g h, c (g * h) = c g + lin g (c h)) :
    c 1 = 0 := by
  have h := hmul 1 1
  rw [mul_one, lin_one] at h
  have := congrArg (fun φ => φ - c 1) h
  simpa using this.symm

/-- The affine action `g ⋆ φ = c g + g · φ`. -/
@[instance_reducible] noncomputable def affAction (c : G → X →₀ L)
    (hmul : ∀ g h, c (g * h) = c g + lin g (c h)) : MulAction G (X →₀ L) where
  smul g φ := c g + lin g φ
  one_smul φ := by
    show c 1 + lin 1 φ = φ
    rw [cocycle_one_eq_zero c hmul, lin_one, zero_add]
  mul_smul g h φ := by
    show c (g * h) + lin (g * h) φ = c g + lin g (c h + lin h φ)
    rw [hmul, lin_mul, lin_add]
    abel

/-- **The criterion.** -/
theorem isAmenable_of_cocycle (Y : Set X) (c : G → X →₀ L)
    (hsupp : ∀ g, (↑(c g).support : Set X) ⊆ Y)
    (hmul : ∀ g h, c (g * h) = c g + Finsupp.mapDomain (fun x => g • x) (c h))
    (hfree : ∀ (g : G) (φ : X →₀ L), c g + Finsupp.mapDomain (fun x => g • x) φ = φ → g = 1)
    (hY : ThompsonAmenability.IsExtensivelyAmenableOn G X Y) : Garrido.IsAmenable G := by
  have hmul' : ∀ g h, c (g * h) = c g + lin g (c h) := hmul
  obtain ⟨μ, hμ, h1, hlin, htr⟩ := exists_affine_mean (L := L) Y hY
  let _ := affAction c hmul'
  have hsmul : ∀ (g : G) (φ : X →₀ L), g • φ = c g + lin g φ := fun _ _ => rfl
  refine isAmenable_of_free (G := G) (Y := X →₀ L) ?_ μ hμ h1 ?_
  · intro g φ hg
    rw [hsmul] at hg
    exact hfree g φ hg
  · intro g S
    have hS : g • S = (c g + ·) '' ((Finsupp.mapDomain (fun x => g • x)) '' S) := by
      ext φ
      simp only [Set.mem_smul_set, Set.mem_image, hsmul, lin]
      constructor
      · rintro ⟨ψ, hψ, rfl⟩; exact ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩; exact ⟨ψ, hψ, rfl⟩
    rw [hS, htr (c g) (hsupp g)]
    exact hlin g S

end Criterion



end FAmenHZ
end

section
/-! `chk_isAmenable_of_isExtensivelyAmenableOn_of_cocycle`: the prove2.me statement `ThompsonAmenability.isAmenable_of_isExtensivelyAmenableOn_of_cocycle`, copied verbatim and renamed, proved by `FAmenHZ.isAmenable_of_cocycle`. -/

namespace ThompsonAmenability

end ThompsonAmenability
end

section
open ThompsonAmenability
theorem solution {G X L : Type*} [Group G] [MulAction G X]
    [AddCommGroup L] (Y : Set X) (c : G → X →₀ L)
    (hsupp : ∀ g, (↑(c g).support : Set X) ⊆ Y)
    (hmul : ∀ g h, c (g * h) = c g + Finsupp.mapDomain (fun x => g • x) (c h))
    (hfree : ∀ (g : G) (φ : X →₀ L), c g + Finsupp.mapDomain (fun x => g • x) φ = φ → g = 1)
    (hY : IsExtensivelyAmenableOn G X Y) : Garrido.IsAmenable G := by
  exact FAmenHZ.isAmenable_of_cocycle Y c hsupp hmul hfree hY
end
