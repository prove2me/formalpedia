-- Prove2me | solution 1 for RestrictedAP.Counting.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:44:37.8802+00:00
-- url     : https://prove2.me/submissions/7cbbd8a4-c529-49ca-8649-1f2e0facec0c

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions

section
set_option autoImplicit false

/-!
# Basic facts about normalized product functions (shared by Lemmas 3.2–3.4)

* F1: `component` of a normalized product function is its factor; norm one, nonzero.
* F2: `proj σs K P` is a normalized product function with components
  `if i ∈ K then component σs P i else 1`.
* F3: powers: `P ^ N = 1 → (proj σs K P) ^ N = 1`; `orderOf (proj σs K P) ∣ orderOf P`.
* F4: rigidity of product decompositions over a nonempty alphabet, and the extraction of a
  small exceptional set from `symbolicDist F 1 < D`.
-/

namespace RestrictedAP.Counting.Dev.ProdBasics
open RestrictedAP.Counting

/-! ## F4: rigidity -/

/-- Evaluating a product decomposition at `s` updated in coordinate `i`. -/
theorem prod_update_eq {α : Type*} {n : ℕ} (w : Fin n → α → ℂ) (s : Fin n → α) (i : Fin n)
    (a : α) :
    ∏ j, w j (Function.update s i a j) = w i a * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), w j (s j) := by
  rw [Fintype.prod_eq_mul_prod_compl i]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ i := by simpa using hj
    simp [Function.update_of_ne this]

theorem prod_compl_ne_zero {α : Type*} {n : ℕ} (w : Fin n → α → ℂ) (hw : ∀ i a, w i a ≠ 0)
    (s : Fin n → α) (i : Fin n) : ∏ j ∈ ({i}ᶜ : Finset (Fin n)), w j (s j) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => hw j (s j)

/-- F4(a): if `∏ w i (t i)` is constant (with `w` nonzero) then every factor is constant. -/
theorem rigid_const {α : Type*} [Nonempty α] {n : ℕ} (w : Fin n → α → ℂ)
    (hw : ∀ i a, w i a ≠ 0) (c : ℂ) (h : ∀ t : Fin n → α, ∏ i, w i (t i) = c)
    (i : Fin n) (a b : α) : w i a = w i b := by
  classical
  obtain ⟨s0⟩ := (inferInstance : Nonempty α)
  let s : Fin n → α := fun _ => s0
  have ha := h (Function.update s i a)
  have hb := h (Function.update s i b)
  rw [prod_update_eq] at ha hb
  exact mul_right_cancel₀ (prod_compl_ne_zero w hw s i) (ha.trans hb.symm)

/-! ## F1: components -/

variable {Sig : Type*} [DecidableEq Sig] {n : ℕ}

theorem component_eq_factor (σs : Sig) (P : (Fin n → Sig) → ℂ) (u : Fin n → Sig → ℂ)
    (hu1 : ∀ i, u i σs = 1) (hP : ∀ x, P x = ∏ i, u i (x i)) (i : Fin n) (a : Sig) :
    component σs P i a = u i a := by
  unfold component
  rw [hP, prod_update_eq]
  simp [hu1]

theorem component_norm (σs : Sig) (P : (Fin n → Sig) → ℂ) (hP : IsProductFunction σs P)
    (i : Fin n) (a : Sig) : ‖component σs P i a‖ = 1 := by
  obtain ⟨u, hu, hu1, hPu⟩ := hP
  rw [component_eq_factor σs P u hu1 hPu]; exact hu i a

theorem component_self (σs : Sig) (P : (Fin n → Sig) → ℂ) (hP : IsProductFunction σs P)
    (i : Fin n) : component σs P i σs = 1 := by
  obtain ⟨u, hu, hu1, hPu⟩ := hP
  rw [component_eq_factor σs P u hu1 hPu]; exact hu1 i

/-- F1: a normalized product function is the product of its components. -/
theorem eq_prod_component (σs : Sig) (P : (Fin n → Sig) → ℂ) (hP : IsProductFunction σs P)
    (x : Fin n → Sig) : P x = ∏ i, component σs P i (x i) := by
  obtain ⟨u, hu, hu1, hPu⟩ := hP
  rw [hPu]
  exact Finset.prod_congr rfl fun i _ => (component_eq_factor σs P u hu1 hPu i (x i)).symm

theorem norm_eq_one (σs : Sig) (P : (Fin n → Sig) → ℂ) (hP : IsProductFunction σs P)
    (x : Fin n → Sig) : ‖P x‖ = 1 := by
  rw [eq_prod_component σs P hP x, norm_prod]
  exact Finset.prod_eq_one fun i _ => component_norm σs P hP i (x i)

/-! ## F2: projections -/

theorem proj_apply (σs : Sig) (K : Finset (Fin n)) (P : (Fin n → Sig) → ℂ) (x : Fin n → Sig) :
    proj σs K P x = ∏ i, (if i ∈ K then component σs P i (x i) else 1) := by
  classical
  unfold proj
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-! ## F3: powers and orders -/

theorem pow_apply_eq_one {α : Type*} (P : α → ℂ) (N : ℕ) (h : P ^ N = 1) (x : α) :
    P x ^ N = 1 := by
  have := congrFun h x; simpa using this

theorem component_pow (σs : Sig) (P : (Fin n → Sig) → ℂ) (N : ℕ) (h : P ^ N = 1) (i : Fin n)
    (a : Sig) : component σs P i a ^ N = 1 :=
  pow_apply_eq_one P N h _

theorem component_pow_orderOf (σs : Sig) (P : (Fin n → Sig) → ℂ) (i : Fin n) (a : Sig) :
    component σs P i a ^ orderOf P = 1 :=
  component_pow σs P _ (pow_orderOf_eq_one P) i a

end RestrictedAP.Counting.Dev.ProdBasics
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RestrictedAP.Counting.Dev.L33
open RestrictedAP.Counting RestrictedAP.Counting.Dev.ProdBasics
open Classical

variable {Sig : Type} [Fintype Sig] [DecidableEq Sig] {n : ℕ}

/-- The lift along coordinate `s` of `Sig³`: `lift1/2/3` for `s = 0, 1, 2`. -/
def Lg (μ : Sig × Sig × Sig → ℝ) (s : Fin 3) (P : (Fin n → Sig) → ℂ) :
    (Fin n → {t // μ t ≠ 0}) → ℂ :=
  fun t => P (fun i => coord3 s (t i).1)

theorem lift1_eq (μ : Sig × Sig × Sig → ℝ) (P : (Fin n → Sig) → ℂ) : lift1 μ P = Lg μ 0 P := by
  funext t; simp [lift1, Lg, coord3]

theorem lift2_eq (μ : Sig × Sig × Sig → ℝ) (P : (Fin n → Sig) → ℂ) : lift2 μ P = Lg μ 1 P := by
  funext t; simp [lift2, Lg, coord3]

theorem lift3_eq (μ : Sig × Sig × Sig → ℝ) (P : (Fin n → Sig) → ℂ) : lift3 μ P = Lg μ 2 P := by
  funext t; simp [lift3, Lg, coord3]

/-- The joint lift of a projected collection, as an image of `PP × Fin 3`. -/
theorem jointLift_eq (μ : Sig × Sig × Sig → ℝ) (σs : Sig) (K : Finset (Fin n))
    (PP : Finset ((Fin n → Sig) → ℂ)) :
    jointLift μ (projColl σs K PP) (projColl σs K PP) (projColl σs K PP) =
      (Finset.univ : Finset (PP × Fin 3)).image (fun x => Lg μ x.2 (proj σs K x.1.1)) := by
  ext f
  simp only [jointLift, projColl, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists, Subtype.exists]
  constructor
  · rintro ((⟨Q, ⟨P, hP, rfl⟩, rfl⟩ | ⟨Q, ⟨P, hP, rfl⟩, rfl⟩) | ⟨Q, ⟨P, hP, rfl⟩, rfl⟩)
    · exact ⟨P, hP, 0, (lift1_eq μ _).symm⟩
    · exact ⟨P, hP, 1, (lift2_eq μ _).symm⟩
    · exact ⟨P, hP, 2, (lift3_eq μ _).symm⟩
  · rintro ⟨P, hP, s, rfl⟩
    fin_cases s
    · exact Or.inl (Or.inl ⟨_, ⟨P, hP, rfl⟩, lift1_eq μ _⟩)
    · exact Or.inl (Or.inr ⟨_, ⟨P, hP, rfl⟩, lift2_eq μ _⟩)
    · exact Or.inr ⟨_, ⟨P, hP, rfl⟩, lift3_eq μ _⟩

/-- The natural `i`-th factor of `F_K(e)`. -/
noncomputable def W (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ)) (e : PP × Fin 3 → ℕ)
    (i : Fin n) (a : Sig × Sig × Sig) : ℂ :=
  ∏ x : PP × Fin 3, (component σs x.1.1 i (coord3 x.2 a)) ^ (e x)

theorem prod_Lg_proj (μ : Sig × Sig × Sig → ℝ) (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (K : Finset (Fin n)) (e : PP × Fin 3 → ℕ) (t : Fin n → {t // μ t ≠ 0}) :
    ∏ x : PP × Fin 3, (Lg μ x.2 (proj σs K x.1.1) t) ^ (e x) = ∏ i ∈ K, W σs PP e i (t i).1 := by
  simp only [Lg, proj, W, ← Finset.prod_pow]
  exact Finset.prod_comm

theorem W_norm (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P) (e : PP × Fin 3 → ℕ) (i : Fin n)
    (a : Sig × Sig × Sig) : ‖W σs PP e i a‖ = 1 := by
  unfold W
  rw [norm_prod]
  refine Finset.prod_eq_one fun x _ => ?_
  rw [norm_pow, component_norm σs _ (hPP _ x.1.2), one_pow]

/-- `e` has a constant `i`-th factor on the support of `μ`. -/
def good (μ : Sig × Sig × Sig → ℝ) (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (e : PP × Fin 3 → ℕ) (i : Fin n) : Prop :=
  ∀ a b : {t // μ t ≠ 0}, W σs PP e i a.1 = W σs PP e i b.1

/-- Reduced exponent vectors. -/
noncomputable def E (PP : Finset ((Fin n → Sig) → ℂ)) : Finset (PP × Fin 3 → ℕ) :=
  Fintype.piFinset (fun x : PP × Fin 3 => Finset.range (orderOf x.1.1))

end RestrictedAP.Counting.Dev.L33

namespace RestrictedAP.Counting

end RestrictedAP.Counting
end

section
set_option autoImplicit false

/-!
# Roots of unity: indicator expansion and the single-coordinate bias bound

* `ind_eq_geom`: for `z ^ N = 1`, `[z = 1] = (1/N) ∑_{k<N} z^k`.
* `norm_one_add_lt_two`, `exists_gap`: distinct `L`-th roots of unity are uniformly far from
  antipodal-free collapse: `‖1 + ζ‖ ≤ 2 - δ_L` for `ζ ^ L = 1`, `ζ ≠ 1`.
* `norm_add_le_gap`: the same for `‖u + v‖` with `u ≠ v` norm-one, `(v/u)^L = 1`.
* `bias_le`, `exists_bias`: a function with `L`-th-root-of-unity values on the support of `μ`
  (atoms `≥ α`) that is non-constant on the support has `‖E_μ w‖ ≤ 1 - γ(L, α)`.
-/

namespace RestrictedAP.Counting.Dev.Fourier
open RestrictedAP.Counting

/-- Indicator of `z = 1` as a geometric mean of powers, for an `N`-th root of unity `z`. -/
theorem ind_eq_geom (z : ℂ) (N : ℕ) (hN : 0 < N) (hz : z ^ N = 1) :
    (if z = 1 then (1 : ℂ) else 0) = (1 / (N : ℂ)) * ∑ k ∈ Finset.range N, z ^ k := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  split_ifs with h
  · subst h; simp [hN']
  · rw [geom_sum_eq h, hz]; simp

/-- Indicator of `a = b` for two `N`-th roots of unity, `b ≠ 0`. -/
theorem ind_eq_geom' (a b : ℂ) (N : ℕ) (hN : 0 < N) (ha : a ^ N = 1) (hb : b ^ N = 1) :
    (if a = b then (1 : ℂ) else 0) = (1 / (N : ℂ)) * ∑ k ∈ Finset.range N, (a / b) ^ k := by
  have hb0 : b ≠ 0 := by
    rintro rfl; rw [zero_pow hN.ne'] at hb; exact zero_ne_one hb
  rw [← ind_eq_geom (a / b) N hN (by rw [div_pow, ha, hb, div_one])]
  congr 1
  exact propext ⟨fun h => by rw [h, div_self hb0], fun h => by
    rw [div_eq_one_iff_eq hb0] at h; exact h⟩

/-- A norm-one complex number other than `1` has `‖1 + ζ‖ < 2`. -/
theorem norm_one_add_lt_two (ζ : ℂ) (h1 : ‖ζ‖ = 1) (hne : ζ ≠ 1) : ‖1 + ζ‖ < 2 := by
  have hsq : ‖ζ‖ ^ 2 = 1 := by rw [h1]; norm_num
  rw [Complex.sq_norm, Complex.normSq_apply] at hsq
  by_contra hge
  push Not at hge
  have h4 : (4 : ℝ) ≤ ‖1 + ζ‖ ^ 2 := by nlinarith
  rw [Complex.sq_norm, Complex.normSq_apply] at h4
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add] at h4
  have hre : ζ.re = 1 := by nlinarith
  have him : ζ.im = 0 := by nlinarith
  exact hne (Complex.ext (by simp [hre]) (by simp [him]))

/-- Uniform gap: there is `δ > 0` with `‖1 + ζ‖ ≤ 2 - δ` for every `L`-th root of unity `ζ ≠ 1`. -/
theorem exists_gap (L : ℕ) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ζ : ℂ, ζ ^ L = 1 → ζ ≠ 1 → ‖1 + ζ‖ ≤ 2 - δ := by
  classical
  set T := (Polynomial.nthRootsFinset L (1 : ℂ)).filter (fun ζ => ζ ≠ 1)
  by_cases hT : T.Nonempty
  · obtain ⟨ζ0, hζ0, hmin⟩ := Finset.exists_min_image T (fun ζ => 2 - ‖1 + ζ‖) hT
    have hmem : ∀ ζ, ζ ∈ T ↔ ζ ^ L = 1 ∧ ζ ≠ 1 := by
      intro ζ; simp [T, Polynomial.mem_nthRootsFinset hL]
    obtain ⟨h0L, h01⟩ := (hmem ζ0).1 hζ0
    refine ⟨2 - ‖1 + ζ0‖, ?_, fun ζ hζL hζ1 => ?_⟩
    · have := norm_one_add_lt_two ζ0 (Complex.norm_eq_one_of_pow_eq_one h0L hL.ne') h01
      linarith
    · have := hmin ζ ((hmem ζ).2 ⟨hζL, hζ1⟩)
      linarith
  · refine ⟨1, one_pos, fun ζ hζL hζ1 => ?_⟩
    exact absurd ⟨ζ, by simp [T, Polynomial.mem_nthRootsFinset hL, hζL, hζ1]⟩ hT

/-- Two distinct norm-one numbers whose ratio is an `L`-th root of unity: `‖u + v‖ ≤ 2 - δ`. -/
theorem norm_add_le_gap (L : ℕ) (δ : ℝ)
    (hgap : ∀ ζ : ℂ, ζ ^ L = 1 → ζ ≠ 1 → ‖1 + ζ‖ ≤ 2 - δ) (u v : ℂ) (hu : ‖u‖ = 1)
    (hu' : u ^ L = 1) (hv' : v ^ L = 1) (hne : u ≠ v) : ‖u + v‖ ≤ 2 - δ := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have h1 : u + v = u * (1 + v / u) := by field_simp
  rw [h1, norm_mul, hu, one_mul]
  refine hgap _ (by rw [div_pow, hu', hv', div_one]) ?_
  intro h; rw [div_eq_one_iff_eq hu0] at h; exact hne h.symm

/-- The bias bound with an explicit gap `δ`. -/
theorem bias_le {Ω : Type*} [Fintype Ω] (L : ℕ) (hL : 0 < L) (δ α : ℝ)
    (hαpos : 0 ≤ α)
    (hgap : ∀ ζ : ℂ, ζ ^ L = 1 → ζ ≠ 1 → ‖1 + ζ‖ ≤ 2 - δ)
    (μ : Ω → ℝ) (w : Ω → ℂ) (hμ : IsDist μ) (hα : AtomsAtLeast μ α)
    (hw1 : ∀ a, ‖w a‖ ≤ 1) (hwL : ∀ a, μ a ≠ 0 → w a ^ L = 1)
    (a b : Ω) (ha : μ a ≠ 0) (hb : μ b ≠ 0) (hab : w a ≠ w b) :
    ‖∑ x, (μ x : ℂ) * w x‖ ≤ 1 - α * δ := by
  classical
  have hneab : a ≠ b := fun h => hab (h ▸ rfl)
  set ν : Ω → ℝ := fun x => μ x - (if x = a then α else 0) - (if x = b then α else 0) with hν
  have hνnn : ∀ x, 0 ≤ ν x := by
    intro x
    simp only [hν]
    by_cases hxa : x = a
    · subst hxa; rw [if_pos rfl, if_neg hneab]; linarith [hα x ha]
    · by_cases hxb : x = b
      · subst hxb; rw [if_neg hxa, if_pos rfl]; linarith [hα x hb]
      · rw [if_neg hxa, if_neg hxb]; linarith [hμ.1 x]
  have hsum : ∑ x, (μ x : ℂ) * w x = (α : ℂ) * (w a + w b) + ∑ x, (ν x : ℂ) * w x := by
    have : ∀ x, (μ x : ℂ) * w x = (ν x : ℂ) * w x + ((if x = a then (α : ℂ) * w x else 0) +
        (if x = b then (α : ℂ) * w x else 0)) := by
      intro x
      by_cases hxa : x = a
      · subst hxa; simp only [hν, if_neg hneab]; push_cast; ring
      · by_cases hxb : x = b
        · subst hxb; simp only [hν, if_neg hxa]; push_cast; ring
        · simp only [hν, if_neg hxa, if_neg hxb]; push_cast; ring
    rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    ring
  have hνsum : ∑ x, ν x = 1 - 2 * α := by
    simp only [hν, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hμ.2]
    ring
  have hwa : ‖w a‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (hwL a ha) hL.ne'
  have hpair := norm_add_le_gap L δ hgap (w a) (w b) hwa (hwL a ha) (hwL b hb) hab
  rw [hsum]
  calc ‖(α : ℂ) * (w a + w b) + ∑ x, (ν x : ℂ) * w x‖
      ≤ ‖(α : ℂ) * (w a + w b)‖ + ‖∑ x, (ν x : ℂ) * w x‖ := norm_add_le _ _
    _ ≤ α * (2 - δ) + ∑ x, ν x := by
        gcongr
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hαpos]
          exact mul_le_mul_of_nonneg_left hpair hαpos
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hνnn x)]
          exact mul_le_of_le_one_right (hνnn x) (hw1 x)
    _ = 1 - α * δ := by rw [hνsum]; ring

/-- The bias bound with a constant depending only on `L` and `α`. -/
theorem exists_bias (L : ℕ) (hL : 0 < L) (α : ℝ) (hα : 0 < α) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 / 2 ∧ ∀ {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (w : Ω → ℂ),
      IsDist μ → AtomsAtLeast μ α → (∀ a, ‖w a‖ ≤ 1) → (∀ a, μ a ≠ 0 → w a ^ L = 1) →
      ∀ a b, μ a ≠ 0 → μ b ≠ 0 → w a ≠ w b → ‖∑ x, (μ x : ℂ) * w x‖ ≤ 1 - γ := by
  obtain ⟨δ, hδ, hgap⟩ := exists_gap L hL
  refine ⟨min (α * δ) (1 / 2), lt_min (mul_pos hα hδ) (by norm_num), min_le_right _ _, ?_⟩
  intro Ω _ μ w hμ hαμ hw1 hwL a b ha hb hab
  have := bias_le L hL δ α hα.le hgap μ w hμ hαμ hw1 hwL a b ha hb hab
  linarith [min_le_left (α * δ) (1 / 2)]

/-- An expectation of a function bounded by one is bounded by one. -/
theorem norm_expect_le_one {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (w : Ω → ℂ) (hμ : IsDist μ)
    (hw1 : ∀ a, ‖w a‖ ≤ 1) : ‖∑ x, (μ x : ℂ) * w x‖ ≤ 1 := by
  refine (norm_sum_le _ _).trans ?_
  rw [← hμ.2]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ.1 x)]
  exact mul_le_of_le_one_right (hμ.1 x) (hw1 x)

end RestrictedAP.Counting.Dev.Fourier
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RestrictedAP.Counting.Dev.L37
open RestrictedAP.Counting RestrictedAP.Counting.Dev.ProdBasics RestrictedAP.Counting.Dev.L33
  RestrictedAP.Counting.Dev.Fourier
open Classical

variable {Sig : Type} [Fintype Sig] [DecidableEq Sig] {n : ℕ}

/-! ## Elementary facts -/

theorem pow_mod_of_pow_eq_one (z : ℂ) (N m : ℕ) (hz : z ^ N = 1) : z ^ (m % N) = z ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m N, pow_add, pow_mul, hz, one_pow, mul_one]

theorem symbolicDist_one_one {α : Type*} : symbolicDist (1 : (Fin n → α) → ℂ) 1 = 0 := by
  unfold symbolicDist
  apply Nat.sInf_eq_zero.mpr
  left
  exact ⟨fun _ _ => 1, fun _ _ => 1, by simp, by simp, by simp, by simp, by simp⟩

theorem coord3_diag (s : Fin 3) (x : Sig) : coord3 s (x, x, x) = x := by
  unfold coord3; split_ifs <;> rfl

/-- Re-indexing a natural-exponent product over an image: fibre sums of the exponents. -/
theorem prod_image_pow {ι γ : Type*} [DecidableEq ι] [DecidableEq (γ → ℂ)] (g : ι → γ → ℂ)
    (e : ι → ℕ) (X : Finset ι) :
    ∃ a : (γ → ℂ) → ℤ, ∀ t, ∏ f ∈ X.image g, (f t) ^ (a f) = ∏ x ∈ X, (g x t) ^ (e x) := by
  refine ⟨fun f => ((∑ x ∈ X.filter (fun x => g x = f), e x : ℕ) : ℤ), fun t => ?_⟩
  rw [← Finset.prod_fiberwise_of_maps_to (g := g) (t := X.image g)
    (fun x hx => Finset.mem_image_of_mem g hx)]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [zpow_natCast, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

/-! ## The coordinate factors `W` -/

theorem W_diag_self (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P) (e : PP × Fin 3 → ℕ) (i : Fin n) :
    W σs PP e i (σs, σs, σs) = 1 := by
  unfold W
  refine Finset.prod_eq_one fun y _ => ?_
  rw [coord3_diag, component_self σs _ (hPP _ y.1.2), one_pow]

theorem W_ne_zero (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P) (e : PP × Fin 3 → ℕ) (i : Fin n)
    (a : Sig × Sig × Sig) : W σs PP e i a ≠ 0 := by
  intro h; have := W_norm σs PP hPP e i a; rw [h] at this; simp at this

theorem W_zero (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ)) (i : Fin n)
    (a : Sig × Sig × Sig) : W σs PP 0 i a = 1 := by
  simp [W]

theorem W_pow_eq_one (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ)) (L : ℕ)
    (hL : ∀ P ∈ PP, orderOf P ∣ L) (e : PP × Fin 3 → ℕ) (i : Fin n) (a : Sig × Sig × Sig) :
    W σs PP e i a ^ L = 1 := by
  unfold W
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun y _ => ?_
  rw [← pow_mul, mul_comm, pow_mul]
  obtain ⟨k, hk⟩ := hL _ y.1.2
  rw [hk, pow_mul, component_pow_orderOf, one_pow, one_pow]

/-- `∏_y (P_y(coord_{s_y} T))^{e y} = ∏_i W e i (T i)`. -/
theorem prod_pow_eq_prod_W (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P) (e : PP × Fin 3 → ℕ)
    (T : Fin n → Sig × Sig × Sig) :
    ∏ y : PP × Fin 3, (y.1.1 (fun i => coord3 y.2 (T i))) ^ (e y) =
      ∏ i, W σs PP e i (T i) := by
  simp only [W]
  rw [Finset.prod_comm (s := (Finset.univ : Finset (Fin n)))]
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [eq_prod_component σs _ (hPP _ y.1.2), Finset.prod_pow]

/-- `β_e = ∏_y (b P_y)^{-e y}`. -/
noncomputable def beta (PP : Finset ((Fin n → Sig) → ℂ)) (b : ((Fin n → Sig) → ℂ) → ℂ)
    (e : PP × Fin 3 → ℕ) : ℂ :=
  ∏ y : PP × Fin 3, ((b y.1.1)⁻¹) ^ (e y)

theorem prod_ratio (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P) (e : PP × Fin 3 → ℕ)
    (T : Fin n → Sig × Sig × Sig) (b : ((Fin n → Sig) → ℂ) → ℂ) :
    ∏ y : PP × Fin 3, (y.1.1 (fun i => coord3 y.2 (T i)) / b y.1.1) ^ (e y) =
      beta PP b e * ∏ i, W σs PP e i (T i) := by
  rw [← prod_pow_eq_prod_W σs PP hPP e T, beta, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [div_eq_mul_inv, mul_pow, mul_comm]

/-! ## Indicator expansion -/

theorem ind_expand {X : Type*} [Fintype X] [DecidableEq X] (N : X → ℕ) (hN : ∀ y, 0 < N y)
    (v c : X → ℂ) (hv : ∀ y, v y ^ N y = 1) (hc : ∀ y, c y ^ N y = 1) :
    (if ∀ y, v y = c y then (1 : ℂ) else 0) =
      (∏ y, (1 / (N y : ℂ))) *
        ∑ e ∈ Fintype.piFinset (fun y => Finset.range (N y)), ∏ y, (v y / c y) ^ (e y) := by
  rw [← Finset.prod_univ_sum, ← Finset.prod_mul_distrib]
  have h : ∀ y, (if v y = c y then (1 : ℂ) else 0) =
      (1 / (N y : ℂ)) * ∑ k ∈ Finset.range (N y), (v y / c y) ^ k :=
    fun y => ind_eq_geom' (v y) (c y) (N y) (hN y) (hv y) (hc y)
  rw [← Finset.prod_congr rfl fun y _ => h y]
  by_cases hall : ∀ y, v y = c y
  · rw [if_pos hall]; exact (Finset.prod_eq_one fun y _ => if_pos (hall y)).symm
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨y, hy⟩ := hall
    exact (Finset.prod_eq_zero (Finset.mem_univ y) (if_neg hy)).symm

/-- The frozen vector: `wJ` on `J`, `t` off `J`. -/
def frz (J : Finset (Fin n)) (wJ t : Fin n → Sig × Sig × Sig) : Fin n → Sig × Sig × Sig :=
  fun i => if i ∈ J then wJ i else t i

theorem event_iff (PP : Finset ((Fin n → Sig) → ℂ)) (J : Finset (Fin n))
    (w w' w'' : Fin n → Sig) (t : Fin n → Sig × Sig × Sig) (b : ((Fin n → Sig) → ℂ) → ℂ) :
    (∀ P ∈ PP, P (fun i => if i ∈ J then w i else (t i).1) = b P ∧
        P (fun i => if i ∈ J then w' i else (t i).2.1) = b P ∧
        P (fun i => if i ∈ J then w'' i else (t i).2.2) = b P) ↔
      ∀ y : PP × Fin 3,
        y.1.1 (fun i => coord3 y.2 (frz J (fun i => (w i, w' i, w'' i)) t i)) = b y.1.1 := by
  have h0 : (fun i => coord3 0 (frz J (fun i => (w i, w' i, w'' i)) t i)) =
      fun i => if i ∈ J then w i else (t i).1 := by
    funext i; by_cases hi : i ∈ J <;> simp [frz, coord3, hi]
  have h1 : (fun i => coord3 1 (frz J (fun i => (w i, w' i, w'' i)) t i)) =
      fun i => if i ∈ J then w' i else (t i).2.1 := by
    funext i; by_cases hi : i ∈ J <;> simp [frz, coord3, hi]
  have h2 : (fun i => coord3 2 (frz J (fun i => (w i, w' i, w'' i)) t i)) =
      fun i => if i ∈ J then w'' i else (t i).2.2 := by
    funext i; by_cases hi : i ∈ J <;> simp [frz, coord3, hi]
  constructor
  · rintro h ⟨⟨P, hP⟩, s⟩
    fin_cases s
    · have := (h P hP).1; rw [← h0] at this; exact this
    · have := (h P hP).2.1; rw [← h1] at this; exact this
    · have := (h P hP).2.2; rw [← h2] at this; exact this
  · intro h P hP
    refine ⟨?_, ?_, ?_⟩
    · have := h (⟨P, hP⟩, 0); rw [h0] at this; exact this
    · have := h (⟨P, hP⟩, 1); rw [h1] at this; exact this
    · have := h (⟨P, hP⟩, 2); rw [h2] at this; exact this

/-- Per-sample expansion of the indicator of the event. -/
theorem ind_t (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ 0 < orderOf P) (J : Finset (Fin n))
    (w w' w'' : Fin n → Sig) (b : ((Fin n → Sig) → ℂ) → ℂ) (hb : ∀ P ∈ PP, b P ∈ Set.range P)
    (t : Fin n → Sig × Sig × Sig) :
    ((if (∀ P ∈ PP, P (fun i => if i ∈ J then w i else (t i).1) = b P ∧
        P (fun i => if i ∈ J then w' i else (t i).2.1) = b P ∧
        P (fun i => if i ∈ J then w'' i else (t i).2.2) = b P) then (1 : ℝ) else 0 : ℝ) : ℂ) =
      (∏ y : PP × Fin 3, (1 / (orderOf y.1.1 : ℂ))) *
        ∑ e ∈ E PP, beta PP b e *
          ∏ i, W σs PP e i (frz J (fun i => (w i, w' i, w'' i)) t i) := by
  have hexp := ind_expand (fun y : PP × Fin 3 => orderOf y.1.1) (fun y => (hPP _ y.1.2).2)
    (fun y => y.1.1 (fun i => coord3 y.2 (frz J (fun i => (w i, w' i, w'' i)) t i)))
    (fun y => b y.1.1) (fun y => pow_apply_eq_one _ _ (pow_orderOf_eq_one _) _)
    (fun y => by
      obtain ⟨x0, hx0⟩ := hb _ y.1.2
      show b y.1.1 ^ orderOf y.1.1 = 1
      rw [← hx0]; exact pow_apply_eq_one _ _ (pow_orderOf_eq_one _) _)
  have hE : E PP = Fintype.piFinset (fun y : PP × Fin 3 => Finset.range (orderOf y.1.1)) := rfl
  rw [hE]
  simp only [← prod_ratio σs PP (fun P hP => (hPP P hP).1)]
  rw [← hexp]
  by_cases h : (∀ P ∈ PP, P (fun i => if i ∈ J then w i else (t i).1) = b P ∧
        P (fun i => if i ∈ J then w' i else (t i).2.1) = b P ∧
        P (fun i => if i ∈ J then w'' i else (t i).2.2) = b P)
  · rw [if_pos h, if_pos ((event_iff PP J w w' w'' t b).1 h)]; simp
  · rw [if_neg h, if_neg (mt (event_iff PP J w w' w'' t b).2 h)]; simp

/-- The coordinate factor `F_{e,i} = E_μ w_{e,i}`. -/
noncomputable def Fe (μ : Sig × Sig × Sig → ℝ) (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (J : Finset (Fin n)) (wJ : Fin n → Sig × Sig × Sig) (e : PP × Fin 3 → ℕ) (i : Fin n) : ℂ :=
  ∑ a, (μ a : ℂ) * W σs PP e i (if i ∈ J then wJ i else a)

theorem sum_factor (μ : Sig × Sig × Sig → ℝ) (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (J : Finset (Fin n)) (wJ : Fin n → Sig × Sig × Sig) (e : PP × Fin 3 → ℕ) :
    ∑ t : Fin n → Sig × Sig × Sig, (tensorPow μ n t : ℂ) * ∏ i, W σs PP e i (frz J wJ t i) =
      ∏ i, Fe μ σs PP J wJ e i := by
  simp only [Fe]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [tensorPow, frz]
  push_cast
  rw [Finset.prod_mul_distrib]

/-! ## Terms with all factors constant on the support -/

theorem Fe_good (μ : Sig × Sig × Sig → ℝ) (hμ : IsDist μ) (hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0)
    (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ)) (hPP : ∀ P ∈ PP, IsProductFunction σs P)
    (J : Finset (Fin n)) (wJ : Fin n → Sig × Sig × Sig) (hwJ : ∀ j ∈ J, μ (wJ j) ≠ 0)
    (e : PP × Fin 3 → ℕ) (hg : ∀ i, good μ σs PP e i) (i : Fin n) :
    Fe μ σs PP J wJ e i = 1 := by
  have h1 : ∀ a, μ a ≠ 0 → W σs PP e i a = 1 := fun a ha => by
    rw [hg i ⟨a, ha⟩ ⟨(σs, σs, σs), hdiag σs⟩]; exact W_diag_self σs PP hPP e i
  have hsum : ∑ a, (μ a : ℂ) = 1 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hμ.2; push_cast at this; exact this
  unfold Fe
  by_cases hi : i ∈ J
  · simp only [if_pos hi, h1 _ (hwJ i hi), mul_one]; exact hsum
  · simp only [if_neg hi]
    rw [← hsum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : μ a = 0
    · simp [ha]
    · rw [h1 a ha, mul_one]

theorem beta_eq_one (μ : Sig × Sig × Sig → ℝ) (hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0)
    (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ 0 < orderOf P) (D : ℝ) (hD : 0 < D)
    (hrank : RankAtLeast PP D) (e : PP × Fin 3 → ℕ) (hg : ∀ i, good μ σs PP e i)
    (b : ((Fin n → Sig) → ℂ) → ℂ) (hb : ∀ P ∈ PP, b P ∈ Set.range P) :
    beta PP b e = 1 := by
  set A : PP → ℕ := fun P => ∑ s : Fin 3, e (P, s) with hA
  have hsplit : ∀ f : PP → ℂ, ∏ y : PP × Fin 3, (f y.1) ^ (e y) = ∏ P : PP, (f P) ^ (A P) := by
    intro f
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun P _ => ?_
    show ∏ s : Fin 3, f P ^ e (P, s) = f P ^ A P
    exact Finset.prod_pow_eq_pow_sum _ _ _
  have hone : ∀ x : Fin n → Sig, ∏ P : PP, (P.1 x) ^ (A P) = 1 := by
    intro x
    rw [← hsplit (fun P => P.1 x)]
    have := prod_pow_eq_prod_W σs PP (fun P hP => (hPP P hP).1) e (fun i => (x i, x i, x i))
    simp only [coord3_diag] at this
    rw [this]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [hg i ⟨_, hdiag (x i)⟩ ⟨_, hdiag σs⟩]
    exact W_diag_self σs PP (fun P hP => (hPP P hP).1) e i
  have hdvd : ∀ P : PP, orderOf P.1 ∣ A P := by
    by_contra hcon
    push Not at hcon
    obtain ⟨P0, hP0⟩ := hcon
    let a : ((Fin n → Sig) → ℂ) → ℕ := fun P => if h : P ∈ PP then A ⟨P, h⟩ % orderOf P else 0
    have hfun : ∏ P ∈ PP, P ^ a P = 1 := by
      funext x
      rw [Finset.prod_apply, ← Finset.prod_coe_sort]
      simp only [Pi.pow_apply, Pi.one_apply]
      rw [← hone x]
      refine Finset.prod_congr rfl fun P _ => ?_
      simp only [a, dif_pos P.2]
      exact pow_mod_of_pow_eq_one _ _ _ (pow_apply_eq_one _ _ (pow_orderOf_eq_one _) _)
    have := hrank a (fun P hP => Or.inr (by
        simp only [a, dif_pos hP]; exact Nat.mod_lt _ (hPP P hP).2))
      ⟨P0.1, P0.2, by
        simp only [a, dif_pos P0.2]; exact fun h => hP0 (Nat.dvd_of_mod_eq_zero h)⟩
    rw [hfun, symbolicDist_one_one] at this
    simp at this; linarith
  unfold beta
  rw [hsplit (fun P => (b P.1)⁻¹)]
  refine Finset.prod_eq_one fun P _ => ?_
  obtain ⟨k, hk⟩ := hdvd P
  obtain ⟨x0, hx0⟩ := hb P.1 P.2
  rw [hk, pow_mul, inv_pow, ← hx0, pow_apply_eq_one _ _ (pow_orderOf_eq_one _) x0, inv_one,
    one_pow]

/-! ## Terms with a non-constant factor -/

theorem projColl_univ (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P) : projColl σs Finset.univ PP = PP := by
  have hpe : ∀ P ∈ PP, proj σs Finset.univ P = P := by
    intro P hP
    funext x
    rw [proj_apply]
    simp only [Finset.mem_univ, if_true]
    exact (eq_prod_component σs P (hPP P hP) x).symm
  unfold projColl
  ext Q
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨P, hP, rfl⟩; rw [hpe P hP]; exact hP
  · intro hQ; exact ⟨Q, hQ, hpe Q hQ⟩

theorem bad_many (μ : Sig × Sig × Sig → ℝ) (hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0) (σs : Sig)
    (PP : Finset ((Fin n → Sig) → ℂ)) (hPP : ∀ P ∈ PP, IsProductFunction σs P) (D : ℝ)
    (hsoft : SoftRankMuAtLeast μ PP D) (e : PP × Fin 3 → ℕ)
    (hbad : ¬ ∀ i, good μ σs PP e i) :
    D ≤ ((Finset.univ.filter fun i => ¬ good μ σs PP e i).card : ℝ) := by
  unfold SoftRankMuAtLeast at hsoft
  rw [← projColl_univ σs PP hPP, jointLift_eq] at hsoft
  obtain ⟨a, ha⟩ := prod_image_pow
    (fun y : PP × Fin 3 => Lg μ y.2 (proj σs Finset.univ y.1.1)) e Finset.univ
  have hG : ∀ t, ∏ f ∈ (Finset.univ : Finset (PP × Fin 3)).image
      (fun y => Lg μ y.2 (proj σs Finset.univ y.1.1)), (f t) ^ (a f) =
      ∏ i, W σs PP e i (t i).1 := by
    intro t; rw [ha, prod_Lg_proj]
  set u : Fin n → {t // μ t ≠ 0} → ℂ := fun i a => W σs PP e i a.1 with hu
  have hu1 : ∀ i a, ‖u i a‖ = 1 := fun i a => W_norm σs PP hPP e i a.1
  rcases hsoft a with ⟨c, hc⟩ | hD
  · exfalso
    apply hbad
    have : Nonempty {t // μ t ≠ 0} := ⟨⟨_, hdiag σs⟩⟩
    intro i x y
    exact rigid_const u (fun i a => W_ne_zero σs PP hPP e i a.1) c
      (fun t => by rw [← hG]; exact hc t) i x y
  · refine hD.trans ?_
    obtain ⟨i0, hi0⟩ : ∃ i0, ¬ good μ σs PP e i0 := by push Not at hbad; exact hbad
    set a0 : {t // μ t ≠ 0} := ⟨_, hdiag σs⟩
    set cc : ℂ := ∏ i ∈ Finset.univ.filter (fun i => good μ σs PP e i), u i a0 with hcc
    have hccn : ‖cc‖ = 1 := by
      rw [hcc, norm_prod]; exact Finset.prod_eq_one fun i _ => hu1 i a0
    have hcc0 : cc ≠ 0 := by intro h; rw [h] at hccn; simp at hccn
    set v : Fin n → {t // μ t ≠ 0} → ℂ := fun i _ =>
      if good μ σs PP e i then u i a0 else if i = i0 then cc⁻¹ else 1 with hv
    have hv1 : ∀ i a, ‖v i a‖ = 1 := by
      intro i a; simp only [hv]
      split_ifs
      · exact hu1 i a0
      · rw [norm_inv, hccn, inv_one]
      · exact norm_one
    have hvprod : ∀ x, (1 : (Fin n → {t // μ t ≠ 0}) → ℂ) x = ∏ i, v i (x i) := by
      intro x
      simp only [hv, Pi.one_apply]
      rw [Finset.prod_ite, Finset.prod_ite_eq' _ i0, if_pos (by simpa using hi0), ← hcc,
        mul_inv_cancel₀ hcc0]
    have hmem : (Finset.univ.filter (fun i => u i ≠ v i)).card ∈
        {k | ∃ u v : Fin n → {t // μ t ≠ 0} → ℂ, (∀ i a, ‖u i a‖ = 1) ∧ (∀ i a, ‖v i a‖ = 1) ∧
          (∀ x, (fun x => ∏ f ∈ (Finset.univ : Finset (PP × Fin 3)).image
            (fun y => Lg μ y.2 (proj σs Finset.univ y.1.1)), (f x) ^ (a f)) x =
              ∏ i, u i (x i)) ∧
          (∀ x, (1 : (Fin n → {t // μ t ≠ 0}) → ℂ) x = ∏ i, v i (x i)) ∧
          (Finset.univ.filter (fun i => u i ≠ v i)).card = k} :=
      ⟨u, v, hu1, hv1, fun x => hG x, hvprod, rfl⟩
    have hle := Nat.sInf_le hmem
    have hsub : Finset.univ.filter (fun i => u i ≠ v i) ⊆
        Finset.univ.filter (fun i => ¬ good μ σs PP e i) := by
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hne hgood
      apply hne
      funext x
      simp only [hv, if_pos hgood, hu]
      exact hgood x a0
    have := hle.trans (Finset.card_le_card hsub)
    unfold symbolicDist
    exact_mod_cast this

/-- The bias bound in the shape produced by `Fourier.exists_bias`. -/
def BiasProp (L : ℕ) (α γ : ℝ) : Prop :=
  ∀ {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (w : Ω → ℂ),
    IsDist μ → AtomsAtLeast μ α → (∀ a, ‖w a‖ ≤ 1) → (∀ a, μ a ≠ 0 → w a ^ L = 1) →
    ∀ a b, μ a ≠ 0 → μ b ≠ 0 → w a ≠ w b → ‖∑ x, (μ x : ℂ) * w x‖ ≤ 1 - γ

/-- Lower bound on the real part of each term. -/
theorem term_re_ge (M : ℕ) (α γ : ℝ) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (hbias : BiasProp M.factorial α γ) (μ : Sig × Sig × Sig → ℝ) (hμ : IsDist μ)
    (hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0) (hαμ : AtomsAtLeast μ α) (σs : Sig)
    (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ 0 < orderOf P ∧ orderOf P ≤ M) (D : ℝ)
    (hD : 0 < D) (hrank : RankAtLeast PP D) (hsoft : SoftRankMuAtLeast μ PP D)
    (J : Finset (Fin n)) (hJ : (J.card : ℝ) ≤ D / 2) (wJ : Fin n → Sig × Sig × Sig)
    (hwJ : ∀ j ∈ J, μ (wJ j) ≠ 0) (b : ((Fin n → Sig) → ℂ) → ℂ)
    (hb : ∀ P ∈ PP, b P ∈ Set.range P) (e : PP × Fin 3 → ℕ) :
    (if e = 0 then (1 : ℝ) else 0) - (1 - γ) ^ (D / 2) ≤
      (beta PP b e * ∏ i, Fe μ σs PP J wJ e i).re := by
  have hPP1 : ∀ P ∈ PP, IsProductFunction σs P := fun P hP => (hPP P hP).1
  have hρ0 : 0 < 1 - γ := by linarith
  have hρpow : 0 ≤ (1 - γ) ^ (D / 2) := Real.rpow_nonneg hρ0.le _
  by_cases hg : ∀ i, good μ σs PP e i
  · rw [beta_eq_one μ hdiag σs PP (fun P hP => ⟨(hPP P hP).1, (hPP P hP).2.1⟩) D hD hrank e hg b
      hb]
    rw [Finset.prod_eq_one fun i _ => Fe_good μ hμ hdiag σs PP hPP1 J wJ hwJ e hg i]
    simp only [mul_one, Complex.one_re]
    split_ifs <;> linarith
  · have he0 : e ≠ 0 := by
      rintro rfl; apply hg; intro i x y; rw [W_zero, W_zero]
    rw [if_neg he0, zero_sub]
    have hβ : ‖beta PP b e‖ = 1 := by
      unfold beta
      rw [norm_prod]
      refine Finset.prod_eq_one fun y _ => ?_
      obtain ⟨x0, hx0⟩ := hb _ y.1.2
      rw [norm_pow, norm_inv, ← hx0, norm_eq_one σs _ (hPP1 _ y.1.2), inv_one, one_pow]
    set S := (Finset.univ.filter fun i => ¬ good μ σs PP e i) \ J with hS
    have hmany := bad_many μ hdiag σs PP hPP1 D hsoft e hg
    have hScard : D / 2 ≤ (S.card : ℝ) := by
      have h1 := Finset.card_le_card_sdiff_add_card
        (s := Finset.univ.filter fun i => ¬ good μ σs PP e i) (t := J)
      have h2 : ((Finset.univ.filter fun i => ¬ good μ σs PP e i).card : ℝ) ≤
          (S.card : ℝ) + J.card := by exact_mod_cast h1
      linarith
    have hL : ∀ P ∈ PP, orderOf P ∣ M.factorial :=
      fun P hP => Nat.dvd_factorial (hPP P hP).2.1 (hPP P hP).2.2
    have hFle : ∀ i, ‖Fe μ σs PP J wJ e i‖ ≤ if i ∈ S then 1 - γ else 1 := by
      intro i
      split_ifs with hiS
      · rw [hS, Finset.mem_sdiff, Finset.mem_filter] at hiS
        obtain ⟨⟨_, hbadi⟩, hiJ⟩ := hiS
        unfold good at hbadi
        push Not at hbadi
        obtain ⟨x, y, hxy⟩ := hbadi
        unfold Fe
        simp only [if_neg hiJ]
        exact hbias μ (W σs PP e i) hμ hαμ (fun a => (W_norm σs PP hPP1 e i a).le)
          (fun a _ => W_pow_eq_one σs PP _ hL e i a) x.1 y.1 x.2 y.2 hxy
      · exact norm_expect_le_one μ _ hμ fun a => (W_norm σs PP hPP1 e i _).le
    have hprod : ‖∏ i, Fe μ σs PP J wJ e i‖ ≤ (1 - γ) ^ S.card := by
      rw [norm_prod]
      calc ∏ i, ‖Fe μ σs PP J wJ e i‖ ≤ ∏ i, (if i ∈ S then 1 - γ else 1) :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hFle i
        _ = (1 - γ) ^ S.card := by rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    have hpow : (1 - γ) ^ S.card ≤ (1 - γ) ^ (D / 2) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hρ0 (by linarith) hScard
    have hnorm : ‖beta PP b e * ∏ i, Fe μ σs PP J wJ e i‖ ≤ (1 - γ) ^ (D / 2) := by
      rw [norm_mul, hβ, one_mul]; exact hprod.trans hpow
    have hre := Complex.abs_re_le_norm (beta PP b e * ∏ i, Fe μ σs PP J wJ e i)
    have := neg_abs_le (beta PP b e * ∏ i, Fe μ σs PP J wJ e i).re
    linarith

/-! ## Assembly -/

theorem main (M : ℕ) (α γ : ℝ) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (hbias : BiasProp M.factorial α γ) (σs : Sig) (μ : Sig × Sig × Sig → ℝ)
    (PP : Finset ((Fin n → Sig) → ℂ)) (D : ℤ) (J : Finset (Fin n))
    (hμ : IsDist μ) (hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0) (hαμ : AtomsAtLeast μ α)
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ IsDiscrete M P)
    (hrank : RankAtLeast PP (D : ℝ)) (hsoft : SoftRankMuAtLeast μ PP (D : ℝ))
    (hJ : (J.card : ℝ) ≤ (D : ℝ) / 2)
    (w w' w'' : Fin n → Sig) (hw : ∀ j ∈ J, μ (w j, w' j, w'' j) ≠ 0)
    (b : ((Fin n → Sig) → ℂ) → ℂ) (hb : ∀ P ∈ PP, b P ∈ Set.range P) :
    (∏ P ∈ PP, (1 / (orderOf P : ℝ) ^ 3)) - (1 - γ) ^ ((D : ℝ) / 2) ≤
      ∑ t : Fin n → Sig × Sig × Sig,
        if (∀ P ∈ PP,
            P (fun i => if i ∈ J then w i else (t i).1) = b P ∧
            P (fun i => if i ∈ J then w' i else (t i).2.1) = b P ∧
            P (fun i => if i ∈ J then w'' i else (t i).2.2) = b P)
        then tensorPow μ n t else 0 := by
  have hPP' : ∀ P ∈ PP, IsProductFunction σs P ∧ 0 < orderOf P ∧ orderOf P ≤ M :=
    fun P hP => ⟨(hPP P hP).1, (hPP P hP).2.1, (hPP P hP).2.2⟩
  have hρ0 : 0 < 1 - γ := by linarith
  have htP : ∀ t, 0 ≤ tensorPow μ n t := fun t => Finset.prod_nonneg fun i _ => hμ.1 _
  have hRHS : 0 ≤ ∑ t : Fin n → Sig × Sig × Sig,
        (if (∀ P ∈ PP,
            P (fun i => if i ∈ J then w i else (t i).1) = b P ∧
            P (fun i => if i ∈ J then w' i else (t i).2.1) = b P ∧
            P (fun i => if i ∈ J then w'' i else (t i).2.2) = b P)
        then tensorPow μ n t else 0) :=
    Finset.sum_nonneg fun t _ => by split_ifs; exacts [htP t, le_rfl]
  -- the product of the reciprocals of the orders
  set C : ℝ := ∏ y : PP × Fin 3, (1 / (orderOf y.1.1 : ℝ)) with hC
  have hCeq : C = ∏ P ∈ PP, (1 / (orderOf P : ℝ) ^ 3) := by
    rw [hC, Fintype.prod_prod_type, ← Finset.prod_coe_sort PP]
    refine Finset.prod_congr rfl fun P _ => ?_
    show ∏ s : Fin 3, (1 / (orderOf P.1 : ℝ)) = 1 / (orderOf P.1 : ℝ) ^ 3
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_div_pow]
  have hCpos : 0 < C := Finset.prod_pos fun y _ => by
    have := (hPP' _ y.1.2).2.1
    positivity
  have hCE : C * ((E PP).card : ℝ) = 1 := by
    rw [hC, E, Fintype.card_piFinset]
    simp only [Finset.card_range]
    push_cast
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun y _ => ?_
    have : (orderOf y.1.1 : ℝ) ≠ 0 := by
      have := (hPP' _ y.1.2).2.1; positivity
    field_simp
  rw [← hCeq]
  rcases le_or_gt D 0 with hD | hD
  · -- trivial case
    have hC1 : C ≤ 1 := by
      rw [hC]
      refine Finset.prod_le_one (fun y _ => by positivity) fun y _ => ?_
      have : (1 : ℝ) ≤ orderOf y.1.1 := by exact_mod_cast (hPP' _ y.1.2).2.1
      rw [div_le_one (by linarith)]; exact this
    have h1 : 1 ≤ (1 - γ) ^ ((D : ℝ) / 2) := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ0 (by linarith)
      have : (D : ℝ) ≤ 0 := by exact_mod_cast hD
      linarith
    linarith
  · have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    set wJ : Fin n → Sig × Sig × Sig := fun i => (w i, w' i, w'' i) with hwJ
    -- complex identity
    have hcx : ((∑ t : Fin n → Sig × Sig × Sig,
        (if (∀ P ∈ PP,
            P (fun i => if i ∈ J then w i else (t i).1) = b P ∧
            P (fun i => if i ∈ J then w' i else (t i).2.1) = b P ∧
            P (fun i => if i ∈ J then w'' i else (t i).2.2) = b P)
        then tensorPow μ n t else 0) : ℝ) : ℂ) =
        (C : ℂ) * ∑ e ∈ E PP, beta PP b e * ∏ i, Fe μ σs PP J wJ e i := by
      have hstep : ∀ t : Fin n → Sig × Sig × Sig,
          (((if (∀ P ∈ PP,
            P (fun i => if i ∈ J then w i else (t i).1) = b P ∧
            P (fun i => if i ∈ J then w' i else (t i).2.1) = b P ∧
            P (fun i => if i ∈ J then w'' i else (t i).2.2) = b P)
            then tensorPow μ n t else 0) : ℝ) : ℂ) =
          (C : ℂ) * ∑ e ∈ E PP, beta PP b e *
            ((tensorPow μ n t : ℂ) * ∏ i, W σs PP e i (frz J wJ t i)) := by
        intro t
        have h := ind_t σs PP (fun P hP => ⟨(hPP' P hP).1, (hPP' P hP).2.1⟩) J w w' w'' b hb t
        have hsplit : (((if (∀ P ∈ PP,
            P (fun i => if i ∈ J then w i else (t i).1) = b P ∧
            P (fun i => if i ∈ J then w' i else (t i).2.1) = b P ∧
            P (fun i => if i ∈ J then w'' i else (t i).2.2) = b P)
            then tensorPow μ n t else 0) : ℝ) : ℂ) =
            (tensorPow μ n t : ℂ) * (((if (∀ P ∈ PP,
            P (fun i => if i ∈ J then w i else (t i).1) = b P ∧
            P (fun i => if i ∈ J then w' i else (t i).2.1) = b P ∧
            P (fun i => if i ∈ J then w'' i else (t i).2.2) = b P)
            then (1 : ℝ) else 0) : ℝ) : ℂ) := by
          split_ifs <;> simp
        rw [hsplit, h]
        have hCc : (C : ℂ) = ∏ y : PP × Fin 3, (1 / (orderOf y.1.1 : ℂ)) := by
          rw [hC]; push_cast; rfl
        rw [hCc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
      rw [Complex.ofReal_sum, Finset.sum_congr rfl fun t _ => hstep t, ← Finset.mul_sum,
        Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.mul_sum, sum_factor]
    have hreal : (∑ t : Fin n → Sig × Sig × Sig,
        (if (∀ P ∈ PP,
            P (fun i => if i ∈ J then w i else (t i).1) = b P ∧
            P (fun i => if i ∈ J then w' i else (t i).2.1) = b P ∧
            P (fun i => if i ∈ J then w'' i else (t i).2.2) = b P)
        then tensorPow μ n t else 0)) =
        C * ∑ e ∈ E PP, (beta PP b e * ∏ i, Fe μ σs PP J wJ e i).re := by
      have := congrArg Complex.re hcx
      rw [Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_sum] at this
      exact this
    rw [hreal]
    have hterm := fun e => term_re_ge M α γ hγ hγ2 hbias μ hμ hdiag hαμ σs PP hPP' (D : ℝ) hDr
      hrank hsoft J hJ wJ (fun j hj => hw j hj) b hb e
    have hsum : 1 - ((E PP).card : ℝ) * (1 - γ) ^ ((D : ℝ) / 2) ≤
        ∑ e ∈ E PP, (beta PP b e * ∏ i, Fe μ σs PP J wJ e i).re := by
      have h0E : (0 : PP × Fin 3 → ℕ) ∈ E PP := by
        simp only [E, Fintype.mem_piFinset, Finset.mem_range]
        exact fun y => (hPP' _ y.1.2).2.1
      calc 1 - ((E PP).card : ℝ) * (1 - γ) ^ ((D : ℝ) / 2) =
            ∑ e ∈ E PP, ((if e = 0 then (1 : ℝ) else 0) - (1 - γ) ^ ((D : ℝ) / 2)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos h0E, Finset.sum_const,
              nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun e _ => hterm e
    calc C - (1 - γ) ^ ((D : ℝ) / 2) = C * (1 - ((E PP).card : ℝ) * (1 - γ) ^ ((D : ℝ) / 2)) := by
          rw [mul_sub, mul_one, ← mul_assoc, hCE, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hCpos.le

end RestrictedAP.Counting.Dev.L37

open Classical

namespace RestrictedAP.Counting

open RestrictedAP.Counting.Dev.L37 RestrictedAP.Counting.Dev.Fourier in
theorem chk_lemma_3_7 (M r : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (μ : Sig × Sig × Sig → ℝ)
        (n : ℕ) (PP : Finset ((Fin n → Sig) → ℂ)) (D : ℤ) (J : Finset (Fin n)),
        IsDist μ → (∀ x : Sig, μ (x, x, x) ≠ 0) → AtomsAtLeast μ α → PP.card = r →
        (∀ P ∈ PP, IsProductFunction σs P ∧ IsDiscrete M P) →
        RankAtLeast PP (D : ℝ) → SoftRankMuAtLeast μ PP (D : ℝ) →
        (J.card : ℝ) ≤ (D : ℝ) / 2 →
        ∀ w w' w'' : Fin n → Sig, (∀ j ∈ J, μ (w j, w' j, w'' j) ≠ 0) →
        ∀ b : ((Fin n → Sig) → ℂ) → ℂ, (∀ P ∈ PP, b P ∈ Set.range P) →
          (∏ P ∈ PP, (1 / (orderOf P : ℝ) ^ 3)) - (2 : ℝ) ^ (-(c * D)) ≤
            ∑ t : Fin n → Sig × Sig × Sig,
              if (∀ P ∈ PP,
                  P (fun i => if i ∈ J then w i else (t i).1) = b P ∧
                  P (fun i => if i ∈ J then w' i else (t i).2.1) = b P ∧
                  P (fun i => if i ∈ J then w'' i else (t i).2.2) = b P)
              then tensorPow μ n t else 0 := by
  obtain ⟨γ, hγ, hγ2, hbias⟩ := exists_bias M.factorial (Nat.factorial_pos M) α hα
  have hρ0 : 0 < 1 - γ := by linarith
  have hρ1 : 1 - γ < 1 := by linarith
  have hlog : Real.logb 2 (1 - γ) < 0 := Real.logb_neg (by norm_num) hρ0 hρ1
  refine ⟨-Real.logb 2 (1 - γ) / 2, by linarith, ?_⟩
  intro Sig _ _ σs μ n PP D J hμ hdiag hαμ _ hPP hrank hsoft hJ w w' w'' hw b hb
  have hkey : (2 : ℝ) ^ (-(-Real.logb 2 (1 - γ) / 2 * (D : ℝ))) = (1 - γ) ^ ((D : ℝ) / 2) := by
    rw [show -(-Real.logb 2 (1 - γ) / 2 * (D : ℝ)) = Real.logb 2 (1 - γ) * ((D : ℝ) / 2) by ring,
      Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hρ0]
  rw [hkey]
  exact main M α γ hγ hγ2 (fun μ w h1 h2 h3 h4 a b ha hb hab => hbias μ w h1 h2 h3 h4 a b ha hb hab)
    σs μ PP D J hμ hdiag hαμ hPP hrank hsoft hJ w w' w'' hw b hb

end RestrictedAP.Counting
end

theorem solution : type_of% @RestrictedAP.Counting.chk_lemma_3_7 := @RestrictedAP.Counting.chk_lemma_3_7
