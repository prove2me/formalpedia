-- Prove2me | solution 1 for RestrictedAP.Counting.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:56:08.787741+00:00
-- url     : https://prove2.me/submissions/7e0f9763-f92b-4e59-b5d8-b98cbde603b6

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions
import Definitions.Def_RestrictedAP_Counting_NoiseOperators

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

/-- The coordinate factor `F_{e,i} = E_μ w_{e,i}`. -/
noncomputable def Fe (μ : Sig × Sig × Sig → ℝ) (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (J : Finset (Fin n)) (wJ : Fin n → Sig × Sig × Sig) (e : PP × Fin 3 → ℕ) (i : Fin n) : ℂ :=
  ∑ a, (μ a : ℂ) * W σs PP e i (if i ∈ J then wJ i else a)

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

/-! ## Assembly -/

end RestrictedAP.Counting.Dev.L37

open Classical

namespace RestrictedAP.Counting

end RestrictedAP.Counting
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RestrictedAP.Counting.Dev.L38
open RestrictedAP.Counting RestrictedAP.Counting.Dev.ProdBasics RestrictedAP.Counting.Dev.L33
  RestrictedAP.Counting.Dev.Fourier RestrictedAP.Counting.Dev.L37
open Classical

variable {Sig : Type} [Fintype Sig] [DecidableEq Sig] {n : ℕ}

/-! ## Indicator expansion with one target per factor -/

/-- `β_e = ∏_y (tg y)^{-e y}`. -/
noncomputable def betaG (PP : Finset ((Fin n → Sig) → ℂ)) (tg : PP × Fin 3 → ℂ)
    (e : PP × Fin 3 → ℕ) : ℂ :=
  ∏ y : PP × Fin 3, ((tg y)⁻¹) ^ (e y)

theorem prod_ratioG (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P) (e : PP × Fin 3 → ℕ)
    (T : Fin n → Sig × Sig × Sig) (tg : PP × Fin 3 → ℂ) :
    ∏ y : PP × Fin 3, (y.1.1 (fun i => coord3 y.2 (T i)) / tg y) ^ (e y) =
      betaG PP tg e * ∏ i, W σs PP e i (T i) := by
  rw [← prod_pow_eq_prod_W σs PP hPP e T, betaG, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [div_eq_mul_inv, mul_pow, mul_comm]

theorem ind_G (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ 0 < orderOf P) (tg : PP × Fin 3 → ℂ)
    (htg : ∀ y : PP × Fin 3, ∃ x, y.1.1 x = tg y) (T : Fin n → Sig × Sig × Sig) :
    (if ∀ y : PP × Fin 3, y.1.1 (fun i => coord3 y.2 (T i)) = tg y then (1 : ℂ) else 0) =
      (∏ y : PP × Fin 3, (1 / (orderOf y.1.1 : ℂ))) *
        ∑ e ∈ E PP, betaG PP tg e * ∏ i, W σs PP e i (T i) := by
  have hexp := ind_expand (fun y : PP × Fin 3 => orderOf y.1.1) (fun y => (hPP _ y.1.2).2)
    (fun y => y.1.1 (fun i => coord3 y.2 (T i))) tg
    (fun y => pow_apply_eq_one _ _ (pow_orderOf_eq_one _) _)
    (fun y => by
      obtain ⟨x0, hx0⟩ := htg y
      rw [← hx0]; exact pow_apply_eq_one _ _ (pow_orderOf_eq_one _) _)
  have hE : E PP = Fintype.piFinset (fun y : PP × Fin 3 => Finset.range (orderOf y.1.1)) := rfl
  rw [hE]
  simp only [← prod_ratioG σs PP (fun P hP => (hPP P hP).1)]
  exact hexp

theorem norm_betaG (PP : Finset ((Fin n → Sig) → ℂ)) (σs : Sig)
    (hPP : ∀ P ∈ PP, IsProductFunction σs P) (tg : PP × Fin 3 → ℂ)
    (htg : ∀ y : PP × Fin 3, ∃ x, y.1.1 x = tg y) (e : PP × Fin 3 → ℕ) :
    ‖betaG PP tg e‖ = 1 := by
  unfold betaG
  rw [norm_prod]
  refine Finset.prod_eq_one fun y _ => ?_
  obtain ⟨x0, hx0⟩ := htg y
  rw [norm_pow, norm_inv, ← hx0, norm_eq_one σs _ (hPP _ y.1.2), inv_one, one_pow]

/-! ## The noise operator on product functions -/

theorem noise_prod {Ω : Type} [Fintype Ω] (ν : Ω → ℝ) (ρ : ℝ) (g : Fin n → Ω → ℂ)
    (x : Fin n → Ω) :
    noiseOp ν ρ n (fun y => ∏ i, g i (y i)) x =
      ∏ i, ∑ b, (noiseKernel ν ρ (x i) b : ℂ) * g i b := by
  unfold noiseOp
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  push_cast
  rw [Finset.prod_mul_distrib]

theorem kernel_sum {Ω : Type} [Fintype Ω] (ν : Ω → ℝ) (ρ : ℝ) (g : Ω → ℂ) (a : Ω) :
    ∑ b, (noiseKernel ν ρ a b : ℂ) * g b = (ρ : ℂ) * g a + (1 - (ρ : ℂ)) * ∑ b, (ν b : ℂ) * g b := by
  have h : ∀ b, (noiseKernel ν ρ a b : ℂ) * g b =
      (if a = b then (ρ : ℂ) * g b else 0) + (1 - (ρ : ℂ)) * ((ν b : ℂ) * g b) := by
    intro b
    unfold noiseKernel
    by_cases hab : a = b
    · rw [if_pos hab, if_pos hab]; push_cast; ring
    · rw [if_neg hab, if_neg hab]; push_cast; ring
  rw [Finset.sum_congr rfl fun b _ => h b, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_single a (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl]

theorem kernel_stat {Ω : Type} [Fintype Ω] (ν : Ω → ℝ) (hν : ∑ a, ν a = 1) (ρ : ℝ) (b : Ω) :
    ∑ a, ν a * noiseKernel ν ρ a b = ν b := by
  have h : ∀ a, ν a * noiseKernel ν ρ a b =
      (if a = b then ρ * ν b else 0) + (1 - ρ) * ν b * ν a := by
    intro a
    unfold noiseKernel
    by_cases hab : a = b
    · rw [if_pos hab, if_pos hab, hab]; ring
    · rw [if_neg hab, if_neg hab]; ring
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, ← Finset.mul_sum, hν,
    Finset.sum_eq_single b (fun a _ ha => if_neg ha) (by simp), if_pos rfl]
  ring

theorem tensor_stat {Ω : Type} [Fintype Ω] (ν : Ω → ℝ) (hν : ∑ a, ν a = 1) (ρ : ℝ)
    (y : Fin n → Ω) :
    ∑ x, tensorPow ν n x * ∏ i, noiseKernel ν ρ (x i) (y i) = tensorPow ν n y := by
  unfold tensorPow
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a => ν a * noiseKernel ν ρ a (y i))]
  exact Finset.prod_congr rfl fun i _ => kernel_stat ν hν ρ (y i)

theorem stationary {Ω : Type} [Fintype Ω] (ν : Ω → ℝ) (hν : ∑ a, ν a = 1) (ρ : ℝ)
    (f : (Fin n → Ω) → ℂ) :
    ∑ x, (tensorPow ν n x : ℂ) * noiseOp ν ρ n f x = ∑ y, (tensorPow ν n y : ℂ) * f y := by
  unfold noiseOp
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h := congrArg (fun r : ℝ => (r : ℂ)) (tensor_stat ν hν ρ y)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul] at h
  rw [← h, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-! ## Variance is minimised by the mean -/

theorem real_pyth {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp : ∑ x, p x = 1) (u : Ω → ℝ)
    (m K : ℝ) (hm : ∑ x, p x * u x = m) :
    ∑ x, p x * (u x - m) ^ 2 ≤ ∑ x, p x * (u x - K) ^ 2 := by
  have key : ∑ x, p x * (u x - K) ^ 2 - ∑ x, p x * (u x - m) ^ 2 = (m - K) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    have : ∀ x, p x * (u x - K) ^ 2 - p x * (u x - m) ^ 2 =
        (2 * (m - K)) * (p x * u x) + (K ^ 2 - m ^ 2) * p x := fun x => by ring
    rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hm, hp]
    ring
  nlinarith [sq_nonneg (m - K)]

theorem cpx_pyth {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp : ∑ x, p x = 1) (f : Ω → ℂ)
    (m K : ℂ) (hm : ∑ x, (p x : ℂ) * f x = m) :
    ∑ x, p x * ‖f x - m‖ ^ 2 ≤ ∑ x, p x * ‖f x - K‖ ^ 2 := by
  have hre : ∑ x, p x * (f x).re = m.re := by
    rw [← hm, Complex.re_sum]; simp only [Complex.re_ofReal_mul]
  have him : ∑ x, p x * (f x).im = m.im := by
    rw [← hm, Complex.im_sum]; simp only [Complex.im_ofReal_mul]
  have e : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [e, Complex.sub_re, Complex.sub_im, mul_add, Finset.sum_add_distrib]
  exact add_le_add (real_pyth p hp _ _ _ hre) (real_pyth p hp _ _ _ him)

/-! ## Factor bounds -/

theorem factor_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (u m : ℂ) (hu : ‖u‖ = 1) :
    ‖(ρ : ℂ) * u + (1 - (ρ : ℂ)) * m‖ ≤ ρ + (1 - ρ) * ‖m‖ := by
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(ρ : ℂ)‖ = ρ := by rw [Complex.norm_real, Real.norm_of_nonneg hρ0]
  have h2 : ‖(1 - (ρ : ℂ))‖ = 1 - ρ := by
    rw [show (1 - (ρ : ℂ)) = ((1 - ρ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [norm_mul, norm_mul, h1, h2, hu, mul_one]

theorem W_one_of_good (μ : Sig × Sig × Sig → ℝ) (hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0)
    (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ)) (hPP : ∀ P ∈ PP, IsProductFunction σs P)
    (e : PP × Fin 3 → ℕ) (i : Fin n) (hg : good μ σs PP e i) (a : Sig × Sig × Sig)
    (ha : μ a ≠ 0) : W σs PP e i a = 1 := by
  rw [hg ⟨a, ha⟩ ⟨(σs, σs, σs), hdiag σs⟩]; exact W_diag_self σs PP hPP e i

/-- The noised `e`-th term at `x`. -/
noncomputable def TF (μ : Sig × Sig × Sig → ℝ) (ρ : ℝ) (σs : Sig)
    (PP : Finset ((Fin n → Sig) → ℂ)) (J : Finset (Fin n)) (wJ : Fin n → Sig × Sig × Sig)
    (e : PP × Fin 3 → ℕ) (x : Fin n → Sig × Sig × Sig) : ℂ :=
  ∏ i, ((ρ : ℂ) * W σs PP e i (frz J wJ x i) + (1 - (ρ : ℂ)) * Fe μ σs PP J wJ e i)

theorem TF_good (μ : Sig × Sig × Sig → ℝ) (hμ : IsDist μ) (hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0)
    (ρ : ℝ) (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ)) (hPP : ∀ P ∈ PP, IsProductFunction σs P)
    (J : Finset (Fin n)) (wJ : Fin n → Sig × Sig × Sig) (hwJ : ∀ j ∈ J, μ (wJ j) ≠ 0)
    (e : PP × Fin 3 → ℕ) (hg : ∀ i, good μ σs PP e i) (x : Fin n → Sig × Sig × Sig)
    (hx : ∀ i, μ (x i) ≠ 0) : TF μ ρ σs PP J wJ e x = 1 := by
  unfold TF
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Fe_good μ hμ hdiag σs PP hPP J wJ hwJ e hg i]
  have hfrz : μ (frz J wJ x i) ≠ 0 := by
    unfold frz; split_ifs with hi
    · exact hwJ i hi
    · exact hx i
  rw [W_one_of_good μ hdiag σs PP hPP e i (hg i) _ hfrz]
  ring

theorem TF_bad (M : ℕ) (α γ : ℝ) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (hbias : BiasProp M.factorial α γ) (μ : Sig × Sig × Sig → ℝ) (hμ : IsDist μ)
    (hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0) (hαμ : AtomsAtLeast μ α) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ 0 < orderOf P ∧ orderOf P ≤ M) (D : ℝ)
    (hsoft : SoftRankMuAtLeast μ PP D)
    (J : Finset (Fin n)) (hJ : (J.card : ℝ) ≤ D / 2) (wJ : Fin n → Sig × Sig × Sig)
    (e : PP × Fin 3 → ℕ) (hg : ¬ ∀ i, good μ σs PP e i) (x : Fin n → Sig × Sig × Sig) :
    ‖TF μ ρ σs PP J wJ e x‖ ≤ (ρ + (1 - ρ) * (1 - γ)) ^ (D / 2) := by
  have hPP1 : ∀ P ∈ PP, IsProductFunction σs P := fun P hP => (hPP P hP).1
  set θ := ρ + (1 - ρ) * (1 - γ) with hθ
  have hθ0 : 0 < θ := by nlinarith
  have hθ1 : θ ≤ 1 := by nlinarith
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
  have hfac : ∀ i, ‖(ρ : ℂ) * W σs PP e i (frz J wJ x i) + (1 - (ρ : ℂ)) * Fe μ σs PP J wJ e i‖
      ≤ if i ∈ S then θ else 1 := by
    intro i
    refine (factor_le ρ hρ0 hρ1.le _ _ (W_norm σs PP hPP1 e i _)).trans ?_
    have := hFle i
    split_ifs at this ⊢
    · rw [hθ]; nlinarith
    · nlinarith
  unfold TF
  rw [norm_prod]
  calc ∏ i, ‖(ρ : ℂ) * W σs PP e i (frz J wJ x i) + (1 - (ρ : ℂ)) * Fe μ σs PP J wJ e i‖
      ≤ ∏ i, (if i ∈ S then θ else 1) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hfac i
    _ = θ ^ S.card := by rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    _ ≤ θ ^ (D / 2) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1 hScard

/-! ## Expansion of the noised indicator -/

theorem X_expand (μ : Sig × Sig × Sig → ℝ) (ρ : ℝ) (σs : Sig)
    (PP : Finset ((Fin n → Sig) → ℂ)) (J : Finset (Fin n)) (wJ : Fin n → Sig × Sig × Sig)
    (tg : PP × Fin 3 → ℂ) (C : ℂ) (oneS : (Fin n → Sig × Sig × Sig) → ℂ)
    (hone : ∀ t, oneS t = C * ∑ e ∈ E PP, betaG PP tg e * ∏ i, W σs PP e i (frz J wJ t i))
    (x : Fin n → Sig × Sig × Sig) :
    noiseOp μ ρ n oneS x = C * ∑ e ∈ E PP, betaG PP tg e * TF μ ρ σs PP J wJ e x := by
  have hG : ∀ e : PP × Fin 3 → ℕ, ∑ y, ((∏ i, noiseKernel μ ρ (x i) (y i) : ℝ) : ℂ) *
      ∏ i, W σs PP e i (frz J wJ y i) = TF μ ρ σs PP J wJ e x := by
    intro e
    have := noise_prod μ ρ (fun i b => W σs PP e i (if i ∈ J then wJ i else b)) x
    unfold noiseOp at this
    simp only [frz]
    rw [this]
    unfold TF
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [kernel_sum]
    rfl
  unfold noiseOp
  simp only [hone, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← hG e]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-! ## Assembly -/

theorem main (M : ℕ) (α γ κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (hbias : BiasProp M.factorial α γ) (σs : Sig) (μ : Sig × Sig × Sig → ℝ)
    (PP : Finset ((Fin n → Sig) → ℂ)) (D : ℝ) (J : Finset (Fin n))
    (hμ : IsDist μ) (hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0) (hαμ : AtomsAtLeast μ α)
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ 0 < orderOf P ∧ orderOf P ≤ M)
    (hsoft : SoftRankMuAtLeast μ PP D) (hJ : (J.card : ℝ) ≤ D / 2)
    (wJ : Fin n → Sig × Sig × Sig) (hwJ : ∀ j ∈ J, μ (wJ j) ≠ 0)
    (tg : PP × Fin 3 → ℂ) (htg : ∀ y : PP × Fin 3, ∃ x, y.1.1 x = tg y)
    (oneS : (Fin n → Sig × Sig × Sig) → ℂ)
    (hone : ∀ t, oneS t =
      if ∀ y : PP × Fin 3, y.1.1 (fun i => coord3 y.2 (frz J wJ t i)) = tg y then 1 else 0)
    (μS : ℝ) (hμS : (μS : ℂ) = ∑ t, (tensorPow μ n t : ℂ) * oneS t) :
    l2Norm (tensorPow μ n) (fun t => noiseOp μ (1 - κ) n oneS t - (μS : ℂ)) ≤
      (1 - κ * γ) ^ (D / 2) := by
  have hPP1 : ∀ P ∈ PP, IsProductFunction σs P := fun P hP => (hPP P hP).1
  set ρ : ℝ := 1 - κ with hρ
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ1 : ρ < 1 := by linarith
  have hθ : ρ + (1 - ρ) * (1 - γ) = 1 - κ * γ := by rw [hρ]; ring
  set θ : ℝ := 1 - κ * γ with hθdef
  have hθ0 : 0 < θ := by nlinarith
  set B : ℝ := θ ^ (D / 2) with hB
  have hB0 : 0 ≤ B := Real.rpow_nonneg hθ0.le _
  -- the normalising constant
  set C : ℝ := ∏ y : PP × Fin 3, (1 / (orderOf y.1.1 : ℝ)) with hC
  have hCpos : 0 < C := Finset.prod_pos fun y _ => by
    have := (hPP _ y.1.2).2.1
    positivity
  have hCE : C * ((E PP).card : ℝ) = 1 := by
    rw [hC, E, Fintype.card_piFinset]
    simp only [Finset.card_range]
    push_cast
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun y _ => ?_
    have : (orderOf y.1.1 : ℝ) ≠ 0 := by
      have := (hPP _ y.1.2).2.1; positivity
    field_simp
  have hCc : (C : ℂ) = ∏ y : PP × Fin 3, (1 / (orderOf y.1.1 : ℂ)) := by
    rw [hC]; push_cast; rfl
  have hone' : ∀ t, oneS t =
      (C : ℂ) * ∑ e ∈ E PP, betaG PP tg e * ∏ i, W σs PP e i (frz J wJ t i) := by
    intro t
    rw [hone t, hCc]
    exact ind_G σs PP (fun P hP => ⟨(hPP P hP).1, (hPP P hP).2.1⟩) tg htg _
  have hX := X_expand μ ρ σs PP J wJ tg (C : ℂ) oneS hone'
  -- the constant
  set K : ℂ := (C : ℂ) * ∑ e ∈ (E PP).filter (fun e => ∀ i, good μ σs PP e i), betaG PP tg e
    with hK
  have hpt : ∀ x : Fin n → Sig × Sig × Sig, (∀ i, μ (x i) ≠ 0) →
      ‖noiseOp μ ρ n oneS x - K‖ ≤ B := by
    intro x hx
    rw [hX x, hK, ← Finset.sum_filter_add_sum_filter_not (E PP) (fun e => ∀ i, good μ σs PP e i)]
    have hgood : ∑ e ∈ (E PP).filter (fun e => ∀ i, good μ σs PP e i),
        betaG PP tg e * TF μ ρ σs PP J wJ e x =
        ∑ e ∈ (E PP).filter (fun e => ∀ i, good μ σs PP e i), betaG PP tg e := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [TF_good μ hμ hdiag ρ σs PP hPP1 J wJ hwJ e (Finset.mem_filter.1 he).2 x hx, mul_one]
    rw [hgood, mul_add, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hCpos.le]
    calc C * ‖∑ e ∈ (E PP).filter (fun e => ¬ ∀ i, good μ σs PP e i),
          betaG PP tg e * TF μ ρ σs PP J wJ e x‖
        ≤ C * ∑ e ∈ (E PP).filter (fun e => ¬ ∀ i, good μ σs PP e i), B := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun e he => ?_)) hCpos.le
          rw [norm_mul, norm_betaG PP σs hPP1 tg htg, one_mul, hB, ← hθ]
          exact TF_bad M α γ hγ hγ2 hbias μ hμ hdiag hαμ ρ hρ0 hρ1 σs PP hPP D hsoft J hJ wJ e
            (Finset.mem_filter.1 he).2 x
      _ ≤ C * ∑ e ∈ E PP, B :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun _ _ _ => hB0) hCpos.le
      _ = B := by rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, hCE, one_mul]
  -- mean and Pythagoras
  have hsum1 : ∑ t, tensorPow μ n t = 1 := by
    unfold tensorPow
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun _ _ => hμ.2
  have hmean : ∑ x, (tensorPow μ n x : ℂ) * noiseOp μ ρ n oneS x = (μS : ℂ) := by
    rw [stationary μ hμ.2 ρ oneS, hμS]
  have hpyth := cpx_pyth (tensorPow μ n) hsum1 (noiseOp μ ρ n oneS) (μS : ℂ) K hmean
  have hK2 : ∑ x, tensorPow μ n x * ‖noiseOp μ ρ n oneS x - K‖ ^ 2 ≤ B ^ 2 := by
    calc ∑ x, tensorPow μ n x * ‖noiseOp μ ρ n oneS x - K‖ ^ 2
        ≤ ∑ x, tensorPow μ n x * B ^ 2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          by_cases h0 : tensorPow μ n x = 0
          · rw [h0, zero_mul, zero_mul]
          · have hx : ∀ i, μ (x i) ≠ 0 := by
              intro i; exact (Finset.prod_ne_zero_iff.1 h0) i (Finset.mem_univ i)
            have htp : 0 ≤ tensorPow μ n x := Finset.prod_nonneg fun i _ => hμ.1 _
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) (hpt x hx) 2) htp
      _ = B ^ 2 := by rw [← Finset.sum_mul, hsum1, one_mul]
  unfold l2Norm
  rw [← Real.sqrt_sq hB0]
  exact Real.sqrt_le_sqrt (hpyth.trans hK2)

/-! ## The targets `a`, `b`, `c'` -/

/-- Target of the factor `y`: `a`, `b` or `c'` according to the coordinate. -/
noncomputable def tgt (PP : Finset ((Fin n → Sig) → ℂ)) (a b c' : ((Fin n → Sig) → ℂ) → ℂ)
    (y : PP × Fin 3) : ℂ :=
  if y.2 = 0 then a y.1.1 else if y.2 = 1 then b y.1.1 else c' y.1.1

theorem tgt_range (PP : Finset ((Fin n → Sig) → ℂ)) (a b c' : ((Fin n → Sig) → ℂ) → ℂ)
    (ha : ∀ P ∈ PP, a P ∈ Set.range P) (hb : ∀ P ∈ PP, b P ∈ Set.range P)
    (hc : ∀ P ∈ PP, c' P ∈ Set.range P) (y : PP × Fin 3) : ∃ x, y.1.1 x = tgt PP a b c' y := by
  unfold tgt
  split_ifs
  exacts [ha _ y.1.2, hb _ y.1.2, hc _ y.1.2]

theorem event_iff3 (PP : Finset ((Fin n → Sig) → ℂ)) (J : Finset (Fin n))
    (w w' w'' : Fin n → Sig) (t : Fin n → Sig × Sig × Sig) (a b c' : ((Fin n → Sig) → ℂ) → ℂ) :
    ((∀ P ∈ PP, P (fun i => if i ∈ J then w i else (t i).1) = a P) ∧
      (∀ P ∈ PP, P (fun i => if i ∈ J then w' i else (t i).2.1) = b P) ∧
      (∀ P ∈ PP, P (fun i => if i ∈ J then w'' i else (t i).2.2) = c' P)) ↔
      ∀ y : PP × Fin 3,
        y.1.1 (fun i => coord3 y.2 (frz J (fun i => (w i, w' i, w'' i)) t i)) =
          tgt PP a b c' y := by
  have h0 : (fun i => coord3 0 (frz J (fun i => (w i, w' i, w'' i)) t i)) =
      fun i => if i ∈ J then w i else (t i).1 := by
    funext i; by_cases hi : i ∈ J <;> simp [frz, coord3, hi]
  have h1 : (fun i => coord3 1 (frz J (fun i => (w i, w' i, w'' i)) t i)) =
      fun i => if i ∈ J then w' i else (t i).2.1 := by
    funext i; by_cases hi : i ∈ J <;> simp [frz, coord3, hi]
  have h2 : (fun i => coord3 2 (frz J (fun i => (w i, w' i, w'' i)) t i)) =
      fun i => if i ∈ J then w'' i else (t i).2.2 := by
    funext i; by_cases hi : i ∈ J <;> simp [frz, coord3, hi]
  have t0 : ∀ P : PP, tgt PP a b c' (P, 0) = a P.1 := fun P => by simp [tgt]
  have t1 : ∀ P : PP, tgt PP a b c' (P, 1) = b P.1 := fun P => by simp [tgt]
  have t2 : ∀ P : PP, tgt PP a b c' (P, 2) = c' P.1 := fun P => by simp [tgt]
  constructor
  · rintro ⟨ha, hb, hc⟩ ⟨⟨P, hP⟩, s⟩
    fin_cases s
    · have := ha P hP; rw [← h0] at this; exact this.trans (t0 ⟨P, hP⟩).symm
    · have := hb P hP; rw [← h1] at this; exact this.trans (t1 ⟨P, hP⟩).symm
    · have := hc P hP; rw [← h2] at this; exact this.trans (t2 ⟨P, hP⟩).symm
  · intro h
    refine ⟨fun P hP => ?_, fun P hP => ?_, fun P hP => ?_⟩
    · have := h (⟨P, hP⟩, 0); rw [h0, t0] at this; exact this
    · have := h (⟨P, hP⟩, 1); rw [h1, t1] at this; exact this
    · have := h (⟨P, hP⟩, 2); rw [h2, t2] at this; exact this

end RestrictedAP.Counting.Dev.L38

open Classical

namespace RestrictedAP.Counting

open RestrictedAP.Counting.Dev.L38 RestrictedAP.Counting.Dev.L37
  RestrictedAP.Counting.Dev.Fourier in
theorem chk_lemma_3_8 (M r : ℕ) (α κ : ℝ) (hα : 0 < α) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (μ : Sig × Sig × Sig → ℝ)
        (n : ℕ) (PP : Finset ((Fin n → Sig) → ℂ)) (D : ℤ) (J : Finset (Fin n)),
        IsDist μ → (∀ x : Sig, μ (x, x, x) ≠ 0) → AtomsAtLeast μ α → PP.card = r →
        (∀ P ∈ PP, IsProductFunction σs P ∧ IsDiscrete M P) →
        SoftRankMuAtLeast μ PP (D : ℝ) →
        (J.card : ℝ) ≤ (D : ℝ) / 2 →
        ∀ w w' w'' : Fin n → Sig, (∀ j ∈ J, μ (w j, w' j, w'' j) ≠ 0) →
        ∀ a b c' : ((Fin n → Sig) → ℂ) → ℂ,
          (∀ P ∈ PP, a P ∈ Set.range P) → (∀ P ∈ PP, b P ∈ Set.range P) →
          (∀ P ∈ PP, c' P ∈ Set.range P) →
          let inS : (Fin n → Sig × Sig × Sig) → Prop := fun t =>
            (∀ P ∈ PP, P (fun i => if i ∈ J then w i else (t i).1) = a P) ∧
            (∀ P ∈ PP, P (fun i => if i ∈ J then w' i else (t i).2.1) = b P) ∧
            (∀ P ∈ PP, P (fun i => if i ∈ J then w'' i else (t i).2.2) = c' P)
          let oneS : (Fin n → Sig × Sig × Sig) → ℂ := fun t => if inS t then 1 else 0
          let μS : ℝ := ∑ t : Fin n → Sig × Sig × Sig, if inS t then tensorPow μ n t else 0
          l2Norm (tensorPow μ n) (fun t => noiseOp μ (1 - κ) n oneS t - (μS : ℂ)) ≤
            (2 : ℝ) ^ (-(c * D)) := by
  obtain ⟨γ, hγ, hγ2, hbias⟩ := exists_bias M.factorial (Nat.factorial_pos M) α hα
  have hθ0 : 0 < 1 - κ * γ := by nlinarith
  have hθ1 : 1 - κ * γ < 1 := by nlinarith
  have hlog : Real.logb 2 (1 - κ * γ) < 0 := Real.logb_neg (by norm_num) hθ0 hθ1
  refine ⟨-Real.logb 2 (1 - κ * γ) / 2, by linarith, ?_⟩
  intro Sig _ _ σs μ n PP D J hμ hdiag hαμ _ hPP hsoft hJ w w' w'' hw a b c' ha hb hc
    inS oneS μS
  have hkey : (2 : ℝ) ^ (-(-Real.logb 2 (1 - κ * γ) / 2 * (D : ℝ))) =
      (1 - κ * γ) ^ ((D : ℝ) / 2) := by
    rw [show -(-Real.logb 2 (1 - κ * γ) / 2 * (D : ℝ)) =
        Real.logb 2 (1 - κ * γ) * ((D : ℝ) / 2) by ring,
      Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hθ0]
  rw [hkey]
  have hone : ∀ t, oneS t =
      if ∀ y : PP × Fin 3, y.1.1 (fun i => coord3 y.2
          (frz J (fun i => (w i, w' i, w'' i)) t i)) = tgt PP a b c' y then 1 else 0 := by
    intro t
    show (if inS t then (1 : ℂ) else 0) = _
    by_cases h : inS t
    · rw [if_pos h, if_pos ((event_iff3 PP J w w' w'' t a b c').1 h)]
    · rw [if_neg h, if_neg (mt (event_iff3 PP J w w' w'' t a b c').2 h)]
  have hμS : (μS : ℂ) = ∑ t, (tensorPow μ n t : ℂ) * oneS t := by
    show ((∑ t : Fin n → Sig × Sig × Sig, if inS t then tensorPow μ n t else 0 : ℝ) : ℂ) = _
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    show _ = (tensorPow μ n t : ℂ) * (if inS t then (1 : ℂ) else 0)
    by_cases h : inS t
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero, Complex.ofReal_zero]
  exact main M α γ κ hκ hκ1 hγ hγ2
    (fun μ w h1 h2 h3 h4 a b ha hb hab => hbias μ w h1 h2 h3 h4 a b ha hb hab)
    σs μ PP (D : ℝ) J hμ hdiag hαμ
    (fun P hP => ⟨(hPP P hP).1, (hPP P hP).2.1, (hPP P hP).2.2⟩) hsoft hJ
    (fun i => (w i, w' i, w'' i)) hw (tgt PP a b c') (tgt_range PP a b c' ha hb hc)
    oneS hone μS hμS

end RestrictedAP.Counting
end

theorem solution : type_of% @RestrictedAP.Counting.chk_lemma_3_8 := @RestrictedAP.Counting.chk_lemma_3_8
