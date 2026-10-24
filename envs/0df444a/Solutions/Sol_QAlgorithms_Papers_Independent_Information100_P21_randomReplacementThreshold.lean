-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.randomReplacementThreshold
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T12:28:46.603985+00:00
-- url     : https://prove2.me/submissions/f6c66cde-610e-4a54-b71d-cee7ba143b2e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Carathéodory: the convex hull of a compact set in finite dimension is compact. -/
lemma x8h_hull_cpt {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  set N := Module.finrank ℝ E + 1
  have key : convexHull ℝ s = ⋃ k ∈ Finset.range (N + 1),
      (fun x : (Fin k → ℝ) × (Fin k → E) => ∑ i, x.1 i • x.2 i) ''
        (stdSimplex ℝ (Fin k) ×ˢ Set.univ.pi (fun _ => s)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨ι, _, z, w, hz, hai, hw, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
      have hcard := hai.card_le_finrank_succ
      have hle : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ Module.finrank ℝ E :=
        Submodule.finrank_le _
      let e := Fintype.equivFin ι
      refine Set.mem_iUnion₂.2 ⟨Fintype.card ι, by simp; omega, ⟨w ∘ e.symm, z ∘ e.symm⟩,
        ⟨⟨fun i => (hw _).le, ?_⟩, fun i _ => hz ⟨_, rfl⟩⟩, ?_⟩
      · simp only [Function.comp]; rw [e.symm.sum_comp (fun i => w i)]; exact hw1
      · simp only [Function.comp]; rw [← hx]; exact e.symm.sum_comp (fun i => w i • z i)
    · intro hx
      obtain ⟨k, -, ⟨w, z⟩, ⟨hw, hz⟩, rfl⟩ := Set.mem_iUnion₂.1 hx
      exact (convex_convexHull ℝ s).sum_mem (fun i _ => hw.1 i) hw.2
        (fun i _ => subset_convexHull ℝ s (hz i trivial))
  rw [key]
  refine (Finset.range (N + 1)).isCompact_biUnion fun k _ => ?_
  exact (IsCompact.prod (isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin k)) (isCompact_univ_pi fun _ => hs)).image (by fun_prop)

section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma x8h_psd_proj (v : Vec I) : (proj v).PosSemidef := by
  have : proj v = Matrix.vecMulVec (⇑v) (star ⇑v) := by
    ext x y; simp [proj, QAlgorithms.pureDensity, Matrix.vecMulVec]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

lemma x8h_tr_proj (v : Vec I) : (proj v).trace = ((‖v‖^2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, proj, QAlgorithms.pureDensity, Matrix.of_apply,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_sum, ← EuclideanSpace.norm_sq_eq]

lemma x8h_dens_proj {v : Vec I} (hv : ‖v‖ = 1) : QAlgorithms.IsDensityMatrix (proj v) :=
  ⟨x8h_psd_proj v, by rw [x8h_tr_proj, hv]; simp⟩

/-- Normalization of a nonzero ket. -/
lemma x8h_proj_norm (u : Vec I) (hu : u ≠ 0) :
    ‖((‖u‖⁻¹ : ℝ) : ℂ) • u‖ = 1 ∧ proj u = ((‖u‖^2 : ℝ) : ℂ) • proj (((‖u‖⁻¹ : ℝ) : ℂ) • u) := by
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  refine ⟨by rw [norm_smul]; simp [hn], ?_⟩
  ext a b
  simp only [proj, QAlgorithms.pureDensity, Matrix.of_apply, Matrix.smul_apply, PiLp.smul_apply,
    smul_eq_mul, map_mul, Complex.conj_ofReal]
  have : ((‖u‖ : ℂ)) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

def x8Pure (I : Type*) [Fintype I] : Set (Op I) := {X | ∃ v : Vec I, ‖v‖ = 1 ∧ X = proj v}
def x8Dens (I : Type*) [Fintype I] : Set (Op I) := {X | QAlgorithms.IsDensityMatrix X}

lemma x8h_proj_cont : Continuous (fun v : Vec I => proj v) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [proj, QAlgorithms.pureDensity, Matrix.of_apply]
  fun_prop

lemma x8h_pure_cpt : IsCompact (x8Pure I) := by
  have : x8Pure I = (fun v : Vec I => proj v) '' Metric.sphere 0 1 := by
    ext X; simp only [x8Pure, Set.mem_setOf_eq, Set.mem_image, mem_sphere_iff_norm, sub_zero]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
  rw [this]; exact (isCompact_sphere 0 1).image x8h_proj_cont

lemma x8h_dens_convex : Convex ℝ (x8Dens I) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨(hX.1.smul (by exact_mod_cast ha)).add (hY.1.smul (by exact_mod_cast hb)), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX.2, hY.2]
  simp only [smul_eq_mul, mul_one, Complex.real_smul, Complex.ofReal_one]
  exact_mod_cast hab

lemma x8h_smul_real {K : Type*} (r : ℝ) (M : Op K) : ((r : ℂ) • M) = r • M := by
  ext x y; simp [Complex.real_smul]

lemma x8h_dens_eq [Nonempty I] : x8Dens I = convexHull ℝ (x8Pure I) := by
  apply Set.Subset.antisymm
  · intro X hX
    obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX.1
    let V : Fin m → Vec I := fun k => WithLp.toLp 2 (v k)
    let e : Vec I := EuclideanSpace.single (Classical.arbitrary I) 1
    let u : Fin m → Vec I := fun k => if V k = 0 then e else ((‖V k‖⁻¹ : ℝ) : ℂ) • V k
    have hu : ∀ k, ‖u k‖ = 1 := by
      intro k; simp only [u]; split_ifs with h
      · simp [e]
      · exact (x8h_proj_norm (V k) h).1
    have hk : ∀ k, Matrix.vecMulVec (v k) (star (v k)) = ((‖V k‖^2 : ℝ) : ℂ) • proj (u k) := by
      intro k
      have hpv : Matrix.vecMulVec (v k) (star (v k)) = proj (V k) := by
        ext a b; simp [proj, QAlgorithms.pureDensity, Matrix.vecMulVec, V]
      rw [hpv]
      by_cases h : V k = 0
      · rw [h]; ext a b; simp [proj, QAlgorithms.pureDensity]
      · simp only [u, if_neg h]; exact (x8h_proj_norm (V k) h).2
    have hX' : X = ∑ k, (‖V k‖^2) • proj (u k) := by
      rw [hv]; refine Finset.sum_congr rfl fun k _ => ?_; rw [hk, x8h_smul_real]
    have h1 : ∑ k, ‖V k‖^2 = 1 := by
      have := hX.2
      rw [hX', Matrix.trace_sum] at this
      simp only [Matrix.trace_smul, x8h_tr_proj, hu, one_pow, Complex.ofReal_one, smul_eq_mul,
        mul_one, Complex.real_smul] at this
      exact_mod_cast this
    rw [hX']
    exact (convex_convexHull ℝ _).sum_mem (fun k _ => by positivity) h1
      (fun k _ => subset_convexHull ℝ _ ⟨u k, hu k, rfl⟩)
  · refine convexHull_min ?_ x8h_dens_convex
    rintro X ⟨v, hv, rfl⟩; exact x8h_dens_proj hv

lemma x8h_dens_cpt [Nonempty I] : IsCompact (x8Dens I) := by
  rw [x8h_dens_eq]; exact x8h_hull_cpt x8h_pure_cpt

end

section
variable {I J : Type*} [Fintype I] [Fintype J]
open QAlgorithms.Entanglement

lemma x8sp_zero : IsSeparablePositive (0 : Op (I × J)) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
  · intro j; exact Fin.elim0 j
  · intro j; exact Fin.elim0 j
  · simp

lemma x8sp_add {X Y : Op (I × J)} (hX : IsSeparablePositive X) (hY : IsSeparablePositive Y) :
    IsSeparablePositive (X + Y) := by
  obtain ⟨q1, w1, A1, B1, hw1, hAB1, rfl⟩ := hX
  obtain ⟨q2, w2, A2, B2, hw2, hAB2, rfl⟩ := hY
  refine ⟨q1 + q2, Fin.append w1 w2, Fin.append A1 A2, Fin.append B1 B2, ?_, ?_, ?_⟩
  · intro j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [hw1]
    · simp [hw2]
  · intro j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [hAB1]
    · simp [hAB2]
  · rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]

lemma x8sp_smul {X : Op (I × J)} {c : ℝ} (hc : 0 ≤ c) (hX : IsSeparablePositive X) :
    IsSeparablePositive ((c : ℂ) • X) := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := hX
  refine ⟨q, fun j => c * w j, A, B, fun j => mul_nonneg hc (hw j), hAB, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]; push_cast; rfl

lemma x8sp_kron {A : Op I} {B : Op J} (hA : QAlgorithms.IsDensityMatrix A)
    (hB : QAlgorithms.IsDensityMatrix B) : IsSeparablePositive (Matrix.kronecker A B) := by
  refine ⟨1, fun _ => 1, fun _ => A, fun _ => B, fun _ => zero_le_one, fun _ => ⟨hA, hB⟩, ?_⟩
  simp

lemma x8sp_sum {T : Type*} [Fintype T] (f : T → Op (I × J)) (h : ∀ t, IsSeparablePositive (f t)) :
    IsSeparablePositive (∑ t, f t) :=
  Finset.sum_induction _ _ (fun _ _ => x8sp_add) x8sp_zero (fun t _ => h t)

lemma x8sp_proj (u : Vec I) (v : Vec J) :
    IsSeparablePositive (Matrix.kronecker (proj u) (proj v)) := by
  by_cases hu : u = 0
  · rw [hu]; convert (x8sp_zero (I := I) (J := J)) using 1
    ext a b; simp [proj, QAlgorithms.pureDensity, Matrix.kronecker, Matrix.kroneckerMap_apply]
  by_cases hv : v = 0
  · rw [hv]; convert (x8sp_zero (I := I) (J := J)) using 1
    ext a b; simp [proj, QAlgorithms.pureDensity, Matrix.kronecker, Matrix.kroneckerMap_apply]
  obtain ⟨hu1, hu2⟩ := x8h_proj_norm u hu
  obtain ⟨hv1, hv2⟩ := x8h_proj_norm v hv
  rw [hu2, hv2, Matrix.kronecker, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, ← Complex.ofReal_mul]
  exact x8sp_smul (by positivity) (x8sp_kron (x8h_dens_proj hu1) (x8h_dens_proj hv1))

lemma x8sp_tr {X : Op (I × J)} (hX : IsSeparablePositive X) :
    ∃ q : ℕ, ∃ w : Fin q → ℝ, ∃ A : Fin q → Op I, ∃ B : Fin q → Op J,
      (∀ j, 0 ≤ w j) ∧ (∀ j, QAlgorithms.IsDensityMatrix (A j) ∧ QAlgorithms.IsDensityMatrix (B j)) ∧
      X = ∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j) ∧ X.trace = ((∑ j, w j : ℝ) : ℂ) := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := hX
  refine ⟨q, w, A, B, hw, hAB, rfl, ?_⟩
  rw [Matrix.trace_sum]; push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.trace_smul, Matrix.kronecker, Matrix.trace_kronecker, (hAB j).1.2, (hAB j).2.2]; simp

def x8Prod (I J : Type*) [Fintype I] [Fintype J] : Set (Op (I × J)) :=
  {X | ∃ A ∈ x8Dens I, ∃ B ∈ x8Dens J, X = Matrix.kronecker A B}

lemma x8h_prod_cpt [Nonempty I] [Nonempty J] : IsCompact (x8Prod I J) := by
  have : x8Prod I J = (fun p : Op I × Op J => Matrix.kronecker p.1 p.2) '' (x8Dens I ×ˢ x8Dens J) := by
    ext X; simp only [x8Prod, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · rintro ⟨A, hA, B, hB, rfl⟩; exact ⟨A, B, ⟨hA, hB⟩, rfl⟩
    · rintro ⟨A, B, ⟨hA, hB⟩, rfl⟩; exact ⟨A, hA, B, hB, rfl⟩
  rw [this]
  refine (x8h_dens_cpt.prod x8h_dens_cpt).image ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
  fun_prop

lemma x8h_sep_eq [Nonempty I] [Nonempty J] :
    {X : Op (I × J) | sep X} = convexHull ℝ (x8Prod I J) := by
  apply Set.Subset.antisymm
  · rintro X ⟨hX, htr⟩
    obtain ⟨q, w, A, B, hw, hAB, rfl, htr'⟩ := x8sp_tr hX
    rw [htr'] at htr
    have h1 : ∑ j, w j = 1 := by exact_mod_cast htr
    have : ∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j) = ∑ j, w j • Matrix.kronecker (A j) (B j) := by
      refine Finset.sum_congr rfl fun j _ => ?_; rw [x8h_smul_real]
    rw [this]
    exact (convex_convexHull ℝ _).sum_mem (fun j _ => hw j) h1
      (fun j _ => subset_convexHull ℝ _ ⟨A j, (hAB j).1, B j, (hAB j).2, rfl⟩)
  · refine convexHull_min ?_ ?_
    · rintro X ⟨A, hA, B, hB, rfl⟩
      refine ⟨x8sp_kron hA hB, ?_⟩
      rw [Matrix.kronecker, Matrix.trace_kronecker, hA.2, hB.2, one_mul]
    · intro X hX Y hY a b ha hb hab
      refine ⟨?_, ?_⟩
      · rw [← x8h_smul_real, ← x8h_smul_real]
        exact x8sp_add (x8sp_smul ha hX.1) (x8sp_smul hb hY.1)
      · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX.2, hY.2]
        simp only [smul_eq_mul, mul_one, Complex.real_smul, Complex.ofReal_one]
        exact_mod_cast hab

lemma x8h_sep_cpt [Nonempty I] [Nonempty J] : IsCompact {X : Op (I × J) | sep X} := by
  rw [x8h_sep_eq]; exact x8h_hull_cpt x8h_prod_cpt

end

section
variable {I J : Type*} [Fintype I] [Fintype J]
open QAlgorithms.Entanglement

lemma x8d_pol (α β γ δ : ℂ) :
    ∑ k : Fin 4, Complex.I ^ (k : ℕ) *
      ((α + Complex.I ^ (k : ℕ) * β) * conj (γ + Complex.I ^ (k : ℕ) * δ)) = 4 * α * conj δ := by
  simp [Fin.sum_univ_four, pow_succ, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]
  ring

abbrev x8T (I J : Type*) := I × I × J × J × Fin 4 × Fin 4

def x8U (t : x8T I J) : Vec I :=
  EuclideanSpace.single t.1 1 + (Complex.I ^ (t.2.2.2.2.1 : ℕ)) • EuclideanSpace.single t.2.1 1
def x8V (t : x8T I J) : Vec J :=
  EuclideanSpace.single t.2.2.1 1 + (Complex.I ^ (t.2.2.2.2.2 : ℕ)) • EuclideanSpace.single t.2.2.2.1 1
def x8M (t : x8T I J) : Op (I × J) := proj (tensor (x8U t) (x8V t))
def x8C (ρ : Op (I × J)) (t : x8T I J) : ℂ :=
  ρ (t.1, t.2.2.1) (t.2.1, t.2.2.2.1) * (1/16) * Complex.I ^ (t.2.2.2.2.1 : ℕ) *
    Complex.I ^ (t.2.2.2.2.2 : ℕ)

lemma x8M_apply (t : x8T I J) (x y : I × J) :
    x8M t x y = (x8U t x.1 * conj (x8U t y.1)) * (x8V t x.2 * conj (x8V t y.2)) := by
  simp only [x8M, proj, QAlgorithms.pureDensity, tensor, Matrix.of_apply, map_mul]; ring

lemma x8U_apply (t : x8T I J) (i : I) :
    x8U t i = (if i = t.1 then 1 else 0) + Complex.I ^ (t.2.2.2.2.1 : ℕ) * (if i = t.2.1 then 1 else 0) := by
  simp [x8U]
lemma x8V_apply (t : x8T I J) (i : J) :
    x8V t i = (if i = t.2.2.1 then 1 else 0) +
      Complex.I ^ (t.2.2.2.2.2 : ℕ) * (if i = t.2.2.2.1 then 1 else 0) := by
  simp [x8V]

lemma x8d_inner (ρ : Op (I × J)) (a a' : I) (b b' : J) (x y : I × J) :
    ∑ k : Fin 4, ∑ l : Fin 4, x8C ρ (a, a', b, b', k, l) * x8M (a, a', b, b', k, l) x y =
      ρ (a, b) (a', b') * ((if x.1 = a then 1 else 0) * conj (if y.1 = a' then 1 else 0)) *
        ((if x.2 = b then 1 else 0) * conj (if y.2 = b' then 1 else 0)) := by
  set A : Fin 4 → ℂ := fun k => Complex.I ^ (k : ℕ) *
    (((if x.1 = a then 1 else 0) + Complex.I ^ (k : ℕ) * (if x.1 = a' then 1 else 0)) *
        conj ((if y.1 = a then 1 else 0) + Complex.I ^ (k : ℕ) * (if y.1 = a' then 1 else 0))) with hA
  set B : Fin 4 → ℂ := fun l => Complex.I ^ (l : ℕ) *
    (((if x.2 = b then 1 else 0) + Complex.I ^ (l : ℕ) * (if x.2 = b' then 1 else 0)) *
        conj ((if y.2 = b then 1 else 0) + Complex.I ^ (l : ℕ) * (if y.2 = b' then 1 else 0))) with hB
  have h : ∀ k l : Fin 4, x8C ρ (a, a', b, b', k, l) * x8M (a, a', b, b', k, l) x y =
      ρ (a, b) (a', b') * (1/16) * (A k * B l) := by
    intro k l
    rw [x8M_apply, x8U_apply, x8U_apply, x8V_apply, x8V_apply, x8C, hA, hB]
    ring
  have hsA : ∑ k, A k = 4 * (if x.1 = a then 1 else 0) * conj (if y.1 = a' then 1 else 0) :=
    x8d_pol _ _ _ _
  have hsB : ∑ l, B l = 4 * (if x.2 = b then 1 else 0) * conj (if y.2 = b' then 1 else 0) :=
    x8d_pol _ _ _ _
  calc ∑ k : Fin 4, ∑ l : Fin 4, x8C ρ (a, a', b, b', k, l) * x8M (a, a', b, b', k, l) x y
      = ∑ k : Fin 4, ∑ l : Fin 4, ρ (a, b) (a', b') * (1/16) * (A k * B l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => h k l
    _ = ρ (a, b) (a', b') * (1/16) * ((∑ k, A k) * (∑ l, B l)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]; simp_rw [Finset.mul_sum]
    _ = _ := by rw [hsA, hsB]; ring

lemma x8d_decC (ρ : Op (I × J)) (x y : I × J) : ρ x y = ∑ t, x8C ρ t * x8M t x y := by
  simp only [Fintype.sum_prod_type]
  simp_rw [x8d_inner]
  obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma x8d_dec {ρ : Op (I × J)} (hρ : ρ.IsHermitian) :
    ρ = ∑ t, (((x8C ρ t).re : ℝ) : ℂ) • x8M t := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have h1 := x8d_decC ρ a b
  have h2 := x8d_decC ρ b a
  have hab : ρ a b = conj (ρ b a) := by
    have := hρ.apply a b; rw [← this]; simp
  have hc : ∀ t, conj (x8C ρ t * x8M t b a) = conj (x8C ρ t) * x8M t a b := by
    intro t; rw [map_mul, x8M_apply, x8M_apply]
    simp only [map_mul, Complex.conj_conj]; ring
  have : ρ a b = (ρ a b + conj (ρ b a)) / 2 := by rw [← hab]; ring
  rw [this, h1, h2, map_sum]
  simp_rw [hc, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← add_mul, Complex.add_conj]
  push_cast; ring

lemma x8M_sep (t : x8T I J) : IsSeparablePositive (x8M t) := by
  have : x8M t = Matrix.kronecker (proj (x8U t)) (proj (x8V t)) := by
    ext x y; rw [x8M_apply]; simp [proj, QAlgorithms.pureDensity, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
  rw [this]; exact x8sp_proj _ _

def x8nM (t : x8T I J) : ℝ := ‖tensor (x8U t) (x8V t)‖ ^ 2

lemma x8M_tr (t : x8T I J) : (x8M t).trace = ((x8nM t : ℝ) : ℂ) := x8h_tr_proj _

lemma x8c_comb (w : x8T I J → ℝ) (hw : ∀ t, 0 ≤ w t) :
    IsSeparablePositive (∑ t, ((w t : ℝ) : ℂ) • x8M t) ∧
    (∑ t, ((w t : ℝ) : ℂ) • x8M t).PosSemidef ∧
    (∑ t, ((w t : ℝ) : ℂ) • x8M t).trace = ((∑ t, w t * x8nM t : ℝ) : ℂ) := by
  refine ⟨x8sp_sum _ fun t => x8sp_smul (hw t) (x8M_sep t),
    Matrix.posSemidef_sum _ fun t _ => (x8h_psd_proj _).smul (by exact_mod_cast hw t), ?_⟩
  rw [Matrix.trace_sum]; push_cast
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.trace_smul, x8M_tr, smul_eq_mul]

lemma x8r_feas {ρ : Op (I × J)} (hρ : QAlgorithms.IsDensityMatrix ρ) :
    ∃ s : ℝ, 0 ≤ s ∧ ∃ ω : Op (I × J), QAlgorithms.IsDensityMatrix ω ∧ sep ω ∧
      sep (mix ρ ω s) := by
  obtain ⟨r, hr⟩ : ∃ r : x8T I J → ℝ, ρ = ∑ t, ((r t : ℝ) : ℂ) • x8M t := ⟨_, x8d_dec hρ.1.1⟩
  have htr : ∑ t, r t * x8nM t = 1 := by
    have h := hρ.2
    rw [hr, Matrix.trace_sum] at h
    simp only [Matrix.trace_smul, x8M_tr, smul_eq_mul] at h
    exact_mod_cast h
  set p : x8T I J → ℝ := fun t => max (r t) 0 with hp
  set q : x8T I J → ℝ := fun t => max (-r t) 0 with hq
  have hp0 : ∀ t, 0 ≤ p t := fun t => le_max_right _ _
  have hq0 : ∀ t, 0 ≤ q t := fun t => le_max_right _ _
  have hrpq : ∀ t, r t = p t - q t := by
    intro t; simp only [hp, hq]
    rcases le_total (r t) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hn0 : ∀ t : x8T I J, 0 ≤ x8nM t := fun t => by unfold x8nM; positivity
  set S := ∑ t, q t * x8nM t with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun t _ => mul_nonneg (hq0 t) (hn0 t)
  have hpS : ∑ t, p t * x8nM t = 1 + S := by
    rw [← htr, hS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hrpq]; ring
  have hw0 : ∀ t, 0 ≤ (p t + q t) / (1 + 2 * S) := fun t =>
    div_nonneg (add_nonneg (hp0 t) (hq0 t)) (by linarith)
  have hw1 : ∑ t, (p t + q t) / (1 + 2 * S) * x8nM t = 1 := by
    have e : ∀ t, (p t + q t) / (1 + 2 * S) * x8nM t =
        (p t * x8nM t + q t * x8nM t) / (1 + 2 * S) := fun t => by ring
    simp_rw [e]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hpS, ← hS]
    field_simp; ring
  have hv0 : ∀ t, 0 ≤ p t / (1 + S) := fun t => div_nonneg (hp0 t) (by linarith)
  have hv1 : ∑ t, p t / (1 + S) * x8nM t = 1 := by
    have e : ∀ t, p t / (1 + S) * x8nM t = p t * x8nM t / (1 + S) := fun t => by ring
    simp_rw [e]
    rw [← Finset.sum_div, hpS]
    field_simp
  obtain ⟨hωs, hωp, hωt⟩ := x8c_comb _ hw0
  obtain ⟨hms, -, hmt⟩ := x8c_comb _ hv0
  refine ⟨1 + 2 * S, by linarith, _, ⟨hωp, by rw [hωt, hw1]; simp⟩, ⟨hωs, by rw [hωt, hw1]; simp⟩, ?_⟩
  have : mix ρ (∑ t, (((p t + q t) / (1 + 2 * S) : ℝ) : ℂ) • x8M t)
      (1 + 2 * S) = ∑ t, ((p t / (1 + S) : ℝ) : ℂ) • x8M t := by
    rw [mix, hr, Finset.smul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_smul, ← add_smul, smul_smul]
    congr 1
    have key : (1 + (1 + 2 * S))⁻¹ * (r t + (1 + 2 * S) * ((p t + q t) / (1 + 2 * S))) =
        p t / (1 + S) := by
      rw [hrpq]; field_simp; ring
    rw [← key]; push_cast; ring
  rw [this]
  exact ⟨hms, by rw [hmt, hv1]; simp⟩

end

section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma x8r_mix_cont (ρ : Op (I × J)) :
    ContinuousOn (fun x : ℝ × Op (I × J) => mix ρ x.2 x.1) (Set.Ici 0 ×ˢ Set.univ) := by
  unfold mix
  have h1 : ContinuousOn (fun x : ℝ × Op (I × J) => (((1 + x.1)⁻¹ : ℝ) : ℂ))
      (Set.Ici 0 ×ˢ Set.univ) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    have : 0 ≤ x.1 := hx.1
    positivity
  have h2 : Continuous (fun x : ℝ × Op (I × J) => ρ + (x.1 : ℂ) • x.2) := by fun_prop
  exact h1.smul h2.continuousOn

lemma x8r_attain [Nonempty I] [Nonempty J] {ρ : Op (I × J)} (hρ : QAlgorithms.IsDensityMatrix ρ)
    (std : Bool) :
    0 ≤ robust {X : Op (I × J) | sep X} std ρ ∧ ∃ ω : Op (I × J), QAlgorithms.IsDensityMatrix ω ∧
      (std = true → sep ω) ∧ sep (mix ρ ω (robust {X : Op (I × J) | sep X} std ρ)) := by
  obtain ⟨s0, hs0, ω0, hω0d, hω0s, hm0⟩ := x8r_feas hρ
  set K : Set (Op (I × J)) := {X | sep X} with hKdef
  have hK : IsCompact K := x8h_sep_cpt
  set D' : Set (Op (I × J)) := {ω | ω ∈ x8Dens (I × J) ∧ (std = true → ω ∈ K)} with hD'
  have hD'c : IsCompact D' := by
    cases std
    · have : D' = x8Dens (I × J) := by ext ω; simp [hD']
      rw [this]; exact x8h_dens_cpt
    · have : D' = x8Dens (I × J) ∩ K := by ext ω; simp [hD']
      rw [this]; exact x8h_dens_cpt.inter_right hK.isClosed
  set base : Set (ℝ × Op (I × J)) := Set.Icc 0 s0 ×ˢ D' with hbase
  have hbc : IsCompact base := isCompact_Icc.prod hD'c
  set G := base ∩ (fun x : ℝ × Op (I × J) => mix ρ x.2 x.1) ⁻¹' K with hG
  have hGcl : IsClosed G :=
    ((x8r_mix_cont ρ).mono (Set.prod_mono Set.Icc_subset_Ici_self (Set.subset_univ _))).preimage_isClosed_of_isClosed
      hbc.isClosed hK.isClosed
  have hGc : IsCompact G := hbc.of_isClosed_subset hGcl Set.inter_subset_left
  have hGne : G.Nonempty := ⟨(s0, ω0), ⟨⟨⟨hs0, le_rfl⟩, hω0d, fun _ => hω0s⟩, hm0⟩⟩
  obtain ⟨x, hxG, hmin⟩ := hGc.exists_isMinOn hGne continuous_fst.continuousOn
  have hR : robust K std ρ = x.1 := by
    unfold robust
    apply le_antisymm
    · exact csInf_le ⟨0, fun s hs => hs.1⟩
        ⟨hxG.1.1.1, x.2, hxG.1.2.1, hxG.1.2.2, hxG.2⟩
    · refine le_csInf ⟨s0, hs0, ω0, hω0d, fun _ => hω0s, hm0⟩ ?_
      rintro s ⟨hs, ω, hω, hωK, hm⟩
      by_cases h : s ≤ s0
      · exact hmin (show (s, ω) ∈ G from ⟨⟨⟨hs, h⟩, hω, hωK⟩, hm⟩)
      · exact le_trans hxG.1.1.2 (le_of_lt (not_le.mp h))
  rw [hR]
  exact ⟨hxG.1.1.1, x.2, hxG.1.2.1, hxG.1.2.2, hxG.2⟩

theorem x8_main [Nonempty I] [Nonempty J]
  (rho : Op (I × J)) (h : QAlgorithms.IsDensityMatrix rho) (standard : Bool) :
  let R := robust {X : Op (I × J) | sep X} standard rho
  IsLeast {p : ℝ | 0≤p ∧ p≤1 ∧ ∃ omega : Op (I × J),
    QAlgorithms.IsDensityMatrix omega ∧ (standard=true → sep omega) ∧
      sep ((1-p:ℂ) • rho+(p:ℂ) • omega)} (R/(1+R)) ∧
  (∀ (s : ℝ) (omega : Op (I × J)), 0 ≤ s →
    mix rho omega s=(1-s/(1+s):ℂ) • rho+(s/(1+s):ℂ) • omega) := by
  intro R
  have hmixid : ∀ (s : ℝ) (omega : Op (I × J)), 0 ≤ s →
      mix rho omega s=(1-s/(1+s):ℂ) • rho+(s/(1+s):ℂ) • omega := by
    intro s ω hs
    have h1 : (1 + (s:ℂ)) ≠ 0 := by exact_mod_cast (show (1 + s : ℝ) ≠ 0 by linarith)
    unfold mix
    ext a b
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  obtain ⟨hR0, ω, hωd, hωK, hm⟩ := x8r_attain h standard
  refine ⟨⟨⟨by positivity, (div_le_one (by positivity)).mpr (by linarith), ω, hωd, hωK, ?_⟩, ?_⟩,
    hmixid⟩
  · rw [hmixid R ω hR0] at hm
    convert hm using 3 <;> push_cast <;> ring
  · rintro p ⟨hp0, hp1, ω', hω'd, hω'K, hsep⟩
    rcases eq_or_lt_of_le hp1 with hp | hp
    · rw [hp]; exact (div_le_one (by positivity)).mpr (by linarith)
    · have h1p : 0 < 1 - p := by linarith
      have hfeas : p / (1 - p) ∈ {s : ℝ | 0 ≤ s ∧ ∃ omega : Op (I × J),
          QAlgorithms.IsDensityMatrix omega ∧ (standard = true → omega ∈ {X : Op (I × J) | sep X}) ∧
            mix rho omega s ∈ {X : Op (I × J) | sep X}} := by
        refine ⟨div_nonneg hp0 h1p.le, ω', hω'd, hω'K, ?_⟩
        show sep (mix rho ω' (p / (1 - p)))
        rw [hmixid _ ω' (div_nonneg hp0 h1p.le)]
        have e : ((p / (1 - p) : ℝ) : ℂ) / (1 + ((p / (1 - p) : ℝ) : ℂ)) = (p : ℂ) := by
          have : (1 - (p:ℂ)) ≠ 0 := by exact_mod_cast h1p.ne'
          push_cast; field_simp; ring
        rw [e]; exact hsep
      have hRle : R ≤ p / (1 - p) := csInf_le ⟨0, fun s hs => hs.1⟩ hfeas
      rw [div_le_iff₀ (by positivity)]
      rw [le_div_iff₀ h1p] at hRle
      nlinarith

end

end QAlgorithms.Papers.Independent.Information100.P21

open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  (rho : Op (I × J)) (h : QAlgorithms.IsDensityMatrix rho) (standard : Bool) :
  let R := robust {X : Op (I × J) | sep X} standard rho
  IsLeast {p : ℝ | 0≤p ∧ p≤1 ∧ ∃ omega : Op (I × J),
    QAlgorithms.IsDensityMatrix omega ∧ (standard=true → sep omega) ∧
      sep ((1-p:ℂ) • rho+(p:ℂ) • omega)} (R/(1+R)) ∧
  (∀ (s : ℝ) (omega : Op (I × J)), 0 ≤ s →
    mix rho omega s=(1-s/(1+s):ℂ) • rho+(s/(1+s):ℂ) • omega) :=
  x8_main rho h standard
