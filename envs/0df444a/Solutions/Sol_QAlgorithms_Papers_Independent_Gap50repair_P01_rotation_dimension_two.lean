-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.rotation_dimension_two
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:59:30.672457+00:00
-- url     : https://prove2.me/submissions/75f693b6-2c62-4b4c-8edc-487d82d5b61a

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

namespace X4CZK

attribute [local instance] Classical.propDecidable

abbrev i0 : Coord 1 := Sum.inl 0
abbrev j0 : Coord 1 := Sum.inr 0

lemma symp_iff (A : GroupedRealMatrix 1) :
    IsSymplectic A ↔ A i0 i0 * A j0 j0 - A i0 j0 * A j0 i0 = 1 := by
  unfold IsSymplectic canonicalJ
  constructor
  · intro h
    have := congrFun (congrFun h i0) j0
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks] at this
    linarith
  · intro h
    ext x y
    rcases x with x | x <;> rcases y with y | y <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Fin.fin_one_eq_zero x,
        Fin.fin_one_eq_zero y] <;> linarith

lemma det_sub (A : GroupedRealMatrix 1) :
    (A - 1).det = (A i0 i0 - 1) * (A j0 j0 - 1) - A i0 j0 * A j0 i0 := by
  rw [← Matrix.det_reindex_self finSumFinEquiv, Matrix.det_fin_two]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  have h0 : (finSumFinEquiv.symm (0 : Fin 2) : Fin 1 ⊕ Fin 1) = i0 := rfl
  have h1 : (finSumFinEquiv.symm (1 : Fin 2) : Fin 1 ⊕ Fin 1) = j0 := rfl
  rw [h0, h1]


def mk (a b c d : ℝ) : GroupedRealMatrix 1 :=
  fun x y => Sum.elim (fun _ => Sum.elim (fun _ => a) (fun _ => b) y)
    (fun _ => Sum.elim (fun _ => c) (fun _ => d) y) x

lemma mk_cont {X : Type*} [TopologicalSpace X] {a b c d : X → ℝ} (ha : Continuous a)
    (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous (fun p => mk (a p) (b p) (c p) (d p)) := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  rcases x with x | x <;> rcases y with y | y <;> simpa [mk]

lemma eq_mk (A : GroupedRealMatrix 1) : A = mk (A i0 i0) (A i0 j0) (A j0 i0) (A j0 j0) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [mk, Fin.fin_one_eq_zero x, Fin.fin_one_eq_zero y]

@[simp] lemma mk00 (a b c d : ℝ) : mk a b c d i0 i0 = a := rfl
@[simp] lemma mk01 (a b c d : ℝ) : mk a b c d i0 j0 = b := rfl
@[simp] lemma mk10 (a b c d : ℝ) : mk a b c d j0 i0 = c := rfl
@[simp] lemma mk11 (a b c d : ℝ) : mk a b c d j0 j0 = d := rfl

/-- parametrisation of `P` (trace < 2). -/
def rP (p : ℝ × ℝ × ℝ) : ℝ := Real.sqrt (1 + p.1^2 + p.2.1^2)
def bP (p : ℝ × ℝ × ℝ) : ℝ := Real.arccos (-1 / rP p)
def phiP (p : ℝ × ℝ × ℝ) : GroupedRealMatrix 1 :=
  let r := rP p
  let φ := p.2.2 * bP p
  mk (-r * Real.cos φ + p.1) (-r * Real.sin φ + p.2.1) (p.2.1 + r * Real.sin φ) (-r * Real.cos φ - p.1)

lemma rP_pos (p : ℝ × ℝ × ℝ) : 1 ≤ rP p := by
  unfold rP
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  nlinarith [sq_nonneg p.1, sq_nonneg p.2.1]

lemma rP_sq (p : ℝ × ℝ × ℝ) : rP p ^ 2 = 1 + p.1^2 + p.2.1^2 := by
  unfold rP; rw [Real.sq_sqrt (by positivity)]

lemma phiP_cont : Continuous phiP := by
  have hr : Continuous rP := by unfold rP; fun_prop
  have hb : Continuous bP := by
    unfold bP
    refine Real.continuous_arccos.comp ?_
    exact Continuous.div continuous_const hr (fun p => by linarith [rP_pos p])
  unfold phiP
  apply mk_cont <;> fun_prop

/-- parametrisation of `M` (trace > 2). -/
def phiM (p : ℝ × ℝ × ℝ) : GroupedRealMatrix 1 :=
  let s := p.1
  let y := p.2.1
  let ρ := Real.sqrt (y^2 + s^2 - 1)
  mk (s + ρ * Real.cos p.2.2) (y + ρ * Real.sin p.2.2) (ρ * Real.sin p.2.2 - y) (s - ρ * Real.cos p.2.2)

lemma phiM_cont : Continuous phiM := by
  unfold phiM; apply mk_cont <;> fun_prop


lemma symp_mk (a b c d : ℝ) : IsSymplectic (mk a b c d) ↔ a * d - b * c = 1 := by
  rw [symp_iff]; simp

lemma det_mk (a b c d : ℝ) : (mk a b c d - 1).det = (a - 1) * (d - 1) - b * c := by
  rw [det_sub]; simp

lemma bP_bounds (p : ℝ × ℝ × ℝ) : 0 < bP p ∧ bP p ≤ Real.pi ∧ Real.cos (bP p) = -1 / rP p := by
  have h1 := rP_pos p
  have hr : 0 < rP p := by linarith
  refine ⟨Real.arccos_pos.2 ?_, Real.arccos_le_pi _, Real.cos_arccos ?_ ?_⟩
  · have : 0 < 1 / rP p := by positivity
    rw [neg_div]; linarith
  · rw [neg_div, neg_le_neg_iff, div_le_one hr]; exact h1
  · rw [neg_div]; have : 0 < 1 / rP p := by positivity
    linarith

lemma phiP_mem (p : ℝ × ℝ × ℝ) (ht : p.2.2 ∈ Set.Ioo (-1 : ℝ) 1) :
    IsSymplectic (phiP p) ∧ 0 < (phiP p - 1).det := by
  obtain ⟨hb0, hbpi, hcb⟩ := bP_bounds p
  have h1 := rP_pos p
  have hr : 0 < rP p := by linarith
  have hsq := rP_sq p
  have hcs := Real.sin_sq_add_cos_sq (p.2.2 * bP p)
  unfold phiP
  simp only [symp_mk, det_mk]
  refine ⟨by nlinarith, ?_⟩
  have hab : |p.2.2 * bP p| < bP p := by
    rw [abs_mul, abs_of_pos hb0]
    have : |p.2.2| < 1 := abs_lt.2 ⟨ht.1, ht.2⟩
    nlinarith
  have hcos : Real.cos (bP p) < Real.cos (p.2.2 * bP p) := by
    rw [← Real.cos_abs (p.2.2 * bP p)]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hbpi hab
  rw [hcb] at hcos
  have : -1 < rP p * Real.cos (p.2.2 * bP p) := by
    have := mul_lt_mul_of_pos_left hcos hr
    rwa [mul_div_cancel₀ _ hr.ne'] at this
  nlinarith

lemma phiP_surj (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (hd : 0 < (A - 1).det) :
    ∃ p ∈ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-1 : ℝ) 1, phiP p = A := by
  rw [symp_iff] at hA
  rw [det_sub] at hd
  set a := A i0 i0; set b := A i0 j0; set c := A j0 i0; set d := A j0 j0
  set s := (a + d) / 2; set u := (a - d) / 2; set v := (b + c) / 2; set y := (b - c) / 2
  have hs : s < 1 := by simp only [s]; nlinarith
  let w : ℂ := ⟨-s, -y⟩
  set θ := Complex.arg w
  let q : ℝ × ℝ × ℝ := (u, v, 0)
  have hrq : rP q = ‖w‖ := by
    simp only [rP, q, w, Complex.norm_def, Complex.normSq_mk]
    congr 1
    simp only [s, u, v, y]; nlinarith
  obtain ⟨hb0, hbpi, hcb⟩ := bP_bounds q
  have h1 := rP_pos q
  have hr : 0 < rP q := by linarith
  have hc : rP q * Real.cos θ = -s := by rw [hrq, Complex.norm_mul_cos_arg]
  have hsn : rP q * Real.sin θ = -y := by rw [hrq, Complex.norm_mul_sin_arg]
  have hθ : |θ| < bP q := by
    by_contra hcon
    push Not at hcon
    have := Real.cos_le_cos_of_nonneg_of_le_pi hb0.le (Complex.abs_arg_le_pi w) hcon
    rw [Real.cos_abs, hcb] at this
    have h2 := mul_le_mul_of_nonneg_left this hr.le
    rw [mul_div_cancel₀ _ hr.ne', hc] at h2
    linarith
  refine ⟨(u, v, θ / bP q), ⟨trivial, trivial, ?_⟩, ?_⟩
  · rw [abs_lt] at hθ
    constructor
    · rw [lt_div_iff₀ hb0]; linarith
    · rw [div_lt_iff₀ hb0]; linarith
  · have e1 : rP (u, v, θ / bP q) = rP q := rfl
    have e2 : bP (u, v, θ / bP q) = bP q := rfl
    have e3 : θ / bP q * bP q = θ := div_mul_cancel₀ _ hb0.ne'
    rw [eq_mk A]
    unfold phiP
    simp only [e1, e2, e3, neg_mul, hc, hsn]
    congr 1 <;> simp only [s, u, v, y, a, b, c, d] <;> ring

lemma phiM_mem (p : ℝ × ℝ × ℝ) (hs : 1 < p.1) :
    IsSymplectic (phiM p) ∧ (phiM p - 1).det < 0 := by
  have hρ := Real.sq_sqrt (show 0 ≤ p.2.1^2 + p.1^2 - 1 by nlinarith [sq_nonneg p.2.1])
  have hcs := Real.sin_sq_add_cos_sq p.2.2
  unfold phiM
  simp only [symp_mk, det_mk]
  constructor
  · linear_combination (-(Real.sqrt (p.2.1 ^ 2 + p.1 ^ 2 - 1))^2) * hcs - hρ
  · nlinarith

lemma phiM_surj (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (hd : (A - 1).det < 0) :
    ∃ p ∈ Set.Ioi (1 : ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ), phiM p = A := by
  rw [symp_iff] at hA
  rw [det_sub] at hd
  set a := A i0 i0; set b := A i0 j0; set c := A j0 i0; set d := A j0 j0
  set s := (a + d) / 2; set u := (a - d) / 2; set v := (b + c) / 2; set y := (b - c) / 2
  have hs : 1 < s := by simp only [s]; nlinarith
  let w : ℂ := ⟨u, v⟩
  have hρ : Real.sqrt (y^2 + s^2 - 1) = ‖w‖ := by
    simp only [w, Complex.norm_def, Complex.normSq_mk]
    congr 1
    simp only [s, u, v, y]; nlinarith
  refine ⟨(s, y, Complex.arg w), ⟨hs, trivial, trivial⟩, ?_⟩
  rw [eq_mk A]
  unfold phiM
  simp only [hρ, Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
  congr 1 <;> simp only [s, u, v, y, w, a, b, c, d] <;> ring

theorem main :
    let P : Set (GroupedRealMatrix 1) := {A | IsSymplectic A ∧ 0 < (A-1).det}
    let M : Set (GroupedRealMatrix 1) := {A | IsSymplectic A ∧ (A-1).det < 0}
    IsConnected P ∧ IsConnected M ∧ Disjoint P M ∧
      {A | IsSymplectic A ∧ (A-1).det ≠ 0} = P ∪ M ∧
      (∀ S : Set (GroupedRealMatrix 1), IsConnected S → S ⊆ P ∪ M → S ⊆ P ∨ S ⊆ M) := by
  intro P M
  have hPimg : P = phiP '' ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-1 : ℝ) 1) := by
    ext A; constructor
    · rintro ⟨h1, h2⟩; obtain ⟨p, hp, rfl⟩ := phiP_surj A h1 h2; exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact phiP_mem p hp.2.2
  have hMimg : M = phiM '' (Set.Ioi (1 : ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    ext A; constructor
    · rintro ⟨h1, h2⟩; obtain ⟨p, hp, rfl⟩ := phiM_surj A h1 h2; exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact phiM_mem p hp.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hPimg]
    exact (isConnected_univ.prod (isConnected_univ.prod (isConnected_Ioo (by norm_num)))).image _
      phiP_cont.continuousOn
  · rw [hMimg]
    exact ((isConnected_Ioi).prod (isConnected_univ.prod isConnected_univ)).image _
      phiM_cont.continuousOn
  · rw [Set.disjoint_left]
    rintro A ⟨_, h1⟩ ⟨_, h2⟩; linarith
  · ext A
    simp only [Set.mem_ofPred_eq, Set.mem_union, P, M]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_gt_of_ne h2 with h | h
      · exact Or.inr ⟨h1, h⟩
      · exact Or.inl ⟨h1, h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2.ne'⟩
      · exact ⟨h1, h2.ne⟩
  · intro S hS hsub
    have hc : Continuous (fun A : GroupedRealMatrix 1 => (A - 1).det) :=
      (continuous_id.sub continuous_const).matrix_det
    have hu : IsOpen {A : GroupedRealMatrix 1 | 0 < (A - 1).det} := isOpen_lt continuous_const hc
    have hv : IsOpen {A : GroupedRealMatrix 1 | (A - 1).det < 0} := isOpen_lt hc continuous_const
    have huv : Disjoint {A : GroupedRealMatrix 1 | 0 < (A - 1).det} {A | (A - 1).det < 0} := by
      rw [Set.disjoint_left]; intro A h1 h2; simp only [Set.mem_ofPred_eq] at h1 h2; linarith
    have hs' : S ⊆ {A : GroupedRealMatrix 1 | 0 < (A - 1).det} ∪ {A | (A - 1).det < 0} := by
      intro A hA
      rcases hsub hA with h | h
      · exact Or.inl h.2
      · exact Or.inr h.2
    rcases hS.isPreconnected.subset_or_subset hu hv huv hs' with h | h
    · left; intro A hA
      rcases hsub hA with h' | h'
      · exact h'
      · exact absurd (h hA) (by simp only [Set.mem_ofPred_eq]; linarith [h'.2])
    · right; intro A hA
      rcases hsub hA with h' | h'
      · exact absurd (h hA) (by simp only [Set.mem_ofPred_eq]; linarith [h'.2])
      · exact h'

end X4CZK


noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

namespace X4CZM

open Polynomial X4CZK

attribute [local instance] Classical.propDecidable

lemma det2 {R : Type*} [CommRing R] (M : Matrix (Coord 1) (Coord 1) R) :
    M.det = M i0 i0 * M j0 j0 - M i0 j0 * M j0 i0 := by
  rw [← Matrix.det_reindex_self finSumFinEquiv, Matrix.det_fin_two]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  have h0 : (finSumFinEquiv.symm (0 : Fin 2) : Fin 1 ⊕ Fin 1) = i0 := rfl
  have h1 : (finSumFinEquiv.symm (1 : Fin 2) : Fin 1 ⊕ Fin 1) = j0 := rfl
  rw [h0, h1]

lemma charpoly_eq (A : GroupedRealMatrix 1) (hA : IsSymplectic A) :
    (complexify A).charpoly = X ^ 2 - C ((A i0 i0 + A j0 j0 : ℝ) : ℂ) * X + 1 := by
  refine (Matrix.charpoly_of_card_eq_two (M := complexify A) (by simp)).trans ?_
  rw [symp_iff] at hA
  have ht : (complexify A).trace = ((A i0 i0 + A j0 j0 : ℝ) : ℂ) := by
    simp [Matrix.trace, Fintype.sum_sum_type, complexify]
  have hd : (complexify A).det = 1 := by
    rw [det2]; simp only [complexify]; exact_mod_cast hA
  rw [ht, hd, C_1]

lemma charpoly_fac (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (z1 z2 : ℂ)
    (hs : z1 + z2 = ((A i0 i0 + A j0 j0 : ℝ) : ℂ)) (hp : z1 * z2 = 1) :
    (complexify A).charpoly = (X - C z1) * (X - C z2) := by
  rw [charpoly_eq A hA, ← hs, ← C_1, ← hp, C_add, C_mul]; ring

lemma roots_eq (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (z1 z2 : ℂ)
    (hs : z1 + z2 = ((A i0 i0 + A j0 j0 : ℝ) : ℂ)) (hp : z1 * z2 = 1) :
    (complexify A).charpoly.roots = {z1, z2} := by
  rw [charpoly_fac A hA z1 z2 hs hp, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]; rfl

lemma sum_count {α : Type*} [DecidableEq α] (s : Multiset α) (P : α → Prop) [DecidablePred P] :
    ∑ x ∈ s.toFinset.filter P, s.count x = Multiset.card (s.filter P) := by
  rw [← Multiset.toFinset_sum_count_eq (s.filter P), Multiset.toFinset_filter]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Multiset.count_filter_of_pos (Finset.mem_filter.1 hx).2]

/-- the exponent sum in `spectralRotation`. -/
lemma neg_sum (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (z1 z2 : ℂ)
    (hs : z1 + z2 = ((A i0 i0 + A j0 j0 : ℝ) : ℂ)) (hp : z1 * z2 = 1) (P : ℂ → Prop) [DecidablePred P] :
    ∑ z ∈ (eigenvalues A).filter P, algebraicMultiplicity A z =
      Multiset.card (({z1, z2} : Multiset ℂ).filter P) := by
  unfold eigenvalues algebraicMultiplicity
  have hne : (complexify A).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  rw [← roots_eq A hA z1 z2 hs hp, ← sum_count]
  apply Finset.sum_congr rfl
  intro x _
  rw [count_roots]

section krein

variable (A : GroupedRealMatrix 1) (ζ ζ' : ℂ)

def uvec : Coord 1 → ℂ := fun x => Sum.elim (fun _ => ((A i0 j0 : ℝ) : ℂ)) (fun _ => ζ - (A i0 i0 : ℝ)) x

lemma shifted_apply (v : Coord 1 → ℂ) (x : Coord 1) :
    shifted A ζ v x = (∑ y, (A x y : ℂ) * v y) - ζ * v x := by
  simp [shifted, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, complexify]

lemma mem_gen (hA : IsSymplectic A) (hs : ζ + ζ' = ((A i0 i0 + A j0 j0 : ℝ) : ℂ)) (hp : ζ * ζ' = 1)
    (hne : ζ ≠ ζ') (hb : A i0 j0 ≠ 0) (v : Coord 1 → ℂ) :
    v ∈ generalizedSpace A ζ ↔ ∃ κ : ℂ, v = κ • uvec A ζ := by
  rw [symp_iff] at hA
  have hdet : ((A i0 i0 : ℝ) : ℂ) * (A j0 j0 : ℝ) - (A i0 j0 : ℝ) * (A j0 i0 : ℝ) = 1 := by
    exact_mod_cast hA
  push_cast at hs
  have hb' : ((A i0 j0 : ℝ) : ℂ) ≠ 0 := by simp [hb]
  have key : ∀ w : Coord 1 → ℂ,
      shifted A ζ w i0 = ((A i0 i0 : ℝ) - ζ) * w i0 + (A i0 j0 : ℝ) * w j0 ∧
      shifted A ζ w j0 = (A j0 i0 : ℝ) * w i0 + ((A j0 j0 : ℝ) - ζ) * w j0 := by
    intro w; constructor <;> rw [shifted_apply] <;> simp [Fintype.sum_sum_type] <;> ring
  unfold generalizedSpace
  rw [LinearMap.mem_ker, pow_two, Module.End.mul_apply]
  constructor
  · intro h
    have e1 := congrFun h i0
    simp only [Pi.zero_apply] at e1
    rw [(key _).1, (key v).1, (key v).2] at e1
    have w1 : (ζ - ζ') * (((A i0 i0 : ℝ) - ζ) * v i0 + (A i0 j0 : ℝ) * v j0) = 0 := by
      linear_combination (-1 : ℂ) * e1 + v i0 * (hp - hdet) -
        ((A i0 i0 : ℝ) * v i0 + (A i0 j0 : ℝ) * v j0) * hs
    have w1' := (mul_eq_zero.1 w1).resolve_left (sub_ne_zero.2 hne)
    refine ⟨v i0 / (A i0 j0 : ℝ), ?_⟩
    funext x
    rcases x with x | x <;> simp only [uvec, Pi.smul_apply, smul_eq_mul, Sum.elim_inl, Sum.elim_inr] <;>
      rw [Fin.fin_one_eq_zero x]
    · field_simp
    · field_simp; linear_combination w1'
  · rintro ⟨κ, rfl⟩
    have hu : shifted A ζ (uvec A ζ) = 0 := by
      funext x
      rcases x with x | x <;> rw [Fin.fin_one_eq_zero x]
      · rw [(key _).1]; simp [uvec]; ring
      · rw [(key _).2]; simp [uvec]
        linear_combination -hdet - ζ * hs + hp
    rw [map_smul, hu, smul_zero, map_zero]

lemma omega_u (κ : ℂ) :
    (omegaC (κ • uvec A ζ) (fun i => star ((κ • uvec A ζ) i))).im =
      -2 * Complex.normSq κ * A i0 j0 * ζ.im := by
  simp [omegaC, uvec, Complex.mul_im, Complex.mul_re, Complex.normSq_apply]
  ring

lemma kP_eq (hA : IsSymplectic A) (hs : ζ + ζ' = ((A i0 i0 + A j0 j0 : ℝ) : ℂ)) (hp : ζ * ζ' = 1)
    (hne : ζ ≠ ζ') (hb : A i0 j0 ≠ 0) :
    kreinPositive A ζ = if A i0 j0 * ζ.im < 0 then 2 else 0 := by
  set u := uvec A ζ
  have hE : ∀ v, v ∈ generalizedSpace A ζ ↔ ∃ κ : ℂ, v = κ • u := mem_gen A ζ ζ' hA hs hp hne hb
  let f : Fin 2 → (Coord 1 → ℂ) := ![u, Complex.I • u]
  have hspan : (generalizedSpace A ζ).restrictScalars ℝ ≤ Submodule.span ℝ (Set.range f) := by
    intro v hv
    rw [Submodule.restrictScalars_mem, hE] at hv
    obtain ⟨κ, rfl⟩ := hv
    have : κ • u = κ.re • f 0 + κ.im • f 1 := by
      simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one]
      funext x; simp [Complex.ext_iff]; ring
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hle : ∀ W : Submodule ℝ (Coord 1 → ℂ), W ≤ (generalizedSpace A ζ).restrictScalars ℝ →
      Module.finrank ℝ W ≤ 2 := by
    intro W hW
    calc Module.finrank ℝ W ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range f)) :=
          Submodule.finrank_mono (hW.trans hspan)
      _ ≤ Fintype.card (Fin 2) := finrank_range_le_card f
      _ = 2 := by simp
  have hpos : ∀ κ : ℂ, κ ≠ 0 → (0 < (omegaC (κ • u) (fun i => star ((κ • u) i))).im ↔
      A i0 j0 * ζ.im < 0) := by
    intro κ hκ
    rw [omega_u]
    have : 0 < Complex.normSq κ := Complex.normSq_pos.2 hκ
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  unfold kreinPositive
  split_ifs with hsg
  · apply le_antisymm
    · apply Finset.sup_le
      intro k hk
      obtain ⟨-, W, hW, rfl, -⟩ := (Finset.mem_filter.1 hk)
      exact hle W hW
    · have hli : LinearIndependent ℝ f := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        have := congrFun hst i0
        simp [u, uvec] at this
        have hb' : ((A i0 j0 : ℝ) : ℂ) ≠ 0 := by simp [hb]
        have h2 : ((s : ℂ) + t * Complex.I) * (A i0 j0 : ℝ) = 0 := by linear_combination this
        have h3 := (mul_eq_zero.1 h2).resolve_right hb'
        have h4 := congrArg Complex.re h3
        have h5 := congrArg Complex.im h3
        simp at h4 h5
        exact ⟨h4, h5⟩
      have hWE : Submodule.span ℝ (Set.range f) ≤ (generalizedSpace A ζ).restrictScalars ℝ := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.restrictScalars_mem, hE]
        fin_cases i
        · exact ⟨1, by simp [f]⟩
        · exact ⟨Complex.I, by simp [f]⟩
      have h2 : 2 ∈ (Finset.range (4 * 1 + 1)).filter (fun k => ∃ W : Submodule ℝ (Coord 1 → ℂ),
          W ≤ (generalizedSpace A ζ).restrictScalars ℝ ∧ Module.finrank ℝ W = k ∧
          ∀ v ∈ W, v ≠ 0 → 0 < (omegaC v (fun i => star (v i))).im) := by
        refine Finset.mem_filter.2 ⟨by simp, Submodule.span ℝ (Set.range f), ?_, ?_, ?_⟩
        · exact hWE
        · rw [finrank_span_eq_card hli]; simp
        · intro v hv hv0
          have hv' := hWE hv
          rw [Submodule.restrictScalars_mem, hE] at hv'
          obtain ⟨κ, rfl⟩ := hv'
          have hκ : κ ≠ 0 := by rintro rfl; simp at hv0
          exact (hpos κ hκ).2 hsg
      exact Finset.le_sup (f := id) h2
  · apply le_antisymm _ (Nat.zero_le _)
    apply Finset.sup_le
    intro k hk
    obtain ⟨-, W, hW, rfl, hWp⟩ := (Finset.mem_filter.1 hk)
    have : W = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      by_contra hv0
      have hv' := hW hv
      rw [Submodule.restrictScalars_mem, hE] at hv'
      obtain ⟨κ, rfl⟩ := hv'
      have hκ : κ ≠ 0 := by rintro rfl; simp at hv0
      exact hsg ((hpos κ hκ).1 (hWp _ hv hv0))
    simp [this]


end krein


def tr (A : GroupedRealMatrix 1) : ℝ := A i0 i0 + A j0 j0
def hc (A : GroupedRealMatrix 1) : ℝ := max (-1) (min 1 (tr A / 2))
/-- explicit formula for the rotation in dimension two. -/
def G (A : GroupedRealMatrix 1) : ℂ :=
  (hc A : ℂ) + Complex.I * ((Real.sign (A j0 i0) * Real.sqrt (1 - hc A ^ 2) : ℝ) : ℂ)

lemma eig_eq (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (z1 z2 : ℂ)
    (hs : z1 + z2 = ((A i0 i0 + A j0 j0 : ℝ) : ℂ)) (hp : z1 * z2 = 1) :
    eigenvalues A = {z1, z2} := by
  unfold eigenvalues
  rw [roots_eq A hA z1 z2 hs hp, Multiset.insert_eq_cons, Multiset.toFinset_cons,
    Multiset.toFinset_singleton]

lemma rot_real (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (r1 r2 : ℝ)
    (hs : r1 + r2 = tr A) (hp : r1 * r2 = 1) :
    spectralRotation A = (-1 : ℂ) ^ (Multiset.card (({(r1 : ℂ), (r2 : ℂ)} : Multiset ℂ).filter
      (fun z => z.im = 0 ∧ z.re < 0)) / 2) := by
  have hs' : (r1 : ℂ) + r2 = ((A i0 i0 + A j0 j0 : ℝ) : ℂ) := by
    unfold tr at hs; exact_mod_cast hs
  have hp' : (r1 : ℂ) * r2 = 1 := by exact_mod_cast hp
  unfold spectralRotation
  rw [neg_sum A hA _ _ hs' hp', eig_eq A hA _ _ hs' hp']
  rw [Finset.filter_eq_empty_iff.2, Finset.prod_empty, mul_one]
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rintro ⟨h1, h2, h3⟩
  rcases hz with rfl | rfl <;> rw [Complex.norm_real, Real.norm_eq_abs] at h1 <;>
    rcases abs_eq (zero_le_one) |>.1 h1 with h | h <;> simp_all

lemma rot_ge (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (ht : 2 ≤ tr A) :
    spectralRotation A = 1 ∧ G A = 1 := by
  set q := Real.sqrt (tr A ^ 2 / 4 - 1)
  have hq := Real.sq_sqrt (show 0 ≤ tr A ^ 2 / 4 - 1 by nlinarith)
  have hq0 := Real.sqrt_nonneg (tr A ^ 2 / 4 - 1)
  have hqt : q < tr A / 2 := by nlinarith
  constructor
  · rw [rot_real A hA (tr A / 2 + q) (tr A / 2 - q) (by ring) (by nlinarith)]
    rw [Multiset.filter_eq_nil.2]
    · simp
    · intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> simp <;> linarith
  · have : hc A = 1 := by unfold hc; rw [min_eq_left (by linarith)]; norm_num
    simp [G, this]

lemma rot_le (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (ht : tr A ≤ -2) :
    spectralRotation A = -1 ∧ G A = -1 := by
  set q := Real.sqrt (tr A ^ 2 / 4 - 1)
  have hq := Real.sq_sqrt (show 0 ≤ tr A ^ 2 / 4 - 1 by nlinarith)
  have hq0 := Real.sqrt_nonneg (tr A ^ 2 / 4 - 1)
  have hqt : q < -(tr A / 2) := by nlinarith
  constructor
  · rw [rot_real A hA (tr A / 2 + q) (tr A / 2 - q) (by ring) (by nlinarith)]
    rw [Multiset.filter_eq_self.2]
    · simp
    · intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> simp <;> linarith
  · have : hc A = -1 := by
      unfold hc; rw [min_eq_right (by linarith)]; exact max_eq_left (by linarith)
    simp [G, this]


lemma bc_neg (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (ht : |tr A| < 2) :
    A i0 j0 * A j0 i0 < 0 := by
  rw [symp_iff] at hA
  unfold tr at ht
  have := abs_lt.1 ht
  nlinarith [sq_nonneg (A i0 i0 - A j0 j0)]

lemma rot_ell (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (ht : |tr A| < 2) :
    spectralRotation A = G A := by
  have ht' := abs_lt.1 ht
  set t := tr A
  set s := Real.sqrt (1 - t ^ 2 / 4)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 - t ^ 2 / 4 by nlinarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by nlinarith)
  set z1 : ℂ := ⟨t / 2, s⟩
  set z2 : ℂ := ⟨t / 2, -s⟩
  have hsum : z1 + z2 = ((A i0 i0 + A j0 j0 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [z1, z2, t, tr]
  have hprod : z1 * z2 = 1 := by
    apply Complex.ext <;> simp [z1, z2] <;> nlinarith
  have hne : z1 ≠ z2 := by
    intro h; have := congrArg Complex.im h; simp [z1, z2] at this; linarith
  have hbc := bc_neg A hA ht
  have hb : A i0 j0 ≠ 0 := by rintro h; rw [h] at hbc; simp at hbc
  have k1 := kP_eq A z1 z2 hA hsum hprod hne hb
  have k2 := kP_eq A z2 z1 hA (by rw [add_comm]; exact hsum) (by rw [mul_comm]; exact hprod) hne.symm hb
  unfold spectralRotation
  rw [neg_sum A hA _ _ hsum hprod, eig_eq A hA _ _ hsum hprod]
  rw [Multiset.filter_eq_nil.2 (by
    intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [z1, z2] <;> intro h <;> linarith)]
  rw [Finset.filter_true_of_mem (by
    intro z hz
    have hn1 : ‖z‖ = 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;>
        rw [Complex.norm_def, Complex.normSq_mk, Real.sqrt_eq_one] <;> nlinarith
    refine ⟨hn1, ?_, ?_⟩ <;>
    · intro h; rw [h] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h' | h' <;> have := congrArg Complex.im h' <;> simp [z1, z2] at this <;> linarith)]
  rw [Finset.prod_pair hne, k1, k2]
  have hc : hc A = t / 2 := by
    unfold hc; rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  simp only [G, hc]
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · have hc0 : 0 < A j0 i0 := by nlinarith
    rw [if_pos (by nlinarith), if_neg (by nlinarith), Real.sign_of_pos hc0]
    apply Complex.ext <;> simp [z1, s] <;> ring_nf
  · have hc0 : A j0 i0 < 0 := by nlinarith
    rw [if_neg (by nlinarith), if_pos (by nlinarith), Real.sign_of_neg hc0]
    apply Complex.ext <;> simp [z2, s] <;> ring_nf

lemma rot_eq (A : GroupedRealMatrix 1) (hA : IsSymplectic A) : spectralRotation A = G A := by
  rcases le_or_gt 2 (tr A) with h | h
  · rw [(rot_ge A hA h).1, (rot_ge A hA h).2]
  rcases le_or_gt (tr A) (-2) with h' | h'
  · rw [(rot_le A hA h').1, (rot_le A hA h').2]
  exact rot_ell A hA (abs_lt.2 ⟨h', h⟩)


def hf (A : GroupedRealMatrix 1) : ℝ := Real.sqrt (1 - hc A ^ 2)

lemma hc_cont : Continuous hc := by
  unfold hc tr; fun_prop

lemma hf_cont : Continuous hf := by
  unfold hf; have := hc_cont; fun_prop

lemma hc_abs (A : GroupedRealMatrix 1) : -1 ≤ hc A ∧ hc A ≤ 1 := by
  unfold hc; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma hf_zero (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (hc0 : A j0 i0 = 0) : hf A = 0 := by
  rw [symp_iff, hc0, mul_zero, sub_zero] at hA
  have h4 : 4 ≤ tr A ^ 2 := by unfold tr; nlinarith [sq_nonneg (A i0 i0 - A j0 j0)]
  have : hc A ^ 2 = 1 := by
    rcases le_or_gt 2 (tr A) with h | h
    · have : hc A = 1 := by unfold hc; rw [min_eq_left (by linarith)]; norm_num
      rw [this]; norm_num
    · have h' : tr A ≤ -2 := by nlinarith
      have : hc A = -1 := by
        unfold hc; rw [min_eq_right (by linarith)]; exact max_eq_left (by linarith)
      rw [this]; norm_num
  unfold hf; rw [this, sub_self, Real.sqrt_zero]

lemma G_eq (A : GroupedRealMatrix 1) : G A = (hc A : ℂ) + Complex.I * ((Real.sign (A j0 i0) * hf A : ℝ) : ℂ) := rfl

lemma G_cont : ContinuousOn G {A | IsSymplectic A} := by
  intro A0 hA0
  have hcC : Continuous (fun A : GroupedRealMatrix 1 => ((hc A : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hc_cont
  have hfC : Continuous (fun A : GroupedRealMatrix 1 => ((hf A : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hf_cont
  have cc : Continuous (fun A : GroupedRealMatrix 1 => A j0 i0) := by fun_prop
  rcases lt_trichotomy (A0 j0 i0) 0 with hneg | hzero | hpos
  · have hev : ∀ᶠ A in nhds A0, G A = (hc A : ℂ) + Complex.I * (-(hf A : ℂ)) := by
      filter_upwards [cc.continuousAt.eventually (gt_mem_nhds hneg)] with A hA
      rw [G_eq, Real.sign_of_neg hA]; push_cast; ring
    have : ContinuousAt G A0 := by
      apply ContinuousAt.congr _ (Filter.EventuallyEq.symm hev)
      exact (hcC.add (continuous_const.mul hfC.neg)).continuousAt
    exact this.continuousWithinAt
  · have hf0 := hf_zero A0 hA0 hzero
    rw [ContinuousWithinAt, G_eq A0, hzero, hf0]
    simp only [Real.sign_zero, mul_zero, Complex.ofReal_zero, add_zero]
    have h1 : Filter.Tendsto (fun A : GroupedRealMatrix 1 => ((hc A : ℝ) : ℂ)) (nhdsWithin A0 {A | IsSymplectic A})
        (nhds ((hc A0 : ℝ) : ℂ)) := hcC.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (fun A : GroupedRealMatrix 1 => Complex.I * ((Real.sign (A j0 i0) * hf A : ℝ) : ℂ))
        (nhdsWithin A0 {A | IsSymplectic A}) (nhds 0) := by
      apply squeeze_zero_norm (a := fun A => |hf A|)
      · intro A
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have : |Real.sign (A j0 i0)| ≤ 1 := by
          rcases Real.sign_apply_eq (A j0 i0) with h | h | h <;> rw [h] <;> norm_num
        nlinarith [abs_nonneg (hf A)]
      · have : Filter.Tendsto (fun A => |hf A|) (nhds A0) (nhds (|hf A0|)) :=
          (continuous_abs.comp hf_cont).continuousAt.tendsto
        rw [hf0, abs_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
    have := h1.add h2
    rw [add_zero] at this
    exact this.congr (fun A => (G_eq A).symm)
  · have hev : ∀ᶠ A in nhds A0, G A = (hc A : ℂ) + Complex.I * (hf A : ℂ) := by
      filter_upwards [cc.continuousAt.eventually (lt_mem_nhds hpos)] with A hA
      rw [G_eq, Real.sign_of_pos hA]; push_cast; ring
    have : ContinuousAt G A0 := by
      apply ContinuousAt.congr _ (Filter.EventuallyEq.symm hev)
      exact (hcC.add (continuous_const.mul hfC)).continuousAt
    exact this.continuousWithinAt

lemma G_norm (A : GroupedRealMatrix 1) (hA : IsSymplectic A) : ‖G A‖ = 1 := by
  have hb := hc_abs A
  have hfs : hf A ^ 2 = 1 - hc A ^ 2 := by unfold hf; rw [Real.sq_sqrt (by nlinarith)]
  rw [G_eq, Complex.norm_def, Real.sqrt_eq_one]
  simp [Complex.normSq_apply]
  rcases Real.sign_apply_eq (A j0 i0) with h | h | h <;> rw [h]
  · nlinarith
  · have := hf_zero A hA ((Real.sign_eq_zero_iff).1 h)
    rw [this] at hfs; nlinarith
  · nlinarith


end X4CZM

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

namespace X4CZN

open X4CZK X4CZM

attribute [local instance] Classical.propDecidable

lemma mk_mul (a b c d e f g h : ℝ) :
    mk a b c d * mk e f g h = mk (a*e+b*g) (a*f+b*h) (c*e+d*g) (c*f+d*h) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [mk, Matrix.mul_apply, Fintype.sum_sum_type]

lemma one_eq : (1 : GroupedRealMatrix 1) = mk 1 0 0 1 := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [mk, Matrix.one_apply, Subsingleton.elim x y]

lemma neg_mk (a b c d : ℝ) : -mk a b c d = mk (-a) (-b) (-c) (-d) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> simp [mk]

lemma inv_mk (a b c d : ℝ) (h : a * d - b * c = 1) : (mk a b c d)⁻¹ = mk d (-b) (-c) a := by
  apply Matrix.inv_eq_right_inv
  rw [mk_mul, one_eq]; congr 1 <;> linarith

lemma tr_mk (a b c d : ℝ) : tr (mk a b c d) = a + d := rfl

lemma cad_eq (A : GroupedRealMatrix 1) :
    complexActionDet A = (A i0 i0 : ℂ) + Complex.I * (A j0 i0 : ℂ) := by
  unfold complexActionDet
  rw [Matrix.det_unique]
  rfl

lemma symp_mul {A B : GroupedRealMatrix 1} (hA : IsSymplectic A) (hB : IsSymplectic B) :
    IsSymplectic (A * B) := by
  rw [symp_iff] at *
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton]
  linear_combination (A j0 j0 * A i0 i0 - A i0 j0 * A j0 i0) * hB + hA

lemma hc_of_abs (A : GroupedRealMatrix 1) (h : |tr A| < 2) : hc A = tr A / 2 := by
  have := abs_lt.1 h
  unfold hc; rw [min_eq_right (by linarith), max_eq_right (by linarith)]

lemma G_ge (A : GroupedRealMatrix 1) (ht : 2 ≤ tr A) : G A = 1 := by
  have : hc A = 1 := by unfold hc; rw [min_eq_left (by linarith)]; norm_num
  simp [G, this]

lemma G_le (A : GroupedRealMatrix 1) (ht : tr A ≤ -2) : G A = -1 := by
  have : hc A = -1 := by
    unfold hc; rw [min_eq_right (by linarith)]; exact max_eq_left (by linarith)
  simp [G, this]

/-! axioms for `G` -/

lemma G_orth (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (hO : IsOrthogonal A) :
    G A = complexActionDet A := by
  rw [symp_iff] at hA
  have e := fun x y => congrFun (congrFun hO x) y
  have e1 := e i0 i0; have e2 := e j0 j0; have e3 := e i0 j0
  simp [Matrix.mul_apply, Fintype.sum_sum_type] at e1 e2 e3
  set a := A i0 i0; set b := A i0 j0; set c := A j0 i0; set d := A j0 j0
  have hd : d = a := by nlinarith [sq_nonneg (a - d), sq_nonneg (b + c)]
  have hb : b = -c := by nlinarith [sq_nonneg (a - d), sq_nonneg (b + c)]
  have htr : tr A = 2 * a := by unfold tr; simp only [a, d] at hd ⊢; linarith
  rw [cad_eq]
  have hac : a ^ 2 + c ^ 2 = 1 := by nlinarith
  rcases eq_or_ne c 0 with hc0 | hc0
  · have : a = 1 ∨ a = -1 := by
      have : (a - 1) * (a + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    rcases this with h | h
    · rw [G_ge A (by rw [htr, h]; norm_num)]
      show (1 : ℂ) = (a : ℂ) + Complex.I * (c : ℂ)
      rw [h, hc0]; simp
    · rw [G_le A (by rw [htr, h]; norm_num)]
      show (-1 : ℂ) = (a : ℂ) + Complex.I * (c : ℂ)
      rw [h, hc0]; simp
  · have hlt : |tr A| < 2 := by
      rw [htr, abs_lt]; constructor <;> nlinarith [sq_pos_of_ne_zero hc0]
    rw [G, hc_of_abs A hlt, htr]
    have : Real.sign c * Real.sqrt (1 - (2 * a / 2) ^ 2) = c := by
      have : 1 - (2 * a / 2) ^ 2 = c ^ 2 := by nlinarith
      rw [this, Real.sqrt_sq_eq_abs]
      rcases lt_or_gt_of_ne hc0 with h | h
      · rw [Real.sign_of_neg h, abs_of_neg h]; ring
      · rw [Real.sign_of_pos h, abs_of_pos h]; ring
    rw [this]; push_cast; ring


lemma sign_eq_of_mul_pos {x y : ℝ} (h : 0 < x * y) : Real.sign x = Real.sign y := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : y < 0 := by nlinarith
    rw [Real.sign_of_neg hx, Real.sign_of_neg this]
  · rw [hx] at h; simp at h
  · have : 0 < y := by nlinarith
    rw [Real.sign_of_pos hx, Real.sign_of_pos this]

lemma G_congr (A B : GroupedRealMatrix 1) (ht : tr A = tr B)
    (hs : |tr A| < 2 → Real.sign (A j0 i0) = Real.sign (B j0 i0)) : G A = G B := by
  rcases le_or_gt 2 (tr A) with h | h
  · rw [G_ge A h, G_ge B (ht ▸ h)]
  rcases le_or_gt (tr A) (-2) with h' | h'
  · rw [G_le A h', G_le B (ht ▸ h')]
  have hl : |tr A| < 2 := abs_lt.2 ⟨h', h⟩
  have hc' : hc A = hc B := by unfold hc; rw [ht]
  unfold G; rw [hc', hs hl]

lemma conj_mk (p q r s a b c d : ℝ) (hK : p * s - q * r = 1) :
    mk p q r s * mk a b c d * (mk p q r s)⁻¹ =
      mk ((p*a+q*c)*s + (p*b+q*d)*(-r)) ((p*a+q*c)*(-q) + (p*b+q*d)*p)
        ((r*a+s*c)*s + (r*b+s*d)*(-r)) ((r*a+s*c)*(-q) + (r*b+s*d)*p) := by
  rw [inv_mk _ _ _ _ hK, mk_mul, mk_mul]

lemma G_conj (A K : GroupedRealMatrix 1) (hA : IsSymplectic A) (hK : IsSymplectic K) :
    G (K * A * K⁻¹) = G A := by
  rw [symp_iff] at hA hK
  have hK' := hK
  rw [eq_mk K, eq_mk A, conj_mk _ _ _ _ _ _ _ _ hK]
  set p := K i0 i0; set q := K i0 j0; set r := K j0 i0; set s := K j0 j0
  set a := A i0 i0; set b := A i0 j0; set c := A j0 i0; set d := A j0 j0
  refine (G_congr _ _ ?_ ?_).symm
  · rw [tr_mk, tr_mk]; linear_combination -(a + d) * hK
  · intro ht
    rw [tr_mk] at ht
    have hbc : b * c < 0 := by
      have := abs_lt.1 ht
      nlinarith [sq_nonneg (a - d)]
    have hc0 : c ≠ 0 := by rintro h; rw [h] at hbc; simp at hbc
    simp only [mk10]
    apply sign_eq_of_mul_pos
    have hc2 : 0 < c ^ 2 := by positivity
    have h4 : 0 < 4 - (a + d) ^ 2 := by
      have := abs_lt.1 ht; nlinarith
    have key : 4 * c ^ 2 * (c * ((r*a+s*c)*s + (r*b+s*d)*(-r))) =
        (2*s*c^2 + r*c*(a-d))^2 + r^2*c^2*(4 - (a+d)^2) := by
      linear_combination (4 * r ^ 2 * c ^ 2) * hA
    rcases eq_or_ne r 0 with hr | hr
    · rw [hr] at hK ⊢
      have hs : s ≠ 0 := by rintro h; rw [h] at hK; simp at hK
      have : 0 < s ^ 2 := by positivity
      nlinarith
    · have : 0 < r ^ 2 * c ^ 2 * (4 - (a + d) ^ 2) := by positivity
      have : 0 < 4 * c ^ 2 * (c * ((r*a+s*c)*s + (r*b+s*d)*(-r))) := by
        rw [key]; nlinarith [sq_nonneg (2*s*c^2 + r*c*(a-d))]
      exact pos_of_mul_pos_right this (by positivity)

lemma eig_mem_ell (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (ht : |tr A| < 2) :
    ∃ z ∈ eigenvalues A, ‖z‖ = 1 := by
  have ht' := abs_lt.1 ht
  set t := tr A
  set s := Real.sqrt (1 - t ^ 2 / 4)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 - t ^ 2 / 4 by nlinarith)
  set z1 : ℂ := ⟨t / 2, s⟩
  set z2 : ℂ := ⟨t / 2, -s⟩
  have hsum : z1 + z2 = ((A i0 i0 + A j0 j0 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [z1, z2, t, tr]
  have hprod : z1 * z2 = 1 := by
    apply Complex.ext <;> simp [z1, z2] <;> nlinarith
  refine ⟨z1, by rw [eig_eq A hA z1 z2 hsum hprod]; simp, ?_⟩
  rw [Complex.norm_def, Complex.normSq_mk, Real.sqrt_eq_one]; nlinarith

lemma G_hyp (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (h : ∀ z ∈ eigenvalues A, ‖z‖ ≠ 1) :
    G A = 1 ∨ G A = -1 := by
  rcases le_or_gt 2 (tr A) with h1 | h1
  · exact Or.inl (G_ge A h1)
  rcases le_or_gt (tr A) (-2) with h2 | h2
  · exact Or.inr (G_le A h2)
  obtain ⟨z, hz, hz1⟩ := eig_mem_ell A hA (abs_lt.2 ⟨h2, h1⟩)
  exact absurd hz1 (h z hz)

lemma axioms_spec : RotationAxiomsTwo spectralRotation := by
  have hG : ∀ A, IsSymplectic A → spectralRotation A = G A := rot_eq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact G_cont.congr (fun A hA => hG A hA)
  · intro A hA; rw [hG A hA]; exact G_norm A hA
  · intro A hA hO; rw [hG A hA]; exact G_orth A hA hO
  · intro A K hA hK
    have hK' : IsSymplectic K⁻¹ := by
      rw [eq_mk K] at hK ⊢; rw [symp_mk] at hK
      rw [inv_mk _ _ _ _ hK, symp_mk]; linarith
    rw [hG _ (symp_mul (symp_mul hK hA) hK'), hG A hA, G_conj A K hA hK]
  · intro A hA h; rw [hG A hA]; exact G_hyp A hA h

end X4CZN

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

namespace X4CZO

open X4CZK X4CZM X4CZN

attribute [local instance] Classical.propDecidable

lemma transpose_mk (a b c d : ℝ) : (mk a b c d)ᵀ = mk a c b d := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> simp [mk, Matrix.transpose_apply]

lemma orth_rot (C S : ℝ) (h : C ^ 2 + S ^ 2 = 1) : IsOrthogonal (mk C (-S) S C) := by
  unfold IsOrthogonal
  rw [transpose_mk, mk_mul, one_eq]
  congr 1 <;> nlinarith

lemma one_symp : IsSymplectic (1 : GroupedRealMatrix 1) := by
  rw [one_eq, symp_mk]; norm_num

lemma one_orth : IsOrthogonal (1 : GroupedRealMatrix 1) := by
  unfold IsOrthogonal; simp

lemma cad_one : complexActionDet (1 : GroupedRealMatrix 1) = 1 := by
  rw [cad_eq, one_eq]; simp

lemma cad_neg_one : complexActionDet (-1 : GroupedRealMatrix 1) = -1 := by
  rw [cad_eq, one_eq, neg_mk]; simp

lemma ell_normal (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (ht : |tr A| < 2) :
    ∃ K : GroupedRealMatrix 1, IsSymplectic K ∧ ∃ C S : ℝ, C ^ 2 + S ^ 2 = 1 ∧
      K * A * K⁻¹ = mk C (-S) S C := by
  rw [symp_iff] at hA
  have ht' := abs_lt.1 ht
  set a := A i0 i0; set b := A i0 j0; set c := A j0 i0; set d := A j0 j0
  have htr : tr A = a + d := rfl
  rw [htr] at ht'
  have hbc : b * c < 0 := by nlinarith [sq_nonneg (a - d)]
  have hc0 : c ≠ 0 := by rintro h; rw [h] at hbc; simp at hbc
  set C := (a + d) / 2
  have hC2 : C ^ 2 < 1 := by simp only [C]; nlinarith
  set s := Real.sqrt (1 - C ^ 2)
  have hs2 : s ^ 2 = 1 - C ^ 2 := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  set S := Real.sign c * s
  have hS2 : S ^ 2 = s ^ 2 := by
    simp only [S]; rcases lt_or_gt_of_ne hc0 with h | h
    · rw [Real.sign_of_neg h]; ring
    · rw [Real.sign_of_pos h]; ring
  have hS0 : S ≠ 0 := by
    intro h; have : S ^ 2 = 0 := by rw [h]; ring
    nlinarith
  set w := c / S
  have hw : 0 < w := by
    simp only [w, S]; rcases lt_or_gt_of_ne hc0 with h | h
    · rw [Real.sign_of_neg h]; exact div_pos_of_neg_of_neg h (by linarith)
    · rw [Real.sign_of_pos h]; exact div_pos h (by linarith)
  set e := (a - C) / S
  have hwS : w * S = c := by simp only [w]; field_simp
  have heS : e * S = a - C := by simp only [e]; field_simp
  set l := Real.sqrt w⁻¹
  have hl : l * l * w = 1 := by
    simp only [l]; rw [Real.mul_self_sqrt (by positivity)]; field_simp
  refine ⟨mk (l * w) (-(l * e)) 0 l, ?_, C, S, by nlinarith, ?_⟩
  · rw [symp_mk]; linear_combination hl
  · rw [eq_mk A, inv_mk _ _ _ _ (by linear_combination hl), mk_mul, mk_mul]
    have hSS : S ^ 2 = 1 - C ^ 2 := by rw [hS2, hs2]
    have hCd : 2 * C = a + d := by simp only [C]; ring
    have hX : S * (((w*a - c*e)*e + (w*b - e*d)*w) + w * S) = 0 := by
      linear_combination (-c*e - d*w + w*C)*heS + (w*b + e*(a-C))*hwS + w*hSS - w*C*hCd - w*hA
    have hX0 := (mul_eq_zero.1 hX).resolve_left hS0
    congr 1
    · linear_combination (a - e * S) * hl + l ^ 2 * e * hwS - heS
    · linear_combination l ^ 2 * hX0 - S * hl
    · linear_combination (S) * hl - l ^ 2 * hwS
    · linear_combination (-l^2*e) * hwS + l^2*w*heS + (a+d-C)*hl - hCd


lemma ell_unique (r : GroupedRealMatrix 1 → ℂ) (hr : RotationAxiomsTwo r)
    (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (ht : |tr A| < 2) : r A = G A := by
  obtain ⟨K, hK, C, S, hCS, hR⟩ := ell_normal A hA ht
  have hRs : IsSymplectic (mk C (-S) S C) := by rw [symp_mk]; nlinarith
  rw [← hr.2.2.2.1 A K hA hK, ← G_conj A K hA hK, hR, hr.2.2.1 _ hRs (orth_rot C S hCS),
    G_orth _ hRs (orth_rot C S hCS)]

lemma lim_const (f : GroupedRealMatrix 1 → ℂ) (hf : ContinuousOn f {A | IsSymplectic A})
    (p : ℝ → GroupedRealMatrix 1) (hp : Continuous p) (hsp : ∀ ε, 0 ≤ ε → IsSymplectic (p ε))
    (c : ℂ) (h : ∀ ε, 0 < ε → f (p ε) = c) : f (p 0) = c := by
  have h1 : ContinuousWithinAt (f ∘ p) (Set.Ioi 0) 0 :=
    (hf (p 0) (hsp 0 le_rfl)).comp hp.continuousWithinAt (fun ε hε => hsp ε (le_of_lt hε))
  have h2 : Filter.Tendsto (f ∘ p) (nhdsWithin 0 (Set.Ioi 0)) (nhds c) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall (fun ε hε => (h ε hε).symm))
  exact tendsto_nhds_unique h1.tendsto h2

lemma const_of_conn (f : GroupedRealMatrix 1 → ℂ) (S : Set (GroupedRealMatrix 1))
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hv : ∀ x ∈ S, f x = 1 ∨ f x = -1)
    (x y : GroupedRealMatrix 1) (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  have hI := (hS.image _ (Complex.continuous_re.comp_continuousOn hf))
  have key : ∀ u ∈ S, ∀ v ∈ S, f u = 1 → f v = -1 → False := by
    intro u hu v hv' hfu hfv
    have := hI.Icc_subset ⟨v, hv', rfl⟩ ⟨u, hu, rfl⟩
    have h0 : (0 : ℝ) ∈ Set.Icc ((Complex.re ∘ f) v) ((Complex.re ∘ f) u) := by
      simp [hfu, hfv]
    obtain ⟨z, hz, hz0⟩ := this h0
    rcases hv z hz with h | h <;> simp [h] at hz0
  rcases hv x hx with h1 | h1 <;> rcases hv y hy with h2 | h2
  · rw [h1, h2]
  · exact (key x hx y hy h1 h2).elim
  · exact (key y hy x hx h2 h1).elim
  · rw [h1, h2]

lemma eig_real (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (ht : 2 < |tr A|) :
    ∀ z ∈ eigenvalues A, ‖z‖ ≠ 1 := by
  have h4 : 4 < tr A ^ 2 := by nlinarith [abs_nonneg (tr A), sq_abs (tr A)]
  set q := Real.sqrt (tr A ^ 2 / 4 - 1)
  have hq := Real.sq_sqrt (show 0 ≤ tr A ^ 2 / 4 - 1 by nlinarith)
  have hs' : ((tr A / 2 + q : ℝ) : ℂ) + ((tr A / 2 - q : ℝ) : ℂ) = ((A i0 i0 + A j0 j0 : ℝ) : ℂ) := by
    push_cast; unfold tr; push_cast; ring
  have hp' : ((tr A / 2 + q : ℝ) : ℂ) * ((tr A / 2 - q : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]; rw [show (tr A / 2 + q) * (tr A / 2 - q) = 1 by nlinarith]; simp
  rw [eig_eq A hA _ _ hs' hp']
  have quad : ∀ x : ℝ, (x = tr A / 2 + q ∨ x = tr A / 2 - q) → x ^ 2 - tr A * x + 1 = 0 := by
    rintro x (rfl | rfl) <;> nlinarith
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  obtain ⟨x, hx, rfl⟩ : ∃ x : ℝ, (x = tr A / 2 + q ∨ x = tr A / 2 - q) ∧ z = (x : ℂ) := by
    rcases hz with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have hx2 := quad x hx
  rw [Complex.norm_real, Real.norm_eq_abs]
  intro h1
  rcases abs_eq (zero_le_one) |>.1 h1 with h | h <;> rw [h] at hx2
  · have : tr A = 2 := by linarith
    rw [this] at ht; norm_num at ht
  · have : tr A = -2 := by linarith
    rw [this] at ht; norm_num at ht

def pathE (σ : ℝ) (ε : ℝ) : GroupedRealMatrix 1 := mk (σ * Real.exp ε) 0 0 (σ * Real.exp (-ε))

lemma pathE_cont (σ : ℝ) : Continuous (pathE σ) := by
  unfold pathE; exact mk_cont (by fun_prop) continuous_const continuous_const (by fun_prop)

lemma hyp_val (r : GroupedRealMatrix 1 → ℂ) (hr : RotationAxiomsTwo r) (σ : ℝ) (hσ : σ ^ 2 = 1)
    (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (ht : 2 < σ * tr A) : r A = σ := by
  set S := {B : GroupedRealMatrix 1 | IsSymplectic B ∧ 2 < σ * tr B}
  have hσ' : σ = 1 ∨ σ = -1 := by
    have : (σ - 1) * (σ + 1) = 0 := by linear_combination hσ
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  have hconn : IsPreconnected S := by
    have hM := (X4CZK.main).2.1.isPreconnected
    have hMS : ∀ B : GroupedRealMatrix 1, IsSymplectic B → ((B - 1).det < 0 ↔ 2 < tr B) := by
      intro B hB; rw [det_sub]; rw [symp_iff] at hB; unfold tr; constructor <;> intro h <;> nlinarith
    rcases hσ' with rfl | rfl
    · convert hM using 1
      ext B; simp only [S, Set.mem_setOf_eq, one_mul]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, (hMS B h1).2 h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, (hMS B h1).1 h2⟩
    · have : S = (fun B => -B) '' {A | IsSymplectic A ∧ (A-1).det < 0} := by
        ext B; simp only [S, Set.mem_setOf_eq, Set.mem_image]
        constructor
        · rintro ⟨h1, h2⟩
          have h1' : IsSymplectic (-B) := by
            rw [eq_mk B, neg_mk, symp_mk]; rw [symp_iff] at h1; linarith
          refine ⟨-B, ⟨h1', (hMS _ h1').2 ?_⟩, neg_neg B⟩
          rw [eq_mk B, neg_mk, tr_mk]; unfold tr at h2; linarith
        · rintro ⟨B', ⟨h1, h2⟩, rfl⟩
          refine ⟨?_, ?_⟩
          · rw [eq_mk B', neg_mk, symp_mk]; rw [symp_iff] at h1; linarith
          · have := (hMS _ h1).1 h2
            rw [eq_mk B', neg_mk, tr_mk]; unfold tr at this; linarith
      rw [this]; exact hM.image _ continuous_neg.continuousOn
  have hsymp : ∀ ε, IsSymplectic (pathE σ ε) := by
    intro ε; unfold pathE; rw [symp_mk]
    rw [show σ * Real.exp ε * (σ * Real.exp (-ε)) = σ ^ 2 * (Real.exp ε * Real.exp (-ε)) by ring,
      ← Real.exp_add]; simp [hσ]
  have hmem : ∀ ε, 0 < ε → pathE σ ε ∈ S := by
    intro ε hε
    refine ⟨hsymp ε, ?_⟩
    unfold pathE; rw [tr_mk]
    have h1 := Real.one_lt_exp_iff.2 hε
    have h2 : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos (-ε)
    rw [show σ * (σ * Real.exp ε + σ * Real.exp (-ε)) = σ ^ 2 * (Real.exp ε + Real.exp (-ε)) by ring, hσ]
    nlinarith
  have hvals : ∀ x ∈ S, r x = 1 ∨ r x = -1 := fun x hx => hr.2.2.2.2 x hx.1 (eig_real x hx.1 (by
    rcases hσ' with rfl | rfl
    · have := hx.2; linarith [le_abs_self (tr x)]
    · have := hx.2; linarith [neg_le_abs (tr x)]))
  have hcont : ContinuousOn r S := hr.1.mono (fun x hx => hx.1)
  have h0 := lim_const r hr.1 (pathE σ) (pathE_cont σ) (fun ε _ => hsymp ε) (r A)
    (fun ε hε => const_of_conn r S hconn hcont hvals _ _ (hmem ε hε) ⟨hA, ht⟩)
  have hp0 : pathE σ 0 = σ • (1 : GroupedRealMatrix 1) := by
    unfold pathE; rw [one_eq]; ext x y
    rcases x with x | x <;> rcases y with y | y <;> simp [mk]
  rw [← h0, hp0]
  rcases hσ' with rfl | rfl
  · rw [one_smul, hr.2.2.1 _ one_symp one_orth, cad_one]; simp
  · rw [neg_one_smul]
    have hs : IsSymplectic (-1 : GroupedRealMatrix 1) := by rw [one_eq, neg_mk, symp_mk]; norm_num
    have ho : IsOrthogonal (-1 : GroupedRealMatrix 1) := by unfold IsOrthogonal; simp
    rw [hr.2.2.1 _ hs ho, cad_neg_one]; simp


lemma r_scal (r : GroupedRealMatrix 1 → ℂ) (hr : RotationAxiomsTwo r) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    r (mk σ 0 0 σ) = σ := by
  have hp0 : mk σ 0 0 σ = σ • (1 : GroupedRealMatrix 1) := by
    rw [one_eq]; ext x y
    rcases x with x | x <;> rcases y with y | y <;> simp [mk]
  rw [hp0]
  rcases hσ with rfl | rfl
  · rw [one_smul, hr.2.2.1 _ one_symp one_orth, cad_one]; simp
  · rw [neg_one_smul]
    have hs : IsSymplectic (-1 : GroupedRealMatrix 1) := by rw [one_eq, neg_mk, symp_mk]; norm_num
    have ho : IsOrthogonal (-1 : GroupedRealMatrix 1) := by unfold IsOrthogonal; simp
    rw [hr.2.2.1 _ hs ho, cad_neg_one]; simp

lemma par_val (r : GroupedRealMatrix 1 → ℂ) (hr : RotationAxiomsTwo r) (σ : ℝ) (hσ : σ ^ 2 = 1)
    (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (ht : σ * tr A = 2) : r A = σ := by
  have hσ' : σ = 1 ∨ σ = -1 := by
    have : (σ - 1) * (σ + 1) = 0 := by linear_combination hσ
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  have hA' := hA
  rw [symp_iff] at hA'
  set a := A i0 i0; set b := A i0 j0; set c := A j0 i0; set d := A j0 j0
  have htr : tr A = a + d := rfl
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · have had : a = d := by
        rw [hc, hb] at hA'; rw [htr] at ht
        nlinarith [sq_nonneg (a - d), sq_nonneg (σ * (a + d))]
      have hA2 : A = mk σ 0 0 σ := by
        have : a = σ := by
          rw [htr, ← had] at ht
          linear_combination (σ / 2) * ht - a * hσ
        rw [eq_mk A]; simp only [a, b, c, d] at *; rw [hb, hc, ← had, this]
      rw [hA2]; exact r_scal r hr σ hσ'
    · set p : ℝ → GroupedRealMatrix 1 := fun ε => A * mk 1 0 (σ * b * ε) 1
      have hp : Continuous p :=
        continuous_const.matrix_mul (mk_cont continuous_const continuous_const (by fun_prop)
          continuous_const)
      have hps : ∀ ε, IsSymplectic (p ε) := fun ε => symp_mul hA (by rw [symp_mk]; ring)
      have h0 := lim_const r hr.1 p hp (fun ε _ => hps ε) σ (fun ε hε => by
        apply hyp_val r hr σ hσ _ (hps ε)
        simp only [p]; rw [eq_mk A, mk_mul, tr_mk]
        have : 0 < b ^ 2 * ε := by positivity
        rw [htr] at ht
        nlinarith)
      have : p 0 = A := by simp only [p, mul_zero, ← one_eq, mul_one]
      rwa [this] at h0
  · set p : ℝ → GroupedRealMatrix 1 := fun ε => A * mk 1 (σ * c * ε) 0 1
    have hp : Continuous p :=
      continuous_const.matrix_mul (mk_cont continuous_const (by fun_prop) continuous_const
        continuous_const)
    have hps : ∀ ε, IsSymplectic (p ε) := fun ε => symp_mul hA (by rw [symp_mk]; ring)
    have h0 := lim_const r hr.1 p hp (fun ε _ => hps ε) σ (fun ε hε => by
      apply hyp_val r hr σ hσ _ (hps ε)
      simp only [p]; rw [eq_mk A, mk_mul, tr_mk]
      have : 0 < c ^ 2 * ε := by positivity
      rw [htr] at ht
      nlinarith)
    have : p 0 = A := by simp only [p, mul_zero, ← one_eq, mul_one]
    rwa [this] at h0

lemma unique (r : GroupedRealMatrix 1 → ℂ) (hr : RotationAxiomsTwo r)
    (A : GroupedRealMatrix 1) (hA : IsSymplectic A) : r A = G A := by
  rcases le_or_gt 2 (tr A) with h | h
  · rw [G_ge A h]
    rcases h.lt_or_eq with h | h
    · simpa using hyp_val r hr 1 (by norm_num) A hA (by linarith)
    · simpa using par_val r hr 1 (by norm_num) A hA (by linarith)
  rcases le_or_gt (tr A) (-2) with h' | h'
  · rw [G_le A h']
    rcases h'.lt_or_eq with h' | h'
    · simpa using hyp_val r hr (-1) (by norm_num) A hA (by linarith)
    · simpa using par_val r hr (-1) (by norm_num) A hA (by linarith)
  exact ell_unique r hr A hA (abs_lt.2 ⟨h', h⟩)

end X4CZO

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

namespace X4CZP

open X4CZK X4CZM X4CZN X4CZO

attribute [local instance] Classical.propDecidable

lemma trace_eq (A : GroupedRealMatrix 1) : A.trace = tr A := by
  simp [Matrix.trace, Fintype.sum_sum_type, tr]

lemma om_vw (v w : Coord 1 → ℝ) :
    (omegaC (fun i => (v i : ℂ) - Complex.I * (w i : ℂ))
      (fun i => star ((v i : ℂ) - Complex.I * (w i : ℂ)))).im = 2 * omegaR v w := by
  simp [omegaC, omegaR, Complex.mul_im, Complex.mul_re]
  ring

lemma third (A : GroupedRealMatrix 1) (hA : IsSymplectic A) (ht : |tr A| < 2) (z : ℂ)
    (v w : Coord 1 → ℝ) (hu0 : (fun i => (v i : ℂ) - Complex.I * (w i : ℂ)) ≠ 0)
    (heig : (complexify A).mulVec (fun i => (v i : ℂ) - Complex.I * (w i : ℂ)) =
      z • (fun i => (v i : ℂ) - Complex.I * (w i : ℂ)))
    (hpos : 0 < omegaR v w) : spectralRotation A = z := by
  set u : Coord 1 → ℂ := fun i => (v i : ℂ) - Complex.I * (w i : ℂ) with hu
  have hsh : shifted A z u = 0 := by
    unfold shifted
    rw [LinearMap.sub_apply, Matrix.toLin'_apply, heig]; simp
  have hA' := hA
  rw [symp_iff] at hA'
  have hdet : ((A i0 i0 : ℝ) : ℂ) * (A j0 j0 : ℝ) - (A i0 j0 : ℝ) * (A j0 i0 : ℝ) = 1 := by
    exact_mod_cast hA'
  have e1 := congrFun hsh i0
  have e2 := congrFun hsh j0
  rw [shifted_apply] at e1 e2
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, Pi.zero_apply,
    Fin.default_eq_zero] at e1 e2
  set t := tr A
  have htC : ((A i0 i0 : ℝ) : ℂ) + (A j0 j0 : ℝ) = (t : ℂ) := by simp [t, tr]
  have hq : z ^ 2 - t * z + 1 = 0 := by
    have k1 : (z ^ 2 - t * z + 1) * u i0 = 0 := by
      rw [← htC]
      linear_combination -(z - (A j0 j0 : ℝ)) * e1 - (A i0 j0 : ℝ) * e2 - u i0 * hdet
    have k2 : (z ^ 2 - t * z + 1) * u j0 = 0 := by
      rw [← htC]
      linear_combination -(A j0 i0 : ℝ) * e1 - (z - (A i0 i0 : ℝ)) * e2 - u j0 * hdet
    by_contra hne
    apply hu0
    funext x
    rcases x with x | x <;> rw [Fin.fin_one_eq_zero x]
    · exact (mul_eq_zero.1 k1).resolve_left hne
    · exact (mul_eq_zero.1 k2).resolve_left hne
  have ht' := abs_lt.1 ht
  set s := Real.sqrt (1 - t ^ 2 / 4)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 - t ^ 2 / 4 by nlinarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by nlinarith)
  set z1 : ℂ := ⟨t / 2, s⟩
  set z2 : ℂ := ⟨t / 2, -s⟩
  have hsum : z1 + z2 = ((A i0 i0 + A j0 j0 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [z1, z2, t, tr]
  have hprod : z1 * z2 = 1 := by
    apply Complex.ext <;> simp [z1, z2] <;> nlinarith
  have hne : z1 ≠ z2 := by
    intro h; have := congrArg Complex.im h; simp [z1, z2] at this; linarith
  have hz : z = z1 ∨ z = z2 := by
    have : (z - z1) * (z - z2) = 0 := by
      have h2 : z1 + z2 = (t : ℂ) := by rw [hsum]; push_cast; exact htC
      linear_combination hq - z * h2 + hprod
    rcases mul_eq_zero.1 this with h | h
    · left; exact sub_eq_zero.1 h
    · right; exact sub_eq_zero.1 h
  have hbc := bc_neg A hA ht
  have hb : A i0 j0 ≠ 0 := by rintro h; rw [h] at hbc; simp at hbc
  have hgen : u ∈ generalizedSpace A z := by
    unfold generalizedSpace
    rw [LinearMap.mem_ker, show 2 * 1 = 2 from rfl, pow_two, Module.End.mul_apply, hsh, map_zero]
  have hbz : A i0 j0 * z.im < 0 := by
    have key : ∀ z' : ℂ, z + z' = ((A i0 i0 + A j0 j0 : ℝ) : ℂ) → z * z' = 1 → z ≠ z' →
        A i0 j0 * z.im < 0 := by
      intro z' h1 h2 h3
      obtain ⟨κ, hκ⟩ := (mem_gen A z z' hA h1 h2 h3 hb u).1 hgen
      have e := omega_u A z κ
      rw [← hκ, om_vw] at e
      have : 0 ≤ Complex.normSq κ := Complex.normSq_nonneg κ
      by_contra hc
      push_neg at hc
      nlinarith [mul_nonneg this hc]
    rcases hz with rfl | rfl
    · exact key z2 hsum hprod hne
    · exact key z1 (by rw [add_comm]; exact hsum) (by rw [mul_comm]; exact hprod) hne.symm
  rw [rot_eq A hA, G, hc_of_abs A ht]
  have hsq : Real.sqrt (1 - (t / 2) ^ 2) = s := by congr 1; ring
  rw [hsq]
  rcases hz with rfl | rfl
  · have hb' : A i0 j0 < 0 := by simp [z1] at hbz; nlinarith
    have hc' : 0 < A j0 i0 := by nlinarith
    rw [Real.sign_of_pos hc']
    apply Complex.ext <;> simp [z1, t]
  · have hb' : 0 < A i0 j0 := by simp [z2] at hbz; nlinarith
    have hc' : A j0 i0 < 0 := by nlinarith
    rw [Real.sign_of_neg hc']
    apply Complex.ext <;> simp [z2, t]

theorem main :
    RotationAxiomsTwo spectralRotation ∧
    (∀ r, RotationAxiomsTwo r → ∀ A, IsSymplectic A → r A = spectralRotation A) ∧
    (∀ A : GroupedRealMatrix 1, IsSymplectic A →
      (1 ≤ A.trace/2 → spectralRotation A = 1) ∧ (A.trace/2 ≤ -1 → spectralRotation A = -1) ∧
      (|A.trace/2| < 1 → ∀ z : ℂ, ∀ v w : Coord 1 → ℝ,
        (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) ≠ 0 →
        (complexify A).mulVec (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) =
          z • (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) →
        0 < omegaR v w → spectralRotation A = z)) := by
  refine ⟨axioms_spec, fun r hr A hA => by rw [unique r hr A hA, rot_eq A hA], ?_⟩
  intro A hA
  rw [trace_eq]
  refine ⟨fun h => (rot_ge A hA (by linarith)).1, fun h => (rot_le A hA (by linarith)).1, ?_⟩
  intro h z v w h0 heig hpos
  have : |tr A| < 2 := by
    rw [abs_lt] at h ⊢; constructor <;> linarith [h.1, h.2]
  exact third A hA this z v w h0 heig hpos

end X4CZP


open QAlgorithms.Papers.Independent.Gap50repair.P01 in
theorem solution :
    RotationAxiomsTwo spectralRotation ∧
    (∀ r, RotationAxiomsTwo r → ∀ A, IsSymplectic A → r A = spectralRotation A) ∧
    (∀ A : GroupedRealMatrix 1, IsSymplectic A →
      (1 ≤ A.trace/2 → spectralRotation A = 1) ∧ (A.trace/2 ≤ -1 → spectralRotation A = -1) ∧
      (|A.trace/2| < 1 → ∀ z : ℂ, ∀ v w : Coord 1 → ℝ,
        (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) ≠ 0 →
        (complexify A).mulVec (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) =
          z • (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) →
        0 < omegaR v w → spectralRotation A = z)) :=
  X4CZP.main
