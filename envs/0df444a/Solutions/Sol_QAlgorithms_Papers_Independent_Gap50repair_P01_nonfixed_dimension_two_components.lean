-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.nonfixed_dimension_two_components
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:08:18.849442+00:00
-- url     : https://prove2.me/submissions/1c617d60-12de-40d9-8094-c3e50eed2d2b

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

open QAlgorithms.Papers.Independent.Gap50repair.P01 in
theorem solution :
    let P : Set (GroupedRealMatrix 1) := {A | IsSymplectic A ∧ 0 < (A-1).det}
    let M : Set (GroupedRealMatrix 1) := {A | IsSymplectic A ∧ (A-1).det < 0}
    IsConnected P ∧ IsConnected M ∧ Disjoint P M ∧
      {A | IsSymplectic A ∧ (A-1).det ≠ 0} = P ∪ M ∧
      (∀ S : Set (GroupedRealMatrix 1), IsConnected S → S ⊆ P ∪ M → S ⊆ P ∨ S ⊆ M) :=
  X4CZK.main
