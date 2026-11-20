-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.short_sum_rational_representative
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-19T20:01:47.07831+00:00
-- url     : https://prove2.me/submissions/90e97621-9ce9-4350-aa51-09a6b235180f

import Mathlib.Data.Int.Interval
import Theorems.Thm_SmaleNinth_exists_minimal_face_point
import Theorems.Thm_SmaleNinth_exists_square_subsystem
import Theorems.Thm_SmaleNinth_abs_det_le_factorial_mul_pow

set_option autoImplicit false
open Matrix LinearOptimization

private theorem smallPoint {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (hne : (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty) :
    ∃ (D : ℤ) (z : Fin n → ℤ), D ≠ 0 ∧ D.natAbs ≤ n.factorial * U^n ∧
      (∀ j, (z j).natAbs ≤ n.factorial * U^n) ∧
      (fun j => (z j : ℝ) / D) ∈ polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) := by
  classical
  let A' := A.map (Int.cast : ℤ → ℝ)
  obtain ⟨x,I,_,hx,hface⟩ := SmaleNinth.exists_minimal_face_point A' _ hne
  obtain ⟨r,y,row,col,hy,hr,hdet,hsolve,hoff⟩ :=
    SmaleNinth.exists_square_subsystem A' _ I x hx
  let M := A.submatrix row col
  let M' := M.map (Int.cast : ℤ → ℝ)
  let b' := fun i => b (row i)
  change M'.det ≠ 0 at hdet
  have hcast : M'.det = (M.det : ℝ) := (Int.cast_det M).symm
  have hneR : (M.det : ℝ) ≠ 0 := hcast ▸ hdet
  have hneZ : M.det ≠ 0 := by exact_mod_cast hneR
  have hsolve' : M'.mulVec (fun k => y (col k)) = (fun k => (b' k : ℝ)) := hsolve
  have hM (a c) : |M a c| ≤ (U : ℤ) := hA _ _
  have hbound (N : Matrix (Fin r) (Fin r) ℤ) (hN : ∀ a c, |N a c| ≤ (U : ℤ)) :
      N.det.natAbs ≤ n.factorial * U^n := by
    have h := SmaleNinth.abs_det_le_factorial_mul_pow U N hN
    have h' : (N.det.natAbs : ℤ) ≤ ((r.factorial * U^r : ℕ) : ℤ) := by
      simpa [Int.natCast_natAbs] using h
    refine (show N.det.natAbs ≤ r.factorial * U^r by exact_mod_cast h').trans ?_
    exact Nat.mul_le_mul (Nat.factorial_le hr) (Nat.pow_le_pow_right hU hr)
  let v := fun i => (M.updateCol i b').det
  have hv (i) : (v i).natAbs ≤ n.factorial * U^n := by
    apply hbound
    intro a c
    by_cases he : c = i <;> simp [he,b',hb,hM]
  have hC : M'.det • (fun k => y (col k)) = M'.cramer (fun k => (b' k : ℝ)) := by
    apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det M').2 (isUnit_iff_ne_zero.2 hdet))
    rw [Matrix.mulVec_smul,hsolve',Matrix.mulVec_cramer]
  have ratio (i) : (v i : ℝ) / M.det = y (col i) := by
    apply (div_eq_iff hneR).2
    have he : (M'.updateCol i (fun k => (b' k : ℝ))) =
        (M.updateCol i b').map (Int.cast : ℤ → ℝ) := by
      ext a c
      by_cases h : c = i <;> simp [h,M']
    have hi := congrFun hC i
    change M'.det * y (col i) = _ at hi
    rw [hcast,Matrix.cramer_apply,he,← Int.cast_det (M.updateCol i b')] at hi
    simpa [v,mul_comm] using hi.symm
  let z (j : Fin n) : ℤ := if h : j ∈ Set.range col then v h.choose else 0
  refine ⟨M.det,z,hneZ,hbound M hM,?_,?_⟩
  · intro j
    by_cases h : j ∈ Set.range col
    · simp only [z,dif_pos h]
      exact hv h.choose
    · simp only [z,dif_neg h,Int.natAbs_zero,Nat.zero_le]
  · have he : (fun j => (z j : ℝ) / M.det) = y := by
      funext j
      by_cases h : j ∈ Set.range col
      · simp only [z,dif_pos h]
        exact (ratio h.choose).trans (congrArg y h.choose_spec)
      · simp only [z,dif_neg h,Int.cast_zero,zero_div,hoff j h]
    rw [he]
    exact hface y hy

private theorem preserveLinear {ι : Type} [Fintype ι] (x : ι → ℝ) (U : ℕ) (hU : 1 ≤ U) :
    ∃ (D : ℤ) (z : ι → ℤ), D ≠ 0 ∧ D.natAbs ≤ (Fintype.card ι).factorial * U^Fintype.card ι ∧
      (∀ i, (z i).natAbs ≤ (Fintype.card ι).factorial * U^Fintype.card ι) ∧
      ∀ (a : ι → ℤ) (b : ℤ), (∀ i, |a i| ≤ U) → |b| ≤ U →
        (b : ℝ) ≤ ∑ i, (a i : ℝ)*x i → (b : ℝ) ≤ ∑ i, (a i : ℝ)*((z i : ℝ)/D) := by
  classical
  let B := ↥(Finset.Icc (-(U : ℤ)) (U : ℤ))
  let R := {p : (ι → B) × B // ((p.2.val : ℤ) : ℝ) ≤ ∑ i, ((p.1 i).val : ℝ) * x i}
  let e := (Fintype.equivFin ι).symm
  let f := (Fintype.equivFin R).symm
  let A : Matrix (Fin (Fintype.card R)) (Fin (Fintype.card ι)) ℤ := fun i j => ((f i).val.1 (e j)).val
  let b := fun i => (f i).val.2.val
  have bound (p : B) : |p.val| ≤ U := abs_le.mpr (Finset.mem_Icc.mp p.property)
  obtain ⟨D,z,hD,hd,hz,hs⟩ := smallPoint U hU A b (fun i j => bound _) (fun i => bound _) (by
    refine ⟨fun j => x (e j),?_⟩
    intro i
    change (b i : ℝ) ≤ ∑ j, (((f i).val.1 (e j)).val : ℝ) * x (e j)
    rw [e.sum_comp (fun j => (((f i).val.1 j).val : ℝ) * x j)]
    exact (f i).property)
  refine ⟨D,fun i => z (e.symm i),hD,hd,fun i => hz _,?_⟩
  intro a b₀ ha hb hx
  let p : R := ⟨(fun i => ⟨a i,Finset.mem_Icc.mpr (abs_le.mp (ha i))⟩,
                     ⟨b₀,Finset.mem_Icc.mpr (abs_le.mp hb)⟩),hx⟩
  have h := hs (f.symm p)
  change ((f (f.symm p)).val.2.val : ℝ) ≤ ∑ j, (((f (f.symm p)).val.1 (e j)).val : ℝ)*((z j : ℝ)/D) at h
  simp only [Equiv.apply_symm_apply] at h
  rw [← e.sum_comp (fun i => (a i : ℝ)*((z (e.symm i) : ℝ)/D))]
  simpa [p] using h

private theorem sumCounts {ι : Type} [Fintype ι] [DecidableEq ι] (s : List ι) (v : ι → ℝ) :
    ∑ i, (s.count i : ℝ)*v i = (s.map v).sum := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.count_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib, ih,List.map_cons,List.sum_cons]
    simp [add_comm]

theorem solution {ι : Type} [Fintype ι] (x : ι → ℝ) (H : ℕ) (hH : 1 ≤ H) :
    ∃ (D : ℤ) (z : ι → ℤ), D ≠ 0 ∧
      D.natAbs ≤ (Fintype.card ι).factorial * (H ^ 2) ^ Fintype.card ι ∧
      (∀ i, (z i).natAbs ≤ (Fintype.card ι).factorial * (H ^ 2) ^ Fintype.card ι) ∧
      ∀ (s t : List ι) (q : ℚ), s.length + t.length ≤ H →
        q.num.natAbs ≤ H → q.den ≤ H →
        (q : ℝ) + (s.map x).sum ≤ (t.map x).sum →
        (q : ℝ) + (s.map (fun i => ((z i : ℝ) / D))).sum ≤
          (t.map (fun i => ((z i : ℝ) / D))).sum := by
  classical
  obtain ⟨D,z,hD,hd,hz,hpres⟩ := preserveLinear x (H^2) (by nlinarith)
  refine ⟨D,z,hD,hd,hz,?_⟩
  intro s t q hlen hnum hden hcmp
  let a (i : ι) : ℤ := q.den * ((t.count i : ℤ) - s.count i)
  have ha (i : ι) : |a i| ≤ ((H^2 : ℕ) : ℤ) := by
    have hs := List.count_le_length (a := i) (l := s)
    have ht := List.count_le_length (a := i) (l := t)
    have hdiff : |(t.count i : ℤ) - s.count i| ≤ H := abs_le.mpr ⟨by omega, by omega⟩
    simp only [a,abs_mul,abs_of_nonneg (Int.natCast_nonneg _),pow_two]
    exact mul_le_mul (by exact_mod_cast hden) hdiff (abs_nonneg _) (Int.natCast_nonneg _)
  have hb : |q.num| ≤ ((H^2 : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast (show q.num.natAbs ≤ H^2 by nlinarith)
  have eqsum (v : ι → ℝ) : (∑ i, (a i : ℝ)*v i) = (q.den : ℝ) * ((t.map v).sum - (s.map v).sum) := by
    simp only [a,Int.cast_mul,Int.cast_natCast,Int.cast_sub,mul_assoc,← Finset.mul_sum,
      sub_mul,Finset.sum_sub_distrib,sumCounts]
  have hp : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have equiv (v : ι → ℝ) : (q : ℝ) + (s.map v).sum ≤ (t.map v).sum ↔
      (q.num : ℝ) ≤ ∑ i, (a i : ℝ)*v i := by
    rw [eqsum,Rat.cast_def,← le_sub_iff_add_le,div_le_iff₀ hp,mul_comm]
  exact (equiv _).2 (hpres a q.num ha hb ((equiv x).1 hcmp))
