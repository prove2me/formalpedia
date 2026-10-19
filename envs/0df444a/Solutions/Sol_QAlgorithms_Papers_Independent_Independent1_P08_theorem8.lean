-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.theorem8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:42:33.315673+00:00
-- url     : https://prove2.me/submissions/8651bfbd-1344-4134-a89f-65be6ea3685c

import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_theorem4
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Matrix MatrixOrder ComplexOrder ComplexConjugate
open QAlgorithms QAlgorithms.Entanglement QAlgorithms.QubitChannels
open QAlgorithms.Papers.Independent.Independent1.P08

private def conditional {a : ℕ}
    (F : Matrix Bool Bool ℂ) (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ) :
    Matrix (Fin a) (Fin a) ℂ :=
  Matrix.of fun i j => (F * X.submatrix (fun t => (i,t)) (fun t => (j,t))).trace

private lemma block_sandwich {a : ℕ} (T : Matrix Bool Bool ℂ)
    (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ) (i j : Fin a) :
    ((Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) T) * X *
      (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) T)ᴴ).submatrix
        (fun t => (i,t)) (fun t => (j,t)) =
      T * X.submatrix (fun t => (i,t)) (fun t => (j,t)) * Tᴴ := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker']
  ext u v
  simp [Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.submatrix_apply]

private lemma traceRight_psd {a : ℕ}
    (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ) (hX : X.PosSemidef) :
    (traceRight X).PosSemidef := by
  have heq : traceRight X = ∑ t, X.submatrix (fun i => (i,t)) (fun i => (i,t)) := by
    ext i j
    simp [traceRight, Matrix.sum_apply, Matrix.submatrix]
  rw [heq]
  exact Matrix.posSemidef_sum _ fun t _ => hX.submatrix _

private lemma conditional_psd {a : ℕ}
    (F : Matrix Bool Bool ℂ) (hF : F.PosSemidef)
    (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ) (hX : X.PosSemidef) :
    (conditional F X).PosSemidef := by
  let T := CFC.sqrt F
  have hT : T.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg F)).isHermitian
  have hTT : T * T = F := by simpa [T, pow_two] using CFC.sq_sqrt F hF.nonneg
  let B := Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) T
  have heq : conditional F X = traceRight (B * X * Bᴴ) := by
    ext i j
    change (F * X.submatrix (fun t => (i,t)) (fun t => (j,t))).trace =
      ((B * X * Bᴴ).submatrix (fun t => (i,t)) (fun t => (j,t))).trace
    rw [block_sandwich, hT.eq, Matrix.trace_mul_cycle, hTT]
  rw [heq]
  exact traceRight_psd _ (hX.mul_mul_conjTranspose_same B)

private lemma output_sum {a m : ℕ}
    (R F : Fin m → Matrix Bool Bool ℂ)
    (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ) :
    idTensorSuperop (Entanglement.holevoMap R F) X =
      ∑ k, Matrix.kronecker (conditional (F k) X) (R k) := by
  ext p q
  simp [idTensorSuperop, Entanglement.holevoMap, conditional,
    Matrix.sum_apply, Matrix.submatrix]

private def axis (j : Fin 3) (b : Bool) : Matrix Bool Bool ℂ :=
  (1/2 : ℂ) • (1 + (if b then (1 : ℂ) else -1) • sigma j)

private lemma axis_density (j : Fin 3) (b : Bool) : IsDensityMatrix (axis j b) := by
  have he : axis j b * (axis j b)ᴴ = axis j b := by
    ext x y
    fin_cases j <;> cases b <;> cases x <;> cases y <;>
      norm_num [axis, sigma, pauliX, pauliY, pauliZ, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Complex.I_sq, map_ofNat] <;> ring_nf <;> norm_num [Complex.I_sq]
  constructor
  · rw [← he]
    simpa using (Matrix.PosSemidef.one.mul_mul_conjTranspose_same (axis j b))
  · fin_cases j <;> cases b <;>
      norm_num [axis, sigma, pauliX, pauliY, pauliZ, Matrix.trace, Matrix.diag]

private def outStates : Fin 7 → Matrix Bool Bool ℂ :=
  ![(1/2 : ℂ) • 1, axis 0 true, axis 0 false,
    axis 1 true, axis 1 false, axis 2 true, axis 2 false]

private def pairEffect (j : Fin 3) (v : ℝ) (b : Bool) : Matrix Bool Bool ℂ :=
  (((|v|+v)/2 : ℝ) : ℂ) • axis j b + (((|v|-v)/2 : ℝ) : ℂ) • axis j (!b)

private def effects (lam : Bloch) : Fin 7 → Matrix Bool Bool ℂ :=
  ![((1 - ∑ j, |lam j| : ℝ) : ℂ) • 1,
    pairEffect 0 (lam 0) true, pairEffect 0 (lam 0) false,
    pairEffect 1 (lam 1) true, pairEffect 1 (lam 1) false,
    pairEffect 2 (lam 2) true, pairEffect 2 (lam 2) false]

private lemma output_states_density (k : Fin 7) : IsDensityMatrix (outStates k) := by
  fin_cases k
  · constructor
    · exact Matrix.PosSemidef.one.smul (by norm_num [Complex.nonneg_iff])
    · norm_num [outStates, Matrix.trace_smul, Matrix.trace_one]
  all_goals apply axis_density

private lemma pairEffect_psd (j : Fin 3) (v : ℝ) (b : Bool) : (pairEffect j v b).PosSemidef := by
  apply Matrix.PosSemidef.add
  · apply (axis_density j b).1.smul
    exact_mod_cast (show 0 ≤ (|v|+v)/2 by linarith [neg_abs_le v])
  · apply (axis_density j (!b)).1.smul
    exact_mod_cast (show 0 ≤ (|v|-v)/2 by linarith [le_abs_self v])

private lemma effects_povm (lam : Bloch) (h : ∑ j, |lam j| ≤ 1) : IsPOVM (effects lam) := by
  constructor
  · intro k
    fin_cases k
    · exact Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.mpr h)
    all_goals exact pairEffect_psd _ _ _
  · ext x y
    cases x <;> cases y <;>
      norm_num [effects, pairEffect, axis, sigma, pauliX, pauliY, pauliZ, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 800000 in
private lemma canonical_holevo (lam : Bloch) : canonical 0 lam = holevoMap outStates (effects lam) := by
  ext X x y
  cases x <;> cases y <;>
    norm_num [canonical, blochAffineMap, outStates, effects, pairEffect, axis, holevoMap,
      Matrix.mul_apply, Matrix.trace, Matrix.diag, Matrix.diagonal,
      sigma, pauliX, pauliY, pauliZ, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [Complex.I_sq, Fin.ext_iff, Matrix.cons_val_two]

private lemma holevo_cpt {m : ℕ} (R F : Fin m → Matrix Bool Bool ℂ)
    (hR : ∀ k, IsDensityMatrix (R k)) (hF : IsPOVM F) :
    CPT (holevoMap R F) := by
  constructor
  · intro X
    simp only [holevoMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace_sum,
      Matrix.trace_smul, (hR _).2, smul_eq_mul, mul_one]
    rw [← Matrix.trace_sum, ← Finset.sum_mul, hF.2, Matrix.one_mul]
  · intro a X hX
    rw [output_sum]
    exact Matrix.posSemidef_sum _ fun k _ =>
      (conditional_psd (F k) (hF.1 k) X hX).kronecker (hR k).1

private lemma canonical_unital (lam : Bloch) : canonical 0 lam 1 = 1 := by
  ext x y
  cases x <;> cases y <;>
    norm_num [canonical, blochAffineMap, Matrix.mul_apply, Matrix.trace, Matrix.diag,
      Matrix.diagonal, sigma, pauliX, pauliY, pauliZ, Fin.sum_univ_succ]

private lemma canonical_rep (lam : Bloch) :
    HasCanonicalRepresentation (canonical 0 lam) 0 lam := by
  refine ⟨1, 1, ?_⟩
  intro X
  simp [conjSuperop, canonical]

private lemma parameters_iff (lam : Bloch) :
    lam ∈ unitalParameters ↔ ∑ j, |lam j| ≤ 1 := by
  constructor
  · intro h
    exact (theorem4 _ h.1 (canonical_unital lam) 0 lam (canonical_rep lam)).mp h.2
  · intro h
    have hc : CPT (canonical 0 lam) := by
      rw [canonical_holevo]
      exact holevo_cpt _ _ output_states_density (effects_povm lam h)
    exact ⟨hc, (theorem4 _ hc (canonical_unital lam) 0 lam (canonical_rep lam)).mpr h⟩

private def ball : Set Bloch := {x | ∑ j, |x j| ≤ 1}

private lemma ball_convex : Convex ℝ ball := by
  intro x hx y hy a b ha hb hab
  change ∑ j, |a * x j + b * y j| ≤ 1
  calc
    _ ≤ ∑ j, (a * |x j| + b * |y j|) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ |a*x j| + |b*y j| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a * (∑ j, |x j|) + b * (∑ j, |y j|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by linarith

private lemma vertex_ball (j : Fin 3) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    Pi.single j s ∈ ball := by
  rcases hs with rfl | rfl <;>
    simp [ball, Pi.single_apply, abs_ite, Finset.sum_ite_eq']

private lemma vertices_subset : octahedronVertices ⊆ ball := by
  rintro x ⟨j,s,hs,rfl⟩
  exact vertex_ball j s hs

private def vertices : Fin 7 → Bloch :=
  ![0, Pi.single 0 1, Pi.single 0 (-1), Pi.single 1 1,
    Pi.single 1 (-1), Pi.single 2 1, Pi.single 2 (-1)]

private def weights (x : Bloch) : Fin 7 → ℝ :=
  ![1 - ∑ j, |x j|, (|x 0|+x 0)/2, (|x 0|-x 0)/2,
    (|x 1|+x 1)/2, (|x 1|-x 1)/2, (|x 2|+x 2)/2, (|x 2|-x 2)/2]

private lemma zero_hull : (0 : Bloch) ∈ convexHull ℝ octahedronVertices := by
  have hp : (Pi.single 0 (1 : ℝ) : Bloch) ∈ convexHull ℝ octahedronVertices :=
    subset_convexHull ℝ _ ⟨0,1,Or.inl rfl,rfl⟩
  have hn : (Pi.single 0 (-1 : ℝ) : Bloch) ∈ convexHull ℝ octahedronVertices :=
    subset_convexHull ℝ _ ⟨0,-1,Or.inr rfl,rfl⟩
  have h := (convex_convexHull ℝ octahedronVertices) hp hn
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1/2 : ℝ)+1/2=1 by norm_num)
  convert h using 1
  ext j
  simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> ring

private lemma ball_hull : ball = convexHull ℝ octahedronVertices := by
  apply Set.Subset.antisymm
  · intro x hx
    have hw : ∀ k ∈ (Finset.univ : Finset (Fin 7)), 0 ≤ weights x k := by
      intro k _
      fin_cases k
      · exact sub_nonneg.mpr hx
      all_goals
        dsimp [weights]
        linarith [neg_abs_le (x 0), le_abs_self (x 0), neg_abs_le (x 1),
          le_abs_self (x 1), neg_abs_le (x 2), le_abs_self (x 2)]
    have hs : ∑ k : Fin 7, weights x k = 1 := by
      norm_num [weights, Fin.sum_univ_succ]
      ring
    have hv : ∀ k ∈ (Finset.univ : Finset (Fin 7)),
        vertices k ∈ convexHull ℝ octahedronVertices := by
      intro k _
      fin_cases k
      · exact zero_hull
      all_goals apply subset_convexHull ℝ _; exact ⟨_,_,by simp,rfl⟩
    have hh := (convex_convexHull ℝ octahedronVertices).sum_mem hw hs hv
    have he : ∑ k : Fin 7, weights x k • vertices k = x := by
      ext j
      fin_cases j <;> norm_num [weights, vertices, Pi.single_apply, Fin.sum_univ_succ, Fin.ext_iff] <;> ring_nf
      all_goals rfl
    rwa [he] at hh
  · exact convexHull_min vertices_subset ball_convex

private lemma coordinate_bound {x : Bloch} (hx : x ∈ ball) (j : Fin 3) : |x j| ≤ 1 := by
  exact (Finset.single_le_sum (fun k _ => abs_nonneg (x k)) (Finset.mem_univ j)).trans hx

private lemma saturated {x : Bloch} (hx : x ∈ ball) (j : Fin 3) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (h : x j = s) : x = Pi.single j s := by
  have habs : |x j| = 1 := by rw [h]; rcases hs with rfl | rfl <;> norm_num
  have hz : ∑ k ∈ Finset.univ.erase j, |x k| = 0 := by
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin 3)) (fun k => |x k|)
      (Finset.mem_univ j)
    have hn : 0 ≤ ∑ k ∈ Finset.univ.erase j, |x k| :=
      Finset.sum_nonneg (fun k _ => abs_nonneg _)
    change ∑ k, |x k| ≤ 1 at hx
    linarith
  ext k
  by_cases hk : k = j
  · subst k
    simpa using h
  · rw [Pi.single_eq_of_ne hk]
    have he := Finset.single_le_sum (fun k _ => abs_nonneg (x k))
      (show k ∈ Finset.univ.erase j by simp [hk])
    rw [hz] at he
    exact abs_eq_zero.mp (le_antisymm he (abs_nonneg _))

private lemma vertex_extreme (j : Fin 3) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    Pi.single j s ∈ ball.extremePoints ℝ := by
  refine ⟨vertex_ball j s hs, ?_⟩
  intro x hx y hy hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hj := congrFun he j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at hj
  have hxj := coordinate_bound hx j
  have hyj := coordinate_bound hy j
  apply saturated hx j s hs
  rcases hs with rfl | rfl
  · have hxx := le_abs_self (x j)
    have hyy := le_abs_self (y j)
    nlinarith
  · have hxx := neg_abs_le (x j)
    have hyy := neg_abs_le (y j)
    nlinarith

theorem solution : unitalParameters = convexHull ℝ octahedronVertices ∧
    unitalParameters.extremePoints ℝ = octahedronVertices := by
  have he : unitalParameters = ball := Set.ext parameters_iff
  constructor
  · exact he.trans ball_hull
  · rw [he]
    apply Set.Subset.antisymm
    · rw [ball_hull]
      exact extremePoints_convexHull_subset
    · rintro x ⟨j,s,hs,rfl⟩
      exact vertex_extreme j s hs

#print axioms solution
