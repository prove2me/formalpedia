-- Prove2me | solution 1 for TwoReLULayers.DepthCollapse.network_geometric_cpwl
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:09:07.142365+00:00
-- url     : https://prove2.me/submissions/42bb8142-8ebd-46d8-a984-2cbf5113c0f7

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

open TwoReLULayers.DepthCollapse
open Finset
noncomputable section

private def composeAffine {R : Subfield ℝ} {n m : ℕ}
    (a : AffineScalar R m) (A : AffineR R n m) : AffineScalar R n where
  bias := a.bias + ∑ i, a.weight i * (A i).bias
  weight := fun j => ∑ i, a.weight i * (A i).weight j

private theorem composeAffine_eval {R : Subfield ℝ} {n m : ℕ}
    (a : AffineScalar R m) (A : AffineR R n m) (x : E n) :
    (composeAffine a A).eval x = a.eval (affineEval A x) := by
  simp [composeAffine, AffineScalar.eval, affineEval, Finset.sum_mul,
    Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_assoc]
  rw [Finset.sum_comm]
  ring

private def zeroAffine {R : Subfield ℝ} {n : ℕ} : AffineScalar R n := ⟨fun _ => 0, 0⟩

private def mask {R : Subfield ℝ} {n m : ℕ}
    (A : AffineR R n m) (s : Fin m → Bool) : AffineR R n m :=
  fun j => if s j then A j else zeroAffine

private def signCell {R : Subfield ℝ} {n m : ℕ}
    (A : AffineR R n m) (s : Fin m → Bool) : Set (E n) :=
  {x | ∀ j, if s j then 0 ≤ (A j).eval x else (A j).eval x ≤ 0}

private theorem masked_eval {R : Subfield ℝ} {n m : ℕ}
    (A : AffineR R n m) (s : Fin m → Bool) {x : E n} (hx : x ∈ signCell A s) :
    affineEval (mask A s) x = relu (affineEval A x) := by
  ext j
  have hj := hx j
  cases h : s j <;> simp [signCell, mask, affineEval, relu, zeroAffine, AffineScalar.eval, h] at hj ⊢
  · exact hj
  · exact hj

private theorem signCell_cover {R : Subfield ℝ} {n m : ℕ}
    (A : AffineR R n m) (x : E n) : ∃ s, x ∈ signCell A s := by
  classical
  refine ⟨fun j => decide (0 ≤ (A j).eval x), fun j => ?_⟩
  by_cases h : 0 ≤ (A j).eval x
  · simp [h]
  · simp [h, (le_of_not_ge h)]

private theorem polyhedral_signCell {R : Subfield ℝ} {n m : ℕ}
    (A : AffineR R n m) (s : Fin m → Bool) : IsPolyhedron (signCell A s) := by
  refine ⟨m,
    (fun j => WithLp.toLp 2 (fun i => if s j then -(A j).weight i else (A j).weight i)),
    (fun j => if s j then ((A j).bias : ℝ) else -((A j).bias : ℝ)), ?_⟩
  ext x
  apply forall_congr'
  intro j
  cases h : s j <;> simp only [h, Bool.false_eq_true, ↓reduceIte, dot, AffineScalar.eval]
  all_goals try simp only [neg_mul, Finset.sum_neg_distrib]
  all_goals (constructor <;> intro hle <;> linarith)

private theorem polyhedral_inter {n : ℕ} {P Q : Set (E n)}
    (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) : IsPolyhedron (P ∩ Q) := by
  obtain ⟨k, a, b, rfl⟩ := hP
  obtain ⟨l, c, d, rfl⟩ := hQ
  refine ⟨k + l, Fin.append a c, Fin.append b d, ?_⟩
  ext x
  simp [Fin.forall_fin_add]

private theorem continuous_affine {R : Subfield ℝ} {n : ℕ} (a : AffineScalar R n) :
    Continuous a.eval := by
  unfold AffineScalar.eval
  fun_prop

private theorem continuous_affineEval {R : Subfield ℝ} {n m : ℕ} (A : AffineR R n m) :
    Continuous (affineEval A) := by
  exact PiLp.continuous_toLp 2 (fun _ => ℝ) |>.comp (continuous_pi fun j => continuous_affine (A j))

private theorem continuous_relu {n : ℕ} : Continuous (relu : E n → E n) := by
  exact PiLp.continuous_toLp 2 (fun _ => ℝ) |>.comp
    (continuous_pi fun i => continuous_const.max (EuclideanSpace.proj i).continuous)

theorem solution {n : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ)
    (N : Network2 R n) : N.eval ∈ CPWL R n := by
  classical
  let B : (Fin N.width₁ → Bool) → AffineR R n N.width₂ :=
    fun s j => composeAffine (N.second j) (mask N.first s)
  let C : ((Fin N.width₁ → Bool) × (Fin N.width₂ → Bool)) → Set (E n) :=
    fun st => signCell N.first st.1 ∩ signCell (B st.1) st.2
  let D : ((Fin N.width₁ → Bool) × (Fin N.width₂ → Bool)) → AffineScalar R n :=
    fun st => composeAffine N.output (mask (B st.1) st.2)
  let e := Fintype.equivFin ((Fin N.width₁ → Bool) × (Fin N.width₂ → Bool))
  refine ⟨?_, Fintype.card _, (fun j => C (e.symm j)), (fun j => D (e.symm j)), ?_, ?_, ?_⟩
  · exact (continuous_affine N.output).comp
      (continuous_relu.comp ((continuous_affineEval N.second).comp
        (continuous_relu.comp (continuous_affineEval N.first))))
  · intro j
    exact polyhedral_inter (polyhedral_signCell _ _) (polyhedral_signCell _ _)
  · intro x
    obtain ⟨s, hs⟩ := signCell_cover N.first x
    obtain ⟨t, ht⟩ := signCell_cover (B s) x
    exact ⟨e (s,t), by simpa [C] using And.intro hs ht⟩
  · intro j x hx
    obtain ⟨hs, ht⟩ := hx
    change N.eval x = (composeAffine N.output (mask (B (e.symm j).1) (e.symm j).2)).eval x
    rw [composeAffine_eval, masked_eval _ _ ht]
    have heq : affineEval (B (e.symm j).1) x =
        affineEval N.second (relu (affineEval N.first x)) := by
      ext i
      change (composeAffine (N.second i) (mask N.first (e.symm j).1)).eval x = _
      rw [composeAffine_eval, masked_eval _ _ hs]
      rfl
    rw [heq]
    rfl
