-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_edge_transport
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:09:56.80021+00:00
-- url     : https://prove2.me/submissions/6aaaf7fd-2df7-44a9-887c-adc70b3d0e33

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Mathlib
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open scoped Classical BigOperators
open ZeroFreeRRG.Hardcore

private lemma pi0 (a : ℝ) : Model.pi .hardcore a (0 : Fin 2) = 1-a := by
  simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two] <;> ring
private lemma pi1 (a : ℝ) : Model.pi .hardcore a (1 : Fin 2) = a := by
  simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two] <;> ring

/-- Equation (25) for the hardcore cavity interaction and edge factor. -/
private theorem hardcore_centered_factors (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
    (x y : Fin 2 → ℝ) (hx : (∑ i, x i) = 1) (hy : (∑ i, y i) = 1) :
    let θ := a/(1-a)
    let h := (x 1-a)/(1-a)
    let k := (y 1-a)/(1-a)
    Mmul .hardcore a x (0 : Fin 2) = 1+θ*h ∧
    Mmul .hardcore a x (1 : Fin 2) = 1-h ∧
    edgeFactor .hardcore a x y = 1-h*k := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hne : 1-a ≠ 0 := by linarith
  have hx' : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx
  have hy' : y 0 + y 1 = 1 := by simpa [Fin.sum_univ_two] using hy
  dsimp
  unfold Mmul edgeFactor
  change (∑ j : Fin 2, Model.M .hardcore a (0 : Fin 2) j * x j) = _ ∧
    (∑ j : Fin 2, Model.M .hardcore a (1 : Fin 2) j * x j) = _ ∧
    (∑ i : Fin 2, ∑ j : Fin 2, x i * Model.M .hardcore a i j * y j) = _
  simp only [Fin.sum_univ_two, Model.M, pi0, pi1, Model.P]
  simp only [Fin.val_zero, Fin.val_one, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero, true_and,
    false_and, ↓reduceIte]
  norm_num only [Nat.one_ne_zero, Nat.zero_ne_one, false_and, ↓reduceIte]
  simp only [ite_false, ite_true]
  constructor
  · field_simp
    <;> nlinarith
  constructor
  · field_simp
    <;> nlinarith
  have hx0 : x 0 = 1 - x 1 := by linarith
  have hy0 : y 0 = 1 - y 1 := by linarith
  rw [hx0, hy0]
  field_simp
  <;> ring


/-- The centered message and edge factor do not change under hardcore transport. -/
theorem solution (a a' : ℝ) (ha : 0 < a) (hlt : a < a') (ha' : a' < 1/2)
    (x y : Fin 2 → ℝ) (hx : (∑ i, x i) = 1) (hy : (∑ i, y i) = 1) :
    let c := (1-a')/(1-a)
    let T := fun (x : Fin 2 → ℝ) i => (1-c)*(if i.val = 1 then 1 else 0) + c*x i
    (∑ i, T x i) = 1 ∧ (∑ i, T y i) = 1 ∧
    (T x 1-a')/(1-a') = (x 1-a)/(1-a) ∧
    (T y 1-a')/(1-a') = (y 1-a)/(1-a) ∧
    edgeFactor .hardcore a' (T x) (T y) = edgeFactor .hardcore a x y := by
  dsimp only
  let c := (1-a')/(1-a)
  let T : (Fin 2 → ℝ) → Fin 2 → ℝ := fun x i => (1-c)*(if i.val=1 then 1 else 0)+c*x i
  have hapos : 0 < a' := by linarith
  have hden : 1-a ≠ 0 := by linarith
  have hden' : 1-a' ≠ 0 := by linarith
  have hsum (z : Fin 2 → ℝ) (hz : (∑ i, z i)=1) : (∑ i, T z i)=1 := by
    have hz' : z 0 + z 1 = 1 := by simpa [Fin.sum_univ_two] using hz
    rw [Fin.sum_univ_two]
    dsimp [T]
    norm_num only [Fin.val_zero, Fin.val_one, Nat.zero_ne_one, ↓reduceIte, mul_zero, zero_add, mul_one]
    nlinarith [congrArg (fun v : ℝ => c*v) hz']
  have hh (z : Fin 2 → ℝ) : (T z 1-a')/(1-a') = (z 1-a)/(1-a) := by
    dsimp [T,c]
    norm_num only [Fin.val_one, ↓reduceIte, mul_one]
    field_simp
    <;> ring
  have he0 := (hardcore_centered_factors a ha (by linarith) x y hx hy).2.2
  have he1 := (hardcore_centered_factors a' hapos ha' (T x) (T y) (hsum x hx) (hsum y hy)).2.2
  change edgeFactor .hardcore a' (T x) (T y) = _ at he1
  rw [hh x,hh y] at he1
  exact ⟨hsum x hx,hsum y hy,hh x,hh y,he1.trans he0.symm⟩
