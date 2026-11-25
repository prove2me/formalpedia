-- Prove2me | solution 1 for SteerableE2CNN.irrep_decomposition_kernel_constraint
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T12:44:16.457042+00:00
-- url     : https://prove2.me/submissions/70839648-532e-48f9-93a1-a7e1e9526a72

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic
set_option autoImplicit false
open Matrix MeasureTheory
namespace SteerableE2CNN

lemma repMat_inv' {H : Type*} [Group H] {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : MatRep H n) (g : H) : (repMat ρ g)⁻¹ = repMat ρ g⁻¹ := by
  unfold repMat
  rw [map_inv]
  exact Matrix.inv_eq_left_inv (ρ g).inv_mul

lemma blk {Iout Iin : Type*} [Fintype Iout] [DecidableEq Iout] [Fintype Iin] [DecidableEq Iin]
    {dOut : Iout → ℕ} {dIn : Iin → ℕ}
    (A : ∀ i, Matrix (Fin (dOut i)) (Fin (dOut i)) ℝ) (B : ∀ j, Matrix (Fin (dIn j)) (Fin (dIn j)) ℝ)
    (K : Matrix (Σ i, Fin (dOut i)) (Σ j, Fin (dIn j)) ℝ) (i : Iout) (j : Iin) :
    kernelBlock (Matrix.blockDiagonal' A * K * Matrix.blockDiagonal' B) i j =
      A i * kernelBlock K i j * B j := by
  ext a b
  simp only [kernelBlock, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sigma,
    Matrix.blockDiagonal'_apply]
  simp [dite_mul, mul_dite, Finset.sum_dite_eq, Finset.sum_dite_eq']

lemma blocks_ext {Iout Iin : Type*} {dOut : Iout → ℕ} {dIn : Iin → ℕ}
    (M N : Matrix (Σ i, Fin (dOut i)) (Σ j, Fin (dIn j)) ℝ) :
    M = N ↔ ∀ i j, kernelBlock M i j = kernelBlock N i j := by
  constructor
  · intro h i j; rw [h]
  · intro h
    ext ⟨i, a⟩ ⟨j, b⟩
    have := congrFun (congrFun (h i j) a) b
    simpa [kernelBlock] using this

theorem irrep_decomposition_kernel_constraint (G : Subgroup O2)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {Iout Iin : Type*} [Fintype Iout] [DecidableEq Iout] [Fintype Iin] [DecidableEq Iin]
    {dOut : Iout → ℕ} {dIn : Iin → ℕ}
    (ψout : ∀ i, MatRep G (Fin (dOut i))) (ψin : ∀ j, MatRep G (Fin (dIn j)))
    (hψout : ∀ i, IsIrrep (ψout i)) (hψin : ∀ j, IsIrrep (ψin j))
    (ρout : MatRep G m) (ρin : MatRep G n)
    (Qout : Matrix (Σ i, Fin (dOut i)) m ℝ) (Qout' : Matrix m (Σ i, Fin (dOut i)) ℝ)
    (hQout : Qout' * Qout = 1) (hQout' : Qout * Qout' = 1)
    (Qin : Matrix (Σ j, Fin (dIn j)) n ℝ) (Qin' : Matrix n (Σ j, Fin (dIn j)) ℝ)
    (hQin : Qin' * Qin = 1) (hQin' : Qin * Qin' = 1)
    (hρout : ∀ g, repMat ρout g = Qout' * Matrix.blockDiagonal' (fun i => repMat (ψout i) g) * Qout)
    (hρin : ∀ g, repMat ρin g = Qin' * Matrix.blockDiagonal' (fun j => repMat (ψin j) g) * Qin) :
    (∀ k : Plane → Matrix m n ℝ, IsSteerable G ρin ρout k ↔
      ∀ i j, IsSteerable G (ψin j) (ψout i) (fun x => kernelBlock (Qout * k x * Qin') i j)) ∧
    (∀ κ : ∀ i j, Plane → Matrix (Fin (dOut i)) (Fin (dIn j)) ℝ,
      (∀ i j, IsSteerable G (ψin j) (ψout i) (κ i j)) →
      IsSteerable G ρin ρout
        (fun x => Qout' *
          (Matrix.of (fun (p : Σ i, Fin (dOut i)) (q : Σ j, Fin (dIn j)) => κ p.1 q.1 x p.2 q.2) :
            Matrix (Σ i, Fin (dOut i)) (Σ j, Fin (dIn j)) ℝ) * Qin)) := by
  have bij : ∀ (X : Matrix m n ℝ) (Y : Matrix (Σ i, Fin (dOut i)) (Σ j, Fin (dIn j)) ℝ),
      X = Qout' * Y * Qin ↔ Qout * X * Qin' = Y := by
    intro X Y
    constructor
    · rintro rfl
      calc Qout * (Qout' * Y * Qin) * Qin' = (Qout * Qout') * Y * (Qin * Qin') := by
            simp only [Matrix.mul_assoc]
        _ = Y := by rw [hQout', hQin']; simp
    · rintro rfl
      calc X = (Qout' * Qout) * X * (Qin' * Qin) := by rw [hQout, hQin]; simp
        _ = _ := by simp only [Matrix.mul_assoc]
  have part1 : ∀ k : Plane → Matrix m n ℝ, IsSteerable G ρin ρout k ↔
      ∀ i j, IsSteerable G (ψin j) (ψout i) (fun x => kernelBlock (Qout * k x * Qin') i j) := by
    intro k
    have step : ∀ (g : G) (x : Plane), (k (gMat g *ᵥ x) = repMat ρout g * k x * (repMat ρin g)⁻¹ ↔
        ∀ i j, kernelBlock (Qout * k (gMat g *ᵥ x) * Qin') i j =
          repMat (ψout i) g * kernelBlock (Qout * k x * Qin') i j * (repMat (ψin j) g)⁻¹) := by
      intro g x
      have hr : repMat ρout g * k x * (repMat ρin g)⁻¹ =
          Qout' * (Matrix.blockDiagonal' (fun i => repMat (ψout i) g) * (Qout * k x * Qin') *
            Matrix.blockDiagonal' (fun j => repMat (ψin j) g⁻¹)) * Qin := by
        rw [repMat_inv', hρout, hρin]; simp only [Matrix.mul_assoc]
      rw [hr, bij, blocks_ext]
      simp only [blk, repMat_inv']
    unfold IsSteerable KernelConstraint
    constructor
    · intro h i j g x
      exact (step g x).1 (h g x) i j
    · intro h g x
      exact (step g x).2 fun i j => h i j g x
  refine ⟨part1, fun κ hκ => ?_⟩
  refine (part1 _).2 fun i j => ?_
  have e : ∀ x, kernelBlock (Qout * (Qout' * (Matrix.of (fun (p : Σ i, Fin (dOut i))
      (q : Σ j, Fin (dIn j)) => κ p.1 q.1 x p.2 q.2)) * Qin) * Qin') i j = κ i j x := by
    intro x
    rw [(bij _ _).1 rfl]
    ext a b; simp [kernelBlock]
  simp only [e]
  exact hκ i j

end SteerableE2CNN
open SteerableE2CNN in
theorem solution (G : Subgroup O2)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {Iout Iin : Type*} [Fintype Iout] [DecidableEq Iout] [Fintype Iin] [DecidableEq Iin]
    {dOut : Iout → ℕ} {dIn : Iin → ℕ}
    (ψout : ∀ i, MatRep G (Fin (dOut i))) (ψin : ∀ j, MatRep G (Fin (dIn j)))
    (hψout : ∀ i, IsIrrep (ψout i)) (hψin : ∀ j, IsIrrep (ψin j))
    (ρout : MatRep G m) (ρin : MatRep G n)
    (Qout : Matrix (Σ i, Fin (dOut i)) m ℝ) (Qout' : Matrix m (Σ i, Fin (dOut i)) ℝ)
    (hQout : Qout' * Qout = 1) (hQout' : Qout * Qout' = 1)
    (Qin : Matrix (Σ j, Fin (dIn j)) n ℝ) (Qin' : Matrix n (Σ j, Fin (dIn j)) ℝ)
    (hQin : Qin' * Qin = 1) (hQin' : Qin * Qin' = 1)
    (hρout : ∀ g, repMat ρout g = Qout' * Matrix.blockDiagonal' (fun i => repMat (ψout i) g) * Qout)
    (hρin : ∀ g, repMat ρin g = Qin' * Matrix.blockDiagonal' (fun j => repMat (ψin j) g) * Qin) :
    (∀ k : Plane → Matrix m n ℝ, IsSteerable G ρin ρout k ↔
      ∀ i j, IsSteerable G (ψin j) (ψout i) (fun x => kernelBlock (Qout * k x * Qin') i j)) ∧
    (∀ κ : ∀ i j, Plane → Matrix (Fin (dOut i)) (Fin (dIn j)) ℝ,
      (∀ i j, IsSteerable G (ψin j) (ψout i) (κ i j)) →
      IsSteerable G ρin ρout
        (fun x => Qout' *
          (Matrix.of (fun (p : Σ i, Fin (dOut i)) (q : Σ j, Fin (dIn j)) => κ p.1 q.1 x p.2 q.2) :
            Matrix (Σ i, Fin (dOut i)) (Σ j, Fin (dIn j)) ℝ) * Qin)) :=
  irrep_decomposition_kernel_constraint G ψout ψin hψout hψin ρout ρin Qout Qout' hQout hQout'
    Qin Qin' hQin hQin' hρout hρin
