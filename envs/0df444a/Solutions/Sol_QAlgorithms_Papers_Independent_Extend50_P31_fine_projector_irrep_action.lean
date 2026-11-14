-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.fine_projector_irrep_action
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:43:29.935084+00:00
-- url     : https://prove2.me/submissions/23d8a33f-7252-411f-aba9-73b1ec5a219e

import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_irreducible_twirl
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms.Papers.Independent.Extend50.P31
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [DecidableEq A] {n : ℕ}
private def bundled (U : UnitaryIrrep G n) : Representation ℂ G (Fin n → ℂ) where
  toFun g := (U.rho g).mulVecLin
  map_one' := by ext v i; simp [U.one]
  map_mul' g h := by ext v i; simp [U.mul, Matrix.mulVec_mulVec]

private lemma bundled_irred (U : UnitaryIrrep G n) : Representation.IsIrreducible (bundled U) := by
  have hn : Nonempty (Fin n) := ⟨⟨0, U.positive⟩⟩
  letI := hn
  have hne : (⊥ : Subrepresentation (bundled U)) ≠ ⊤ := by
    intro h
    have hh := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top hh
  refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := ?_ }
  intro S
  rcases U.irreducible S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [DecidableEq A]
private lemma rho_inverse {n : ℕ} (U : UnitaryIrrep G n) (g : G) : U.rho g⁻¹ = (U.rho g)ᴴ := by
  calc
    U.rho g⁻¹ = U.rho g⁻¹ * (U.rho g * (U.rho g)ᴴ) := by rw [(U.unitary g).2,Matrix.mul_one]
    _ = (U.rho g⁻¹ * U.rho g) * (U.rho g)ᴴ := (Matrix.mul_assoc _ _ _).symm
    _ = (U.rho g)ᴴ := by rw [← U.mul,inv_mul_cancel,U.one,Matrix.one_mul]

private lemma cross_average_zero (F : IrrepFamily G A) (a b : A) (hab : a ≠ b)
    (X : Matrix (Fin (F.dim b)) (Fin (F.dim a)) ℂ) :
    (∑ g : G, (F.irrep b).rho g * X * (F.irrep a).rho g⁻¹) = 0 := by
  classical
  let Y := ∑ g : G, (F.irrep b).rho g * X * (F.irrep a).rho g⁻¹
  have hY (h : G) : Y * (F.irrep a).rho h = (F.irrep b).rho h * Y := by
    have he := Equiv.sum_comp (Equiv.mulLeft h)
      (fun k : G => (F.irrep b).rho k * X * (F.irrep a).rho (k⁻¹*h))
    dsimp at he
    simp only [mul_inv_rev, inv_mul_cancel_right] at he
    calc
      Y * (F.irrep a).rho h = ∑ g, (F.irrep b).rho g * X * (F.irrep a).rho (g⁻¹*h) := by
        simp [Y,Matrix.sum_mul,(F.irrep a).mul,Matrix.mul_assoc]
      _ = ∑ g, (F.irrep b).rho (h*g) * X * (F.irrep a).rho g⁻¹ := he.symm
      _ = (F.irrep b).rho h * Y := by
        simp [Y,Matrix.mul_sum,(F.irrep b).mul,Matrix.mul_assoc]
  letI := bundled_irred (F.irrep a)
  letI := bundled_irred (F.irrep b)
  let f : Representation.IntertwiningMap (bundled (F.irrep a)) (bundled (F.irrep b)) :=
    { toLinearMap := Y.mulVecLin
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        change Y.mulVec ((F.irrep a).rho g |>.mulVec v) =
          ((F.irrep b).rho g).mulVec (Y.mulVec v)
        simp only [Matrix.mulVec_mulVec,hY] }
  have hf : f = 0 := by
    rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | hz
    · have e := f.ofBijective hb
      exact False.elim (hab (F.inequivalent a b ⟨e.toLinearEquiv,fun g v =>
        Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v⟩))
    · exact hz
  change Y = 0
  apply Matrix.toLin'.injective
  have he := congrArg Representation.IntertwiningMap.toLinearMap hf
  change Y.mulVecLin = (0 : Matrix (Fin (F.dim b)) (Fin (F.dim a)) ℂ).mulVecLin
  simpa [f] using he

private lemma sandwich_single_entry {d e : ℕ}
    (A : Mat d) (B : Mat e) (l : Fin d) (i : Fin e) (k : Fin d) (j : Fin e) :
    (A * Matrix.single l i (1 : ℂ) * B) k j = A k l * B i j := by
  simp [Matrix.mul_apply,Matrix.single_apply,ite_and]


set_option autoImplicit false

set_option autoImplicit false

theorem solution {G A : Type*} [Group G] [Fintype G] [DecidableEq A] (F : IrrepFamily G A) (a b : A) (i : Fin (F.dim a)) :
    ((F.dim a : ℂ) / Fintype.card G) •
      (∑ g : G, (F.irrep a).rho g⁻¹ i i • (F.irrep b).rho g) =
      if h : a = b then Matrix.single (Fin.cast (congrArg F.dim h) i)
        (Fin.cast (congrArg F.dim h) i) 1 else 0 := by
  classical
  have hg : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  split_ifs with hab
  · subst b
    ext k l
    have h := irreducible_twirl (F.irrep a) (matrixUnit l i)
    have he := congrArg (fun M : Mat (F.dim a) => M k i) h
    simp only [Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul] at he
    change (Fintype.card G : ℂ)⁻¹ *
      (∑ g, ((F.irrep a).rho g * (matrixUnit l i * ((F.irrep a).rho g)ᴴ)) k i) =
      (Matrix.trace (matrixUnit l i) / F.dim a) * (1 : Mat (F.dim a)) k i at he
    simp only [← Matrix.mul_assoc, matrixUnit, ← rho_inverse, sandwich_single_entry] at he
    simp only [Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,Matrix.zero_apply]
    change ((F.dim a : ℂ) / Fintype.card G) *
      (∑ g, (F.irrep a).rho g⁻¹ i i * (F.irrep a).rho g k l) =
      Matrix.single i i 1 k l
    have hd : (F.dim a : ℂ) ≠ 0 := by exact_mod_cast (F.irrep a).positive.ne'
    calc
      _ = (F.dim a : ℂ) * ((Fintype.card G : ℂ)⁻¹ *
          ∑ g, (F.irrep a).rho g k l * (F.irrep a).rho g⁻¹ i i) := by
            simp only [div_eq_mul_inv,mul_comm ((F.irrep a).rho _ i i)]; ring
      _ = (F.dim a : ℂ) * ((Matrix.trace (matrixUnit l i) / F.dim a) * (1 : Mat (F.dim a)) k i)  := by rw [he]; rfl
      _ = _ := by
        by_cases hli : l = i <;> by_cases hki : k = i <;>
          simp [matrixUnit,Matrix.trace_single_eq_of_ne,Matrix.trace_single_eq_same,
            Matrix.single_apply,Matrix.one_apply,hli,hki,eq_comm,hd]
        all_goals simp_all only [mul_inv_cancel₀ hd,eq_comm]
        all_goals simp
  · ext k l
    have h := cross_average_zero F a b hab (Matrix.single l i 1)
    have he := congrArg (fun M : Matrix (Fin (F.dim b)) (Fin (F.dim a)) ℂ => M k i) h
    have hz : (∑ g : G, (F.irrep b).rho g k l * (F.irrep a).rho g⁻¹ i i) = 0 := by
      simpa only [Matrix.sum_apply,sandwich_single_entry,Matrix.zero_apply] using he
    simp only [Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,Matrix.zero_apply]
    change ((F.dim a : ℂ) / Fintype.card G) *
      (∑ g, (F.irrep a).rho g⁻¹ i i * (F.irrep b).rho g k l) = 0
    simpa only [mul_comm ((F.irrep a).rho _ i i),hz,mul_zero]