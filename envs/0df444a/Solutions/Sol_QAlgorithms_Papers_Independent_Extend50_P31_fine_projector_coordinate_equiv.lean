-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.fine_projector_coordinate_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:52:13.016194+00:00
-- url     : https://prove2.me/submissions/5bdef67d-1713-40b8-ae41-37804b3a9aa3

import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_projector_irrep_action
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
private lemma fine_coordinates (D : Data G A n)
    (T : ((Fin n × Fin n) → ℂ) ≃ₗ[ℂ] ((b : OccurringIrrep D) → Fin (D.F.dim b.val) → ℂ))
    (hT : ∀ g v b, T ((tensorConjugate D.U g).mulVec v) b =
      ((D.F.irrep b.val).rho g).mulVec (T v b))
    (a : A) (i : Fin (D.F.dim a)) (v : (Fin n × Fin n) → ℂ) (b : OccurringIrrep D) :
    T ((fineMatrix D.U D.F a i).mulVec v) b =
      (if h : a = b.val then Matrix.single (Fin.cast (congrArg D.F.dim h) i)
        (Fin.cast (congrArg D.F.dim h) i) 1 else 0).mulVec (T v b) := by
  have h := congrArg (fun M : Mat (D.F.dim b.val) => M.mulVec (T v b))
    (fine_projector_irrep_action D.F a b.val i)
  simp only [fineMatrix, Matrix.smul_mulVec, Matrix.sum_mulVec,
    map_smul, map_sum, Finset.sum_apply, Pi.smul_apply, hT]
  simpa only [Matrix.smul_mulVec, Matrix.sum_mulVec] using h


set_option autoImplicit false

set_option autoImplicit false

theorem solution {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ} (D : Data G A n) :
    ∃ C : ((Fin n × Fin n) → ℂ) ≃ₗ[ℂ] (Row D → ℂ),
      ∀ (r : Row D) (v : (Fin n × Fin n) → ℂ),
        C ((fineMatrix D.U D.F r.1.val r.2).mulVec v) = Pi.single r (C v r) := by
  classical
  obtain ⟨T,hT⟩ := D.decomposition
  let C := T.trans (LinearEquiv.piCurry ℂ (fun (a : OccurringIrrep D) (_ : Fin (D.F.dim a.val)) => ℂ)).symm
  refine ⟨C,?_⟩
  intro r v
  funext s
  rcases r with ⟨a,i⟩
  rcases s with ⟨b,j⟩
  change T ((fineMatrix D.U D.F a.val i).mulVec v) b j = (Pi.single (⟨a,i⟩ : Row D) (T v a i) : Row D → ℂ) ⟨b,j⟩
  have h := congrArg (fun w : Fin (D.F.dim b.val) → ℂ => w j) (fine_coordinates D T hT a.val i v b)
  by_cases hab : a = b
  · subst b
    simpa [Matrix.single_mulVec,Matrix.single_apply,Pi.single_apply,Function.update] using h
  · have hn : a.val ≠ b.val := fun he => hab (Subtype.ext he)
    have hs : (⟨b,j⟩ : Row D) ≠ ⟨a,i⟩ := fun he => hab (congrArg Sigma.fst he).symm
    simpa [hn,Pi.single_apply,hs] using h