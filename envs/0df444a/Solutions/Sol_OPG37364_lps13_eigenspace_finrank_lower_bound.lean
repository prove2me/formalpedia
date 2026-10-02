-- Prove2me | solution 1 for OPG37364.lps13_eigenspace_finrank_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-10T10:21:28.992992+00:00
-- url     : https://prove2.me/submissions/629aeeac-346a-411b-b855-d199837c215d

import Definitions.Def_opg37364_lps13_eigenspaces
import Theorems.Thm_OPG37364_psl2_complex_rep_finrank_lower_bound
import Theorems.Thm_OPG37364_lps13Graph_regular14
import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option autoImplicit false
noncomputable section
open scoped Classical
open Matrix

namespace OPG37364

variable {q : ℕ} [Fact q.Prime]

/-- The quadratic character of the determinant on GL₂. -/
noncomputable def lps13GLDetChar :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod q) →* ℤ :=
  (quadraticChar (ZMod q)).toMonoidHom.comp
    ((Units.coeHom (ZMod q)).comp Matrix.GeneralLinearGroup.det)

/-- Scalar matrices have square determinant, so their character is trivial. -/
theorem lps13GLDetChar_scalar (r : (ZMod q)ˣ) :
    lps13GLDetChar (Matrix.GeneralLinearGroup.scalar (Fin 2) r) = 1 := by
  change quadraticChar (ZMod q) ((Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin 2) r) : (ZMod q)ˣ) : ZMod q) = 1
  simpa only [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
    Units.val_pow_eq_pow_val] using quadraticChar_sq_one' r.ne_zero

/-- Determinant square class on PGL₂, with values +1 and -1. -/
noncomputable def lps13DetChar :
    Matrix.ProjGenLinGroup (Fin 2) (ZMod q) →* ℤ :=
  Matrix.ProjGenLinGroup.lift lps13GLDetChar (by
    ext r
    exact lps13GLDetChar_scalar r)

theorem lps13DetChar_mk (v : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) :
    lps13DetChar (Matrix.ProjGenLinGroup.mk v) =
      quadraticChar (ZMod q) (v.det : ZMod q) := rfl

theorem lps13DetChar_dichotomy (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :
    lps13DetChar v = 1 ∨ lps13DetChar v = -1 := by
  induction v using Matrix.ProjGenLinGroup.induction_on with
  | mk v => exact quadraticChar_dichotomy v.det.ne_zero

theorem lps13DetChar_ne_zero (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :
    lps13DetChar v ≠ 0 := by
  rcases lps13DetChar_dichotomy v with h | h <;> simp [h]

variable (hq : 13 < q) (i : LPS13Root q)

/-- Reuse the norm/determinant certificates in the published Stage 7 definitions. -/
theorem lps13GL_det_val (a : Fin 14) :
    ((lps13GL hq i a).det : ZMod q) = 13 := by
  change (lps13Matrix i a).det = 13
  rw [lps13Matrix, lps13QuaternionMatrix_det, lps13Quaternion_norm]
  norm_num

theorem lps13DetChar_generator (a : Fin 14) :
    lps13DetChar (lps13Generator hq i a) = legendreSym q 13 := by
  rw [lps13Generator, lps13DetChar_mk, lps13GL_det_val]
  simp [legendreSym]


end OPG37364

namespace OPG37364
namespace Multiplicity

variable {q : ℕ} [Fact q.Prime]

theorem detChar_toPGL (g : LPS13ActingGroup q) :
    lps13DetChar (lps13PSLToPGL g) = 1 := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    change quadraticChar (ZMod q) ((Matrix.SpecialLinearGroup.toGL g).det : ZMod q) = 1
    simp

theorem exists_toPGL_of_detChar (v : LPS13Vertex q) (hv : lps13DetChar v = 1) :
    ∃ g : LPS13ActingGroup q, lps13PSLToPGL g = v := by
  induction v using Matrix.ProjGenLinGroup.induction_on with
  | mk M =>
    have hs : IsSquare (M.det : ZMod q) :=
      (quadraticChar_one_iff_isSquare M.det.ne_zero).mp hv
    obtain ⟨t, ht⟩ := hs
    have ht0 : t ≠ 0 := by
      intro he
      apply M.det.ne_zero
      simp [he] at ht
      exact ht
    let r : (ZMod q)ˣ := Units.mk0 t ht0
    have hr : r ^ 2 = M.det := by
      apply Units.ext
      simpa [r, pow_two] using ht.symm
    have hi : r⁻¹ ^ Fintype.card (Fin 2) * M.det = 1 := by
      rw [Fintype.card_fin, ← hr]
      simp
    simp only [Units.ext_iff, Units.val_mul, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_smul M.1 (r⁻¹).1,
      Units.val_one] at hi
    use QuotientGroup.mk ⟨(r⁻¹).1 • M.1, hi⟩
    change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
      ⟨(r⁻¹).1 • M.1, hi⟩) = Matrix.ProjGenLinGroup.mk M
    rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨r, Units.ext ?_⟩
    change ((r⁻¹ : (ZMod q)ˣ) : ZMod q) • (M : Matrix (Fin 2) (Fin 2) (ZMod q)) *
      Matrix.diagonal (fun _ => (r : ZMod q)) = (M : Matrix (Fin 2) (Fin 2) (ZMod q))
    ext j k
    simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    rw [mul_right_comm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem mem_range_iff_detChar (v : LPS13Vertex q) :
    v ∈ lps13PSLToPGL.range ↔ lps13DetChar v = 1 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact detChar_toPGL g
  · exact exists_toPGL_of_detChar v

theorem invariant_eq_of_detChar (f : LPS13Functions q)
    (hf : ∀ g : LPS13ActingGroup q, lps13LeftRepresentation g f = f)
    {v w : LPS13Vertex q} (hvw : lps13DetChar v = lps13DetChar w) : f v = f w := by
  have hker : lps13DetChar (v * w⁻¹) = 1 := by
    apply mul_right_cancel₀ (lps13DetChar_ne_zero w)
    rw [← map_mul]
    simpa [mul_assoc] using hvw
  obtain ⟨g, hg⟩ := exists_toPGL_of_detChar (v * w⁻¹) hker
  have h := congrFun (hf g⁻¹) w
  simpa [lps13LeftRepresentation_apply, hg, mul_assoc] using h

variable (hq : 13 < q) (i : LPS13Root q) (hnr : legendreSym q 13 = -1)
include hnr

theorem detChar_adj {v w : LPS13Vertex q} (h : (lps13Graph hq i).Adj v w) :
    lps13DetChar w = -lps13DetChar v := by
  obtain ⟨_, s, hs, hm⟩ := (SimpleGraph.mulCayley_adj' _ v w).mp h
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
  rcases hm with rfl | rfl <;>
    simp [map_mul, lps13DetChar_generator, hnr]

/-- The minimal two-coset characterization: equal determinant classes give equal values. -/
theorem invariant_two_values (f : LPS13Functions q)
    (hf : ∀ g : LPS13ActingGroup q, lps13LeftRepresentation g f = f) :
    ∀ v, f v = if lps13DetChar v = 1 then f 1 else f (lps13Generator hq i 0) := by
  intro v
  split_ifs with hv
  · apply invariant_eq_of_detChar f hf
    simpa using hv
  · apply invariant_eq_of_detChar f hf
    rcases lps13DetChar_dichotomy v with h | h
    · exact (hv h).elim
    · simpa [lps13DetChar_generator, hnr] using h

theorem adjacency_on_invariant (f : LPS13Functions q)
    (hf : ∀ g : LPS13ActingGroup q, lps13LeftRepresentation g f = f)
    (v : LPS13Vertex q) :
    lps13AdjacencyEnd hq i f v = 14 * f (v * lps13Generator hq i 0) := by
  have hc : ((lps13Graph hq i).neighborFinset v).card = 14 := by
    have h := lps13Graph_regular14 hq i v
    rw [← SimpleGraph.coe_neighborFinset, Set.encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  change (((lps13Graph hq i).adjMatrix ℂ) *ᵥ f) v = _
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  calc
    ∑ w ∈ (lps13Graph hq i).neighborFinset v, f w =
        ∑ _w ∈ (lps13Graph hq i).neighborFinset v, f (v * lps13Generator hq i 0) := by
      apply Finset.sum_congr rfl
      intro w hw
      apply invariant_eq_of_detChar f hf
      rw [detChar_adj hq i hnr ((SimpleGraph.mem_neighborFinset _ _ _).mp hw)]
      simp [map_mul, lps13DetChar_generator, hnr]
    _ = 14 * f (v * lps13Generator hq i 0) := by simp [hc, nsmul_eq_mul]

theorem invariant_eigenvalue_eq (μ : ℝ) (f : lps13AdjacencyEigenspace hq i μ)
    (hf : f ≠ 0)
    (hinv : ∀ g : LPS13ActingGroup q,
      lps13LeftRepresentation g (f : LPS13Functions q) = f) :
    μ = 14 ∨ μ = -14 := by
  have hfne : (f : LPS13Functions q) ≠ 0 := by
    intro he
    exact hf (Subtype.ext he)
  obtain ⟨v, hv⟩ : ∃ v, (f : LPS13Functions q) v ≠ 0 := by
    by_contra h
    push Not at h
    exact hfne (funext h)
  let s := lps13Generator hq i 0
  have htwice : (f : LPS13Functions q) ((v * s) * s) = (f : LPS13Functions q) v := by
    apply invariant_eq_of_detChar (f : LPS13Functions q) hinv
    simp [s, map_mul, lps13DetChar_generator, hnr]
  have he := Module.End.mem_eigenspace_iff.mp f.property
  have h1 := congrFun he v
  have h2 := congrFun he (v * s)
  rw [adjacency_on_invariant hq i hnr _ hinv] at h1 h2
  change 14 * (f : LPS13Functions q) (v * s) = (μ : ℂ) * (f : LPS13Functions q) v at h1
  change 14 * (f : LPS13Functions q) ((v * s) * s) = (μ : ℂ) * (f : LPS13Functions q) (v * s) at h2
  rw [htwice] at h2
  have heq : ((μ : ℂ) ^ 2 - 14 ^ 2) * (f : LPS13Functions q) v = 0 := by
    linear_combination -(μ : ℂ) * h1 - 14 * h2
  have hsq : (μ : ℂ) ^ 2 = 14 ^ 2 := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right hv)
  have hr : μ ^ 2 = (14 : ℝ) ^ 2 := by exact_mod_cast hsq
  have hfac : (μ - 14) * (μ + 14) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · left; linarith
  · right; linarith

end Multiplicity

theorem lps13_eigenspace_rep_nontrivial
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
    (hnr : legendreSym q 13 = -1) (μ : ℝ) (hμ14 : μ ≠ 14) (hμneg14 : μ ≠ -14)
    (hE : Nontrivial (lps13AdjacencyEigenspace hq i μ)) :
    ∃ g : LPS13ActingGroup q, lps13EigenspaceRepresentation hq i μ g ≠ 1 := by
  by_contra h
  push Not at h
  let := hE
  obtain ⟨f, hf⟩ := exists_ne (0 : lps13AdjacencyEigenspace hq i μ)
  have hinv : ∀ g : LPS13ActingGroup q,
      lps13LeftRepresentation g (f : LPS13Functions q) = f := by
    intro g
    have he := LinearMap.congr_fun (h g) f
    exact congrArg (fun x : lps13AdjacencyEigenspace hq i μ => (x : LPS13Functions q)) he
  rcases Multiplicity.invariant_eigenvalue_eq hq i hnr μ f hf hinv with he | he
  · exact hμ14 he
  · exact hμneg14 he

/-- The fixed-p=13, nonsquare-determinant case of DSV Proposition 4.4.3. -/
theorem _root_.solution
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
    (hnr : legendreSym q 13 = -1) (μ : ℝ) (hμ14 : μ ≠ 14) (hμneg14 : μ ≠ -14)
    (hE : Nontrivial (lps13AdjacencyEigenspace hq i μ)) :
    q - 1 ≤ 2 * Module.finrank ℂ (lps13AdjacencyEigenspace hq i μ) := by
  exact psl2_complex_rep_finrank_lower_bound q Fact.out (by omega)
    (lps13EigenspaceRepresentation hq i μ)
    (lps13_eigenspace_rep_nontrivial hq i hnr μ hμ14 hμneg14 hE)

end OPG37364
