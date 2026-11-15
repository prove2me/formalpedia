-- Prove2me | solution 1 for QuantumLinearAlgebra.sorted_svd_of_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-15T04:16:11.785196+00:00
-- url     : https://prove2.me/submissions/04827030-d329-469b-a40e-908b5c7f7f8f

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
noncomputable section
open scoped InnerProduct ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTSVD
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
lemma linear_svd (T : E →ₗ[ℂ] F) (hnm : Module.finrank ℂ E ≤ Module.finrank ℂ F) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
      (c : OrthonormalBasis (Fin (Module.finrank ℂ F)) ℂ F)
      (s : Fin (Module.finrank ℂ E) → ℝ),
      (∀ i, 0 ≤ s i) ∧ Antitone s ∧
      ∀ i, T (b i) = (s i : ℂ) • c (Fin.castLE hnm i) := by
  classical
  let hH := T.isSymmetric_adjoint_comp_self
  let b := hH.eigenvectorBasis rfl
  let l := hH.eigenvalues rfl
  let s : Fin (Module.finrank ℂ E) → ℝ := fun i => Real.sqrt (l i)
  have hl (i) : 0 ≤ l i := T.isPositive_adjoint_comp_self.nonneg_eigenvalues rfl i
  have hs (i) : 0 ≤ s i := Real.sqrt_nonneg _
  have hsq (i) : s i * s i = l i := Real.mul_self_sqrt (hl i)
  have hgram (i j) : inner ℂ (T (b i)) (T (b j)) = if i=j then (l i:ℂ) else 0 := by
    rw [← T.adjoint_inner_right]
    change inner ℂ (b i) ((T.adjoint ∘ₗ T) (b j)) = _
    rw [hH.apply_eigenvectorBasis rfl j,inner_smul_right,b.inner_eq_ite]
    split_ifs with hij
    · subst j; simp [l]
    · simp
  let v : Fin (Module.finrank ℂ F) → F := fun j =>
    if h : j.val < Module.finrank ℂ E then
      ((s ⟨j.val,h⟩:ℂ)⁻¹) • T (b ⟨j.val,h⟩) else 0
  let S : Set (Fin (Module.finrank ℂ F)) := {j | ∃ h : j.val < Module.finrank ℂ E, s ⟨j.val,h⟩ ≠ 0}
  have hv : Orthonormal ℂ (S.domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    obtain ⟨hi,hsi⟩ := i.property
    obtain ⟨hj,hsj⟩ := j.property
    simp only [Set.domRestrict_apply,v,dif_pos hi,dif_pos hj,inner_smul_left,inner_smul_right,
      map_inv₀,Complex.conj_ofReal,hgram]
    by_cases hij : i=j
    · subst j
      simp only [ite_true]
      have hne : (s ⟨i.val.val,hi⟩:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsi
      have hh : (s ⟨i.val.val,hi⟩:ℂ)*(s ⟨i.val.val,hi⟩:ℂ)=(l ⟨i.val.val,hi⟩:ℂ) := by exact_mod_cast hsq ⟨i.val.val,hi⟩
      rw [← hh]
      field_simp
    · have hne : (⟨i.val.val,hi⟩ : Fin (Module.finrank ℂ E)) ≠ ⟨j.val.val,hj⟩ := by
        intro hh;apply hij;apply Subtype.ext;apply Fin.ext;exact congrArg (fun z : Fin (Module.finrank ℂ E) => z.val) hh
      simp [hne,hij]
  obtain ⟨c,hc⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ F = Fintype.card (Fin (Module.finrank ℂ F)))
  refine ⟨b,c,s,hs,?_,?_⟩
  · intro i j hij
    exact Real.sqrt_le_sqrt (hH.eigenvalues_antitone rfl hij)
  · intro i
    by_cases hi : s i = 0
    · have hh : inner ℂ (T (b i)) (T (b i))=0 := by
        rw [hgram,if_pos rfl,← hsq i,hi];simp
      have hz : T (b i)=0 := inner_self_eq_zero.mp hh
      simp [hi,hz]
    · have hh := hc (Fin.castLE hnm i) ⟨i.isLt,hi⟩
      simp only [v,Fin.val_castLE,dif_pos i.isLt,Fin.eta] at hh
      rw [hh,smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hi),one_smul]
end QSVTSVD

set_option autoImplicit false


theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) (hnm : Module.finrank ℂ E ≤ Module.finrank ℂ F) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
      (c : OrthonormalBasis (Fin (Module.finrank ℂ F)) ℂ F)
      (s : Fin (Module.finrank ℂ E) → ℝ),
      (∀ i, 0 ≤ s i) ∧ Antitone s ∧
      ∀ i, T (b i) = (s i : ℂ) • c (Fin.castLE hnm i) := by
  exact @QSVTSVD.linear_svd E F _ _ _ _ _ _ T hnm