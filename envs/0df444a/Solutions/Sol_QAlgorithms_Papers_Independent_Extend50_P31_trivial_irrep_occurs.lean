-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.trivial_irrep_occurs
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:24:57.898259+00:00
-- url     : https://prove2.me/submissions/3700b7f3-d3e6-41a7-98bd-32bd8128c1db

import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_character_orthogonality
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_row_representative_calculus
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31 QAlgorithms.Papers.Independent.Information100.P44 QAlgorithms.Papers.Independent.Dependency50.P16
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
private lemma char_average (F : IrrepFamily G A) (a : A) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, character (F.irrep a) g⁻¹ =
      if a = F.trivial then 1 else 0 := by
  have ht (g : G) : character (F.irrep F.trivial) g = 1 := by
    simp [character, F.trivial_action, Matrix.trace_one, F.trivial_dim]
  have h := character_orthogonality F F.trivial a
  simpa only [ht, one_mul, eq_comm] using h

private lemma fixed_eq_zero (F : IrrepFamily G A) (a : A) (ha : a ≠ F.trivial)
    (v : Fin (F.dim a) → ℂ) (hv : ∀ g, ((F.irrep a).rho g).mulVec v = v) : v = 0 := by
  by_contra hn
  let S := Submodule.span ℂ ({v} : Set (Fin (F.dim a) → ℂ))
  have hi : ∀ g w, w ∈ S → ((F.irrep a).rho g).mulVec w ∈ S := by
    intro g w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [Matrix.mulVec_smul, hv]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have hs : S = ⊤ := ((F.irrep a).irreducible S hi).resolve_left (by
    intro h
    have hh : v ∈ S := Submodule.mem_span_singleton_self v
    rw [h] at hh
    exact hn (by simpa using hh))
  have hr (g : G) : (F.irrep a).rho g = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro w
    have hw : w ∈ S := by rw [hs]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [Matrix.toLin'_apply, Matrix.mulVec_smul, hv]
  have h := char_average F a
  simp only [ha, if_false, character, hr, Matrix.trace_one, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hg : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hz : (F.dim a : ℂ) = 0 := by simpa [← mul_assoc, hg] using h
  exact (by exact_mod_cast (F.irrep a).positive.ne' : (F.dim a : ℂ) ≠ 0) hz


set_option autoImplicit false

set_option autoImplicit false

theorem solution {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ} (D : Data G A n) : D.F.trivial ∈ D.theta := by
  classical
  by_contra hn
  obtain ⟨T,hT⟩ := D.decomposition
  let v := rowVec (1 : Mat n)
  have hv (g : G) : (tensorConjugate D.U g).mulVec v = v := by
    obtain ⟨ha,_,hs⟩ := row_representative_calculus n
    have hm : rowMatrixRepresentative (conjugationMap D.U g) = tensorConjugate D.U g := by
      rw [conjugationMap, hs]
      rfl
    rw [← hm, ← ha]
    congr 1
    change D.U.rho g * (1 * (D.U.rho g)ᴴ) = 1
    simpa using (D.U.unitary g).2
  have hz : T v = 0 := by
    funext a
    apply fixed_eq_zero D.F a.val (fun h => hn (h ▸ a.property))
    intro g
    rw [← hT, hv]
  have hvz : v = 0 := T.injective (by simpa using hz)
  have h : (1 : Mat n) = 0 := rowVec.injective (by simpa [v] using hvz)
  have hi : Fin n := ⟨0,D.U.positive⟩
  have hh := congrArg (fun X : Mat n => X hi hi) h
  norm_num at hh