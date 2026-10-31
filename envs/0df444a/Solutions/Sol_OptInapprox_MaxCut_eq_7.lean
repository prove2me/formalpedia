-- Prove2me | solution 1 for OptInapprox.MaxCut.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:18:28.978855+00:00
-- url     : https://prove2.me/submissions/9926c4b0-0ed2-49a4-97ca-843382a85efd

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Verifier

open OptInapprox.MaxCut

def composeEquiv {M : ℕ} (σ : Equiv.Perm (Fin M)) : (Fin M → Bool) ≃ (Fin M → Bool) where
  toFun z := compose z σ
  invFun x := compose x σ.symm
  left_inv z := by ext i; simp [compose]
  right_inv x := by ext i; simp [compose]

lemma chi_compose_symm {M : ℕ} (S : Finset (Fin M)) (σ : Equiv.Perm (Fin M)) (x : Fin M → Bool) :
    chi S (compose x σ.symm) = chi (S.map σ.symm.toEmbedding) x := by
  unfold chi compose
  rw [Finset.prod_map]
  rfl

lemma fourier_compose {M : ℕ} (g : (Fin M → Bool) → ℝ) (σ : Equiv.Perm (Fin M)) (S : Finset (Fin M)) :
    OptInapprox.MaxCut.fourier (fun z => g (compose z σ)) S =
      OptInapprox.MaxCut.fourier g (S.map σ.symm.toEmbedding) := by
  unfold OptInapprox.MaxCut.fourier cubeE
  congr 1
  have h := Equiv.sum_comp (composeEquiv σ).symm
    (fun z => g (compose z σ) * chi S z)
  rw [← h]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h1 : compose ((composeEquiv σ).symm x) σ = x := (composeEquiv σ).right_inv x
  have h2 : chi S ((composeEquiv σ).symm x) = chi (S.map σ.symm.toEmbedding) x :=
    chi_compose_symm S σ x
  rw [h1, h2]

lemma fourier_gv (L : ULC) (F : Fin L.nW → (Fin L.M → Bool) → Bool) (v : Fin L.nV)
    (S : Finset (Fin L.M)) :
    OptInapprox.MaxCut.fourier (gv L F v) S =
      ((L.nbrs v).card : ℝ)⁻¹ * ∑ w ∈ L.nbrs v,
        OptInapprox.MaxCut.fourier (fun x => pm (F w x)) (S.map (L.σ v w).symm.toEmbedding) := by
  have hlin : OptInapprox.MaxCut.fourier (gv L F v) S =
      ((L.nbrs v).card : ℝ)⁻¹ * ∑ w ∈ L.nbrs v,
        OptInapprox.MaxCut.fourier (fun z => pm (F w (compose z (L.σ v w)))) S := by
    unfold OptInapprox.MaxCut.fourier cubeE gv
    simp_rw [mul_assoc, Finset.sum_mul]
    rw [← Finset.mul_sum, ← mul_assoc, mul_comm (2 ^ L.M : ℝ)⁻¹, mul_assoc]
    congr 1
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum]
  rw [hlin]
  congr 1
  refine Finset.sum_congr rfl (fun w _ => fourier_compose (fun x => pm (F w x)) (L.σ v w) S)

lemma avg_sq_le_avg_sq {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ((s.card : ℝ)⁻¹ * ∑ w ∈ s, a w) ^ 2 ≤ (s.card : ℝ)⁻¹ * ∑ w ∈ s, (a w) ^ 2 := by
  by_cases hs : s.card = 0
  · have hse : s = ∅ := Finset.card_eq_zero.mp hs
    subst hse
    simp
  · have hpos : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s a (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hcs
    have hmul := mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ ((s.card : ℝ)⁻¹) ^ 2)
    calc ((s.card : ℝ)⁻¹ * ∑ w ∈ s, a w) ^ 2
        = ((s.card : ℝ)⁻¹) ^ 2 * (∑ w ∈ s, a w) ^ 2 := by ring
      _ ≤ ((s.card : ℝ)⁻¹) ^ 2 * ((∑ w ∈ s, a w ^ 2) * (s.card : ℝ)) := hmul
      _ = (s.card : ℝ)⁻¹ * ∑ w ∈ s, a w ^ 2 := by
          field_simp [hpos.ne']

def finsetPermEquiv {M : ℕ} (σ : Equiv.Perm (Fin M)) : Finset (Fin M) ≃ Finset (Fin M) where
  toFun S := S.map σ.symm.toEmbedding
  invFun T := T.map σ.toEmbedding
  left_inv S := by ext x; simp
  right_inv T := by ext x; simp

lemma sum_lowDegInf_perm {M : ℕ} (g : (Fin M → Bool) → ℝ) (σ : Equiv.Perm (Fin M))
    (k : ℕ) (j : Fin M) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin M) => j ∈ S ∧ S.card ≤ k),
        OptInapprox.MaxCut.fourier g (S.map σ.symm.toEmbedding) ^ 2 =
      lowDegInf k (σ.symm j) g := by
  unfold lowDegInf
  simp_rw [Finset.sum_filter]
  have h := Equiv.sum_comp (finsetPermEquiv σ)
    (fun T : Finset (Fin M) => if σ.symm j ∈ T ∧ T.card ≤ k then OptInapprox.MaxCut.fourier g T ^ 2 else 0)
  rw [← h]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  have hmem : (σ.symm j ∈ (finsetPermEquiv σ S)) ↔ (j ∈ S) := by
    simp [finsetPermEquiv]
  have hcard : (finsetPermEquiv σ S).card = S.card := by
    simp [finsetPermEquiv]
  change (if j ∈ S ∧ S.card ≤ k then OptInapprox.MaxCut.fourier g (finsetPermEquiv σ S) ^ 2 else 0) =
    if σ.symm j ∈ finsetPermEquiv σ S ∧ (finsetPermEquiv σ S).card ≤ k then
      OptInapprox.MaxCut.fourier g (finsetPermEquiv σ S) ^ 2 else 0
  exact if_ctx_congr (and_congr hmem.symm (by rw [hcard])) (fun _ => rfl) (fun _ => rfl)

theorem solution (L : ULC) (F : Fin L.nW → (Fin L.M → Bool) → Bool) (v : Fin L.nV) :
    (∀ S : Finset (Fin L.M), OptInapprox.MaxCut.fourier (gv L F v) S =
      ((L.nbrs v).card : ℝ)⁻¹ * ∑ w ∈ L.nbrs v,
        OptInapprox.MaxCut.fourier (fun x => pm (F w x)) (S.map (L.σ v w).symm.toEmbedding)) ∧
    ∀ (k : ℕ) (j : Fin L.M), lowDegInf k j (gv L F v) ≤
      ((L.nbrs v).card : ℝ)⁻¹ * ∑ w ∈ L.nbrs v,
        lowDegInf k ((L.σ v w).symm j) (fun x => pm (F w x)) := by
  refine ⟨fourier_gv L F v, ?_⟩
  intro k j
  unfold lowDegInf
  have hle : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin L.M) => j ∈ S ∧ S.card ≤ k),
        OptInapprox.MaxCut.fourier (gv L F v) S ^ 2 ≤
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin L.M) => j ∈ S ∧ S.card ≤ k),
        ((L.nbrs v).card : ℝ)⁻¹ * ∑ w ∈ L.nbrs v,
          OptInapprox.MaxCut.fourier (fun x => pm (F w x)) (S.map (L.σ v w).symm.toEmbedding) ^ 2 := by
    refine Finset.sum_le_sum (fun S _ => ?_)
    rw [fourier_gv]
    exact avg_sq_le_avg_sq (L.nbrs v)
      (fun w => OptInapprox.MaxCut.fourier (fun x => pm (F w x)) (S.map (L.σ v w).symm.toEmbedding))
  refine hle.trans_eq ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun w _ => ?_)
  exact sum_lowDegInf_perm (fun x => pm (F w x)) (L.σ v w) k j
