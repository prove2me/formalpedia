-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P11.covariant_choi_simulation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:01:14.660164+00:00
-- url     : https://prove2.me/submissions/8dd4b526-c2de-40a0-a316-209578e97048

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace X7L1CC

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P11
open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

lemma X7L1_sumlin {ι κ α : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Fintype α]
    (Phi : Superop ι κ) (hPhi : IsChannel Phi) (f : α → ℂ) (Y : α → Matrix ι ι ℂ) :
    Phi (∑ a, f a • Y a) = ∑ a, f a • Phi (Y a) := by
  obtain ⟨m, E, -, hPhiE⟩ := hPhi
  simp only [hPhiE, krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]
  rw [Finset.sum_comm]

lemma X7L1_sum {ι κ α : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Fintype α]
    (Phi : Superop ι κ) (hPhi : IsChannel Phi) (Y : α → Matrix ι ι ℂ) :
    Phi (∑ a, Y a) = ∑ a, Phi (Y a) := by
  have := X7L1_sumlin Phi hPhi (fun _ => 1) Y
  simpa using this

lemma X7L1_lin {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Phi : Superop ι κ) (hPhi : IsChannel Phi) (M : Matrix ι ι ℂ) :
    Phi M = ∑ p, ∑ q, M p q • Phi (Matrix.single p q 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  have h1 : ∀ p q, Matrix.single p q (M p q) = M p q • Matrix.single p q (1 : ℂ) := by
    intro p q; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  simp only [h1]
  rw [X7L1_sum Phi hPhi]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [X7L1_sumlin Phi hPhi]

lemma X7L1_idChannel {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsChannel (fun Y : Matrix ι ι ℂ => Y) :=
  ⟨1, fun _ => 1, by simp [IsKrausFamily], fun ρ => by simp [krausApply]⟩

variable {I O : Type} [Fintype I] [Fintype O]

/-- the teleported operator for outcome `c` -/
def sig {C : Type*} [Fintype C] (M : Superop (I × I) C) (X : Matrix I I ℂ) (c : C) :
    Matrix I I ℂ :=
  fun a a' => (Fintype.card I : ℂ)⁻¹ *
    M (Matrix.of fun u v => X u.1 v.1 * (if u.2 = a ∧ v.2 = a' then 1 else 0)) c c

lemma X7L1_block {C : Type*} [Fintype C] (M : Superop (I × I) C) (hM : IsChannel M)
    (Phi : Superop I O) (hPhi : IsChannel Phi) (X : Matrix I I ℂ) (c : C) :
    (fun i j => M (fun u v => X u.1 v.1 * choiState Phi (u.2, i) (v.2, j)) c c) =
      Phi (sig M X c) := by
  ext i j
  rw [X7L1_lin Phi hPhi (sig M X c)]
  have hmat : (show Matrix (I × I) (I × I) ℂ from
        fun u v : I × I => X u.1 v.1 * choiState Phi (u.2, i) (v.2, j)) =
      ∑ a, ∑ a', ((Fintype.card I : ℂ)⁻¹ * Phi (Matrix.single a a' 1) i j) •
        (Matrix.of fun u v : I × I => X u.1 v.1 * (if u.2 = a ∧ v.2 = a' then 1 else 0)) := by
    ext u v
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, choiState, choi, Matrix.of_apply]
    rw [Finset.sum_eq_single u.2]
    · rw [Finset.sum_eq_single v.2]
      · simp only [and_self, if_true, mul_one, Matrix.smul_apply, smul_eq_mul]
        ring
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun b' _ => ?_
      simp [Ne.symm hb]
    · simp
  rw [hmat, X7L1_sum M hM]
  simp only [X7L1_sumlin M hM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, sig]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  ring

end X7L1CC

end

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)
open QAlgorithms.Papers.Independent.Information100.P21 (pt)
open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)
open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)
open QAlgorithms.Papers.Independent.Information100.P69 (replacer)
open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P11 X7L1CC in
theorem solution {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]
    (N : Superop I O) (hN : IsChannel N) {C : Type*} [Fintype C] [Nonempty C]
    (M : Superop (I × I) C) (hM : IsChannel M) (hclassical : ∀ X, dephasing (M X) = M X)
    (U : C → Matrix.unitaryGroup I ℂ) (V : C → Matrix.unitaryGroup O ℂ)
    (hteleport : ∀ X, resourceSim (choiState (fun Y : Matrix I I ℂ => Y)) M
      (classicalControlledUnitary (fun c => (U c : Matrix I I ℂ))) X = X)
    (hcov : ∀ c X, N (conjSuperop (U c : Matrix I I ℂ) X) =
      conjSuperop (V c : Matrix O O ℂ) (N X)) :
    (∀ X, resourceSim (choiState N) M (classicalControlledUnitary (fun c => (V c : Matrix O O ℂ))) X = N X) ∧
    HasChoiSimulation N := by
  have part1 : ∀ X, resourceSim (choiState N) M
      (classicalControlledUnitary (fun c => (V c : Matrix O O ℂ))) X = N X := by
    intro X
    have hT := hteleport X
    simp only [resourceSim, classicalControlledUnitary] at hT ⊢
    simp only [X7L1_block M hM N hN X] at ⊢
    simp only [X7L1_block M hM (fun Y : Matrix I I ℂ => Y) X7L1_idChannel X] at hT
    simp only [← hcov]
    rw [← X7L1_sum N hN, hT]
  refine ⟨part1, ?_⟩
  set e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C with he
  refine ⟨Fintype.card C, Fintype.card_pos, fun Y => (M Y).submatrix e.symm e.symm,
    classicalControlledUnitary (fun k => (V (e.symm k) : Matrix O O ℂ)), ?_, ?_, ?_, ?_⟩
  · obtain ⟨n, E, hE, hME⟩ := hM
    refine ⟨n, fun j => (E j).submatrix e.symm id, ?_, ?_⟩
    · unfold IsKrausFamily at hE ⊢
      rw [← hE]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
    · intro Y
      show (M Y).submatrix e.symm e.symm = _
      rw [hME]
      ext a b
      simp only [krausApply, Matrix.submatrix_apply, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, id]
  · refine ⟨Fintype.card C, fun k => Matrix.of fun o p =>
      if p.1 = k then (V (e.symm k) : Matrix O O ℂ) o p.2 else 0, ?_, ?_⟩
    · unfold IsKrausFamily
      ext p q
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
      have hu : ∀ k, (star (V (e.symm k) : Matrix O O ℂ)) * (V (e.symm k) : Matrix O O ℂ) = 1 :=
        fun k => Matrix.mem_unitaryGroup_iff'.mp (V (e.symm k)).2
      obtain ⟨k1, o1⟩ := p
      obtain ⟨k2, o2⟩ := q
      rw [Finset.sum_eq_single k1]
      · by_cases hq : k2 = k1
        · subst hq
          have := congrFun (congrFun (hu k2) o1) o2
          simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at this
          simp only [if_true, Matrix.one_apply, Prod.mk.injEq, true_and]
          rw [← this]
        · simp [hq, Matrix.one_apply, Ne.symm hq]
      · intro k _ hk
        simp [Ne.symm hk]
      · simp
    · intro Y
      ext o o'
      simp [krausApply, classicalControlledUnitary, conjSuperop, Matrix.sum_apply,
        Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply, ite_mul,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single c (fun x _ hx => by simp [hx]) (by simp)]
      refine Finset.sum_congr rfl fun j _ => ?_
      erw [Matrix.mul_apply]
      rw [Finset.sum_mul]
      simp only [if_true]
  · intro Y
    ext a b
    have h := congrFun (congrFun (hclassical Y) (e.symm a)) (e.symm b)
    simp only [dephasing, Matrix.diagonal_apply, Matrix.submatrix_apply] at h ⊢
    rw [← h]
    simp [e.symm.injective.eq_iff]
  · intro X
    rw [← part1 X]
    simp only [resourceSim, classicalControlledUnitary, Matrix.submatrix_apply]
    exact Fintype.sum_equiv e.symm _ _ (fun k => rfl)
