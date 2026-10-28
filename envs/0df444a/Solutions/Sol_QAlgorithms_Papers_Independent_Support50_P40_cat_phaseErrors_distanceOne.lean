-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P40.cat_phaseErrors_distanceOne
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:22:22.450926+00:00
-- url     : https://prove2.me/submissions/5e6238f2-fe35-4176-824a-01b908ef3245

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40


namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- cat basis vector -/
def x5czK (m : ℕ) (b : Bool) : EuclideanSpace ℂ (Qubits (m + 1)) := ket (fun _ : Fin (m + 1) => b)

def x5czS (b : Bool) : ℂ := if b then -1 else 1

lemma x5cz_act_ket {n : ℕ} (E : Matrix (Qubits n) (Qubits n) ℂ) (x : Qubits n) (c : ℂ)
    (h : ∀ y, E y x = if y = x then c else 0) : act E (ket x) = c • ket x := by
  ext y
  simp only [act, ket, PiLp.smul_apply, smul_eq_mul]
  simp [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply, h]

lemma x5cz_act_add {n : ℕ} (E : Matrix (Qubits n) (Qubits n) ℂ) (u v : EuclideanSpace ℂ (Qubits n)) :
    act E (u + v) = act E u + act E v := by
  ext y; simp [act, Matrix.mulVec_add]

lemma x5cz_act_smul {n : ℕ} (E : Matrix (Qubits n) (Qubits n) ℂ) (c : ℂ) (u : EuclideanSpace ℂ (Qubits n)) :
    act E (c • u) = c • act E u := by
  ext y; simp [act, Matrix.mulVec_smul]

lemma x5cz_act_zero {n : ℕ} (E : Matrix (Qubits n) (Qubits n) ℂ) :
    act E 0 = 0 := by
  ext y; simp [act]

lemma x5cz_act_mul {n : ℕ} (A B : Matrix (Qubits n) (Qubits n) ℂ) (u : EuclideanSpace ℂ (Qubits n)) :
    act (A * B) u = act A (act B u) := by
  ext y; simp [act, Matrix.mulVec_mulVec]

lemma x5cz_mat_diag (P : Pauli) (hP : P = .I ∨ P = .Z) (u v : Bool) (h : u ≠ v) : P.mat u v = 0 := by
  rcases hP with rfl | rfl
  · simp [Pauli.mat, Matrix.one_apply, h]
  · simp [Pauli.mat, pauliZ, Matrix.diagonal_apply, h]

lemma x5cz_singleZ {m : ℕ} (a : Fin (m + 1)) (b : Bool) :
    act (singleZ a) (x5czK m b) = x5czS b • x5czK m b := by
  unfold x5czK
  apply x5cz_act_ket
  intro y
  simp only [singleZ, pauliOps, PauliString.toMatrix, Matrix.of_apply, ZMod.val_zero, pow_zero,
    one_mul]
  by_cases hy : y = fun _ => b
  · rw [if_pos hy, hy]
    rw [Finset.prod_eq_single a]
    · simp only [if_true, x5czS]
      cases b <;> simp [Pauli.mat, pauliZ, Matrix.diagonal_apply]
    · intro q _ hq; simp [hq, Pauli.mat]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [if_neg hy]
    obtain ⟨q, hq⟩ : ∃ q, y q ≠ b := by
      by_contra hc; push Not at hc; exact hy (funext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ q) ?_
    apply x5cz_mat_diag _ _ _ _ hq
    by_cases h : q = a
    · right; simp [h]
    · left; simp [h]

lemma x5cz_span_ind {m : ℕ} (P : EuclideanSpace ℂ (Qubits (m + 1)) → Prop)
    (h0 : P 0) (hadd : ∀ u v, P u → P v → P (u + v)) (hsmul : ∀ (c : ℂ) u, P u → P (c • u))
    (hb : ∀ b, P (x5czK m b)) : ∀ psi ∈ catSpace m, P psi := by
  intro psi hpsi
  unfold catSpace at hpsi
  induction hpsi using Submodule.span_induction with
  | mem x hx => obtain ⟨b, rfl⟩ := hx; exact hb b
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

lemma x5cz_on (m : ℕ) : Orthonormal ℂ (x5czK m) := by
  have := (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Qubits (m + 1))).comp
    (fun b : Bool => (fun _ : Fin (m + 1) => b)) (fun b b' h => congrFun h 0)
  exact this

lemma x5cz_rank (m : ℕ) : Module.finrank ℂ (catSpace m) = 2 := by
  unfold catSpace
  have h := finrank_span_eq_card (x5cz_on m).linearIndependent
  rw [Fintype.card_bool] at h
  exact h

lemma x5cz_norm (m : ℕ) (b : Bool) : ‖x5czK m b‖ = 1 := (x5cz_on m).1 b

lemma x5cz_mem (m : ℕ) (b : Bool) : x5czK m b ∈ catSpace m :=
  Submodule.subset_span ⟨b, rfl⟩

end

end QAlgorithms.Papers.Independent.Support50.P40


namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

lemma x5cz_inner_eig {m : ℕ} (E : Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ) (b : Bool) (c : ℂ)
    (h : act E (x5czK m b) = c • x5czK m b) : inner ℂ (x5czK m b) (act E (x5czK m b)) = c := by
  rw [h, inner_smul_right, inner_self_eq_norm_sq_to_K, x5cz_norm]; simp

lemma x5cz_d0 {n : ℕ} (E : Matrix (Qubits n) (Qubits n) ℂ) (hE : ActsOnAtMost 0 E) :
    ∃ c : ℂ, ∀ psi : EuclideanSpace ℂ (Qubits n), act E psi = c • psi := by
  obtain ⟨F, hF, k, w, M, hr, rfl⟩ := hE
  have hF0 : F = ∅ := Finset.card_eq_zero.1 (by omega)
  subst hF0
  have hk : k = 0 := by
    by_contra hk
    have := hr ⟨⟨0, by omega⟩, rfl⟩
    simp at this
  subst hk
  refine ⟨M (fun x => Fin.elim0 x) (fun x => Fin.elim0 x), fun psi => ?_⟩
  ext y
  have hrange : ∀ a : Fin n, a ∉ Set.range w := fun a ⟨x, _⟩ => Fin.elim0 x
  simp only [act, embedOp, Matrix.mulVec, dotProduct, Matrix.of_apply, PiLp.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single y]
  · rw [if_pos (fun _ _ => rfl)]
    congr 2 <;> exact Subsingleton.elim _ _
  · intro z _ hz
    rw [if_neg]; · simp
    intro hc; exact hz (funext fun a => (hc a (hrange a)).symm)
  · intro h; exact absurd (Finset.mem_univ y) h

lemma x5cz_dist (m : ℕ) : HasDistance (catSpace m) 1 := by
  refine ⟨fun E hE => ?_, ?_⟩
  · obtain ⟨c, hc⟩ := x5cz_d0 E hE
    refine ⟨c, fun psi _ hpsi => ?_⟩
    rw [hc, inner_smul_right, inner_self_eq_norm_sq_to_K, hpsi]; simp
  · let M : Matrix (Qubits 1) (Qubits 1) ℂ := Matrix.diagonal fun y => x5czS (y 0)
    refine ⟨embedOp M (wire1 0), ⟨{0}, by simp, 1, wire1 0, M, ?_, rfl⟩, ?_⟩
    · rintro _ ⟨x, rfl⟩; simp; rfl
    · rintro ⟨c, hc⟩
      have hact : ∀ b, act (embedOp M (wire1 0)) (x5czK m b) = x5czS b • x5czK m b := by
        intro b
        apply x5cz_act_ket
        intro y
        simp only [embedOp, Matrix.of_apply]
        by_cases hy : y = fun _ => b
        · subst hy
          rw [if_pos (fun _ _ => rfl)]
          simp [M, Matrix.diagonal_apply, wire1]
        · rw [if_neg hy]
          obtain ⟨q, hq⟩ : ∃ q, y q ≠ b := by
            by_contra hc; push Not at hc; exact hy (funext hc)
          by_cases h0 : q = 0
          · subst h0
            split_ifs
            · simp only [M, Matrix.diagonal_apply]
              rw [if_neg]
              intro he
              exact hq (congrFun he 0)
            · rfl
          · rw [if_neg]
            intro hc'
            exact hq (hc' q (by rintro ⟨x, hx⟩; simp [wire1] at hx; exact h0 hx.symm))
      have h1 := hc (x5czK m false) (x5cz_mem m false) (x5cz_norm m false)
      have h2 := hc (x5czK m true) (x5cz_mem m true) (x5cz_norm m true)
      rw [x5cz_inner_eig _ _ _ (hact false)] at h1
      rw [x5cz_inner_eig _ _ _ (hact true)] at h2
      simp [x5czS] at h1 h2
      rw [← h1] at h2; norm_num at h2

end

end QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Papers.Independent.Support50.P40
open scoped ComplexConjugate Matrix

theorem solution (m : ℕ) :
    Module.finrank ℂ (catSpace m) = 2 ∧ HasDistance (catSpace m) 1 ∧
    (∀ (a b : Fin (m + 1)) (psi : EuclideanSpace ℂ (Qubits (m + 1))),
      psi ∈ catSpace m → act (singleZ a) psi = act (singleZ b) psi) ∧
    (∀ (a b : Fin (m + 1)), a ≠ b →
      ∀ psi : EuclideanSpace ℂ (Qubits (m + 1)), psi ∈ catSpace m →
        act (singleZ a * singleZ b) psi = psi) := by
  refine ⟨x5cz_rank m, x5cz_dist m, ?_, ?_⟩
  · intro a b
    refine x5cz_span_ind _ (by simp [x5cz_act_zero]) ?_ ?_ ?_
    · intro u v hu hv; rw [x5cz_act_add, x5cz_act_add, hu, hv]
    · intro c u hu; rw [x5cz_act_smul, x5cz_act_smul, hu]
    · intro bb; rw [x5cz_singleZ, x5cz_singleZ]
  · intro a b _
    refine x5cz_span_ind _ (by simp [x5cz_act_zero]) ?_ ?_ ?_
    · intro u v hu hv; rw [x5cz_act_add, hu, hv]
    · intro c u hu; rw [x5cz_act_smul, hu]
    · intro bb
      rw [x5cz_act_mul, x5cz_singleZ, x5cz_act_smul, x5cz_singleZ, smul_smul]
      cases bb <;> simp [x5czS]

