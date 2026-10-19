-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.quantumHamming_errorDimension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T02:33:07.010987+00:00
-- url     : https://prove2.me/submissions/1a31a099-d422-4a25-8535-eac4e19e9391

import Definitions.Def_QAlgorithms_Defs_FTCircuit
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix ComplexConjugate
namespace CodeBoundsProof
private def tens {n : ℕ} (A : Fin n → Matrix Bool Bool ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ := fun y z => ∏ q, A q (y q) (z q)

private lemma tens_mul {n : ℕ} (A B : Fin n → Matrix Bool Bool ℂ) :
    tens A * tens B = tens (fun q => A q * B q) := by
  ext y z
  simp only [Matrix.mul_apply, tens, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun q b => A q (y q) b * B q b (z q)).symm

private lemma tens_star {n : ℕ} (A : Fin n → Matrix Bool Bool ℂ) :
    star (tens A) = tens (fun q => star (A q)) := by
  ext y z
  simp [tens, Matrix.star_apply]

private lemma mat_star (p : Pauli) : star p.mat = p.mat := by
  cases p <;> ext a b <;> cases a <;> cases b <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.star_apply]

private lemma tens_within {n : ℕ} (A : Fin n → Matrix Bool Bool ℂ)
    (F : Finset (Fin n)) (hA : ∀ i ∉ F, A i = 1) :
    ActsWithin F (tens A) := by
  classical
  let e : Fin F.card ≃ F := F.equivFin.symm
  let w : Fin F.card ↪ Fin n := ⟨fun i => (e i).1, fun i j h => e.injective (Subtype.ext h)⟩
  refine ⟨F.card, w, tens (fun i => A (w i)), ?_, ?_⟩
  · rintro i ⟨j, rfl⟩; exact (e j).2
  · ext y z
    simp only [embedOp, Matrix.of_apply, tens]
    by_cases h : ∀ i, i ∉ Set.range w → y i = z i
    · rw [if_pos h]
      have hr : Set.range w = (F : Set (Fin n)) := by
        ext i; constructor
        · rintro ⟨j,rfl⟩; exact (e j).2
        · intro hi; exact ⟨e.symm ⟨i,hi⟩, by simp [w]⟩
      have hp : (∏ i : Fin n, A i (y i) (z i)) = ∏ i ∈ F, A i (y i) (z i) := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro i _ hi
        rw [hA i hi, Matrix.one_apply, if_pos (h i (by simpa [hr] using hi))]
      rw [hp]
      exact (F.prod_attach (fun i => A i (y i) (z i))).symm.trans
        (Fintype.prod_equiv e.symm _ _ (by intro i; simp [w]))
    · rw [if_neg h]
      push Not at h
      obtain ⟨i,hi,hne⟩ := h
      have hnF : i ∉ F := by
        intro hF
        apply hi
        exact ⟨e.symm ⟨i,hF⟩, by simp [w]⟩
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by
        rw [hA i hnF, Matrix.one_apply, if_neg hne])

private lemma pauli_product_local {n t : ℕ} (a b : Fin n → Pauli)
    (ha : opsWeight a ≤ t) (hb : opsWeight b ≤ t) :
    ActsOnAtMost (2*t) ((pauliOps a)ᴴ * pauliOps b) := by
  classical
  let F := Finset.univ.filter (fun i => a i ≠ .I)
  let G := Finset.univ.filter (fun i => b i ≠ .I)
  have heq : (pauliOps a)ᴴ * pauliOps b = tens (fun i => (a i).mat * (b i).mat) := by
    have hp (o : Fin n → Pauli) : pauliOps o = tens (fun i => (o i).mat) := by
      ext y z; simp [pauliOps,PauliString.toMatrix,tens]
    rw [hp a,hp b]
    change star (tens (fun i => (a i).mat)) * tens (fun i => (b i).mat) = _
    rw [tens_star]
    simp only [mat_star, tens_mul]
  refine ⟨F ∪ G, (Finset.card_union_le F G).trans (by change F.card + G.card ≤ _; change opsWeight a + opsWeight b ≤ _; omega), ?_⟩
  rw [heq]
  apply tens_within
  intro i hi
  have h : a i = .I ∧ b i = .I := by simpa [F,G] using hi
  simp [h.1,h.2,Pauli.mat]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private lemma act_lin (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act A v = Matrix.toEuclideanLin A v := rfl
omit [DecidableEq ι] in
private lemma act_mul (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  simp only [act, Matrix.mulVec_mulVec, WithLp.ofLp_toLp]
private lemma inner_act (A : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ x (act Aᴴ y) = inner ℂ (act A x) y := by
  rw [act_lin, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_right _ _ _
omit [DecidableEq ι] in
private lemma unit_normalize (x : EuclideanSpace ℂ ι) (hx : x ≠ 0) :
    ‖((‖x‖ : ℂ)⁻¹) • x‖ = 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

private lemma detectable_cross (C : Submodule ℂ (EuclideanSpace ℂ ι))
    (E F : Matrix ι ι ℂ) (h : IsDetectable C (Eᴴ * F)) :
    ∃ c : ℂ, ∀ x ∈ C, ∀ y ∈ C,
      inner ℂ (act E x) (act F y) = c * inner ℂ x y := by
  obtain ⟨c,hc⟩ := h
  refine ⟨c, ?_⟩
  have diag : ∀ x ∈ C, inner ℂ (act E x) (act F x) = c * inner ℂ x x := by
    intro x hx
    by_cases hz : x = 0
    · simp [hz,act_lin]
    have hu := hc (((‖x‖ : ℂ)⁻¹) • x) (C.smul_mem _ hx) (unit_normalize x hz)
    rw [act_mul,inner_act] at hu
    simp only [act_lin, map_smul, inner_smul_left, inner_smul_right,
      map_inv₀, Complex.conj_ofReal] at hu
    rw [inner_self_eq_norm_sq_to_K x]
    have hn : (↑‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    field_simp [hn] at hu
    change inner ℂ (act E x) (act F x) = c * (↑‖x‖ : ℂ)^2
    change inner ℂ (act E x) (act F x) = _ at hu
    rw [hu]; ring
  intro x hx y hy
  have hp := diag (x+y) (C.add_mem hx hy)
  have hm := diag (x-y) (C.sub_mem hx hy)
  have hpi := diag (x+Complex.I • y) (C.add_mem hx (C.smul_mem _ hy))
  have hmi := diag (x-Complex.I • y) (C.sub_mem hx (C.smul_mem _ hy))
  simp only [act_lin, map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I] at hp hm hpi hmi
  simp only [act_lin]
  linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
    (hp - hm - Complex.I*hpi + Complex.I*hmi) / 4

end CodeBoundsProof
open CodeBoundsProof

theorem solution {n k d : ℕ}
    (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n)))
    (hC : IsQCode n k d C) (hnd : IsNondegenerate C ((d-1)/2)) :
    Fintype.card {o : Fin n → Pauli // opsWeight o ≤ (d-1)/2} * 2^k ≤ 2^n := by
  classical
  let t := (d-1)/2
  let E := {o : Fin n → Pauli // opsWeight o ≤ t}
  let b := stdOrthonormalBasis ℂ C
  have hpos : 0 < Module.finrank ℂ C := by rw [hC.1]; positivity
  let i₀ : Fin (Module.finrank ℂ C) := ⟨0,hpos⟩
  let v (i : Fin (Module.finrank ℂ C)) : EuclideanSpace ℂ (Qubits n) := b i
  have hv (i) : ‖v i‖ = 1 := b.orthonormal.1 i
  have hip (i j : Fin (Module.finrank ℂ C)) : inner ℂ (v i) (v j) = if i=j then 1 else 0 := by
    by_cases hij : i=j
    · subst j; simp [inner_self_eq_norm_sq_to_K,hv]
    · rw [if_neg hij]
      exact b.orthonormal.2 hij
  let g : Matrix E E ℂ := fun a a' => inner ℂ (act (pauliOps a.1) (v i₀)) (act (pauliOps a'.1) (v i₀))
  have hg : g.det ≠ 0 := hnd (v i₀) (b i₀).property (hv i₀)
  have hcross (a a' : E) (i j) :
      inner ℂ (act (pauliOps a.1) (v i)) (act (pauliOps a'.1) (v j)) =
        g a a' * (if i=j then 1 else 0) := by
    have hloc := pauli_product_local a.1 a'.1 a.2 a'.2
    have hlocal : ActsOnAtMost (d-1) ((pauliOps a.1)ᴴ * pauliOps a'.1) := by
      obtain ⟨F,hF,h⟩ := hloc
      exact ⟨F,hF.trans (by dsimp [t]; omega),h⟩
    obtain ⟨c,hc⟩ := detectable_cross C _ _ (hC.2 _ hlocal)
    have hzero := hc (v i₀) (b i₀).property (v i₀) (b i₀).property
    have hval : g a a' = c := by simpa [g,inner_self_eq_norm_sq_to_K,hv] using hzero
    rw [hc (v i) (b i).property (v j) (b j).property,hip,← hval]
  let f : E × Fin (Module.finrank ℂ C) → EuclideanSpace ℂ (Qubits n) :=
    fun z => act (pauliOps z.1.1) (v z.2)
  have hgram : Matrix.gram ℂ f = Matrix.blockDiagonal (fun _ : Fin (Module.finrank ℂ C) => g) := by
    ext ⟨a,i⟩ ⟨a',j⟩
    rw [Matrix.gram_apply,Matrix.blockDiagonal_apply]
    change inner ℂ (act (pauliOps a.1) (v i)) (act (pauliOps a'.1) (v j)) = _
    rw [hcross]
    split_ifs <;> simp_all
  have hdet : (Matrix.gram ℂ f).det ≠ 0 := by
    rw [hgram,Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => hg)
  have hdim := (Matrix.linearIndependent_of_det_gram_ne_zero hdet).fintype_card_le_finrank
  simpa [Fintype.card_prod,hC.1,finrank_euclideanSpace,Qubits] using hdim
