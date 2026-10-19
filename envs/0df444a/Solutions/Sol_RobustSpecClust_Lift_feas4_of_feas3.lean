-- Prove2me | solution 1 for RobustSpecClust.Lift.feas4_of_feas3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T08:54:31.024579+00:00
-- url     : https://prove2.me/submissions/41c7acc9-8072-491b-8486-aae68c31d47b

import Definitions.Def_RobustSpecClust_Lift_Setting
set_option autoImplicit false
open Matrix
noncomputable section
namespace RobustSpecClust.Lift

lemma row_zero_or_unit_core {N r : ℕ} (X : Matrix (Fin N) (Fin N) ℝ)
    (G : Matrix (Fin N) (Fin r) ℝ) (hX : X = G * G.transpose)
    (hbinary : ∀ i j, X i j = 0 ∨ X i j = 1) :
    ∀ i, G i = 0 ∨ ∑ k, G i k ^ 2 = 1 := by
  intro i
  have hi := hbinary i i
  rw [hX, Matrix.mul_apply] at hi
  simp only [Matrix.transpose_apply, ← sq] at hi
  rcases hi with hz | hu
  · left
    funext k
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (G i j))).mp hz k (Finset.mem_univ _)
    exact sq_eq_zero_iff.mp hk
  · exact Or.inr hu

lemma rows_eq_or_orthogonal_core {N r : ℕ} (X : Matrix (Fin N) (Fin N) ℝ)
    (G : Matrix (Fin N) (Fin r) ℝ) (hX : X = G * G.transpose)
    (hbinary : ∀ i j, X i j = 0 ∨ X i j = 1) :
    ∀ i j, G i ≠ 0 → G j ≠ 0 → G i = G j ∨ ∑ k, G i k * G j k = 0 := by
  intro i j hi hj
  have hui := (row_zero_or_unit_core X G hX hbinary i).resolve_left hi
  have huj := (row_zero_or_unit_core X G hX hbinary j).resolve_left hj
  have hij := hbinary i j
  rw [hX, Matrix.mul_apply] at hij
  simp only [Matrix.transpose_apply] at hij
  rcases hij with hz | ho
  · exact Or.inr hz
  · left
    have hsum : ∑ k, (G i k - G j k)^2 = 0 := by
      calc
        _ = (∑ k, G i k^2) + (∑ k, G j k^2) - 2*∑ k, G i k*G j k := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = 0 := by rw [hui,huj,ho]; norm_num
    funext k
    have : (G i k-G j k)^2=0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg (G i l-G j l))).mp hsum k (Finset.mem_univ _)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)

lemma assignment_row {N r : ℕ} (Z : Matrix (Fin N) (Fin r) ℝ) (hZ : Feas3 Z) (i : Fin N) :
    Z i = 0 ∨ ∃ k, Z i = Pi.single k 1 := by
  classical
  by_cases hz : Z i = 0
  · exact Or.inl hz
  right
  obtain ⟨k,hk⟩ : ∃ k, Z i k ≠ 0 := Function.ne_iff.mp hz
  have hk1 := (hZ.1 i k).resolve_left hk
  refine ⟨k, ?_⟩
  funext l
  by_cases hl : l=k
  · subst l; simpa using hk1
  have hln : 0 ≤ Z i l := by rcases hZ.1 i l with h|h <;> simp [h]
  have hsum : Z i k + Z i l ≤ ∑ j, Z i j := by
    calc
      Z i k + Z i l = ∑ j ∈ ({k,l}:Finset (Fin r)), Z i j := by simp [hl,Ne.symm hl]
      _ ≤ ∑ j, Z i j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intro j _ _; rcases hZ.1 i j with h|h <;> simp [h])
  have : Z i l=0 := by linarith [hZ.2 i]
  simp [Pi.single_apply,hl,this]

lemma feas4_of_feas3_core {N r : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (γ : ℝ)
    (Z : Matrix (Fin N) (Fin r) ℝ) (hZ : Feas3 Z) :
    Feas4 r (Z * Z.transpose) ∧ obj4 K γ (Z * Z.transpose) = obj3 K γ Z := by
  classical
  refine ⟨⟨?_,?_,?_⟩,rfl⟩
  · intro i j
    rcases assignment_row Z hZ i with hi | ⟨k,hi⟩
    · left; simp [Matrix.mul_apply,hi]
    · rcases assignment_row Z hZ j with hj | ⟨l,hj⟩
      · left; simp [Matrix.mul_apply,hj]
      · by_cases hkl : k=l
        · right; simp [Matrix.mul_apply,Matrix.transpose_apply,hi,hj,hkl,Pi.single_apply]
        · left; simp [Matrix.mul_apply,Matrix.transpose_apply,hi,hj,Pi.single_apply,hkl,Ne.symm hkl]
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose Z
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width Z)

lemma square_factor {N : ℕ} (X : Matrix (Fin N) (Fin N) ℝ) (hp : X.PosSemidef) :
    ∃ G : Matrix (Fin N) (Fin N) ℝ, X=G*G.transpose := by
  open scoped MatrixOrder in
    obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hp.nonneg
    refine ⟨B.transpose, ?_⟩
    simpa only [star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial,transpose_transpose] using hB

lemma gram_entry {N r : ℕ} (X : Matrix (Fin N) (Fin N) ℝ)
    (G : Matrix (Fin N) (Fin r) ℝ) (hX : X = G*G.transpose)
    (hb : ∀ i j, X i j=0 ∨ X i j=1) (i j : Fin N) :
    X i j = if G i=0 then 0 else if G i=G j then 1 else 0 := by
  classical
  by_cases hi : G i=0
  · simp [hi,hX,Matrix.mul_apply]
  rw [if_neg hi]
  by_cases he : G i=G j
  · rw [if_pos he,hX,Matrix.mul_apply]
    simpa only [Matrix.transpose_apply,← he,← sq] using
      (row_zero_or_unit_core X G hX hb i).resolve_left hi
  rw [if_neg he,hX,Matrix.mul_apply]
  by_cases hj : G j=0
  · simp [Matrix.transpose_apply,hj]
  exact (rows_eq_or_orthogonal_core X G hX hb i j hi hj).resolve_left he

lemma assignment_factor {N r : ℕ} (X : Matrix (Fin N) (Fin N) ℝ)
    (hX : Feas4 r X) : ∃ Z : Matrix (Fin N) (Fin r) ℝ, Feas3 Z ∧ X=Z*Z.transpose := by
  classical
  obtain ⟨G,hG⟩ := square_factor X hX.2.1
  let V : Finset (Fin N → ℝ) := (Finset.univ.image G).erase 0
  have hV (v : Fin N → ℝ) : v ∈ V ↔ v≠0 ∧ ∃ i, G i=v := by
    change (v ∈ (Finset.univ.image G).erase 0) ↔ _
    rw [Finset.mem_erase]
    constructor
    · rintro ⟨hn,hm⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
      exact ⟨hn,i,hi⟩
    · rintro ⟨hn,i,hi⟩
      exact ⟨hn,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩⟩
  choose rep hrep using fun v : ↥V => ((hV v).mp v.property).2
  have hvne (v : ↥V) : (v : Fin N → ℝ) ≠ 0 := ((hV v).mp v.property).1
  have hminor : X.submatrix rep rep = (1 : Matrix ↥V ↥V ℝ) := by
    ext v w
    rw [Matrix.submatrix_apply,gram_entry X G hG hX.1]
    simp only [hrep,if_neg (hvne v),Matrix.one_apply,Subtype.coe_inj]
  have hcard : Fintype.card ↥V ≤ r := by
    have hh := Matrix.rank_submatrix_le X rep rep
    rw [hminor,Matrix.rank_one] at hh
    exact hh.trans hX.2.2
  obtain ⟨e⟩ : Nonempty (↥V ↪ Fin r) := Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  let Z : Matrix (Fin N) (Fin r) ℝ := fun i =>
    if h : G i ∈ V then Pi.single (e ⟨G i,h⟩) 1 else 0
  have hmem (i : Fin N) : G i ∈ V ↔ G i≠0 := by rw [hV]; exact and_iff_left ⟨i,rfl⟩
  have hZ : Feas3 Z := by
    constructor
    · intro i k
      by_cases hi : G i ∈ V
      · simp only [Z,dif_pos hi,Pi.single_apply]
        split_ifs <;> simp
      · simp [Z,hi]
    · intro i
      by_cases hi : G i ∈ V <;> simp [Z,hi]
  refine ⟨Z,hZ,?_⟩
  ext i j
  rw [gram_entry X G hG hX.1]
  change (if G i=0 then 0 else if G i=G j then 1 else 0) = ∑ k, Z i k*Z j k
  by_cases hi : G i ∈ V
  · have hi0 := (hmem i).mp hi
    rw [if_neg hi0]
    by_cases hj : G j ∈ V
    · have heq : e ⟨G i,hi⟩ = e ⟨G j,hj⟩ ↔ G i=G j := by
        rw [e.injective.eq_iff,Subtype.ext_iff]
      simp only [Matrix.mul_apply,Matrix.transpose_apply,Z,dif_pos hi,dif_pos hj]
      simp only [Pi.single_apply]
      simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
      exact if_congr heq.symm rfl rfl
    · have hj0 : G j=0 := not_ne_iff.mp ((hmem j).not.mp hj)
      rw [if_neg (by simpa [hj0] using hi0)]
      simp only [Z,dif_neg hj,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  · have hi0 : G i=0 := not_ne_iff.mp ((hmem i).not.mp hi)
    rw [if_pos hi0]
    simp only [Z,dif_neg hi,Pi.zero_apply,zero_mul,Finset.sum_const_zero]

lemma proposition_1_core {N r : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (γ : ℝ)
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : IsOpt4 K γ r X) :
    ∃ G : Matrix (Fin N) (Fin r) ℝ, X=G*G.transpose ∧
      ∃ O ∈ Matrix.orthogonalGroup (Fin r) ℝ,
        IsOpt3 K γ (G*O) ∧ obj3 K γ (G*O)=obj4 K γ X := by
  obtain ⟨Z,hZ,hXZ⟩ := assignment_factor X hX.1
  refine ⟨Z,hXZ,1,?_,?_⟩
  · exact (Matrix.orthogonalGroup (Fin r) ℝ).one_mem
  simp only [Matrix.mul_one]
  have heq : obj3 K γ Z=obj4 K γ X := by rw [hXZ]; rfl
  refine ⟨⟨hZ,?_⟩,heq⟩
  intro Z' hZ'
  have hf := feas4_of_feas3_core K γ Z' hZ'
  rw [heq,← hf.2]
  exact hX.2 _ hf.1
end RobustSpecClust.Lift


open RobustSpecClust.Lift

theorem solution {N r : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (γ : ℝ)
    (Z : Matrix (Fin N) (Fin r) ℝ) (hZ : Feas3 Z) :
    Feas4 r (Z * Z.transpose) ∧ obj4 K γ (Z * Z.transpose) = obj3 K γ Z := by exact feas4_of_feas3_core K γ Z hZ


#print axioms solution
